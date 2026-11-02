#!/usr/bin/env python3
"""Check pass-profile output and unchanged points-to sets and actual VDGs."""
import argparse
import itertools
import json
from pathlib import Path
import re
import subprocess
import tempfile

from check_lopa_vdg_stats import summaries


MODES = {
    'pus': ['-lopa'],
    'cg-wave': ['-lopa-cgfspta'],
    'cg-sfr': ['-lopa-cgfspta', '-cg-sfr=true'],
    'vsfs': ['-lopa-vsfs'],
}
CONFIGS = {
    'default': [],
    'lower-bound-off': ['-lopa-obj-fs-lower-bound=false', '-vdg-pass-order=B'],
    'uncompressed': ['-lopa-no-offline=true'],
}
PROFILES = {'coverage': 'on', 'sweep': 'kill=1,0;order=B,SPC'}


def execute(wpa, extapi, source, flags, directory, vdg_stat=True):
    directory.mkdir(parents=True, exist_ok=True)
    command = [str(wpa), *flags, '-node-alloc-strat=dense', '-ff-eq-base=true',
               f'-vdg-stat={str(vdg_stat).lower()}', '-print-pts',
               f'-extapi={extapi}', str(source)]
    result = subprocess.run(command, cwd=directory, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=60)
    (directory / 'command.json').write_text(json.dumps(command, indent=2) + '\n')
    (directory / 'analysis.log').write_text(result.stdout)
    result.check_returncode()
    return result.stdout


def points(text):
    # Preanalysis also prints points-to sets; compare the final analysis only.
    final = text.rsplit('Pointer Analysis Stat', 1)
    assert len(final) == 2, 'missing final analysis statistics'
    rows = re.findall(r'NodeID\s+(\d+)\s+PointsTo:\s*\{([^}]*)\}', final[-1])
    assert rows, 'missing final points-to sets'
    return {int(node): sorted(int(v) for v in values.split() if v != 'empty')
            for node, values in rows}


def profile_rows(text):
    # Pass durations vary between runs; all counts and output fields must agree.
    return sorted(re.sub(r' time:[^\s]+', '', line)
                  for line in text.splitlines() if line.startswith('vdg.passprofile.'))


def check_profile(text, spec):
    rows = profile_rows(text)
    assert any(line.startswith('vdg.passprofile.step1.summary') for line in rows)
    assert any(line.startswith('vdg.passprofile.step5.summary') for line in rows)
    configs = re.findall(r'^vdg\.passprofile\.config\.summary config=kill:([01]),order:(\w+)',
                         text, re.MULTILINE)
    if spec == 'on':
        assert not configs, configs
    else:
        expected = set(itertools.product(('1', '0'), ('B', 'SPC', 'S', 'SP')))
        assert len(configs) == len(expected) and set(configs) == expected, configs
        passes = re.findall(r'^vdg\.passprofile\.config\.pass .* time:([\d.eE+-]+)$',
                            text, re.MULTILINE)
        assert len(passes) == 8 and all(float(value) >= 0 for value in passes), passes
    if '# VDG stats' in text:
        assert text.index('vdg.passprofile.') < text.index('# VDG stats')
    return rows


def run(args, output):
    fixtures = Path(__file__).resolve().parent
    recursion = (fixtures / 'indirect_recursion.ll').read_text()
    nonrecursive = output / 'nonrecursive.ll'
    nonrecursive.write_text(recursion.replace('@dispatch = global ptr @recur',
                                             '@dispatch = global ptr @leaf'))
    sources = {
        'recursion': fixtures / 'indirect_recursion.ll',
        'nonrecursive': nonrecursive,
        'empty-target': fixtures / 'empty_target_store.ll',
    }
    legacy = {}
    records = []
    cases = itertools.product(sources.items(), MODES.items(),
                              ('mutable', 'persistent'), CONFIGS.items())
    for (fixture, source), (mode, mode_flags), backing, (config, config_flags) in cases:
        name = f'{fixture}/{mode}/{backing}/{config}'
        directory = output / name
        flags = [*mode_flags, f'-ptd={backing}', *config_flags]
        baseline = execute(args.wpa, args.extapi, source, flags, directory / 'off')
        expected_points, expected_vdg = points(baseline), summaries(baseline)
        assert expected_vdg and expected_vdg[0]['graphs'] > 0, name
        assert not profile_rows(baseline), name
        if args.reference_wpa:
            reference = execute(args.reference_wpa, args.extapi, source, flags,
                                directory / 'reference-off')
            assert points(reference) == expected_points, f'{name}: baseline facts changed'
            assert summaries(reference) == expected_vdg, f'{name}: baseline VDG changed'

        for profile, spec in PROFILES.items():
            profiled = execute(args.wpa, args.extapi, source,
                               [*flags, f'-vdg-pass-profile={spec}'], directory / profile)
            rows = check_profile(profiled, spec)
            assert points(profiled) == expected_points, f'{name}/{profile}: facts changed'
            assert summaries(profiled) == expected_vdg, f'{name}/{profile}: VDG changed'
            if args.reference_wpa:
                # The previous VSFS adapter still reaches the original profiler.
                key = (fixture, backing, config, profile)
                if key not in legacy:
                    reference = execute(args.reference_wpa, args.extapi, source,
                                        ['-lopa-vsfs', f'-ptd={backing}', *config_flags,
                                         f'-vdg-pass-profile={spec}'],
                                        output / 'legacy' / fixture / backing / config / profile)
                    legacy[key] = profile_rows(reference)
                assert rows == legacy[key], f'{name}/{profile}: legacy statistics changed'
        records.append({'case': name, 'points_equal': True, 'vdg_equal': True})

    empty = output / 'empty.ll'
    empty.write_text('define i32 @main() { ret i32 0 }\n')
    for mode, flags in MODES.items():
        baseline = execute(args.wpa, args.extapi, empty, flags, output / 'empty' / mode / 'off')
        for profile, spec in PROFILES.items():
            text = execute(args.wpa, args.extapi, empty,
                           [*flags, f'-vdg-pass-profile={spec}'], output / 'empty' / mode / profile)
            check_profile(text, spec)
            blocks = summaries(text)
            assert blocks == summaries(baseline) and all(row['graphs'] == 0 for row in blocks)
            assert points(text) == points(baseline)

        baseline = execute(args.wpa, args.extapi, sources['recursion'], flags,
                           output / 'without-vdg-stat' / mode / 'off', vdg_stat=False)
        for profile, spec in PROFILES.items():
            text = execute(args.wpa, args.extapi, sources['recursion'],
                           [*flags, f'-vdg-pass-profile={spec}'],
                           output / 'without-vdg-stat' / mode / profile, vdg_stat=False)
            check_profile(text, spec)
            assert not summaries(text)
            assert points(text) == points(baseline)

    (output / 'summary.json').write_text(json.dumps({
        'passed': True, 'cases': records, 'empty_graph_runs': 8, 'without_vdg_stat_runs': 8,
        'legacy_statistics_equal': bool(args.reference_wpa),
    }, indent=2) + '\n')
    print(f'PASS: {len(records)} cases, coverage/sweep preserve facts and VDGs, '
          '8 empty-graph runs, 8 runs without -vdg-stat'
          + (', legacy statistics unchanged' if args.reference_wpa else ''))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('wpa', type=Path)
    parser.add_argument('--extapi', type=Path, required=True)
    parser.add_argument('--reference-wpa', type=Path,
                        help='optional pre-change binary for legacy statistics comparison')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    args.wpa, args.extapi = args.wpa.resolve(), args.extapi.resolve()
    if args.reference_wpa:
        args.reference_wpa = args.reference_wpa.resolve()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=True)
        run(args, args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='vdg-pass-profile-') as directory:
            run(args, Path(directory))


if __name__ == '__main__':
    main()
