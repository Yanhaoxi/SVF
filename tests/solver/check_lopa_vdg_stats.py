#!/usr/bin/env python3
"""Check streamed VDG summaries and ensure diagnostics preserve final facts."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile


def summaries(text):
    result = []
    for section in text.split('# VDG stats\n')[1:]:
        row, histogram = {}, {}
        for line in section.splitlines():
            if not line.startswith('  '):
                break
            field = re.fullmatch(r'  (\w+): ([\d.eE+-]+)', line)
            bucket = re.fullmatch(r'    (\d+) : (\d+)', line)
            if field:
                row[field[1]] = float(field[2])
            elif bucket:
                histogram[int(bucket[1])] = int(bucket[2])
        assert row['graphs'] == sum(histogram.values()), (row, histogram)
        assert row['total_supernodes'] == sum(n * count for n, count in histogram.items())
        assert row['total_edges'] == row['solid_edges'] + row['virtual_edges']
        assert row['load_consume_supernodes'] <= row['total_supernodes']
        assert row['min_supernodes'] == min(histogram, default=0)
        assert row['max_supernodes'] == max(histogram, default=0)
        average = row['total_supernodes'] / row['graphs'] if row['graphs'] else 0
        assert abs(row['avg_supernodes'] - average) <= 1e-5 * max(1, average)
        result.append(row)
    return result


def run(args, output):
    source = Path(__file__).with_name('indirect_recursion.ll').resolve()
    cases = [
        ('pus', ['-lopa']),
        ('pus-uncompressed', ['-lopa', '-lopa-no-offline=true']),
        ('cg-wave', ['-lopa-cgfspta']),
        ('cg-sfr', ['-lopa-cgfspta', '-cg-sfr=true']),
        ('vsfs', ['-lopa-vsfs']),
    ]
    records = []
    for name, flags in cases:
        outputs = []
        for enabled in (False, True):
            command = [str(args.wpa), *flags, '-ptd=persistent', '-node-alloc-strat=dense',
                       '-print-pts',
                       f'-extapi={args.extapi}', f'-vdg-stat={str(enabled).lower()}', str(source)]
            result = subprocess.run(command, cwd=output, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, timeout=120, check=True)
            (output / f'{name}-{enabled}.log').write_text(result.stdout)
            final = result.stdout.rsplit('Pointer Analysis Stat', 1)[-1]
            points = re.findall(r'NodeID\s+(\d+)\s+PointsTo:\s*\{([^}]*)\}', final)
            assert points, name
            outputs.append({node: sorted(values.split()) for node, values in points})
            blocks = summaries(result.stdout)
            assert bool(blocks) == enabled, (name, enabled)
            if enabled:
                assert blocks[0]['graphs'] > 0, name
                if flags[0] == '-lopa':
                    counts = dict(re.findall(r'^(PUS\w+) (\d+)$', result.stdout, re.MULTILINE))
                    assert blocks[0]['total_supernodes'] == int(counts['PUSNodes']) - int(counts['PUSValueBindings'])
                records.append({'name': name, 'command': command, 'vdg': blocks[0]})
        assert outputs[0] == outputs[1], f'{name}: statistics changed points-to results'
    compressed = [row['vdg'] for row in records if row['name'] != 'pus-uncompressed']
    assert all(row == compressed[0] for row in compressed), 'backends disagree on the same offline graphs'

    empty = output / 'empty.ll'
    empty.write_text('define i32 @main() { ret i32 0 }\n')
    command = [str(args.wpa), '-lopa', '-vdg-stat', f'-extapi={args.extapi}', str(empty)]
    result = subprocess.run(command, cwd=output, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=120, check=True)
    (output / 'empty.log').write_text(result.stdout)
    assert summaries(result.stdout)[0]['graphs'] == 0
    (output / 'summary.json').write_text(json.dumps({'passed': True, 'cases': records,
                                                   'empty_graph_summary': True}, indent=2) + '\n')
    print('PASS: five VDG summaries, unchanged facts, backend agreement, empty graph summary')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('wpa', type=Path)
    parser.add_argument('--extapi', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    args.wpa, args.extapi = args.wpa.resolve(), args.extapi.resolve()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=True)
        run(args, args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='lopa-vdg-stat-') as directory:
            run(args, Path(directory))


if __name__ == '__main__':
    main()
