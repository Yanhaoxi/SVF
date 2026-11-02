#!/usr/bin/env python3
"""Check Store preservation for empty targets and a nonempty weak-update control."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile


def check(wpa, extapi, source, empty, uncompressed, directory,
          analysis="-lopa-cgfspta", extra_flags=(), expect_retained_before=None,
          backing="mutable"):
    if expect_retained_before is None:
        expect_retained_before = (analysis in ("-lopa", "-lopa-cgfspta", "-lopa-vsfs")
                                  and "-lopa-obj-fs-lower-bound=false" not in extra_flags)
    if not empty:
        source = source.replace("  store ptr null, ptr %slot\n", "")
    directory.mkdir(parents=True, exist_ok=True)
    case = directory / "case.ll"
    case.write_text(source)
    command = [str(wpa), analysis, *extra_flags, f"-ptd={backing}",
               "-node-alloc-strat=dense", "-ff-eq-base=true", "-dump-pag",
               "-print-pts", f"-extapi={extapi}", str(case)]
    if uncompressed:
        command.insert(2, "-lopa-no-offline=true")
    result = subprocess.run(command, cwd=directory, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=60, check=False)
    (directory / "analysis.log").write_text(result.stdout)
    (directory / "command.json").write_text(json.dumps(command, indent=2) + "\n")
    result.check_returncode()
    dot = (directory / "svfir_initial.dot").read_text()

    def node(pattern):
        matches = re.findall(pattern, dot)
        assert len(matches) == 1, (pattern, matches)
        return int(matches[0])

    def points(ident):
        dumps = re.findall(rf"NodeID {ident}\s+PointsTo: \{{([^}}]*)\}}", result.stdout)
        assert len(dumps) == 2, (ident, dumps)
        return [{int(x) for x in group.split() if x != "empty"} for group in dumps]

    before = node(r"GlobalObjVar ID: (\d+)\\n @before =")
    after = node(r"GlobalObjVar ID: (\d+)\\n @after =")
    array = node(r"GlobalObjVar ID: (\d+)\\n @array =")
    q = node(r"ValVar ID: (\d+)\\n\s+%q = load")
    observed = node(r"ValVar ID: (\d+)\\n\s+%observed = load")
    q_preanalysis, q_final = points(q)
    assert array in q_preanalysis, q_preanalysis
    assert q_final == (set() if empty else {array}), q_final
    actual = points(observed)[-1]
    expected = ({before} if expect_retained_before else set()) if empty else {before, after}
    assert actual == expected, (
        f"empty={empty}, uncompressed={uncompressed}: expected {expected}, got {actual}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("wpa", type=Path)
    parser.add_argument("--extapi", type=Path, required=True)
    parser.add_argument("--analysis", default="-lopa-cgfspta")
    parser.add_argument("--flag", action="append", default=[])
    parser.add_argument("--output", type=Path)
    parser.add_argument("--ptd", choices=("mutable", "persistent"), default="mutable")
    args = parser.parse_args()
    source = Path(__file__).with_name("empty_target_store.ll").read_text()

    def run(output):
        for empty in (True, False):
            for uncompressed in (False, True):
                directory = output / f"empty-{empty}-uncompressed-{uncompressed}"
                check(args.wpa.resolve(), args.extapi.resolve(), source,
                      empty, uncompressed, directory, args.analysis, args.flag,
                      backing=args.ptd)

    if args.output:
        run(args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="cg-empty-store-") as temporary:
            run(Path(temporary))
    print("PASS: empty Store target and nonempty control, compressed and uncompressed")


if __name__ == "__main__":
    main()
