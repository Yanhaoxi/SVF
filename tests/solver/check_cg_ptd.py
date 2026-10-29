#!/usr/bin/env python3
"""Check CG storage backends, including late recursion and cached deltas."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile


MODES = {
    "cg-wave": ["-cgfspta"],
    "cg-sfr": ["-cgfspta", "-cg-sfr=true"],
    "lopa-cg-wave": ["-lopa-cgfspta"],
    "lopa-cg-sfr": ["-lopa-cgfspta", "-cg-sfr=true"],
}


def check(wpa, extapi, source, mode, backing, recursive, directory):
    directory.mkdir(parents=True)
    if not recursive:
        source = source.replace("@dispatch = global ptr @recur",
                                "@dispatch = global ptr @leaf")
    case = directory / "case.ll"
    case.write_text(source)
    command = [str(wpa), *MODES[mode], f"-ptd={backing}",
               "-node-alloc-strat=dense", "-ff-eq-base=true", "-dump-pag",
               "-print-pts", f"-extapi={extapi}", str(case)]
    result = subprocess.run(command, cwd=directory, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=60, check=False)
    (directory / "analysis.log").write_text(result.stdout)
    (directory / "command.json").write_text(json.dumps(command, indent=2) + "\n")
    result.check_returncode()
    final = result.stdout.rsplit("Pointer Analysis Stat", 1)[-1]
    rows = re.findall(r"NodeID\s+(\d+)\s+PointsTo:\s*\{([^}]*)\}", final)
    points = {int(node): sorted(map(int, re.findall(r"\d+", values)))
              for node, values in rows}
    assert points and len(points) == len(rows), "Missing or duplicate final points-to rows"
    dot = (directory / "svfir_initial.dot").read_text()

    def node(pattern):
        matches = re.findall(pattern, dot)
        assert len(matches) == 1, (pattern, matches)
        return int(matches[0])

    before = node(r"GlobalObjVar ID: (\d+)\\n @before =")
    after = node(r"GlobalObjVar ID: (\d+)\\n @after =")
    checked = node(r"ValVar ID: (\d+)\\n\s+%checked = call")
    expected = {before, after} if recursive else {after}
    assert set(points[checked]) == expected, (mode, backing, recursive, points[checked], expected)

    if backing == "persistent":
        # Preanalysis has a separate cache. Check the final CG cache: the old
        # Cell::pts/sent solver recorded no delta operations in this cache.
        cache = result.stdout.rsplit("Persistent Points-To Cache Statistics:", 1)[-1]
        complements = re.search(r"(?m)^TotalComplements\s+(\d+)", cache)
        assert complements and int(complements[1]) > 0, "CG deltas bypass the persistent cache"
    return points


def run(args, output):
    source = Path(__file__).with_name("indirect_recursion.ll").read_text()
    comparisons = []
    for mode in args.mode or MODES:
        for recursive in (False, True):
            results = {}
            for backing in ("mutable", "persistent"):
                directory = output / mode / str(recursive) / backing
                results[backing] = check(args.wpa.resolve(), args.extapi.resolve(),
                                         source, mode, backing, recursive, directory)
            assert results["mutable"] == results["persistent"], (mode, recursive)
            comparisons.append({"mode": mode, "recursive": recursive, "points_equal": True})
    (output / "summary.json").write_text(json.dumps(comparisons, indent=2) + "\n")
    print(f"PASS: {len(comparisons)} full-set comparisons, independent recursion checks, persistent deltas")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("wpa", type=Path)
    parser.add_argument("--extapi", type=Path, required=True)
    parser.add_argument("--mode", action="append", choices=MODES)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=True)
        run(args, args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="cg-ptd-test-") as directory:
            run(args, Path(directory))


if __name__ == "__main__":
    main()
