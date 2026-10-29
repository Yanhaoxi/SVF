#!/usr/bin/env python3
"""Check late recursion invalidates strong updates, with a nonrecursive control."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile


def check(wpa, extapi, source, recursive, uncompressed, directory, analysis="-lopa", extra_flags=()):
    if not recursive:
        source = source.replace("@dispatch = global ptr @recur",
                                "@dispatch = global ptr @leaf")
    case = directory / "case.ll"
    case.write_text(source)
    command = [str(wpa), analysis, "-ptd=mutable", "-node-alloc-strat=dense",
               "-ff-eq-base=true", "-dump-pag", "-print-pts",
               f"-extapi={extapi}", str(case)]
    command[2:2] = extra_flags
    if uncompressed:
        command.insert(2, "-lopa-no-offline")
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

    before = node(r"GlobalObjVar ID: (\d+)\\n @before =")
    after = node(r"GlobalObjVar ID: (\d+)\\n @after =")
    checked = node(r"ValVar ID: (\d+)\\n\s+%checked = call")
    # The log contains Andersen's dump followed by LOPA's dump; keep the last.
    dumps = re.findall(rf"NodeID {checked}\s+PointsTo: \{{([^}}]*)\}}", result.stdout)
    assert len(dumps) == 2, result.stdout
    actual = {int(x) for x in dumps[-1].split() if x != "empty"}
    expected = {before, after} if recursive else {after}
    assert actual == expected, (
        f"recursive={recursive}, uncompressed={uncompressed}: "
        f"expected {expected}, got {actual}\n{result.stdout}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("wpa", type=Path)
    parser.add_argument("--extapi", type=Path, required=True)
    parser.add_argument("--analysis", default="-lopa")
    parser.add_argument("--flag", action="append", default=[])
    args = parser.parse_args()
    source = Path(__file__).with_name("indirect_recursion.ll").read_text()
    with tempfile.TemporaryDirectory(prefix="lopa-recursion-test-") as temporary:
        for recursive in (True, False):
            for uncompressed in (False, True):
                directory = Path(temporary) / f"{recursive}-{uncompressed}"
                directory.mkdir()
                check(args.wpa.resolve(), args.extapi.resolve(), source,
                      recursive, uncompressed, directory, args.analysis, args.flag)
    print("PASS: late recursion and nonrecursive control, compressed and uncompressed")


if __name__ == "__main__":
    main()
