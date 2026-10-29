#!/usr/bin/env python3
"""Check the optional LOPA object lower-bound rule against CG's deferred default."""
import argparse
from pathlib import Path
import subprocess
import tempfile

from check_empty_target_store import check


def run(wpa, extapi, output, backing="mutable"):
    source = Path(__file__).with_name("empty_target_store.ll").read_text()
    policies = [
        ("default", (), False),
        ("deferred", ("-lopa-cg-store-policy=deferred",), False),
        ("object-lower-bound", ("-lopa-cg-store-policy=object-lower-bound",), True),
        ("lower-bound-disabled", ("-lopa-cg-store-policy=object-lower-bound",
                                  "-lopa-obj-fs-lower-bound=false"), False),
    ]
    for sfr in (False, True):
        backend = "sfr" if sfr else "wave"
        for name, flags, retained in policies:
            if sfr:
                flags = (*flags, "-cg-sfr=true")
            for empty in (True, False):
                for uncompressed in (False, True):
                    directory = output / backend / name / f"{empty}-{uncompressed}"
                    check(wpa, extapi, source, empty, uncompressed, directory,
                          "-lopa-cgfspta", flags, expect_retained_before=retained,
                          backing=backing)
        # The adapter option cannot change the uncompressed CG frontend.
        flags = ("-lopa-cg-store-policy=object-lower-bound",)
        if sfr:
            flags += ("-cg-sfr=true",)
        for empty in (True, False):
            check(wpa, extapi, source, empty, False,
                  output / backend / "pure-cg" / str(empty), "-cgfspta", flags,
                  backing=backing)

    output.mkdir(parents=True, exist_ok=True)
    invalid = subprocess.run([str(wpa), "-lopa-cgfspta",
                              "-lopa-cg-store-policy=unknown"], text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             timeout=60, check=False)
    (output / "invalid-option.log").write_text(invalid.stdout)
    assert invalid.returncode != 0, invalid.stdout
    assert "Bad value for: lopa-cg-store-policy" in invalid.stdout, invalid.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("wpa", type=Path)
    parser.add_argument("--extapi", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--ptd", choices=("mutable", "persistent"), default="mutable")
    args = parser.parse_args()
    wpa, extapi = args.wpa.resolve(), args.extapi.resolve()
    if args.output:
        run(wpa, extapi, args.output.resolve(), args.ptd)
    else:
        with tempfile.TemporaryDirectory(prefix="cg-store-policy-") as temporary:
            run(wpa, extapi, Path(temporary), args.ptd)
    print("PASS: deferred and object-lower-bound policies, both backends, invalid value rejected")


if __name__ == "__main__":
    main()
