#!/usr/bin/env python3
"""Check the LOPA object lower-bound switch and the independent pure CG frontend."""
import argparse
from pathlib import Path
import tempfile

from check_empty_target_store import check


def run(wpa, extapi, output, backing="mutable"):
    source = Path(__file__).with_name("empty_target_store.ll").read_text()
    policies = [
        ("default", (), True),
        ("enabled", ("-lopa-obj-fs-lower-bound=true",), True),
        ("disabled", ("-lopa-obj-fs-lower-bound=false",), False),
    ]
    for analysis, sfr, backend in (("-lopa", False, "pus"),
                                   ("-lopa-cgfspta", False, "wave"),
                                   ("-lopa-cgfspta", True, "sfr")):
        for name, flags, retained in policies:
            if sfr:
                flags = (*flags, "-cg-sfr=true")
            for empty in (True, False):
                for uncompressed in (False, True):
                    directory = output / backend / name / f"{empty}-{uncompressed}"
                    check(wpa, extapi, source, empty, uncompressed, directory,
                          analysis, flags, expect_retained_before=retained,
                          backing=backing)
        # The offline lower-bound switch does not change the pure CG frontend.
        if analysis == "-lopa":
            continue
        flags = ("-lopa-obj-fs-lower-bound=true",)
        if sfr:
            flags += ("-cg-sfr=true",)
        for empty in (True, False):
            check(wpa, extapi, source, empty, False,
                  output / backend / "pure-cg" / str(empty), "-cgfspta", flags,
                  backing=backing)


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
    print("PASS: lower bound default/on/off, PUS and CG backends, pure CG unchanged")


if __name__ == "__main__":
    main()
