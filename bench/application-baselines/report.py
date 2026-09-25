#!/usr/bin/env python3
"""Render recorded complete-application costs; never substitute primitive costs."""

import argparse
import json
from pathlib import Path


def workload(d):
    name = d["application"] + "/" + Path(d["run"]).name
    return name + (
        " [" + d["direct_algorithm"] + "]" if "direct_algorithm" in d else ""
    )


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("results", type=Path, nargs="+")
    a = p.parse_args()
    data = [json.loads(path.read_text()) for path in a.results]
    assert len({v["binary_sha256"] for v in data}) == 1, "mixed baseline binaries"
    print(
        "Direct warm excludes proof I/O; native CLI run includes it. These columns are not an interpreter-overhead subtraction.\n"
    )
    print(
        "| Workload | Prove ms, direct warm / native CLI run (with proof I/O) | Verify ms, direct warm / native CLI run (with proof I/O) | Bytes direct / native |"
    )
    print("|---|---:|---:|---:|")
    for d in data:
        cells = [workload(d)]
        for role, native in [("prove", "produce"), ("verify", "validate")]:
            cells.append(
                f"{d['direct_summary'][role]['warm_seconds'] * 1000:.3f} / {d['native_summary'][native]['run_seconds'] * 1000:.3f}"
            )
        cells.append(f"{d['direct_proof_bytes']} / {d['native_proof_bytes']}")
        print("| " + " | ".join(cells) + " |")
    print(
        "\n| Workload | Prove process ms, direct / native / native pipeline (app and optional claims) | Verify process ms, direct / native / native pipeline (app and optional claims) |"
    )
    print("|---|---:|---:|")
    for d in data:
        cells = [workload(d)]
        for role, native in [("prove", "produce"), ("verify", "validate")]:
            dd, nn = d["direct_summary"][role], d["native_summary"][native]
            cells.append(
                f"{dd['process_seconds'] * 1000:.3f} / {nn['process_seconds'] * 1000:.3f} / {nn['pipeline_seconds'] * 1000:.3f}"
            )
        print("| " + " | ".join(cells) + " |")


if __name__ == "__main__":
    main()
