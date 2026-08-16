#!/usr/bin/env python3
"""Generate the benchmark's prover crate from the instance description.

The pipeline is the repository's own: family -> seal -> project ->
translate -> emit. Everything lands under generated/ (untracked); the
bench crate path-depends on the emitted prover, so this script runs
before the first `cargo bench`.
"""

import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BUILD = ROOT / "build" / "bin"
OUT = HERE / "generated"


def run(*argv: str) -> None:
    subprocess.run(argv, check=True)


def main() -> None:
    OUT.mkdir(exist_ok=True)
    instance = HERE / "instance-a.json"
    vocab = OUT / "vocab.json"
    run(str(BUILD / "zkc-family"), str(instance),
        f"--emit-vocabulary={vocab}", f"--emit-spine={OUT / 'spine.mlir'}")
    run(str(BUILD / "zkc-opt"),
        f"-pir-seal=protocol-vocabulary={vocab} "
        f"construction-profile-registry={ROOT / 'registry' / 'construction-profiles.json'}",
        str(OUT / "spine.mlir"), "-o", str(OUT / "sealed.mlir"))
    run(str(BUILD / "zkc-opt"),
        f"-pir-project=endpoint-kind=prover_skeleton protocol-vocabulary={vocab} "
        f"construction-profile-registry={ROOT / 'registry' / 'construction-profiles.json'}",
        str(OUT / "sealed.mlir"), "-o", str(OUT / "prover.mlir"))
    run(str(BUILD / "zkc-translate"), "--oir-canonical",
        str(OUT / "prover.mlir"), "-o", str(OUT / "prover.json"))
    run("cargo", "run", "--locked", "--quiet",
        "--manifest-path", str(ROOT / "emit" / "Cargo.toml"),
        "-p", "zkc-emit", "--",
        "--doc", str(OUT / "prover.json"),
        "--binding", str(ROOT / "emit" / "bindings" / "plonky3-zero-iv.json"),
        "--rt-path", str(ROOT / "emit" / "zkc-rt"),
        "--out", str(OUT / "crate"),
        "--crate-name", "zkc-fri-prover")
    # The golden wire: the replay runner drives the pinned upstream
    # prover over the same document; the bench holds the emitted leg to
    # byte equality with it before timing anything, so the two legs can
    # never silently measure different work.
    import re
    record = subprocess.run(
        ["cargo", "run", "--locked", "--quiet", "--release",
         "--manifest-path",
         str(ROOT / "evaluation" / "upstream" / "plonky3-replay" / "Cargo.toml"),
         "--bin", "prove", "--", str(OUT / "prover.json")],
        check=True, capture_output=True, text=True).stdout
    wire = re.search(r"wire: ([0-9a-f]+)", record).group(1)
    froot = re.search(r"statement f_root: (\d+)", record).group(1)
    (OUT / "golden-wire.hex").write_text(wire)
    (OUT / "golden-froot.txt").write_text(froot)
    print(f"generated: {OUT / 'crate'} (golden wire {len(wire) // 2} bytes)")


if __name__ == "__main__":
    sys.exit(main())
