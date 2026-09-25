#!/usr/bin/env python3
"""Compile both circuits and generate the PUBLIC, INSECURE test setup."""

import argparse
from pathlib import Path

from common import NODE, ROOT, SNARK, Runner, read_json, require_workspace


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reuse-setup", action="store_true")
    args = parser.parse_args()
    require_workspace()
    run = Runner("build").run
    config = read_json(ROOT / ".groth16-workdir.json")
    setup = read_json(ROOT / "SOURCE_PINS.json")["setup"]
    compiler = config.get("circomBinary")
    if not compiler:
        raise ValueError("Compilation requires --circom or --circom-source")

    for depth in (2, 16):
        out = f"artifacts/depth{depth}"
        Path(out).mkdir(parents=True, exist_ok=True)
        run(
            f"compile-depth{depth}",
            [
                compiler,
                f"circuits/depth{depth}.circom",
                "--r1cs",
                "--wasm",
                "--sym",
                "--O2",
                "--prime",
                "bn128",
                "-o",
                out,
            ],
        )
    run("make-inputs", NODE + ["scripts/make-inputs.mjs"])
    for depth in (2, 16):
        out = f"artifacts/depth{depth}"
        run(
            f"witness-depth{depth}",
            [
                "node",
                f"{out}/depth{depth}_js/generate_witness.js",
                f"{out}/depth{depth}_js/depth{depth}.wasm",
                f"{out}/input.json",
                f"{out}/witness.wtns",
            ],
        )
        run(
            f"witness-check-depth{depth}",
            SNARK
            + [
                "wtns",
                "check",
                f"{out}/depth{depth}.r1cs",
                f"{out}/witness.wtns",
            ],
        )
        run(
            f"r1cs-json-depth{depth}",
            SNARK
            + [
                "r1cs",
                "export",
                "json",
                f"{out}/depth{depth}.r1cs",
                f"{out}/r1cs.json",
            ],
        )
        run(
            f"witness-json-depth{depth}",
            SNARK
            + [
                "wtns",
                "export",
                "json",
                f"{out}/witness.wtns",
                f"{out}/witness.json",
            ],
        )

    Path("artifacts/setup").mkdir(exist_ok=True)
    initial = "artifacts/setup/pot13_0000.ptau"
    beacon = "artifacts/setup/pot13_beacon.ptau"
    prepared = "artifacts/setup/pot13_final.ptau"
    exponent = str(setup["beaconIterationsExponent"])
    label = "-n=PUBLIC TEST BEACON - NOT SECURE"
    if not args.reuse_setup:
        run(
            "ptau-new",
            SNARK + ["powersoftau", "new", "bn128", str(setup["power"]), initial],
        )
        run(
            "ptau-beacon",
            SNARK
            + [
                "powersoftau",
                "beacon",
                initial,
                beacon,
                setup["ptauBeacon"],
                exponent,
                label,
            ],
        )
        run(
            "ptau-prepare",
            SNARK + ["powersoftau", "prepare", "phase2", beacon, prepared],
        )
    for depth in (2, 16):
        out = f"artifacts/depth{depth}"
        run(
            f"setup-depth{depth}",
            SNARK
            + [
                "groth16",
                "setup",
                f"{out}/depth{depth}.r1cs",
                prepared,
                f"{out}/initial.zkey",
            ],
        )
        run(
            f"zkey-beacon-depth{depth}",
            SNARK
            + [
                "zkey",
                "beacon",
                f"{out}/initial.zkey",
                f"{out}/final.zkey",
                setup["zkeyBeacon"],
                exponent,
                label,
            ],
        )
        run(
            f"zkey-verify-depth{depth}",
            SNARK
            + [
                "zkey",
                "verify",
                f"{out}/depth{depth}.r1cs",
                prepared,
                f"{out}/final.zkey",
            ],
        )
        run(
            f"vk-depth{depth}",
            SNARK
            + [
                "zkey",
                "export",
                "verificationkey",
                f"{out}/final.zkey",
                f"{out}/vk.json",
            ],
        )
        run(
            f"prove-random-depth{depth}",
            SNARK
            + [
                "groth16",
                "prove",
                f"{out}/final.zkey",
                f"{out}/witness.wtns",
                f"{out}/proof.json",
                f"{out}/public.json",
            ],
        )
        run(
            f"verify-random-depth{depth}",
            SNARK
            + [
                "groth16",
                "verify",
                f"{out}/vk.json",
                f"{out}/public.json",
                f"{out}/proof.json",
            ],
        )


if __name__ == "__main__":
    main()
