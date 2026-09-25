#!/usr/bin/env python3
"""Run exact fixed-proof, independent algebra and all 80 fixture controls."""

import sys

from common import NODE, ROOT, SNARK, Runner, read_json, require_workspace


def main():
    require_workspace()
    run = Runner("validation").run
    run("prepare-reference", [sys.executable, "scripts/prepare_reference.py"])
    for depth in (2, 16):
        out = f"artifacts/depth{depth}"
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
            f"zkey-verify-depth{depth}",
            SNARK
            + [
                "zkey",
                "verify",
                f"{out}/depth{depth}.r1cs",
                "artifacts/setup/pot13_final.ptau",
                f"{out}/final.zkey",
            ],
        )
        # Check the ordinary prover too; this output is intentionally not a golden.
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
        for r, s in ((1, 2), (0, 0)):
            run(
                f"deterministic-depth{depth}-r{r}-s{s}",
                NODE
                + [
                    "scripts/deterministic-prove.mjs",
                    out,
                    str(r),
                    str(s),
                ],
            )
            run(
                f"cli-verify-depth{depth}-r{r}-s{s}",
                SNARK
                + [
                    "groth16",
                    "verify",
                    f"{out}/vk.json",
                    f"{out}/public.json",
                    f"{out}/proof-r{r}-s{s}.json",
                ],
            )
        run(f"math-reference-depth{depth}", NODE + ["scripts/math-reference.mjs", out])
        run(f"controls-depth{depth}", NODE + ["scripts/controls.mjs", out])
    # Check integrity again after executing upstream code.
    run(
        "source-integrity-after-validation",
        [sys.executable, "scripts/prepare_reference.py"],
    )
    total = sum(
        read_json(ROOT / f"artifacts/depth{d}/controls/results.json")["passed"]
        for d in (2, 16)
    )
    if total != 80:
        raise ValueError(f"Expected 80 fixture controls, got {total}")


if __name__ == "__main__":
    main()
