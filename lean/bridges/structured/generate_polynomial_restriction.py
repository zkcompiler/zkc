#!/usr/bin/env python3
"""Regenerate the bounded coefficient-restriction example using shared printers.

The mathematical and source-binding proofs are maintained Lean modules. This
script only exports and prints constructor data and exact bodies; it is not a
second evaluator or proof checker. Run from any working directory.
"""

import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "lean"))
from bridges.structured import bodies, snapshot  # noqa: E402

NAMESPACE = "ZkcExamples.Structured.PolynomialRestriction"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=ROOT / "build/lean/polynomial-restriction")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    compiler, output = args.compiler.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)

    def run(arguments, cwd=ROOT):
        return subprocess.check_output([str(argument) for argument in arguments], cwd=cwd, text=True)

    def emit(suffix, text):
        path = ROOT / "lean" / Path(*NAMESPACE.split(".")).with_name("PolynomialRestriction" + suffix + ".lean")
        if args.check:
            if path.read_text() != text:
                raise RuntimeError(f"generated source differs: {path}")
        else:
            path.write_text(text)

    flags = ["--source-format=zkc", "--subject=polynomial_restriction::Restriction",
             "--module=polynomial_restriction=examples/projects/polynomial-restriction/main.zkc",
             "--module=zkc::bilinear_restriction=libraries/core/polynomial/bilinear_restriction.zkc"]
    original = output / "original.mlir"
    original.write_text(run([compiler, "language-emit", *flags]))
    interface = json.loads(run([compiler, "language-interface", *flags]))
    exported = run([compiler, "protocol-structured", original, f"--symbol={interface['protocol']}"])
    (output / "snapshot.json").write_text(exported)
    data = json.loads(exported)
    emit("Data", snapshot.render(data, NAMESPACE + "Data"))
    run(["lake", "build", NAMESPACE + "Data"], ROOT / "lean")
    helpers = [item for item in data[7] if item[0] == "function" and item[2] != "protocol"]
    if sorted((len(item[4]), len(item[5]), item[2]) for item in helpers) != [(3, 1, "math"), (5, 2, "math")]:
        raise RuntimeError("unexpected restriction helper signatures")
    names = {item[1]: "restrict" if len(item[4]) == 5 else "evaluate" for item in helpers}
    names[interface["protocol"]] = "caller"
    emit("Bodies", bodies.generate(NAMESPACE + "Data", NAMESPACE + "Bodies", closed=True,
                                  names=names, fresh=True))


if __name__ == "__main__":
    main()
