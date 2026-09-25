#!/usr/bin/env python3
"""Export trusted public sparse matrices once, outside timed direct proof work."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--run", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--compiler", type=Path, default=Path("build/compiler/zkc-compile"))
    a = p.parse_args()
    a.output.mkdir(parents=True, exist_ok=True)
    matrices = []
    shapes = []
    for component in ("cpu", "memory", "link"):
        relation = json.loads(
            subprocess.check_output(
                [
                    str(a.compiler),
                    "relation-read",
                    str(a.run / "relation" / f"{component}.r1cs"),
                ]
            )
        )
        assert relation[:2] == ["zkc.relation.r1cs/1", "bls12-381.fr"]
        shapes.append(
            (int(relation[2]), int(relation[3]) + int(relation[4]), len(relation[5]))
        )
        triple = [[], [], []]
        for row, equation in enumerate(relation[5]):
            for kind, linear in enumerate(equation):
                for col, value in linear:
                    triple[kind].append([row, int(col), value])
        matrices.append(triple)
    assert len(set(shapes)) == 1, shapes
    wires, public_count, rows = shapes[0]
    config = json.loads((a.run / "public/config.json").read_text())
    statement = json.loads((a.run / "public/statement.json").read_text())
    assert config == json.loads((a.run / "relation/config.json").read_text())
    assert statement == json.loads((a.run / "relation/statement.json").read_text())
    assert len(statement) == public_count
    source = (a.run / "public/execution-proof.pir").read_bytes()
    public = dict(
        version="zkc-direct-execution-public/1",
        wires=wires,
        rows=1 << (max(2, rows) - 1).bit_length(),
        columns=1 << (max(2, wires) - 1).bit_length(),
        statement=list(map(str, statement)),
        config=config,
        source_sha256=hashlib.sha256(source).hexdigest(),
        matrices=matrices,
    )
    setup = json.loads((a.run / "setup/setup.json").read_text())
    vk = bytes.fromhex(setup["verifier_key"])
    # Public trusted setup file, never a pin obtained from a candidate proof.
    assert vk[:8] == b"ZKCAR006"
    setup["verifier_key_id"] = vk[49:81].hex()
    setup["prover_key_file"] = str(Path(setup["prover_key_file"]).resolve())
    for name, value in [("public.json", public), ("setup.json", setup)]:
        (a.output / name).write_text(
            json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n"
        )
    print(
        json.dumps(
            dict(
                wires=wires,
                rows=public["rows"],
                columns=public["columns"],
                openings=public_count + 4,
                output=str(a.output),
            )
        )
    )


if __name__ == "__main__":
    main()
