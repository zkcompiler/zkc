#!/usr/bin/env python3
"""Compare maintained authoring files with frozen pre-redesign source/artifact hashes."""
import copy
import hashlib
import json
from pathlib import Path
from commands import Commands
from tools import compiler, corpus, records

# Ordinary declarations cannot contain '.', so the examples renamed these
# binding symbols (never their contracts, sites or schemas) when the baseline
# was already frozen. Undoing exactly these renames must restore every hash.
ORIGINAL_BINDING_NAMES = {
    name.replace(".", "_"): name for name in (
        "bool.and", "control.require", "curve.add", "curve.append", "curve.at",
        "curve.commit", "curve.empty", "curve.equal", "curve.generator",
        "curve.public", "curve.response", "curve.scale", "field.equal", "field.mul",
        "pcs.check", "pcs.commit", "pcs.equal", "pcs.open", "poly.append_point",
        "poly.boundary", "poly.empty_point", "poly.fold", "poly.product_round",
        "poly.round_evaluate", "random.draw",
    )
}


def original_binding_names(program):
    """A protocol record with the renamed binding symbols restored."""
    program = copy.deepcopy(program)
    for binding in program[1]:
        binding[0] = ORIGINAL_BINDING_NAMES.get(binding[0], binding[0])

    def body(instructions):
        for instruction in instructions:
            if instruction[0] == "op":
                instruction[2] = ORIGINAL_BINDING_NAMES.get(instruction[2], instruction[2])
            elif instruction[0] == "loop":
                body(instruction[5])
            elif instruction[0] == "local-region":
                body(instruction[-1])

    for function in program[2]:
        body(function[4])
    return program


def digest(value):
    canonical = json.dumps(value, ensure_ascii=False, separators=(",", ":"))
    return hashlib.sha256(canonical.encode()).hexdigest()


def main():
    root = Path(__file__).resolve().parents[2]
    commands = Commands(records())
    baseline = json.loads((corpus / "preservation-baseline.json").read_text())

    def run(mode, *files, text=None):
        return commands.run([compiler, mode, *(files or ("-",))], stdin=text)

    compared = []
    for record in baseline["corpus"]:
        path = root / record["path"]
        parsed = json.loads(run("protocol-source", path))
        actual = digest(parsed)
        restored = parsed
        if parsed[0] == "zkc.protocol/1":
            restored = original_binding_names(parsed)
        restored = digest(restored)
        assert restored == record["source_sha256"], record["path"]
        formatted = run("protocol-format", path)
        assert formatted == run("protocol-format", text=formatted), record["path"]
        assert digest(json.loads(run("protocol-source", text=formatted))) == actual
        compared.append({"path": record["path"], "source_equal": True,
                       "format_roundtrip": True, "format_idempotent": True})
    artifacts = []
    for record in baseline["artifacts"]:
        source = root / Path(record["source"]).with_suffix(".pir")
        construction = root / Path(record["construction"]).with_suffix(".pir")
        # Constructed names digest the whole program, so construct the source
        # record with its original binding names.
        restored = original_binding_names(json.loads(run("protocol-source", source)))
        actual = digest(json.loads(run("protocol-construct", "-", construction,
                                       text=json.dumps(restored))))
        assert actual == record["artifact_sha256"], record["source"]
        artifacts.append({"source": str(source.relative_to(root)), "artifact_equal": True})
    print(f"preservation: {len(compared)} source records, {len(artifacts)} constructed artifacts")


if __name__ == "__main__":
    main()
