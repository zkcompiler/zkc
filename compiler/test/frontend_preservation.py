#!/usr/bin/env python3
"""Compare maintained authoring files with frozen pre-redesign source/artifact hashes."""
import hashlib
import json
from pathlib import Path
from commands import Commands
from tools import compiler, corpus, records


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
        actual = digest(json.loads(run("protocol-source", path)))
        assert actual == record["source_sha256"], record["path"]
        formatted = run("protocol-format", path)
        assert formatted == run("protocol-format", text=formatted), record["path"]
        assert digest(json.loads(run("protocol-source", text=formatted))) == actual
        compared.append({"path": record["path"], "source_equal": True,
                       "format_roundtrip": True, "format_idempotent": True})
    artifacts = []
    for record in baseline["artifacts"]:
        source = root / Path(record["source"]).with_suffix(".pir")
        construction = root / Path(record["construction"]).with_suffix(".pir")
        actual = digest(json.loads(run("protocol-construct", source, construction)))
        assert actual == record["artifact_sha256"], record["source"]
        artifacts.append({"source": str(source.relative_to(root)), "artifact_equal": True})
    print(f"preservation: {len(compared)} source records, {len(artifacts)} constructed artifacts")


if __name__ == "__main__":
    main()
