"""Shared work-directory helpers; never write to the maintained package."""

import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]
NODE = ["node", "--require", "./scripts/limit-workers.cjs"]
SNARK = NODE + ["node_modules/snarkjs/build/cli.cjs"]


def require_workspace():
    if not (ROOT / ".groth16-workdir.json").is_file():
        raise RuntimeError(
            "Run reproduce.py; these scripts require a staged work directory"
        )
    os.chdir(ROOT)
    (ROOT / "logs").mkdir(exist_ok=True)
    (ROOT / "reference").mkdir(exist_ok=True)


def read_json(path):
    return json.loads(Path(path).read_text())


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def sha256(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def check_files(root, manifest):
    for relative, expected in manifest.items():
        path = Path(root) / relative
        if not path.is_file() or sha256(path) != expected["sha256"]:
            raise ValueError(f"Artifact hash mismatch: {relative}")
        if path.stat().st_size != expected["bytes"]:
            raise ValueError(f"Artifact length mismatch: {relative}")


class Runner:
    def __init__(self, stage):
        self.stage = stage
        self.timings = []

    def run(self, name, command):
        command = [str(argument) for argument in command]
        print(f"START {name}", flush=True)
        with (ROOT / "logs/commands.sh").open("a") as stream:
            stream.write(shlex.join(command) + "\n")
        started = time.monotonic()
        logfile = ROOT / "logs" / f"{name}.log"
        with logfile.open("w") as stream:
            result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - started
        self.timings.append(
            {
                "name": name,
                "seconds": elapsed,
                "returncode": result.returncode,
                "command": command,
            }
        )
        write_json(ROOT / "logs" / f"{self.stage}-timings.json", self.timings)
        output = logfile.read_text(errors="replace")
        print(f"END {name}: {elapsed:.3f}s, exit {result.returncode}", flush=True)
        # snarkjs setup has failure branches that log an error and exit zero.
        if result.returncode or "[ERROR]" in output:
            raise RuntimeError(f"{name} failed; see {logfile}\n{output[-6000:]}")
