"""Authoritative header imports from the selected Lean, shared by both checks.

No import modules are loaded. Parser errors are fatal, including invalid import
modifiers. The persistent process amortizes loading Lean across the inventory.
"""

import json
from pathlib import Path
import subprocess

# The formal package, which is this module's parent now that it sits in
# support/: it runs Lean over Tools/ImportHeaders.lean from there.
ROOT = Path(__file__).resolve().parents[1]


class HeaderParser:
    def __init__(self, lean="lean", root=ROOT, lake=None):
        command = [lake, "env", "lean"] if lake else [lean]
        self.process = subprocess.Popen(
            [*command, "-DwarningAsError=true", "--run", str(ROOT / "Tools/ImportHeaders.lean")],
            cwd=root, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        self.cache = {}

    def imports(self, source, path="<input>"):
        if source not in self.cache:
            self.process.stdin.write(json.dumps({"source": source, "path": str(path)}) + "\n")
            self.process.stdin.flush()
            line = self.process.stdout.readline()
            if not line:
                raise ValueError(f"Lean header parser terminated while reading {path}")
            result = json.loads(line)
            if "error" in result:
                raise ValueError(f"invalid Lean header: {path}: {result['error']}")
            self.cache[source] = result["imports"]
        return self.cache[source]

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.process.stdin.close()
        self.process.stdout.close()
        if self.process.wait(timeout=10) != 0:
            raise ValueError("Lean header parser failed")
