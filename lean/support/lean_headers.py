"""Authoritative header imports from the selected Lean, shared by both checks.

No import modules are loaded. Parser errors are fatal, including invalid import
modifiers. The persistent process amortizes loading Lean across the inventory.
"""

import json
import os
import re
from pathlib import Path
import subprocess

from support.packages import module_path, tool_module

# Resolve the explicitly pinned toolchain from the parser's owning package.
ROOT = Path(__file__).resolve().parents[1] / "program"
PARSER = module_path(tool_module("program", "ImportHeaders"))


class HeaderParser:
    def __init__(self, lean="lean", root=ROOT, lake=None):
        toolchain = (ROOT / "lean-toolchain").read_text().strip()
        # Elan honors this selection; native Lean/Lake ignore it. Both use the
        # ordinary CLI and must report the pinned version before parsing input.
        environment = dict(os.environ, ELAN_TOOLCHAIN=toolchain)
        command = [lake, "env", "lean"] if lake else [lean]
        version = subprocess.check_output([*command, "--version"], cwd=ROOT,
                                          env=environment, text=True).strip()
        expected = toolchain.split(":v")[-1]
        found = re.search(r"version (\d+\.\d+\.\d+)", version)
        if found is None or found[1] != expected:
            raise ValueError(f"wrong Lean toolchain: {version}; expected {expected}")
        self.process = subprocess.Popen(
            [*command, "-DautoImplicit=false", "-DwarningAsError=true", "--run", str(PARSER)],
            cwd=ROOT, env=environment, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        self.cache = {}
        self.module_headers = {}

    def details(self, source, path="<input>"):
        """Retain visibility and phase from Lean's parsed Import records."""
        if source not in self.cache:
            self.process.stdin.write(json.dumps({"source": source, "path": str(path)}) + "\n")
            self.process.stdin.flush()
            line = self.process.stdout.readline()
            if not line:
                raise ValueError(f"Lean header parser terminated while reading {path}")
            result = json.loads(line)
            if "error" in result:
                raise ValueError(f"invalid Lean header: {path}: {result['error']}")
            self.cache[source] = result["import_details"]
            self.module_headers[source] = result["is_module"]
        return self.cache[source]

    def is_module(self, source, path="<input>"):
        self.details(source, path)
        return self.module_headers[source]

    def imports(self, source, path="<input>"):
        return [entry["module"] for entry in self.details(source, path)]

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.process.stdin.close()
        self.process.stdout.close()
        if self.process.wait(timeout=10) != 0:
            raise ValueError("Lean header parser failed")
