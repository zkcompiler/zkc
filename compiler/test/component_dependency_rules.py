"""Negative controls for component ownership and private-header boundaries."""

from contextlib import redirect_stdout
import io
import os
from pathlib import Path
import shutil
from unittest.mock import patch

from cases import case
from tools import records
import component_dependencies as policy


directory = records()
root = Path(directory) / "compiler"
for area in ("include", "lib", "tools", "examples/service"):
    shutil.copytree(policy.ROOT / area, root / area)
original_manifest = Path(os.environ["ZKC_CTEST_COMPONENTS"])
manifest = Path(directory) / "component-dependencies.txt"
manifest.write_text(original_manifest.read_text())
generated = []
for name in (original_manifest.parent / "ir-generated-files.txt").read_text().splitlines():
    source = Path(name)
    target = manifest.parent / source.relative_to(original_manifest.parent)
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    generated.append(str(target))
(manifest.parent / "ir-generated-files.txt").write_text("\n".join(generated) + "\n")

def check():
    with patch.object(policy, "ROOT", root), patch.dict(os.environ, {"ZKC_CTEST_COMPONENTS": str(manifest)}), redirect_stdout(io.StringIO()):
        policy.main()

def rejects(name, path, transform, message):
    with case(name):
        before = path.read_text()
        try:
            path.write_text(transform(before))
            try:
                check()
            except AssertionError as error:
                assert message in str(error), str(error)
            else:
                raise AssertionError("invalid dependency accepted")
        finally:
            path.write_text(before)

with case("the actual component graph passes in an isolated tree"):
    check()
rejects("a bridge does not grant its owner's other private headers",
        root / "lib/Claims/Analysis.h",
        lambda text: '#include "Internal.h"\n' + text,
        "private component dependency: ZkcIR")
rejects("the manifest cannot add an unrecognized component", manifest,
        lambda text: text + "ZkcExtra|||\n", "ownership policy disagree")
rejects("the manifest cannot repeat a component", manifest,
        lambda text: text + "ZkcSupport|LLVM|LLVM|\n", "duplicate component")
rejects("frontend cannot use C file I/O headers", root / "lib/Frontend/Analysis.cpp",
        lambda text: '#include <cstdio>\n' + text, "input loading belongs to FrontendLoading")
rejects("loading cannot reach the unused lexer bridge", root / "lib/Frontend/Loading/Relations.cpp",
        lambda text: '#include "../Syntax/Lexer.h"\n' + text, "private component dependency")
rejects("installed headers cannot reach an implementation", root / "include/zkc/Claims/Claims.h",
        lambda text: '#include "../../../lib/Claims/Internal.h"\n' + text,
        "public header includes private implementation")
rejects("a dylib does not permit an upward target edge", manifest,
        lambda text: text.replace("ZkcIR|", "ZkcIR|ZkcFrontend;", 1),
        "hidden private or extra interface dependencies")
# Adding both links preserves direct/interface agreement and must still fail.
def mixed_mlir(text):
    lines = text.splitlines()
    for i, line in enumerate(lines):
        if line.startswith("ZkcIR|"):
            name, links, interface, sources = line.split("|")
            addition = "MLIRIR" if "MLIR" in links.split(";") else "MLIR"
            lines[i] = f"{name}|{links};{addition}|{interface};{addition}|{sources}"
    return "\n".join(lines) + "\n"

rejects("static MLIR components cannot be mixed with its dylib", manifest,
        mixed_mlir, "ZkcIR")
