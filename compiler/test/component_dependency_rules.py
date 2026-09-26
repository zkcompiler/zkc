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
        root / "lib/Claims/Admission.h",
        lambda text: '#include "Internal.h"\n' + text,
        "private component dependency: ZkcClaimTranslation")
rejects("claim translation cannot include other checker internals",
        root / "lib/ClaimTranslation/Claims.cpp",
        lambda text: '#include "../Claims/Internal.h"\n' + text,
        "private component dependency: ZkcClaimTranslation")
rejects("ordinary IR cannot include the claim checker",
        root / "lib/Dialect/Claim/IR/ClaimDialect.cpp",
        lambda text: '#include "zkc/Claims/Claims.h"\n' + text,
        "ZkcIR: upward include")
rejects("ordinary IR cannot include optional claim translation",
        root / "lib/Dialect/Claim/IR/ClaimDialect.cpp",
        lambda text: '#include "zkc/ClaimTranslation/Claims.h"\n' + text,
        "ZkcIR: upward include")
rejects("claim translation public headers cannot expose the private bridge",
        root / "include/zkc/ClaimTranslation/Claims.h",
        lambda text: '#include "../../../lib/Claims/Admission.h"\n' + text,
        "public header includes private implementation")
rejects("public extension headers cannot reexport raw builders",
        root / "include/zkc/Dialect/IR.h",
        lambda text: '#include "zkc/Dialect/detail/Builders.h"\n' + text,
        "public header exposes unsupported detail")

def move_source(text, source, destination):
    lines = []
    for line in text.splitlines():
        name, links, interface, sources = line.split("|")
        items = [item for item in sources.split(";") if item and item != source]
        if name == destination:
            items.append(source)
        lines.append(f"{name}|{links}|{interface}|{';'.join(items)}")
    return "\n".join(lines) + "\n"

for source in ("lib/Dialect/Claim/IR/ClaimDialect.cpp", "lib/Dialect/PIR/IR/Protocol.cpp"):
    rejects(f"mandatory IR source cannot move to optional translation: {source}", manifest,
            lambda text, source=source: move_source(text, source, "ZkcClaimTranslation"),
            "mandatory component ownership")
rejects("claim translation must retain its audited direct dependency", manifest,
        lambda text: text.replace("ZkcClaimTranslation|ZkcClaims;", "ZkcClaimTranslation|", 1),
        "Claims bridge requires a direct Claims dependency")
rejects("the manifest cannot add an unrecognized component", manifest,
        lambda text: text + "ZkcExtra|||\n", "ownership policy disagree")
rejects("the manifest cannot repeat a component", manifest,
        lambda text: text + "ZkcSupport|LLVM|LLVM|\n", "duplicate component")
rejects("frontend cannot use C file I/O headers", root / "lib/Frontend/Analysis.cpp",
        lambda text: '#include <cstdio>\n' + text, "input loading belongs to FrontendLoading")
rejects("loading cannot reach private lexer internals", root / "lib/Frontend/Loading/Capture.cpp",
        lambda text: '#include "../Syntax/Lexer.h"\n' + text, "frontend phase dependency")
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
