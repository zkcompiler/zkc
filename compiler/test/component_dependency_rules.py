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
# Relocate the exact extension inventory too, when this runs on an extended
# installation. Never drop its sources to manufacture a base-only fixture.
contribution_manifest = manifest.parent / "contribution-dependencies.txt"
original_contributions = original_manifest.parent / contribution_manifest.name
if original_contributions.exists():
    rows = []
    text = manifest.read_text()
    for line in original_contributions.read_text().splitlines():
        kind, package, owner, value, installed = line.split("|")
        if kind not in ("LIBRARY", "DEPENDENCY"):
            source = Path(value)
            target = Path(directory) / "contribution-inputs" / source.relative_to("/")
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
            text = text.replace(value, str(target))
            value = str(target)
        rows.append("|".join((kind, package, owner, value, installed)))
    manifest.write_text(text)
    contribution_manifest.write_text("".join(row + "\n" for row in rows))
generated = []
for name in (original_manifest.parent / "ir-generated-files.txt").read_text().splitlines():
    source = Path(name)
    target = manifest.parent / source.relative_to(original_manifest.parent)
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    generated.append(str(target))
(manifest.parent / "ir-generated-files.txt").write_text("\n".join(generated) + "\n")
declarations = Path("include/zkc/Contracts/Declarations.cpp.inc")
(manifest.parent / declarations).parent.mkdir(parents=True, exist_ok=True)
shutil.copyfile(original_manifest.parent / declarations, manifest.parent / declarations)

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
for filename in ("BuiltinHeaders.h.inc", "BuiltinDialects.inc", "NativeDialects.inc",
                 "ContributionHeaders.h.inc", "ContributionDialects.inc"):
    for source in ("lib/Dialect/Claim/IR/ClaimDialect.cpp", "include/zkc/Dialect/Registry.h"):
        rejects(f"registration fragment is private: {filename} from {source}",
                root / source,
                lambda text, filename=filename: f'#include "zkc/Dialect/{filename}"\n' + text,
                "private dialect registration fragment")
rejects("absolute registration fragment cannot bypass ownership",
        root / "lib/Dialect/Claim/IR/ClaimDialect.cpp",
        lambda text: f'#include "{manifest.parent / "include/zkc/Dialect/BuiltinDialects.inc"}"\n' + text,
        "private dialect registration fragment")
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

for source in ("lib/Dialect/Claim/IR/ClaimDialect.cpp", "lib/Dialect/Protocol/IR/Protocol.cpp"):
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
rejects("carrier decoding cannot invoke authored name resolution", root / "lib/Frontend/Carrier/Reader.cpp",
        lambda text: '#include "../Resolution/Names.h"\n' + text, "frontend phase dependency")
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

# A real, explicitly owned extension exercises the same checker without a
# compiler build. Generated declarations and definitions are separate owners.
extension = Path(directory) / "policy-extension"
extension.mkdir()
ir_source = extension / "IR.cpp"
transform_source = extension / "Pass.cpp"
api = extension / "Api.h"
pass_header = extension / "Pass.h"
generated_header = extension / "Api.h.inc"
generated_source = extension / "Api.cpp.inc"
api.write_text('#include "zkc/Dialect/IR.h"\n#include "policy_fixture/Api.h.inc"\n')
pass_header.write_text('#include <mlir/Pass/Pass.h>\n')
generated_header.write_text("// Generated declaration.\n")
generated_source.write_text("// Generated definition.\n")
ir_source.write_text('#include "policy_fixture/Api.h"\n#include "policy_fixture/Api.cpp.inc"\n')
transform_source.write_text('#include "policy_fixture/Api.h"\n#include "policy_fixture/Pass.h"\n')
extra = [
    ("SOURCE", "ZkcIR", ir_source, ""),
    ("SOURCE", "ZkcTransforms", transform_source, ""),
    ("HEADER", "ZkcIR", api, "policy_fixture/Api.h"),
    ("HEADER", "ZkcTransforms", pass_header, "policy_fixture/Pass.h"),
    ("HEADER", "ZkcIR", generated_header, "policy_fixture/Api.h.inc"),
    ("GENERATED", "ZkcIR", generated_source, "policy_fixture/Api.cpp.inc"),
    ("LIBRARY", "ZkcIR", "Fixture::IR", ""),
    ("LIBRARY", "ZkcTransforms", "Fixture::Pass", ""),
]
previous = contribution_manifest.read_text() if contribution_manifest.exists() else ""
contribution_manifest.write_text(previous + "".join(f"{kind}|policy_fixture|{owner}|{value}|{installed}\n" for kind, owner, value, installed in extra))
text = move_source(manifest.read_text(), str(ir_source), "ZkcIR")
text = move_source(text, str(transform_source), "ZkcTransforms")
def add_external(text, owner, library, static=True):
    lines = []
    for line in text.splitlines():
        name, links, interface, sources = line.split("|")
        if name == owner:
            links += ";" + library
            if static:
                interface += ";$<LINK_ONLY:" + library + ">"
        lines.append("|".join((name, links, interface, sources)))
    return "\n".join(lines) + "\n"
manifest.write_text(add_external(add_external(text, "ZkcIR", "Fixture::IR"), "ZkcTransforms", "Fixture::Pass"))
with case("explicit extension sources, public headers, generated outputs and static external links pass"):
    check()
with case("explicit private external links pass with shared linkage"):
    before = manifest.read_text()
    try:
        manifest.write_text(before.replace(";$<LINK_ONLY:Fixture::IR>", "").replace(";$<LINK_ONLY:Fixture::Pass>", ""))
        check()
    finally:
        manifest.write_text(before)
rejects("an extension source cannot move to a different component", manifest,
        lambda text: move_source(text, str(ir_source), "ZkcTransforms"), "contribution component ownership")
rejects("an extension source cannot have two manifest owners", contribution_manifest,
        lambda text: text + f"SOURCE|duplicate|ZkcIR|{ir_source}|\n", "multiple contribution owners")
rejects("IR contributions cannot include core transforms", ir_source,
        lambda text: '#include "zkc/Transforms/Passes.h"\n' + text, "ZkcIR: upward include")
rejects("IR contributions cannot include MLIR passes", api,
        lambda text: '#include <mlir/Pass/Pass.h>\n' + text, "transformation dependency")
rejects("IR contributions cannot include contributed transform headers", ir_source,
        lambda text: '#include "policy_fixture/Pass.h"\n' + text, "ZkcIR: upward include")
rejects("relative contribution includes preserve transform ownership", ir_source,
        lambda text: '#include "Pass.h"\n' + text, "ZkcIR: upward header dependency")
rejects("contribution public headers cannot expose core implementation headers", api,
        lambda text: f'#include "{root / "lib/Dialect/Verification.h"}"\n' + text,
        "public header includes private implementation")
rejects("generated contribution headers are traversed", generated_header,
        lambda text: '#include <mlir/Pass/Pass.h>\n' + text, "transformation dependency")
rejects("transforms cannot include generated definitions", transform_source,
        lambda text: '#include "policy_fixture/Api.cpp.inc"\n' + text, "generated implementation outside its owner")
rejects("contributions cannot shadow a header destination", contribution_manifest,
        lambda text: text.replace("policy_fixture/Pass.h", "policy_fixture/Api.h"), "conflicting installed contribution path")
rejects("contribution metadata cannot widen the core library graph", contribution_manifest,
        lambda text: text + "LIBRARY|policy_fixture|ZkcIR|ZkcTransforms|\n", "cannot extend the core dependency graph")
rejects("an external library is permitted only on its declared owner", manifest,
        lambda text: add_external(text, "ZkcContracts", "Fixture::IR"), "hidden private or extra interface dependencies")
rejects("missing source registration is not an ownership exemption", contribution_manifest,
        lambda text: text.replace(f"SOURCE|policy_fixture|ZkcIR|{ir_source}|\n", ""), "unowned or nonexistent implementations")
rejects("missing generated registration is refused", contribution_manifest,
        lambda text: text.replace(f"GENERATED|policy_fixture|ZkcIR|{generated_source}|policy_fixture/Api.cpp.inc\n", ""), "unregistered contribution include")
rejects("an unresolved local generated include cannot evade registration", ir_source,
        lambda text: '#include "Unregistered.h.inc"\n' + text, "unregistered contribution include")
with case("declared generated contribution headers must exist after the build"):
    contents = generated_header.read_text()
    try:
        generated_header.unlink()
        try:
            check()
        except AssertionError as error:
            assert "missing or noncanonical contribution file" in str(error), str(error)
        else:
            raise AssertionError("missing generated output accepted")
    finally:
        generated_header.write_text(contents)

# Private contribution headers and generated transform definitions retain their
# package/component ownership without becoming installed public interfaces.
private_header = extension / "Internal.hpp"
private_header.write_text("// Private implementation helper.\n")
transform_generated = extension / "Patterns.cpp.inc"
transform_generated.write_text("// Transform-owned generated definitions.\n")
contribution_manifest.write_text(contribution_manifest.read_text() +
    f"PRIVATE|policy_fixture|ZkcIR|{private_header}|\n" +
    f"GENERATED|policy_fixture|ZkcTransforms|{transform_generated}|policy_fixture/Patterns.cpp.inc\n")
ir_source.write_text(ir_source.read_text() + '#include "Internal.hpp"\n')
transform_source.write_text(transform_source.read_text() + '#include "policy_fixture/Patterns.cpp.inc"\n')
with case("private contribution headers and transform definitions retain ownership"):
    check()
rejects("public contribution headers cannot expose private helpers", api,
        lambda text: '#include "Internal.hpp"\n' + text, "public header includes private implementation")
rejects("IR cannot include transform generated definitions", ir_source,
        lambda text: '#include "policy_fixture/Patterns.cpp.inc"\n' + text, "generated implementation outside its owner")
other_api = extension / "Other.h"
other_api.write_text("// Another contribution.\n")
contribution_manifest.write_text(contribution_manifest.read_text() +
    f"HEADER|other_fixture|ZkcIR|{other_api}|other_fixture/Other.h\n")
rejects("cross-package native headers require a declared dependency", api,
        lambda text: '#include "other_fixture/Other.h"\n' + text, "undeclared contribution dependency")
contribution_manifest.write_text(contribution_manifest.read_text() +
    "DEPENDENCY|policy_fixture|ZkcIR|other_fixture|\n")
api.write_text(api.read_text() + '#include "other_fixture/Other.h"\n')
with case("declared cross-package native header dependency passes"):
    check()
rejects("dependencies cannot expose another package's private helper", other_api,
        lambda text: '#include "Internal.hpp"\n' + text, "cross-package private include")

private_rules = extension / "PrivateRules.cpp.inc"
private_rules.write_text("// Private transform definitions.\n")
contribution_manifest.write_text(contribution_manifest.read_text() +
    f"PRIVATE|policy_fixture|ZkcTransforms|{private_rules}|\n" +
    f"HEADER|policy_fixture|ZkcIR|{api}|policy_fixture/Alias.hpp\n")
transform_source.write_text(transform_source.read_text() + '#include "PrivateRules.cpp.inc"\n')
with case("relative private transform definitions and public aliases retain their owners"):
    check()
rejects("an IR source cannot consume relative private transform definitions", ir_source,
        lambda text: '#include "PrivateRules.cpp.inc"\n' + text, "generated implementation outside its owner")
other_definitions = extension / "Other.cpp.inc"
other_definitions.write_text("// Other package definitions.\n")
contribution_manifest.write_text(contribution_manifest.read_text() +
    f"GENERATED|other_fixture|ZkcIR|{other_definitions}|other_fixture/Other.cpp.inc\n")
rejects("declared dependencies do not authorize including another package definitions", ir_source,
        lambda text: '#include "other_fixture/Other.cpp.inc"\n' + text, "cross-package generated definitions")

rejects("IR cannot depend on carrier translation",
        root / "lib/Dialect/Algebra/IR/Mathematical.cpp",
        lambda text: '#include "zkc/Translation/Protocol.h"\n' + text,
        "ZkcIR: upward include")

rejects("SSA transforms cannot depend on carrier translation",
        root / "lib/Transforms/Algorithms.cpp",
        lambda text: '#include "zkc/Translation/Protocol.h"\n' + text,
        "ZkcTransforms: upward include")

rejects("IR cannot own transformation preservation checks",
        root / "lib/Dialect/Protocol/IR/Projection.cpp",
        lambda text: '#include "zkc/Transforms/Mathematical.h"\n' + text,
        "ZkcIR: upward include")
rejects("IR cannot consume private mathematical transform helpers",
        root / "lib/Dialect/Protocol/IR/Projection.cpp",
        lambda text: '#include "../../../Transforms/MathematicalSupport.h"\n' + text,
        "private component dependency")

rejects("IR cannot parse invocation input",
        root / "lib/Dialect/Protocol/IR/Projection.cpp",
        lambda text: '#include "mlir/Parser/Parser.h"\n' + text,
        "parsing belongs to CompilerCore or Driver")
rejects("transforms cannot parse invocation input",
        root / "lib/Transforms/Algorithms.cpp",
        lambda text: '#include "mlir/Parser/Parser.h"\n' + text,
        "parsing belongs to CompilerCore or Driver")
