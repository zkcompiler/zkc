"""Enforce source/header ownership and component/private phase dependencies."""

import os
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
COMPONENTS = ("ZkcSupport", "ZkcContracts", "ZkcRelation", "ZkcProtocol", "ZkcIR", "ZkcFrontend", "ZkcFrontendLoading", "ZkcClaims", "ZkcClaimTranslation", "ZkcTransforms", "ZkcCompilerCore", "ZkcDriver")
ALLOWED = {
    "ZkcFrontend": {"ZkcProtocol"},
    "ZkcFrontendLoading": {"ZkcFrontend"},
    "ZkcSupport": {"LLVMSupport"},
    "ZkcContracts": {"ZkcSupport"},
    "ZkcRelation": {"ZkcContracts"},
    "ZkcProtocol": {"ZkcRelation"},
    "ZkcClaims": {"ZkcProtocol"},
    "ZkcClaimTranslation": {"ZkcClaims", "ZkcIR"},
    "ZkcTransforms": {"ZkcIR", "MLIRPass", "MLIRTransforms", "MLIRTransformUtils"},
    "ZkcCompilerCore": {"ZkcTransforms", "ZkcFrontend", "ZkcClaimTranslation"},
    "ZkcDriver": {"ZkcCompilerCore", "ZkcFrontendLoading", "MLIRParser"},
    "ZkcIR": {"ZkcProtocol", "MLIRIR", "MLIRControlFlowInterfaces", "MLIRSideEffectInterfaces", "MLIRInferTypeOpInterface", "MLIRFuncDialect"},
}
HEADER_ROOTS = {
    "ZkcFrontend": ["Frontend"],
    "ZkcFrontendLoading": ["Frontend/Loading.h"],
    "ZkcSupport": ["Support/Refusal.h", "Support/Json.h", "Support/MLIRInput.h"],
    "ZkcContracts": ["Contracts"],
    "ZkcRelation": [f"Relation/{name}.h" for name in ("R1CS", "AIR", "AIRPolynomial", "Matrices")],
    "ZkcProtocol": ["Source", "Analysis", "Protocol/Admission.h", "Protocol/Instantiation.h", "Protocol/PhysicalOptions.h"],
    "ZkcClaims": ["Claims"],
    "ZkcClaimTranslation": ["ClaimTranslation"],
    "ZkcTransforms": ["Transforms", "Target"],
    "ZkcCompilerCore": ["Compiler"],
    "ZkcDriver": ["Driver"],
    "ZkcIR": ["Dialect", "Interfaces", "Translation"],
}

# Private frontend headers are phase contracts. The model and syntax owners
# cannot reach a checker; selection cannot perform library elaboration; no pure
# phase can discover inputs through the optional loader.
FRONTEND_LAYERS = {
    "Library": {"Library", "Work.h"},
    "Model": {"Model"},
    "Syntax": {"Syntax"},
    "Static": {"Static", "Syntax", "Work.h"},
    "Resolution": {"Resolution", "Syntax"},
    "Instantiation": {"Instantiation", "Model", "Resolution", "Static", "Syntax", "Work.h"},
    "Lowering": {"Lowering", "Library", "Model", "Resolution", "Syntax", "LibrarySource.h", "Work.h"},
    "Semantics": {"Semantics", "Instantiation", "Library", "Model", "Resolution", "Static", "Syntax", "LibrarySource.h", "Work.h"},
    "Tooling": {"Tooling", "Lowering", "Model", "Resolution", "Semantics", "Syntax"},
    "Loading": {"Loading"},
}


def header_set(entries):
    result = set()
    for entry in entries:
        path = ROOT / "include/zkc" / entry
        result.update(path.rglob("*.h") if path.is_dir() else [path])
    return result


def main():
    manifest = Path(os.environ["ZKC_CTEST_COMPONENTS"]).resolve()
    targets = {}
    owners = {}
    for line in manifest.read_text().splitlines():
        name, links, interface, sources = line.split("|")
        assert name not in targets, f"duplicate component: {name}"
        targets[name] = (
            set(filter(None, links.split(";"))),
            set(filter(None, interface.split(";"))),
            list(filter(None, sources.split(";"))),
        )
        for source in targets[name][2]:
            assert source not in owners, f"{source} compiled by both {owners.get(source)} and {name}"
            owners[source] = name
    assert set(targets) == set(COMPONENTS) | {"ZkcCompiler"}, "component manifest and ownership policy disagree"
    implementation = {str(path.relative_to(ROOT)) for path in (ROOT / "lib").rglob("*.cpp")}
    assert set(owners) == implementation, f"unowned or nonexistent implementations: {set(owners) ^ implementation}"
    for source, owner in {
        "lib/ClaimTranslation/Claims.cpp": "ZkcClaimTranslation",
        "lib/Dialect/Claim/IR/ClaimDialect.cpp": "ZkcIR",
        "lib/Dialect/PIR/IR/Protocol.cpp": "ZkcIR",
    }.items():
        assert owners[source] == owner, f"mandatory component ownership: {source} belongs to {owner}"
    assert targets["ZkcCompiler"] == (set(), {"ZkcCompilerCore", "ZkcDriver"}, []), "aggregate must not compile sources"
    private_headers = {
        "ZkcSupport": {ROOT / "lib/Support/Input.h"},
        "ZkcContracts": {ROOT / "lib/Contracts/RequirementChecks.h"},
        "ZkcRelation": {ROOT / "lib/Relation/Field.h"},
        "ZkcProtocol": {ROOT / "lib/Protocol/EncodingLimits.h", ROOT / "lib/Protocol/ConstructionState.h", ROOT / "lib/Protocol/Construction.h"},
        "ZkcIR": {ROOT / "lib/Dialect/Plan/IR/PhysicalEncoding.h", ROOT / "lib/Dialect/Verification.h"},
    }
    private_headers["ZkcClaims"] = {ROOT / "lib/Claims/Internal.h", ROOT / "lib/Claims/Admission.h"}
    private_headers["ZkcClaimTranslation"] = set()
    private_headers["ZkcTransforms"] = {
        ROOT / "lib/Conversion/Bindings.h", ROOT / "lib/Target/PhysicalPlan.h"
    }
    private_headers["ZkcCompilerCore"] = set()
    private_headers["ZkcDriver"] = set((ROOT / "lib/Driver").glob("*.h"))
    private_headers["ZkcFrontend"] = set((ROOT / "lib/Frontend").rglob("*.h")) - set((ROOT / "lib/Frontend/Loading").rglob("*.h"))
    private_headers["ZkcFrontendLoading"] = set((ROOT / "lib/Frontend/Loading").rglob("*.h"))
    public_headers = {name: header_set(roots) for name, roots in HEADER_ROOTS.items()}
    public_headers["ZkcFrontend"] -= public_headers["ZkcFrontendLoading"]

    header_owners = {}
    for name in COMPONENTS:
        for path in public_headers[name] | private_headers[name]:
            assert path.is_file(), f"nonexistent header: {path}"
            assert path not in header_owners, f"multiple owners: {path}"
            header_owners[path] = name
    assert set(header_owners) == set((ROOT / "include/zkc").rglob("*.h")) | set((ROOT / "lib").rglob("*.h")), "unowned headers"
    private = set().union(*private_headers.values())
    # Implementation bridges are explicit and uninstalled. Each grants only
    # the named header, never the rest of its owner's private implementation.
    bridges = {
        ("ZkcCompilerCore", ROOT / "lib/Protocol/Construction.h"),
        ("ZkcClaimTranslation", ROOT / "lib/Claims/Admission.h"),
        ("ZkcDriver", ROOT / "lib/Support/Input.h"),
        ("ZkcFrontendLoading", ROOT / "lib/Support/Input.h"),
    }
    # The sole Claims bridge is same-version and backed by a direct link.
    assert "ZkcClaims" in targets["ZkcClaimTranslation"][0], "Claims bridge requires a direct Claims dependency"
    assert not (ROOT / "include/zkc/Dialect/Builders.h").exists(), "raw builders belong to unsupported detail"

    def check_private_edge(component, path, target):
        if target in private:
            assert not path.is_relative_to(ROOT / "include"), f"public header includes private implementation: {path} -> {target}"
            assert header_owners[target] == component or (component, target) in bridges, f"private component dependency: {component}: {path} -> {target}"

    def closure(name):
        result = {name}
        for dependency in ALLOWED[name]:
            if dependency in ALLOWED:
                result |= closure(dependency)
        return result

    generated = {Path(line).resolve() for line in (manifest.parent / "ir-generated-files.txt").read_text().splitlines()}
    assert generated and all(path.is_file() for path in generated), "missing declared TableGen outputs"
    for name in COMPONENTS:
        links, interface, sources = targets[name]
        assert links == interface, f"{name}: hidden private or extra interface dependencies"
        expected = ALLOWED[name]
        mlir = {link for link in expected if link.startswith("MLIR")}
        dylib = expected - mlir | {"MLIR"} if mlir else expected
        assert links in (expected, dylib) or (name == "ZkcSupport" and links == {"LLVM"}), (name, links)
        permitted = set().union(*(public_headers[d] | private_headers[d] for d in closure(name)))
        if name == "ZkcFrontend":
            permitted.discard(ROOT / "lib/Support/Input.h")
        if "ZkcIR" in closure(name):
            permitted.update(generated)
        visited = set()

        def visit(path):
            path = path.resolve()
            if path in visited:
                return
            visited.add(path)
            if path.suffix in (".h", ".inc"):
                assert path in permitted, f"{name}: upward header dependency {path}"
            for include in re.findall(r'^\s*#\s*include\s*[<"]([^">]+)[">]', path.read_text(), re.M):
                if name == "ZkcFrontend":
                    assert include not in (
                        "filesystem", "fstream", "cstdio", "stdio.h", "llvm/Support/FileSystem.h",
                        "llvm/Support/MemoryBuffer.h", "llvm/Support/Program.h",
                    ), f"{name}: input loading belongs to FrontendLoading: {path}"
                if name != "ZkcDriver":
                    assert not include.startswith("mlir/Parser/"), f"{name}: parsing belongs to Driver: {path}"
                if name == "ZkcIR":
                    assert not include.startswith(("mlir/Pass/", "mlir/Transforms/")), f"{name}: transformation dependency {include}"
                elif "ZkcIR" not in closure(name):
                    assert not include.startswith("mlir/"), f"{name}: {path} includes {include}"
                if include.endswith(".cpp.inc"):
                    assert owners.get(str(path.relative_to(ROOT))) == "ZkcIR" and path.suffix == ".cpp", f"generated implementation outside IR: {path} -> {include}"
                if include.startswith("zkc/"):
                    if path.is_relative_to(ROOT / "include") and "detail" not in path.relative_to(ROOT / "include").parts:
                        assert "/detail/" not in include, f"public header exposes unsupported detail: {path} -> {include}"
                    target = ROOT / "include" / include
                    if include.endswith(".inc"):
                        target = manifest.parent / "include" / include
                    assert target in permitted, f"{name}: upward include {path} -> {include}"
                    visit(target)
                elif (path.parent / include).is_file():
                    target = (path.parent / include).resolve()
                    frontend = ROOT / "lib/Frontend"
                    if path.is_relative_to(frontend) and target.is_relative_to(frontend):
                        owner = path.relative_to(frontend).parts[0]
                        dependency = target.relative_to(frontend).parts[0]
                        if owner in FRONTEND_LAYERS:
                            assert dependency in FRONTEND_LAYERS[owner], f"frontend phase dependency: {path} -> {target}"
                    check_private_edge(name, path, target)
                    visit(target)

        for path in public_headers[name] | {ROOT / source for source in sources}:
            visit(path)
    # Tools consume public interfaces. The source benchmark is itself a bounded
    # file-reading CLI, so it shares only the driver's private input helper.
    for directory in (ROOT / "tools", ROOT / "examples/service"):
        for path in directory.rglob("*"):
            if path.suffix not in (".cpp", ".h", ".td"):
                continue
            for include in re.findall(r'^\s*(?:#\s*include|include)\s*[<"]([^">]+)[">]', path.read_text(), re.M):
                target = (path.parent / include).resolve()
                allowed_input = path == ROOT / "tools/zkc-source-bench.cpp" and target == ROOT / "lib/Support/Input.h"
                assert not target.is_relative_to(ROOT / "lib") or allowed_input, f"tool/extension includes compiler implementation: {path} -> {include}"
                assert not include.startswith("zkc/") or not include.endswith(".cpp.inc"), f"tool/extension includes generated definitions: {path} -> {include}"
    print("component source ownership, target edges and all component include closures passed")


if __name__ == "__main__":
    main()
