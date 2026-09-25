"""Enforce common, IR and pure frontend dependency boundaries."""

import os
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
COMPONENTS = ("ZkcSupport", "ZkcContracts", "ZkcRelation", "ZkcProtocol", "ZkcIR", "ZkcFrontend", "ZkcFrontendLoading")
ALLOWED = {
    "ZkcFrontend": {"ZkcProtocol"},
    "ZkcFrontendLoading": {"ZkcFrontend"},
    "ZkcSupport": {"LLVMSupport"},
    "ZkcContracts": {"ZkcSupport"},
    "ZkcRelation": {"ZkcContracts"},
    "ZkcProtocol": {"ZkcRelation"},
    "ZkcIR": {"ZkcProtocol", "MLIRIR", "MLIRControlFlowInterfaces", "MLIRSideEffectInterfaces", "MLIRInferTypeOpInterface", "MLIRFuncDialect"},
}
HEADER_ROOTS = {
    "ZkcFrontend": ["Frontend"],
    "ZkcFrontendLoading": ["Frontend/Loading.h"],
    "ZkcSupport": ["Support/Json.h", "Support/MLIRInput.h"],
    "ZkcContracts": ["Contracts"],
    "ZkcRelation": [f"Relation/{name}.h" for name in ("R1CS", "AIR", "AIRPolynomial", "Matrices")],
    "ZkcProtocol": ["Source", "Analysis", "Protocol/Admission.h", "Protocol/Instantiation.h", "Protocol/PhysicalOptions.h"],
    "ZkcIR": ["Dialect", "Interfaces", "Translation"],
}

# Private frontend headers are phase contracts. The model and syntax owners
# cannot reach a checker; selection cannot perform library elaboration; no pure
# phase can discover inputs through the optional loader.
FRONTEND_LAYERS = {
    "Library": {"Library"},
    "Model": {"Model"},
    "Syntax": {"Syntax"},
    "Static": {"Static", "Syntax"},
    "Resolution": {"Resolution", "Syntax"},
    "Instantiation": {"Instantiation", "Resolution", "Static", "Syntax"},
    "Lowering": {"Lowering", "Library", "Model", "Resolution", "Syntax"},
    "Semantics": {"Semantics", "Instantiation", "Library", "Lowering", "Model", "Resolution", "Static", "Syntax"},
    "Tooling": {"Tooling", "Lowering", "Model", "Resolution", "Semantics", "Syntax"},
    "Loading": {"Loading", "Syntax"},
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
        targets[name] = (
            set(filter(None, links.split(";"))),
            set(filter(None, interface.split(";"))),
            list(filter(None, sources.split(";"))),
        )
        for source in targets[name][2]:
            assert source not in owners, f"{source} compiled by both {owners.get(source)} and {name}"
            owners[source] = name
    implementation = {str(path.relative_to(ROOT)) for path in (ROOT / "lib").rglob("*.cpp")}
    assert set(owners) == implementation, f"unowned or nonexistent implementations: {set(owners) ^ implementation}"
    assert targets["ZkcCompiler"] == (set(), {"ZkcCompilerCore"}, []), "aggregate must not compile sources"
    private_headers = {
        "ZkcSupport": {ROOT / "lib/Support/Input.h"},
        "ZkcContracts": {ROOT / "lib/Contracts/RequirementChecks.h"},
        "ZkcRelation": {ROOT / "lib/Relation/Field.h"},
        "ZkcProtocol": {ROOT / "lib/Protocol/EncodingLimits.h"},
        "ZkcIR": {ROOT / "lib/Dialect/Plan/IR/PhysicalEncoding.h", ROOT / "lib/Dialect/Verification.h"},
    }
    private_headers["ZkcFrontend"] = set((ROOT / "lib/Frontend").rglob("*.h")) - set((ROOT / "lib/Frontend/Loading").rglob("*.h"))
    private_headers["ZkcFrontendLoading"] = set((ROOT / "lib/Frontend/Loading").rglob("*.h"))
    public_headers = {name: header_set(roots) for name, roots in HEADER_ROOTS.items()}
    public_headers["ZkcFrontend"] -= public_headers["ZkcFrontendLoading"]

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
        assert links == ALLOWED[name] or (name == "ZkcSupport" and links == {"LLVM"}), (name, links)
        permitted = set().union(*(public_headers[d] | private_headers[d] for d in closure(name)))
        if name == "ZkcFrontend":
            permitted.discard(ROOT / "lib/Support/Input.h")
        if name == "ZkcIR":
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
                        "filesystem", "fstream", "llvm/Support/FileSystem.h",
                        "llvm/Support/MemoryBuffer.h", "llvm/Support/Program.h",
                    ), f"{name}: input loading belongs to FrontendLoading: {path}"
                if name == "ZkcIR":
                    assert not include.startswith(("mlir/Pass/", "mlir/Transforms/")), f"{name}: transformation dependency {include}"
                else:
                    assert not include.startswith("mlir/"), f"{name}: {path} includes {include}"
                if include.startswith("zkc/"):
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
                    visit(target)

        for path in public_headers[name] | {ROOT / source for source in sources}:
            visit(path)
    print("component source ownership, target edges and common/IR/frontend include closures passed")


if __name__ == "__main__":
    main()
