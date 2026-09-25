"""Enforce common-service and coordinated IR dependency boundaries."""

import os
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
COMPONENTS = ("ZkcSupport", "ZkcContracts", "ZkcRelation", "ZkcProtocol", "ZkcIR")
ALLOWED = {
    "ZkcSupport": {"LLVMSupport"},
    "ZkcContracts": {"ZkcSupport"},
    "ZkcRelation": {"ZkcContracts"},
    "ZkcProtocol": {"ZkcRelation"},
    "ZkcIR": {"ZkcProtocol", "MLIRIR", "MLIRControlFlowInterfaces", "MLIRSideEffectInterfaces", "MLIRInferTypeOpInterface", "MLIRFuncDialect"},
}
HEADER_ROOTS = {
    "ZkcSupport": ["Support/Json.h", "Support/MLIRInput.h"],
    "ZkcContracts": ["Contracts"],
    "ZkcRelation": [f"Relation/{name}.h" for name in ("R1CS", "AIR", "AIRPolynomial", "Matrices")],
    "ZkcProtocol": ["Source", "Analysis", "Protocol/Admission.h", "Protocol/Instantiation.h", "Protocol/PhysicalOptions.h"],
    "ZkcIR": ["Dialect", "Interfaces", "Translation"],
}


def header_set(entries):
    result = set()
    for entry in entries:
        path = ROOT / "include/zkc" / entry
        result.update(path.rglob("*.h") if path.is_dir() else [path])
    return result


def main():
    manifest = Path(os.environ["ZKC_CTEST_COMPONENTS"])
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
    permitted = set()
    generated = {Path(line).resolve() for line in (manifest.parent / "ir-generated-files.txt").read_text().splitlines()}
    assert generated and all(path.is_file() for path in generated), "missing declared TableGen outputs"
    for name in COMPONENTS:
        links, interface, sources = targets[name]
        assert links == interface, f"{name}: hidden private or extra interface dependencies"
        assert links == ALLOWED[name] or (name == "ZkcSupport" and links == {"LLVM"}), (name, links)
        permitted.update(header_set(HEADER_ROOTS[name]) | private_headers[name])
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
                    visit(path.parent / include)

        for path in header_set(HEADER_ROOTS[name]) | {ROOT / source for source in sources}:
            visit(path)
    print("component source ownership, target edges and common/IR include closures passed")


if __name__ == "__main__":
    main()
