"""Enforce source/header ownership and component/private phase dependencies."""

from dataclasses import dataclass, field
import os
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
COMPONENTS = ("ZkcSupport", "ZkcContracts", "ZkcLanguage", "ZkcRelation", "ZkcProgram", "ZkcIR", "ZkcTranslation", "ZkcTransforms", "ZkcCompiler", "ZkcDriver")
ALLOWED = {
    "ZkcLanguage": {"ZkcContracts", "ZkcRelation"},
    "ZkcSupport": {"LLVMSupport"},
    "ZkcContracts": {"ZkcSupport"},
    "ZkcRelation": {"ZkcContracts"},
    "ZkcProgram": {"ZkcContracts"},
    "ZkcTransforms": {"ZkcIR", "MLIRPass", "MLIRTransforms", "MLIRTransformUtils"},
    "ZkcCompiler": {"ZkcTransforms", "ZkcTranslation", "MLIRParser"},
    "ZkcDriver": {"ZkcCompiler", "MLIRParser"},
    "ZkcTranslation": {"ZkcIR", "ZkcLanguage"},
    "ZkcIR": {"ZkcProgram", "ZkcRelation", "MLIRIR", "MLIRControlFlowInterfaces", "MLIRSideEffectInterfaces", "MLIRInferTypeOpInterface", "MLIRFuncDialect", "MLIRFunctionInterfaces", "MLIRCallInterfaces", "MLIRArithDialect", "MLIRTensorDialect"},
}
HEADER_ROOTS = {
    "ZkcLanguage": ["Language"],
    "ZkcSupport": ["Support"],
    "ZkcContracts": ["Contracts"],
    "ZkcRelation": [f"Relation/{name}.h" for name in ("R1CS", "AIR", "AIRPolynomial", "Matrices")],
    "ZkcProgram": ["Program"],
    "ZkcTransforms": ["Transforms", "Target"],
    "ZkcCompiler": [f"Compiler/{name}.h" for name in (
        "Compilation", "Diagnostics", "Language", "LanguageInterface",
        "LanguagePackage", "LanguageInspection", "NativeProof", "Run",
        "PolynomialReduction", "PublicCoin", "Passes", "Pipelines")],
    "ZkcDriver": ["Driver"],
    "ZkcIR": ["Dialect", "Interfaces"],
    "ZkcTranslation": ["Translation"],
}

def header_set(entries):
    result = set()
    for entry in entries:
        path = ROOT / "include/zkc" / entry
        result.update((p for p in path.rglob("*") if p.suffix in (".h", ".def")) if path.is_dir() else [path])
    return result


@dataclass
class ContributionInventory:
    sources: dict = field(default_factory=dict)
    headers: dict = field(default_factory=dict)
    generated: dict = field(default_factory=dict)
    includes: dict = field(default_factory=dict)
    libraries: dict = field(default_factory=lambda: {name: set() for name in COMPONENTS})
    private: dict = field(default_factory=dict)
    packages: dict = field(default_factory=dict)
    dependencies: dict = field(default_factory=dict)
    registration_header: Path | None = None

    def check_package_edge(self, source, target):
        source_package, target_package = self.packages.get(source), self.packages.get(target)
        if target_package is None or source_package == target_package:
            return
        if source_package is None:
            # The central native registry is the only core file that imports
            # contributed headers. Its installation list is generated explicitly.
            assert source in (ROOT / "lib/Dialect/Registry.cpp", self.registration_header), f"core imports contribution: {source} -> {target}"
            return
        assert target not in self.private, f"cross-package private include: {source} -> {target}"
        reachable, pending = set(), [source_package]
        while pending:
            name = pending.pop()
            if name not in reachable:
                reachable.add(name)
                pending.extend(self.dependencies.get(name, ()))
        assert target_package in reachable, f"undeclared contribution dependency: {source} -> {target}"


def contributions(manifest):
    """Read only explicit extension data; core inventory/edges stay independent."""
    inventory = ContributionInventory(registration_header=manifest.parent / "include/zkc/Dialect/ContributionHeaders.h.inc")
    sources, headers, generated, includes = inventory.sources, inventory.headers, inventory.generated, inventory.includes
    private, libraries = inventory.private, inventory.libraries
    metadata = manifest.parent / "contribution-dependencies.txt"
    if not metadata.exists():
        return inventory
    for line in metadata.read_text().splitlines():
        kind, package, owner, value, installed = line.split("|")
        assert re.fullmatch(r"[A-Za-z0-9_.-]+", package) and package != "base", "invalid contribution owner"
        assert owner in ("ZkcIR", "ZkcTransforms"), "invalid contribution component"
        if kind == "DEPENDENCY":
            assert not installed and re.fullmatch(r"[A-Za-z0-9_.-]+", value), "invalid contribution dependency"
            inventory.dependencies.setdefault(package, set()).add(value)
            continue
        if kind == "LIBRARY":
            assert not installed and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.:+-]*", value), "invalid external library"
            assert not value.startswith(("Zkc", "LLVM", "MLIR")), "contribution cannot extend the core dependency graph"
            libraries[owner].add(value)
            continue
        assert kind in ("SOURCE", "HEADER", "GENERATED", "PRIVATE"), "invalid contribution inventory kind"
        path = Path(value)
        assert path.is_absolute() and path == path.resolve() and path.is_file(), f"missing or noncanonical contribution file: {path}"
        assert not path.is_relative_to(ROOT / "lib") and not path.is_relative_to(ROOT / "include"), f"contribution cannot own core files: {path}"
        alias = kind == "HEADER" and headers.get(path) == owner and inventory.packages.get(path) == package
        assert alias or (path not in sources and path not in headers and path not in generated and path not in private), f"multiple contribution owners: {path}"
        inventory.packages[path] = package
        if kind == "PRIVATE":
            assert not installed and path.suffix in (".h", ".hpp", ".def", ".inc"), "invalid private header"
            private[path] = owner
        elif kind == "SOURCE":
            assert not installed and path.suffix == ".cpp", f"invalid contribution source: {path}"
            sources[path] = owner
        else:
            relative = Path(installed)
            assert installed and not relative.is_absolute() and ".." not in relative.parts and relative.as_posix() == installed, "invalid installed contribution path"
            assert relative.parts[0] != "zkc", f"reserved core include namespace: {installed}"
            assert installed not in includes, f"conflicting installed contribution path: {installed}"
            includes[installed] = path
            if kind == "GENERATED":
                assert installed.endswith(".cpp.inc"), "invalid generated implementation owner"
                generated[path] = owner
            else:
                assert installed.endswith((".h", ".hpp", ".def", ".td", ".inc")) and not installed.endswith(".cpp.inc"), "invalid public header"
                assert owner == "ZkcIR" or installed.endswith((".h", ".hpp", ".def", ".inc")), "invalid transform header"
                headers[path] = owner
    return inventory


def main():
    manifest = Path(os.environ["ZKC_CTEST_COMPONENTS"]).resolve()
    extra = contributions(manifest)
    extra_sources, extra_headers, extra_generated = extra.sources, extra.headers, extra.generated
    extra_includes, extra_libraries, extra_private = extra.includes, extra.libraries, extra.private
    extra_namespaces = {item.split("/")[0] for item in extra_includes}
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
            source = (ROOT / source).resolve()
            assert source not in owners, f"{source} compiled by both {owners.get(source)} and {name}"
            owners[source] = name
    assert set(targets) == set(COMPONENTS), "component manifest and ownership policy disagree"
    implementation = {path.resolve() for path in (ROOT / "lib").rglob("*.cpp")}
    assert set(owners) == implementation | set(extra_sources), f"unowned or nonexistent implementations: {set(owners) ^ (implementation | set(extra_sources))}"
    for source, owner in extra_sources.items():
        assert owners[source] == owner, f"contribution component ownership: {source} belongs to {owner}"
    for source, owner in {
        "lib/Program/Admission.cpp": "ZkcProgram",
        "lib/Dialect/Algebra/IR/Mathematical.cpp": "ZkcIR",
        "lib/Dialect/Protocol/IR/Protocol.cpp": "ZkcIR",
        "lib/Transforms/MathematicalPreservation.cpp": "ZkcTransforms",
        "lib/Transforms/MathLoweringVerification.cpp": "ZkcTransforms",
    }.items():
        assert owners[ROOT / source] == owner, f"mandatory component ownership: {source} belongs to {owner}"
    private_headers = {
        "ZkcLanguage": {ROOT / f"lib/Language/{name}.h" for name in ("Internal", "State", "Semantics", "Checker", "BodyCheck", "Placement", "TypeInference")},
        "ZkcSupport": {ROOT / "lib/Support/Input.h"},
        "ZkcContracts": {ROOT / "lib/Contracts/RequirementChecks.h"},
        "ZkcRelation": {ROOT / "lib/Relation/Field.h"},
        "ZkcProgram": {ROOT / "lib/Program/EncodingLimits.h", ROOT / "lib/Program/Structure.h"},
        "ZkcIR": {ROOT / "lib/Dialect/Protocol/IR/ResourceOrigins.h", ROOT / "lib/Dialect/Verification.h", ROOT / "lib/Dialect/DomainVerification.h"},
    }
    private_headers["ZkcTranslation"] = set()
    private_headers["ZkcIR"].update((ROOT / "lib/Dialect/TypeAdapters").rglob("*.h"))
    private_headers["ZkcTransforms"] = {
        ROOT / "lib/Conversion/Bindings.h", ROOT / "lib/Target/PhysicalPlan.h",
        ROOT / "lib/Transforms/MathematicalSupport.h",
        ROOT / "lib/Transforms/MathematicalValues.h",
        ROOT / "lib/Transforms/PreparedProtocol.h",
        ROOT / "lib/Transforms/ProtocolApplications.h"
    }
    private_headers["ZkcCompiler"] = {
        ROOT / "lib/Compiler/CompilationState.h",
        ROOT / "lib/Compiler/Run.h", ROOT / "lib/Compiler/ArtifactJson.h",
        ROOT / "lib/Compiler/LanguageInterface.h",
        ROOT / "lib/Compiler/NativeDeployment.h",
        ROOT / "lib/Compiler/NativeProofVerification.h",
    }
    private_headers["ZkcDriver"] = set((ROOT / "lib/Driver").glob("*.h"))
    public_headers = {name: header_set(roots) for name, roots in HEADER_ROOTS.items()}

    header_owners = {}
    for name in COMPONENTS:
        for path in public_headers[name] | private_headers[name]:
            assert path.is_file(), f"nonexistent header: {path}"
            assert path not in header_owners, f"multiple owners: {path}"
            header_owners[path] = name
    assert set(header_owners) == {p for p in (ROOT / "include/zkc").rglob("*") if p.suffix in (".h", ".def")} | set((ROOT / "lib").rglob("*.h")), "unowned headers"
    for path, owner in extra_headers.items():
        header_owners[path] = owner
        if path.suffix != ".td":
            public_headers[owner].add(path)
    for path, owner in extra_private.items():
        header_owners[path] = owner
        private_headers[owner].add(path)
    public = set().union(*public_headers.values())
    supported_public = {
        path for path in public
        if not (path.is_relative_to(ROOT / "include") and
                "detail" in path.relative_to(ROOT / "include").parts)
    }
    private = set().union(*private_headers.values())
    # Implementation bridges are explicit and uninstalled. Each grants only
    # the named header, never the rest of its owner's private implementation.
    bridges = {("ZkcDriver", ROOT / "lib/Support/Input.h"),
               ("ZkcCompiler", ROOT / "lib/Transforms/PreparedProtocol.h")}
    assert not (ROOT / "include/zkc/Dialect/Builders.h").exists(), "raw builders belong to unsupported detail"

    def check_private_edge(component, path, target):
        if target.resolve() in registration_fragments:
            assert path == ROOT / "lib/Dialect/Registry.cpp", f"private dialect registration fragment: {path} -> {target}"
        semantic_files = {"State.h", "Semantics.h", "Semantics.cpp", "SemanticContracts.cpp",
                          "KernelSignatures.cpp", "IntrinsicSignatures.cpp", "Permissions.cpp",
                          "Capabilities.cpp", "Specialize.cpp", "Layout.cpp"}
        if path.parent == ROOT / "lib/Language" and path.name in semantic_files:
            assert target not in {ROOT / f"lib/Language/{name}.h" for name in ("Internal", "Checker", "BodyCheck")}, f"semantic queries cannot depend on source checking: {path} -> {target}"
        if target in private:
            assert path not in public, f"public header includes private implementation: {path} -> {target}"
            assert header_owners[target] == component or (component, target) in bridges, f"private component dependency: {component}: {path} -> {target}"

    def closure(name):
        result = {name}
        for dependency in ALLOWED[name]:
            if dependency in ALLOWED:
                result |= closure(dependency)
        return result

    generated = {Path(line).resolve() for line in (manifest.parent / "ir-generated-files.txt").read_text().splitlines()}
    registration_fragments = {
        (manifest.parent / "include/zkc/Dialect" / filename).resolve()
        for filename in ("BuiltinHeaders.h.inc", "BuiltinDialects.inc",
                         "ContributionHeaders.h.inc", "ContributionDialects.inc")
    }
    assert registration_fragments <= generated, "missing private registration inventory"
    contract_declarations = manifest.parent / "include/zkc/Contracts/Declarations.cpp.inc"
    assert contract_declarations.is_file(), "missing neutral contract declarations"
    assert contract_declarations not in generated, "neutral declarations must not belong to IR generation"
    assert generated and all(path.is_file() for path in generated), "missing declared TableGen outputs"
    for name in COMPONENTS:
        links, interface, sources = targets[name]
        # PRIVATE external links appear as LINK_ONLY interface requirements in
        # static builds and disappear from the interface in shared builds.
        external = extra_libraries[name]
        assert external <= links, f"{name}: missing declared external dependency"
        links = links - external
        interface = interface - external - {f"$<LINK_ONLY:{link}>" for link in external}
        assert links == interface, f"{name}: hidden private or extra interface dependencies"
        expected = ALLOWED[name]
        mlir = {link for link in expected if link.startswith("MLIR")}
        dylib = expected - mlir | {"MLIR"} if mlir else expected
        assert links in (expected, dylib) or (name == "ZkcSupport" and links == {"LLVM"}), (name, links)
        permitted = set().union(*(public_headers[d] | private_headers[d] for d in closure(name)))
        if name in ("ZkcLanguage",):
            permitted.discard(ROOT / "lib/Support/Input.h")
        if "ZkcIR" in closure(name):
            permitted.update(generated)
        permitted.update(path for path, owner in extra_generated.items() if owner in closure(name))
        if name == "ZkcContracts":
            permitted.add(contract_declarations)
        visited = set()

        def visit(path):
            path = path.resolve()
            if path in visited:
                return
            visited.add(path)
            if path.suffix in (".h", ".hpp", ".def", ".inc"):
                assert path in permitted, f"{name}: upward header dependency {path}"
            for include in re.findall(r'^\s*#\s*include\s*[<"]([^">]+)[">]', path.read_text(), re.M):
                if name in ("ZkcLanguage",):
                    assert include not in (
                        "filesystem", "fstream", "cstdio", "stdio.h", "llvm/Support/FileSystem.h",
                        "llvm/Support/MemoryBuffer.h", "llvm/Support/Program.h",
                    ), f"{name}: input loading belongs to Driver: {path}"
                # Invocation owns in-memory MLIR parsing; Driver additionally
                # owns command-line file loading. Lower layers consume IR.
                if name not in ("ZkcCompiler", "ZkcDriver"):
                    assert not include.startswith("mlir/Parser/"), f"{name}: parsing belongs to Compiler or Driver: {path}"
                if name == "ZkcIR":
                    assert not include.startswith(("mlir/Pass/", "mlir/Transforms/")), f"{name}: transformation dependency {include}"
                elif "ZkcIR" not in closure(name):
                    assert not include.startswith("mlir/"), f"{name}: {path} includes {include}"
                if include.endswith(".cpp.inc"):
                    neutral = (path == ROOT / "lib/Contracts/Declarations.cpp" and
                               include == "zkc/Contracts/Declarations.cpp.inc" and
                               owners.get(path) == "ZkcContracts")
                    contribution = extra_includes.get(include)
                    if contribution is None and (path.parent / include).is_file():
                        contribution = (path.parent / include).resolve()
                    generated_owner = extra_generated.get(contribution) or extra_private.get(contribution)
                    implementation_owner = owners.get(path)
                    if generated_owner:
                        assert extra.packages.get(path) == extra.packages[contribution], f"cross-package generated definitions: {path} -> {include}"
                    allowed = (implementation_owner == generated_owner if generated_owner else implementation_owner == "ZkcIR")
                    assert neutral or (allowed and path.suffix == ".cpp"), f"generated implementation outside its owner: {path} -> {include}"
                if include.startswith("zkc/"):
                    if path in supported_public:
                        assert "/detail/" not in include, f"public header exposes unsupported detail: {path} -> {include}"
                    target = ROOT / "include" / include
                    if include.endswith(".inc"):
                        target = manifest.parent / "include" / include
                    assert target in permitted, f"{name}: upward include {path} -> {include}"
                    extra.check_package_edge(path, target)
                    check_private_edge(name, path, target)
                    visit(target)
                elif include in extra_includes:
                    target = extra_includes[include]
                    assert target in permitted, f"{name}: upward include {path} -> {include}"
                    extra.check_package_edge(path, target)
                    check_private_edge(name, path, target)
                    visit(target)
                elif (path.parent / include).is_file():
                    target = (path.parent / include).resolve()
                    extra.check_package_edge(path, target)
                    check_private_edge(name, path, target)
                    visit(target)
                elif (include.split("/")[0] in extra_namespaces or
                      (include.endswith((".h.inc", ".cpp.inc")) and
                       not include.startswith(("mlir/", "llvm/")))):
                    raise AssertionError(f"unregistered contribution include: {path} -> {include}")

        for path in public_headers[name] | {ROOT / source for source in sources}:
            visit(path)
    comparison = (ROOT / "lib/Translation/Language/Comparison.cpp").read_text()
    assert "emitOriginal(" not in comparison, "source comparison must not call emission"
    # Tools and extensions consume public interfaces.
    for directory in (ROOT / "tools", ROOT / "examples"):
        for path in directory.rglob("*"):
            if path.suffix not in (".cpp", ".h", ".td"):
                continue
            for include in re.findall(r'^\s*(?:#\s*include|include)\s*[<"]([^">]+)[">]', path.read_text(), re.M):
                target = (path.parent / include).resolve()
                if include.startswith("zkc/") and include.endswith(".inc"):
                    target = (manifest.parent / "include" / include).resolve()
                assert target not in registration_fragments, f"private dialect registration fragment: {path} -> {target}"
                assert not target.is_relative_to(ROOT / "lib"), f"tool/extension includes compiler implementation: {path} -> {include}"
                assert not include.startswith("zkc/") or not include.endswith(".cpp.inc"), f"tool/extension includes generated definitions: {path} -> {include}"
    print("component source ownership, target edges and all component include closures passed")


if __name__ == "__main__":
    main()
