"""Finite installation ownership, deterministic order and dependency checks."""

import hashlib
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from tools import ROOT, records, tool


def cmake_controls(args):
    """Script and minimal project controls never configure MLIR or build code."""
    from cases import case

    # A private compiler tree permits core-file and symlink refusal controls
    # without creating files in the checkout's owned include/lib directories.
    compiler = args.work / "compiler"
    module = compiler / "cmake/ZkcContributions.cmake"
    module.parent.mkdir(parents=True, exist_ok=True)
    module.write_text(args.cmake_module.read_text())
    descriptor = module.with_name("BuiltinIR.cmake")
    descriptor.write_text(args.cmake_module.with_name(descriptor.name).read_text())
    core_source = compiler / "lib/Core.cpp"
    core_header = compiler / "include/Core.h"
    for path in (core_source, core_header):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("// Core-owned fixture.\n")

    def configure(declarations, expected=None):
        script = args.work / "assembly.cmake"
        script.write_text(
            f'cmake_minimum_required(VERSION 3.21)\ninclude("{module}")\n'
            + declarations + f'\nzkc_assemble_contributions("{args.work / "output/include"}")\n'
        )
        result = subprocess.run(["cmake", "-P", str(script)], text=True, capture_output=True, check=False)
        if expected:
            assert result.returncode > 0 and expected in result.stderr, result.stderr
            return None
        assert result.returncode == 0, result.stderr
        return (args.work / "output/include/zkc/Contracts/Installation.td").read_text()

    def registration(name, extra=""):
        directory = args.work / name / "include"
        directory.mkdir(parents=True, exist_ok=True)
        neutral = directory / f"{name}.td"
        native = directory / f"{name}-native.td"
        neutral.write_text("// Neutral fragment.\n")
        native.write_text("// Native fragment.\n")
        return f'zkc_add_contribution(NAME {name} DECLARATIONS "{neutral}" BINDINGS "{native}" INCLUDE_DIRECTORIES "{directory}" {extra})\n'

    assert configure(registration("first") + registration("second")) == configure(registration("second") + registration("first"))
    # Identifiers are strings, including names CMake treats as false constants.
    for name in ("OFF", "0", "NO", "FALSE", "missing-NOTFOUND"):
        with case(f"literal contribution name: {name}"):
            assert f'ZKC_Contribution<"{name}"' in configure(registration(name))
            assembled = configure(registration("first", f"DEPENDS {name}") + registration(name))
            assert assembled.index(f'ZKC_Contribution<"{name}"') < assembled.index('ZKC_Contribution<"first"')
    with case("false-valued unknown registration argument"):
        configure(registration("first").replace("NAME first", "OFF NAME first"),
                  "Invalid zkc contribution arguments")
    configure(registration("first", "DEPENDS missing"), "Missing zkc contribution dependency")
    configure(registration("first", "DEPENDS second") + registration("second", "DEPENDS first"), "Cyclic zkc contribution dependencies")
    configure(registration("first") * 2, "Duplicate zkc contribution")
    configure('zkc_add_contribution(NAME partial DECLARATIONS "missing.td")', "Missing DECLARATIONS fragment")
    configure(f'zkc_add_contribution(NAME partial DECLARATIONS "{args.work / "first/include/first.td"}")', "requires BINDINGS")

    first = args.work / "first/include"
    second = args.work / "second/include"
    header = first / "Shared.h"
    other = second / "Shared.h"
    header.write_text("// First owner.\n")
    other.write_text("// Second owner.\n")
    configure(registration("first") + registration("second"), "Conflicting installed contribution path")
    header.unlink()
    other.unlink()
    # One physical header must not acquire two declared owners either.
    shared = registration("second").replace(f'INCLUDE_DIRECTORIES "{second}"', f'INCLUDE_DIRECTORIES "{first}"')
    configure(registration("first") + shared, "Multiple contribution header owners")
    header.write_text("// Transform-only interface.\n")
    configure(registration("first", f'TRANSFORM_HEADERS "{header}"'))
    configure(registration("first", f'TRANSFORM_HEADERS "{header}" HEADERS Shared.h'), "HEADERS must name an owned IR header")
    configure(registration("first", f'TRANSFORM_HEADERS "{first / "first.td"}"'), "TRANSFORM_HEADERS must name inventoried headers or generated sources")
    configure(registration("first", f'PUBLIC_HEADERS "{header}"'), "PUBLIC_HEADERS requires generated .h.inc paths")
    configure(registration("first", f'GENERATED_SOURCES "{header}"'), "GENERATED_SOURCES requires generated .cpp.inc paths")
    outside = args.work / "Outside.h.inc"
    configure(registration("first", f'PUBLIC_HEADERS "{outside}"'), "Contribution file must belong to one include root")
    nested = first / "nested"
    nested.mkdir(exist_ok=True)
    nested_header = nested / "Api.h"
    nested_header.write_text("// Ambiguous include root.\n")
    overlapping = registration("first").replace(f'INCLUDE_DIRECTORIES "{first}"', f'INCLUDE_DIRECTORIES "{first}" "{nested}"')
    configure(overlapping, "Ambiguous installed contribution path")
    nested_header.unlink()
    header.unlink()
    source = args.work / "native.cpp"
    source.write_text("// IR implementation.\n")
    configure(registration("first", f'IR_SOURCES "{source}" TRANSFORM_SOURCES "{source}"'), "Multiple contribution source owners")
    configure(registration("first", f'IR_SOURCES "{source}"') + registration("second", f'IR_SOURCES "{source}"'), "Multiple contribution source owners")
    for library in ("ZkcTransforms", "Zkc::Frontend", "MLIRPass", "$<LINK_ONLY:ZkcTransforms>"):
        configure(registration("first", f'LINK_LIBRARIES "{library}"'), "Invalid contribution external library")
    configure(registration("first", 'LINK_LIBRARIES Vendor::IR TRANSFORM_LINK_LIBRARIES Vendor::Pass'))

    def project(name, targets, extra="LINK_LIBRARIES Vendor::IR", expected=None):
        directory = args.work / "link-controls" / name
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "CMakeLists.txt").write_text(
            f'cmake_minimum_required(VERSION 3.21)\nproject(ExternalLinks NONE)\ninclude("{module}")\n'
            + targets + registration("first", extra)
            + '\nzkc_assemble_contributions("${CMAKE_CURRENT_BINARY_DIR}/include")\n'
            # Like Components.cmake, resolve forward references only after
            # assembly and after all core targets have been defined.
            + 'add_library(ZkcFrontend INTERFACE)\n'
            + 'add_library(Zkc::Frontend ALIAS ZkcFrontend)\n'
            + 'add_library(LLVMCore INTERFACE IMPORTED)\n'
            + 'add_library(MLIRPass INTERFACE IMPORTED)\n'
            + 'add_library(Vendor::CoreAlias ALIAS ZkcFrontend)\n'
            + 'add_library(Vendor::LLVMAlias ALIAS LLVMCore)\n'
            + 'zkc_validate_contribution_libraries()\n'
        )
        result = subprocess.run(
            ["cmake", "-S", str(directory), "-B", str(directory / "build")],
            text=True, capture_output=True, check=False,
        )
        (directory / "configure.log").write_text(result.stdout + result.stderr)
        if expected:
            assert result.returncode > 0 and expected in result.stderr, result.stderr
        else:
            assert result.returncode == 0, result.stderr

    with case("header inventory follows incremental additions and removals"):
        directory = args.work / "inventory-project"
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "CMakeLists.txt").write_text(
            f'cmake_minimum_required(VERSION 3.21)\nproject(Inventory NONE)\ninclude("{module}")\n'
            + registration("inventory")
            + '\nzkc_assemble_contributions("${CMAKE_CURRENT_BINARY_DIR}/include")\n')
        build = directory / "build"
        subprocess.run(["cmake", "-S", str(directory), "-B", str(build)],
                       check=True, capture_output=True, text=True)
        manifest = build / "contribution-dependencies.txt"
        added = args.work / "inventory/include/Added.h"
        assert str(added) not in manifest.read_text()
        added.write_text("// Incrementally discovered public header.\n")
        subprocess.run(["cmake", "--build", str(build)], check=True, capture_output=True, text=True)
        assert str(added) in manifest.read_text()
        added.unlink()
        subprocess.run(["cmake", "--build", str(build)], check=True, capture_output=True, text=True)
        assert str(added) not in manifest.read_text()

    with case("symlinked contribution fragments share canonical include roots"):
        canonical = args.work / "symlinked"
        declaration = registration("symlinked")
        alias = args.work / "alias"
        alias.symlink_to(canonical, target_is_directory=True)
        assert 'include "symlinked.td"' in configure(declaration.replace(str(canonical), str(alias)))

    with case("private headers and transform generated definitions have explicit owners"):
        private = args.work / "Internal.hpp"
        private.write_text("// Private implementation.\n")
        generated = first / "Pass.cpp.inc"
        configure(registration("first", f'PRIVATE_HEADERS "{private}" GENERATED_SOURCES "{generated}" TRANSFORM_HEADERS "{private}" "{generated}"'))
        inventory = (args.work / "output/contribution-dependencies.txt").read_text()
        assert f"PRIVATE|first|ZkcTransforms|{private}|" in inventory
        assert f"GENERATED|first|ZkcTransforms|{generated}|" in inventory
        configure(registration("first", f'PRIVATE_HEADERS "{first / "first.td"}"'), "PRIVATE_HEADERS must name private source headers")
        public = first / "Public.h"
        public.write_text("// Public.\n")
        configure(registration("first", f'PRIVATE_HEADERS "{public}"'), "inside a public include root")
        public.unlink()

    with case("handwritten fragments install; stale generated outputs stay outside inventory"):
        fragment = first / "Fields.inc"
        fragment.write_text("// Handwritten public include.\n")
        configure(registration("first", f'TRANSFORM_HEADERS "{fragment}"'))
        inventory = (args.work / "output/contribution-dependencies.txt").read_text()
        assert f"HEADER|first|ZkcTransforms|{fragment}|" in inventory
        fragment.unlink()
        generated = first / "Hidden.cpp.inc"
        generated.write_text("// Generated implementation.\n")
        configure(registration("first"))
        assert "Hidden.cpp.inc" not in (args.work / "output/contribution-dependencies.txt").read_text()
        generated.unlink()

    with case("public header aliases preserve spelling and canonical ownership"):
        real = first / "Real.hpp"
        real.write_text("// Shared public header.\n")
        alias = first / "Alias.hpp"
        alias.symlink_to(real.name)
        configure(registration("first", 'HEADERS Alias.hpp'))
        inventory = (args.work / "output/contribution-dependencies.txt").read_text()
        assert f"HEADER|first|ZkcIR|{real}|Alias.hpp" in inventory
        assert f"HEADER|first|ZkcIR|{real}|Real.hpp" in inventory
        private = args.work / "Private.h"
        private.write_text("// Must not be exported by an alias.\n")
        leak = first / "Public.h"
        leak.symlink_to(private)
        configure(registration("first", f'PRIVATE_HEADERS "{private}"'), "aliases a private implementation")
        leak.unlink()
        alias.unlink()
        real.unlink()
        outside = args.work / "outside"
        outside.mkdir()
        (outside / "Nested.h").write_text("// Shared directory.\n")
        linked = first / "linked"
        linked.symlink_to(outside, target_is_directory=True)
        configure(registration("first"))
        inventory = (args.work / "output/contribution-dependencies.txt").read_text()
        assert f"{outside / 'Nested.h'}|linked/Nested.h" in inventory
        linked.unlink()
        stale = first / "Stale.h.inc"
        stale.write_text("// Obsolete generated output.\n")
        configure(registration("first"))
        assert "Stale.h.inc" not in (args.work / "output/contribution-dependencies.txt").read_text()
        stale.unlink()

    imported = 'add_library(Vendor::IR INTERFACE IMPORTED)\n'
    leaf = 'add_library(Vendor::Leaf INTERFACE IMPORTED)\n'
    with case("imported contribution libraries and alias"):
        project("imported", imported + leaf + 'add_library(Vendor::Alias ALIAS Vendor::Leaf)\n',
                "LINK_LIBRARIES Vendor::IR TRANSFORM_LINK_LIBRARIES Vendor::Alias")
    with case("imported binary library with platform dependencies"):
        project("imported-binary", f'''
add_library(Vendor::IR UNKNOWN IMPORTED)
set_target_properties(Vendor::IR PROPERTIES
  IMPORTED_LOCATION "{args.work / 'libvendor.a'}"
  INTERFACE_LINK_LIBRARIES "pthread;m;dl")
''')
    with case("imported location metadata cannot disguise reserved libraries"):
        project("reserved-location", 'add_library(Vendor::IR UNKNOWN IMPORTED)\nset_target_properties(Vendor::IR PROPERTIES IMPORTED_LOCATION "/vendor/libMLIR.so")\n', expected="imported location reaches a reserved library")
        project("reserved-config-location", 'add_library(Vendor::IR UNKNOWN IMPORTED)\nset_target_properties(Vendor::IR PROPERTIES IMPORTED_CONFIGURATIONS DEBUG IMPORTED_LOCATION_DEBUG "/vendor/libLLVMCore.a")\n', expected="imported location reaches a reserved library")

    with case("transitive imported wrappers, platform libraries and cycle"):
        project("wrapped", imported + leaf + '''
add_library(Vendor::Alias ALIAS Vendor::Leaf)
set_property(TARGET Vendor::IR PROPERTY INTERFACE_LINK_LIBRARIES
  "$<LINK_ONLY:$<BUILD_INTERFACE:Vendor::Alias;pthread>>;$<INSTALL_INTERFACE:m;dl>;-pthread")
set_property(TARGET Vendor::Leaf PROPERTY INTERFACE_LINK_LIBRARIES "Vendor::IR")
''')
    with case("external library paths, -l flags and configuration branches"):
        library = args.work / "libvendor.a"
        library.write_bytes(b"!<arch>\n")
        project("library-path", imported + f'set_property(TARGET Vendor::IR PROPERTY INTERFACE_LINK_LIBRARIES "{library};-lm;$<$<CONFIG:Debug>:pthread>;$<$<NOT:$<CONFIG:Debug>>:dl>")\n')
        reserved = args.work / "libLLVMCore.a"
        reserved.write_bytes(b"!<arch>\n")
        project("reserved-file", imported + f'set_property(TARGET Vendor::IR PROPERTY INTERFACE_LINK_LIBRARIES "{reserved}")\n', expected="reaches a reserved target")
        project("reserved-config", imported + 'set_property(TARGET Vendor::IR PROPERTY INTERFACE_LINK_LIBRARIES "$<$<CONFIG:Debug>:MLIRPass>")\n', expected="reaches a reserved target")
        project("reserved-flag", imported + 'set_property(TARGET Vendor::IR PROPERTY INTERFACE_LINK_LIBRARIES "-lLLVMCore")\n', expected="reaches a reserved target")

    helper = f'add_library(helper STATIC "{source}")\ntarget_link_libraries(helper PUBLIC ZkcFrontend)\n'
    for name, targets, extra, expected in (
        ("helper", helper, "LINK_LIBRARIES helper", "must be IMPORTED: helper"),
        ("helper-alias", helper + 'add_library(Vendor::Helper ALIAS helper)\n',
         "LINK_LIBRARIES Vendor::Helper", "must be IMPORTED: helper"),
        ("transform-helper", helper, "TRANSFORM_LINK_LIBRARIES helper", "must be IMPORTED: helper"),
        ("raw-registration", "", "LINK_LIBRARIES pthread", "must name an IMPORTED target"),
        ("missing-registration", "", "LINK_LIBRARIES Vendor::Missing", "must name an IMPORTED target"),
    ):
        with case(f"external library refusal: {name}"):
            project(name, targets, extra, expected)
    for name, dependency, expected in (
        ("upward", "ZkcFrontend", "reaches a reserved target"),
        ("core-alias", "Vendor::CoreAlias", "reaches a reserved target"),
        ("llvm-alias", "Vendor::LLVMAlias", "reaches a reserved target"),
        ("llvm", "LLVMCore", "reaches a reserved target"),
        ("mlir", "MLIRPass", "reaches a reserved target"),
        ("reserved-raw", "MLIRFuture", "reaches a reserved target"),
        ("local-transitive", "helper", "must be IMPORTED: helper"),
        ("local-alias-transitive", "Vendor::Helper", "must be IMPORTED: helper"),
        ("link-only", "$<LINK_ONLY:ZkcFrontend>", "reaches a reserved target"),
        ("build-interface", "$<BUILD_INTERFACE:ZkcFrontend>", "reaches a reserved target"),
        ("install-interface", "$<INSTALL_INTERFACE:ZkcFrontend>", "reaches a reserved target"),
        ("wrapper-list", "$<LINK_ONLY:$<BUILD_INTERFACE:m;Vendor::CoreAlias>>", "reaches a reserved target"),
        ("configuration-core", "$<$<CONFIG:Debug>:ZkcFrontend>", "reaches a reserved target"),
        ("unsupported-nested", "$<LINK_ONLY:$<TARGET_NAME_IF_EXISTS:ZkcFrontend>>", "Unsupported contribution external link interface"),
        ("unclosed", "$<LINK_ONLY:m", "Unsupported contribution external link interface"),
        ("extra-close", "m>", "Unsupported contribution external link interface"),
        ("link-flag", "-lZkcFrontend", "reaches a reserved target"),
        ("missing-transitive", "Vendor::Missing", "target is not visible"),
    ):
        with case(f"transitive external library refusal: {name}"):
            project(name, imported + leaf + helper + 'add_library(Vendor::Helper ALIAS helper)\n'
                    + 'set_property(TARGET Vendor::IR PROPERTY INTERFACE_LINK_LIBRARIES Vendor::Leaf)\n'
                    + f'set_property(TARGET Vendor::Leaf PROPERTY INTERFACE_LINK_LIBRARIES "{dependency}")\n',
                    expected=expected)

    for kind, path in (
        ("IR_SOURCES", core_source), ("TRANSFORM_SOURCES", core_source),
        ("INCLUDE_DIRECTORIES", compiler / "include"),
        ("INCLUDE_DIRECTORIES", compiler / "lib"),
        ("TRANSFORM_HEADERS", core_header),
        ("PUBLIC_HEADERS", compiler / "include/missing/Future.h.inc"),
        ("GENERATED_SOURCES", compiler / "lib/missing/Future.cpp.inc"),
    ):
        with case(f"core path refusal: {kind} {path.name}"):
            configure(registration("first", f'{kind} "{path}"'), "Contribution cannot own core files")
    source_alias = args.work / "core-source.cpp"
    source_alias.symlink_to(core_source)
    include_alias = args.work / "core-include"
    include_alias.symlink_to(compiler / "include", target_is_directory=True)
    for kind, path in (
        ("IR_SOURCES", source_alias), ("INCLUDE_DIRECTORIES", include_alias),
        ("PUBLIC_HEADERS", include_alias / "missing/Future.h.inc"),
    ):
        with case(f"symlink core path refusal: {kind}"):
            configure(registration("first", f'{kind} "{path}"'), "Contribution cannot own core files")
    with case("inventoried symlink header cannot own core file"):
        header_alias = first / "CoreAlias.h"
        header_alias.symlink_to(core_header)
        try:
            configure(registration("first"), "Contribution cannot own core files")
        finally:
            header_alias.unlink()
    with case("dangling generated header symlink refuses"):
        header_alias = first / "FutureAlias.h.inc"
        header_alias.symlink_to(compiler / "include/missing/Future.h.inc")
        try:
            configure(registration("first", f'PUBLIC_HEADERS "{header_alias}"'),
                      "Unresolved contribution path symlink")
        finally:
            header_alias.unlink()

    # Future outputs participate before any producer has run.
    generated = first / "Future.h.inc"
    conflict = second / "Future.h.inc"
    configure(registration("first", f'PUBLIC_HEADERS "{generated}"'))
    metadata = (args.work / "output/contribution-dependencies.txt").read_text()
    assert f'HEADER|first|ZkcIR|{generated}|Future.h.inc' in metadata
    configure(registration("first", f'PUBLIC_HEADERS "{generated}"') + registration("second", f'PUBLIC_HEADERS "{conflict}"'), "Conflicting installed contribution path")
    generated.write_text("// Existing generated public header.\n")
    configure(registration("first"))
    assert str(generated) not in (args.work / "output/contribution-dependencies.txt").read_text()
    configure(registration("first", f'PUBLIC_HEADERS "{generated}"'))
    configure(registration("first", f'PUBLIC_HEADERS "{generated}"') + registration("second", f'PUBLIC_HEADERS "{conflict}"'), "Conflicting installed contribution path")
    conflict.write_text("// Conflicting generated public header.\n")
    configure(registration("first", f'PUBLIC_HEADERS "{generated}"') + registration("second", f'PUBLIC_HEADERS "{conflict}"'), "Conflicting installed contribution path")
    generated.unlink()
    conflict.unlink()
    for installed in ("zkc/Support/Future.h", "zkc/Dialect/Future.h.inc", "zkc/Future.td"):
        reserved = first / installed
        reserved.parent.mkdir(parents=True, exist_ok=True)
        if installed.endswith(".inc"):
            configure(registration("first", f'PUBLIC_HEADERS "{reserved}"'), "Reserved core include namespace")
        else:
            reserved.write_text("// Reserved core path.\n")
            configure(registration("first"), "Reserved core include namespace")
            reserved.unlink()
    configure(registration("first", 'HEADERS "absent/Api.h"'), "HEADERS must name an owned IR header")
    for owner in ("Installed", "Resources", "CoreTypeAdapters", "ResourceTypeAdapters"):
        with case(f"base adapter output and owner collision: {owner}"):
            configure(registration("first", f'ADAPTER_OWNERS {owner}'), "Invalid or duplicate contribution adapter owner")
    with case("base dialect class collision in standalone assembly"):
        configure(registration("first", 'DIALECT_CLASSES ::zkc::PIRDialect'), "Invalid or duplicate contribution dialect")
    base_descriptor = descriptor.read_text()
    controls = (
        ("empty dialect inventory", 'set(zkc_builtin_dialects)\n', "Missing built-in IR records"),
        ("empty adapter inventory", 'set(zkc_builtin_type_adapters)\n', "Missing built-in IR records"),
        ("malformed dialect", 'list(APPEND zkc_builtin_dialects "oops")\n', "Malformed built-in dialect record"),
        ("duplicate namespace", 'list(APPEND zkc_builtin_dialects "pir|Other|none")\n', "Duplicate built-in dialect record"),
        ("duplicate class", 'list(APPEND zkc_builtin_dialects "other|PIR|types")\n', "Duplicate built-in dialect record"),
        ("malformed adapter", 'list(APPEND zkc_builtin_type_adapters "oops")\n', "Malformed built-in adapter record"),
        ("duplicate adapter owner", 'list(APPEND zkc_builtin_type_adapters "CoreTypeAdapters|Other")\n', "Duplicate built-in adapter record"),
        ("duplicate adapter output", 'list(APPEND zkc_builtin_type_adapters "Other|Resources")\n', "Duplicate built-in adapter record"),
        ("reserved combined output", 'list(APPEND zkc_builtin_type_adapters "Other|Installed")\n', "Duplicate built-in adapter record"),
    )
    for name, mutation, message in controls:
        with case(name):
            try:
                descriptor.write_text(base_descriptor + mutation)
                configure("", message)
            finally:
                descriptor.write_text(base_descriptor)
    with case("missing built-in descriptor fails standalone assembly"):
        try:
            descriptor.unlink()
            configure("", "include could not find requested file")
        finally:
            descriptor.write_text(base_descriptor)
    fragment = first / "Fragment.inc"
    fragment.write_text("// Not an installed TableGen fragment.\n")
    configure(registration("first").replace(str(first / "first.td"), str(fragment)), "DECLARATIONS must name an owned .td fragment")


def main():
    args = SimpleNamespace(
        tblgen=tool("tablegen"), include=ROOT / "compiler/include",
        cmake_module=ROOT / "compiler/cmake/ZkcContributions.cmake",
        work=Path(records()),
    )
    args.work.mkdir(parents=True, exist_ok=True)

    def inventory(text, expected=None):
        source = args.work / "input.td"
        source.write_text(text)
        result = subprocess.run(
            [str(args.tblgen), "-dump-contract-declarations", "-I", str(args.include), str(source)],
            text=True, capture_output=True, check=False,
        )
        if expected:
            assert result.returncode and expected in result.stderr, result.stderr
            return None
        assert result.returncode == 0, result.stderr
        return json.loads(result.stdout)

    base = inventory('include "zkc/Contracts/Declarations.td"\n')
    prefix = '''include "zkc/Contracts/Declarations/Schema.td"
defset list<ZKC_Declaration> BaseRecords = {
  include "zkc/Contracts/Declarations.td"
}
def BaseContribution : ZKC_Contribution<"base", [], BaseRecords>;
'''
    assert inventory(prefix) == base
    expected = (ROOT / "compiler/test/fixtures/contracts/base-inventory.sha256").read_text().strip()
    actual = hashlib.sha256(json.dumps(base, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    assert actual == expected, "base contract inventory changed; review and update the fixture deliberately"
    # Equal member names under different owners have distinct semantic keys.
    members = '''defset list<ZKC_Declaration> MemberRecords = {
      def SortA : ZKC_Sort<"MemberA">;
      def SortB : ZKC_Sort<"MemberB">;
      def OwnerA : ZKC_Domain<SortA>;
      def OwnerB : ZKC_Domain<SortB>;
      def FirstMember : ZKC_Member<"Element", OwnerA, TypeParameter>;
      def LastMember : ZKC_Member<"Element", OwnerB, TypeParameter>;
    }
    def Members : ZKC_Contribution<"members", ["base"], MemberRecords>;
'''
    assert inventory(prefix + members) == inventory(prefix + members.replace(
        "FirstMember", "ZMember").replace("LastMember", "AMember"))
    first = '''defset list<ZKC_Declaration> FirstRecords = {
def ExtraType : ZKC_Type<"extension_value">;
def Zed : ZKC_Operation<"extra.zed", [], [], []> { int ordinal = -200; }
def Abe : ZKC_Operation<"extra.abe", [], [], []> { int ordinal = 900; }
}
def First : ZKC_Contribution<"first", ["base"], FirstRecords>;
'''
    second = '''defset list<ZKC_Declaration> SecondRecords = {
def Beta : ZKC_Operation<"other.beta", [], [], []>;
}
def Second : ZKC_Contribution<"second", ["base"], SecondRecords>;
'''
    forward = inventory(prefix + first + second)
    assert forward == inventory(prefix + second + first)
    operations_key = "operations"
    assert forward[operations_key][:len(base[operations_key])] == base[operations_key]
    assert [r["name"] for r in forward[operations_key][-3:]] == ["extra.abe", "extra.zed", "other.beta"]
    # Extension record spellings and textual order cannot change identity.
    renamed = first.replace("ExtraType", "RenamedType").replace("Zed", "AnonymousZ").replace("Abe", "AnonymousA")
    assert inventory(prefix + renamed + second) == forward
    ordered_dependency = first.replace('["base"], FirstRecords', '["second"], FirstRecords')
    reverse = inventory(prefix + ordered_dependency + second)
    assert [r["name"] for r in reverse[operations_key][-3:]] == ["other.beta", "extra.abe", "extra.zed"]
    inventory(prefix + first.replace('["base"]', '["missing"]'), "missing contribution dependency")
    inventory(prefix + ordered_dependency + second.replace('["base"]', '["first"]'), "cyclic contribution dependencies")
    inventory(prefix + first + 'def Duplicate : ZKC_Contribution<"first", [], []>;', "duplicate contribution identifier")
    inventory(prefix + first + 'def Duplicate : ZKC_Contribution<"other", [], FirstRecords>;', "multiple contribution owners")
    inventory(prefix + 'def Extra : ZKC_Type<"unowned">;', "no contribution owner")
    cross = '''defset list<ZKC_Declaration> CrossRecords = {
def CrossOp : ZKC_Operation<"cross.identity", [], [ZKC_Apply<ExtraType>], [ZKC_Apply<ExtraType>]>;
}
def Cross : ZKC_Contribution<"cross", ["base"], CrossRecords>;
'''
    inventory(prefix + first + cross, "undeclared contribution dependency")
    inventory(prefix + first + cross.replace('["base"], CrossRecords', '["first"], CrossRecords'))
    # References in extension metadata are dependencies even inside DAG fields.
    # Check both the DAG operator and an argument rather than only lists/defs.
    for expression in ("(ExtraType)", "(TypeParameter ExtraType)"):
        dag_cross = cross.replace(
            'def CrossOp : ZKC_Operation<"cross.identity", [], [ZKC_Apply<ExtraType>], [ZKC_Apply<ExtraType>]>;',
            'def CrossOp : ZKC_Operation<"cross.identity", [], [], []> {'
            f' dag metadata = {expression}; }}')
        inventory(prefix + first + dag_cross, "undeclared contribution dependency")
        inventory(prefix + first + dag_cross.replace(
            '["base"], CrossRecords', '["first"], CrossRecords'))

    cmake_controls(args)
    print("Contribution assembly: baseline, ordering, dependency, ownership and CMake controls passed")


if __name__ == "__main__":
    main()
