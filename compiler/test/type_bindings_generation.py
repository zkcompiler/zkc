#!/usr/bin/env python3
"""Exercise production binding coverage and compile-time helper agreement.

CTest selects this build's generator, compiler and dependency include paths.
"""
import json
from pathlib import Path
import subprocess

from cases import case, counted
from tools import records, tool
from types import SimpleNamespace


def run(command, expected=None):
    result = subprocess.run(command, text=True, capture_output=True)
    if expected is None:
        assert result.returncode == 0, result.stderr
    else:
        assert result.returncode > 0, (result.returncode, result.stderr)
        assert expected in result.stderr, result.stderr
    return result.stdout


def main():
    tblgen = tool("tablegen")
    settings = json.loads((tblgen.parent / "generation-settings.json").read_text())
    args = SimpleNamespace(tblgen=str(tblgen), **settings)
    include = ["-I", args.source_include]
    for path in args.dependency_include:
        include += ["-I", path]
    prelude = '''include "zkc/Dialect/TypeBindings.td"
def TestDialect : Dialect { let name = "binding_test"; let cppNamespace = "::test"; }
def Native : TypeDef<TestDialect, "Native"> { let mnemonic = "native"; }
def OtherNative : TypeDef<TestDialect, "Other"> { let mnemonic = "other"; }
def Owner : ZKC_TypeAdapterOwner<"test", "adapters">;
def Logical : ZKC_Type<"test", [TypeParameter, NatParameter]>;
'''
    direct = 'def Binding : ZKC_DirectBinding<Logical, Native, "Helper", Owner>;\n'
    custom = ('def Binding : ZKC_CustomBinding<Logical, ["::test::NativeType"], '
              '"decode", "encode", Owner>;\n')
    fixtures = [
        ("direct", direct, None),
        ("missing", "", "missing native binding decision"),
        ("non-common missing", direct + 'def Hidden : ZKC_Type<"hidden"> { let commonGeneric = 0; }',
         "missing native binding decision: hidden"),
        ("duplicate", direct + 'def Duplicate : ZKC_UnavailableBinding<Logical, "reason">;',
         "duplicate native binding decision"),
        ("unclassified", 'def Binding : ZKC_TypeBinding<Logical>;',
         "expected direct, custom or unavailable"),
        ("unavailable", 'def Binding : ZKC_UnavailableBinding<Logical, "no native representation">;', None),
        ("empty reason", 'def Binding : ZKC_UnavailableBinding<Logical, "  ">;',
         "unavailable binding requires a reason"),
        ("empty helper", direct.replace('"Helper"', '""'),
         "direct binding requires a typed helper"),
        ("invalid direct head", 'def BadDialect : Dialect { let name = "bad"; '
         'let cppNamespace = "::bad-name"; } '
         'def BadNative : TypeDef<BadDialect, "Bad"> { let mnemonic = "bad"; } '
         'def Binding : ZKC_DirectBinding<Logical, BadNative, "Helper", Owner>;',
         "invalid direct native head"),
        ("unsupported parameter kind", direct +
         'def FutureKind : ZKC_ParameterKind<"Future">; '
         'def FutureParameter : ZKC_Parameter<FutureKind>; '
         'def FutureLogical : ZKC_Type<"future", [FutureParameter]>; '
         'def FutureBinding : ZKC_DirectBinding<FutureLogical, OtherNative, "Helper", Owner>;',
         "unsupported direct logical parameter kind"),
        ("custom", custom, None),
        ("empty heads", custom.replace('["::test::NativeType"]', '[]'),
         "custom binding requires declared native heads"),
        ("empty callback", custom.replace('"decode"', '""'),
         "custom binding requires decode and encode"),
        ("unqualified head", custom.replace('::test::NativeType', 'test::NativeType'),
         "invalid or repeated custom native head"),
        ("repeated head", custom.replace('["::test::NativeType"]',
                                        '["::test::NativeType", "::test::NativeType"]'),
         "invalid or repeated custom native head"),
        ("direct overlap", direct + 'def Another : ZKC_Type<"another">; '
         'def Collision : ZKC_DirectBinding<Another, Native, "Helper", Owner>;',
         "duplicate direct native head"),
        ("direct custom overlap", direct + 'def Another : ZKC_Type<"another">; '
         'def Collision : ZKC_CustomBinding<Another, ["::test::NativeType"], "decode", "encode", Owner>;',
         "direct/custom native head overlap"),
        ("custom sharing", custom + 'def Another : ZKC_Type<"another">; '
         'def Tagged : ZKC_CustomBinding<Another, ["::test::NativeType"], "decode", "encode", Owner>;', None),
        ("missing special", direct + 'def VariantSyntax : ZKC_SpecialType<"variant">;',
         "missing native binding decision: variant"),
        ("special", direct + 'def VariantSyntax : ZKC_SpecialType<"variant">; '
         'def VariantBinding : ZKC_SpecialBinding<VariantSyntax, ["::test::VariantType"], "decode", "encode", Owner>;', None),
        ("special collision", direct + 'def Special : ZKC_SpecialType<"test">; '
         'def SpecialBinding : ZKC_SpecialBinding<Special, ["::test::SpecialType"], "decode", "encode", Owner>;',
         "duplicate native binding constructor"),
        ("owner collision", direct + 'def OtherOwner : ZKC_TypeAdapterOwner<"test", "adapters">;',
         "duplicate adapter owner function"),
        ("invalid owner", direct + 'def BadOwner : ZKC_TypeAdapterOwner<"test", "not-a-function">;',
         "invalid adapter owner C++ namespace or function"),
    ]
    temp = records("type-bindings-generation")
    td = temp / "fixture.td"
    command = [args.tblgen, "--gen-type-bindings", *include, str(td)]
    for label, text, expected in fixtures:
        with case(label):
            fixture = temp / (label.replace(" ", "-") + ".td")
            fixture.write_text(prelude + text)
            run([*command[:-1], str(fixture)], expected)
    with case("unknown owner"):
        td.write_text(prelude + direct)
        run([*command, "--type-binding-owner=Missing"], "unknown type binding owner")
    with case("installed exhaustive inventory"):
        run([args.tblgen, "--gen-type-bindings", *include,
             str(Path(args.source_include) / "zkc/Dialect/InstalledTypeBindings.td")])
    with case("compile helper fixture generation"):
        td.write_text(prelude + direct)
        (temp / "owner.inc").write_text(run([*command, "--type-binding-owner=Owner"]))
    # These assertions use real generated registration and the installed
    # public helper signature vocabulary, not test-only projection metadata.
    source = '''#include "zkc/Dialect/TypeAdapters.h"
namespace test {
struct NativeType {};
struct OtherType {};
struct Helper {
  using Native = NATIVE;
  using Parameters = zkc::protocol::type_adapters::ParameterKinds<KINDS>;
  static mlir::Type decode(mlir::MLIRContext *, const zkc::protocol::BoundType &);
  static std::optional<zkc::protocol::BoundType> encode(mlir::Type, llvm::StringRef);
};
}
#include "owner.inc"
'''
    compile_command = [args.cxx, "-std=c++17", "-fsyntax-only", "-I", args.source_include,
                       "-I", args.generated_include]
    for path in args.dependency_include:
        compile_command += ["-isystem", path]
    kinds = "zkc::protocol::type_adapters::ParameterKind::"
    for label, native, parameters, expected in [
        ("typed helper accepted", "NativeType", kinds + "Type, " + kinds + "Nat", None),
        ("native helper mismatch", "OtherType", kinds + "Type, " + kinds + "Nat",
         "native binding helper type mismatch"),
        ("kind order mismatch", "NativeType", kinds + "Nat, " + kinds + "Type",
         "native binding helper parameter kinds mismatch"),
        ("kind arity mismatch", "NativeType", kinds + "Type",
         "native binding helper parameter kinds mismatch"),
    ]:
        with case(label):
            cpp = temp / (label.replace(" ", "-") + ".cpp")
            cpp.write_text(source.replace("NATIVE", native).replace("KINDS", parameters))
            run([*compile_command, str(cpp)], expected)
    print(f"{counted()} native binding generation cases exercised")


if __name__ == "__main__":
    main()
