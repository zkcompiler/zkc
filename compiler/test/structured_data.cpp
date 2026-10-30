#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinOps.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/Parameters.h"
#include "zkc/Dialect/StructuredData.h"
#include "zkc/Support/Json.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
json::Value read(StringRef text) { return take(json::parse(text)); }
void accepted(Error result) {
  if (result)
    throw std::runtime_error(toString(std::move(result)));
}
void rejected(Error result) {
  require(bool(result), "changed interchange accepted");
  require(toString(std::move(result)).find("structured-data") !=
              std::string::npos,
          "wrong interchange refusal identifier");
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler silence(&context,
                                  [](Diagnostic &) { return success(); });
  Builder builder(&context);
  Cases cases;
  auto imported = [&](StringRef text) {
    return take(importLogicalTypeData(&context, read(text)));
  };
  cases.run("independent complete logical witnesses", [&] {
    for (
        StringRef text : {
            R"(["apply","bool",[]])",
            R"(["apply","index",[]])",
            R"(["apply","field",[["domain","Field","koala-bear.ext4-binomial3"]]])",
            R"(["apply","field_array",[["domain","Field","bls12-381.fr"],["nat","3"]]])",
            R"(["apply","sequence",[["type",["apply","bool",[]]]]])",
            R"(["variant",["tuple",[["atom","record"],["atom","phantom"]]],[["empty",[]],["value",[["apply","bool",[]],["apply","index",[]]]]]])",
            R"(["oracle","table",[["type",["apply","field",[["domain","Field","koala-bear"]]]],["nat","16"]]])",
            R"(["oracle_sequence","table",[["type",["apply","bool",[]]]],"0"])",
            R"(["service","random.bls12-381.fr/0"])",
        }) {
      auto expected = read(text);
      auto type = take(importLogicalTypeData(&context, expected));
      require(equalNaturalJson(take(exportLogicalTypeData(type)), expected),
              "independently authored schema changed");
    }
  });
  for (
      StringRef text : {
          R"("!algebra.field<\"bls12-381.fr\">")",
          R"(["field","bls12-381.fr"])",
          R"(["product","[\"old\"]","value",[]])",
          R"(["variant","[\"old\"]",[["value",[]]]])",
          R"(["apply","unknown",[]])",
          R"(["apply","bool",[],"extra"])",
          R"(["apply","field",[["domain","Group","bls12-381.fr"]]])",
          R"(["apply","field",[["domain","Field","bls12-381.g1"]]])",
          R"(["apply","field",[["type",["apply","bool",[]]]]])",
          R"(["apply","field_array",[["domain","Field","bls12-381.fr"],["nat","03"]]])",
          R"(["apply","field_array",[["domain","Field","bls12-381.fr"],["nat",3]]])",
          R"(["variant",["atom",""],[["value",[]]]])",
          R"(["variant",["atom","record"],[["value",[]],["value",[]]]])",
          R"(["oracle","table",[["nat","16"]]])",
          R"(["oracle_sequence","table",[["type",["apply","bool",[]]]],"18446744073709551616"])",
          R"(["service","random.unknown/0"])",
      })
    cases.run("logical reader refuses " + text, [&] {
      refuses(importLogicalTypeData(&context, read(text)), "structured-data");
    });
  cases.run("variant identity, alternative and payload order are semantic", [&] {
    auto expected = read(
        R"(["variant",["tuple",[["atom","R"],["atom","F"]]],[["first",[["apply","bool",[]],["apply","index",[]]]],["second",[]]]])");
    auto original = take(importLogicalTypeData(&context, expected));
    auto change = [&](llvm::function_ref<void(json::Array &)> mutate) {
      auto changed = read(printJson(expected));
      mutate(*changed.getAsArray());
      require(take(importLogicalTypeData(&context, changed)) != original,
              "changed nominal structure merged with original");
    };
    change([&](auto &row) {
      (*(*(*row[1].getAsArray())[1].getAsArray())[1].getAsArray())[1] = "G";
    });
    change([&](auto &row) {
      auto &arms = *row[2].getAsArray();
      std::swap(arms[0], arms[1]);
    });
    change([&](auto &row) {
      auto &payload =
          *(*(*row[2].getAsArray())[0].getAsArray())[1].getAsArray();
      std::swap(payload[0], payload[1]);
    });
  });
  cases.run("expanded sharing and depth are bounded", [&] {
    json::Value value = read(R"(["apply","bool",[]])");
    for (unsigned i = 0; i < 65; ++i)
      value = json::Array{"apply", "sequence",
                          json::Array{json::Array{"type", std::move(value)}}};
    refuses(importLogicalTypeData(&context, value), "structured-data");
    SmallVector<Type> roots(200001, builder.getI1Type());
    refuses(exportLogicalTypesData(roots), "structured-data");
    json::Array rows;
    for (unsigned i = 0; i < 200001; ++i)
      rows.push_back(json::Array{"apply", "bool", json::Array{}});
    refuses(importLogicalTypesData(&context, rows), "structured-data");
    refuses(exportLogicalTypeData(builder.getF32Type()), "structured-data");
  });
  cases.run("missing loaded owners do not load dialects", [&] {
    MLIRContext empty;
    refuses(
        importLogicalTypeData(
            &empty,
            read(R"(["apply","field",[["domain","Field","bls12-381.fr"]]])")),
        "structured-data");
    require(!empty.getLoadedDialect<algebra::AlgebraDialect>(),
            "interchange loaded a missing owner");
  });

  cases.run("standalone inventory preserves order and rejects duplicate roots", [&] {
    auto expected = read(
        R"(["zkc.logical-types/0",[["apply","bool",[]],["apply","index",[]]]])");
    auto types = take(importLogicalTypeInventory(&context, expected));
    require(equalNaturalJson(take(exportLogicalTypeInventory(types)), expected),
            "standalone inventory changed");
    MLIRContext other(registry);
    other.loadAllAvailableDialects();
    SmallVector<Type> acrossContexts{
        types.front(),
        take(importLogicalTypeData(&other, read(R"(["apply","bool",[]])")))};
    refuses(exportLogicalTypeInventory(acrossContexts), "structured-data");
    types.push_back(types.front());
    refuses(exportLogicalTypeInventory(types), "structured-data");
    auto &rows = *(*expected.getAsArray())[1].getAsArray();
    rows.push_back(rows.front());
    refuses(importLogicalTypeInventory(&context, expected), "structured-data");
    while (rows.size() < 4097)
      rows.push_back(nullptr);
    refuses(importLogicalTypeInventory(&context, expected), "structured-data");
  });
  auto base =
      imported(R"(["apply","field",[["domain","Field","koala-bear"]]])");
  auto extension = imported(
      R"(["apply","field",[["domain","Field","koala-bear.ext4-binomial3"]]])");
  OwningOpRef<ModuleOp> module(ModuleOp::create(builder.getUnknownLoc()));
  OpBuilder operations(module->getBody(), module->getBody()->end());
  auto binding = runtime::BindingOp::create(
      operations, module->getLoc(), "embed", "field.embed",
      builder.getArrayAttr(
          {builder.getStringAttr("koala-bear.ext4-binomial3")}),
      "",
      executableBindingSignature(builder.getFunctionType({base}, {extension})),
      ArrayAttr{}, ArrayAttr{});
  auto bindingWitness = read(
      R"(["field.embed",[["domain","Field","koala-bear.ext4-binomial3"]],"",[["apply","field",[["domain","Field","koala-bear"]]]],[["apply","field",[["domain","Field","koala-bear.ext4-binomial3"]]]]])");
  cases.run("binding ports rederive the associated base", [&] {
    require(equalNaturalJson(json::Value(take(exportBindingData(binding))),
                             bindingWitness),
            "binding lost its associated base or full ports");
    accepted(checkBindingData(binding, bindingWitness));
  });
  for (StringRef mutation : {"kind", "nominal", "base", "ports", "old"})
    cases.run("binding reader refuses " + mutation, [&] {
      auto changed = read(printJson(bindingWitness));
      auto &row = *changed.getAsArray();
      if (mutation == "kind")
        (*(*row[1].getAsArray())[0].getAsArray())[0] = "type";
      else if (mutation == "nominal")
        (*(*row[1].getAsArray())[0].getAsArray())[2] = "koala-bear";
      else if (mutation == "base")
        row[3] =
            read(R"([["apply","field",[["domain","Field","bls12-381.fr"]]]])");
      else if (mutation == "ports")
        std::swap(row[3], row[4]);
      else
        row = json::Array{"field.embed",
                          json::Array{"koala-bear.ext4-binomial3"}, ""};
      rejected(checkBindingData(binding, changed));
    });
  cases.run("producer refuses forged callable ports", [&] {
    auto signature = binding.getFunctionType();
    binding->setAttr("function_type",
                     TypeAttr::get(executableBindingSignature(
                         builder.getFunctionType({extension}, {base}))));
    refuses(exportBindingData(binding), "structured-data");
    binding->setAttr("function_type", TypeAttr::get(signature));
  });
  auto noArguments = builder.getArrayAttr({});
  auto parameters = builder.getArrayAttr({builder.getIntegerAttr(
      IntegerType::get(&context, 64, IntegerType::Unsigned), 42)});
  cases.run("structured naturals preserve program parameter bytes", [&] {
    auto expected = read(R"([["natural","42"]])");
    accepted(checkInvocationParametersData("index.constant", noArguments,
                                           parameters, expected));
    require(take(protocol::encodeInvocationParameters(
                "index.constant", noArguments, parameters)) ==
                std::vector<std::string>{"42"},
            "program/0 parameter bytes changed");
  });
  for (StringRef text :
       {R"(["42"])", R"([["nat","42"]])", R"([["natural",42]])",
        R"([["natural","042"]])", R"([["natural","43"]])"})
    cases.run("parameter reader refuses " + text, [&] {
      rejected(checkInvocationParametersData("index.constant", noArguments,
                                             parameters, read(text)));
    });
  cases.run("parameter producer refuses wrong native kinds and domains", [&] {
    refuses(exportInvocationParametersData(
                "index.constant", noArguments,
                builder.getArrayAttr({builder.getStringAttr("42")})),
            "structured-data");
    auto literal = take(algebra::makeFieldLiteral(
        cast<algebra::FieldType>(base), APInt(32, 17)));
    auto arguments =
        builder.getArrayAttr({builder.getStringAttr("bls12-381.fr")});
    refuses(exportInvocationParametersData("field.constant", arguments,
                                           builder.getArrayAttr({literal})),
            "structured-data");
  });
  cases.run("field literals and origins remain structured parameters", [&] {
    auto literal = take(algebra::makeFieldLiteral(
        cast<algebra::FieldType>(base), APInt(32, 17)));
    auto arguments =
        builder.getArrayAttr({builder.getStringAttr("koala-bear")});
    require(
        equalNaturalJson(
            json::Value(take(exportInvocationParametersData(
                "field.constant", arguments, builder.getArrayAttr({literal})))),
            read(R"([["field_literal","koala-bear","natural","17"]])")),
        "field literal schema differs");
    protocol::NativeOriginTemplate origin;
    origin.entry = "main";
    origin.path.push_back(
        {protocol::NativeOriginStep::Kind::Apply, "parent", "call"});
    origin.event = protocol::NativeQueryOrigin{
        "child", "query", 2, "random.bls12-381.fr/0", "draw", "V"};
    auto native = take(runtime::importNativeOrigin(&context, origin));
    auto encoded = take(exportSemanticAttributeData(native));
    require(
        equalNaturalJson(
            encoded,
            read(
                R"(["parameter",["origin",["zkc.native-origin-template/0","main",[["apply","parent","call"]],[],["query","child","query","input_2","random.bls12-381.fr/0","draw","V"]]]])")),
        "native origin was printed or lost its path");
  });
  cases.run("asset identity and format remain separate parameter fields", [&] {
    StringRef digest =
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    auto asset =
        take(runtime::decodeAssetReference(&context, "zkc.matrix/0", digest));
    auto arguments =
        builder.getArrayAttr({builder.getStringAttr("koala-bear")});
    auto parameters = builder.getArrayAttr({asset});
    auto expected = read(
        R"([["asset","zkc.matrix/0","0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"]])");
    accepted(checkInvocationParametersData("matrix.identity_check", arguments,
                                           parameters, expected));
    (*(*expected.getAsArray())[0].getAsArray())[1] = "zkc.ring/0";
    rejected(checkInvocationParametersData("matrix.identity_check", arguments,
                                           parameters, expected));
    refuses(exportInvocationParametersData(
                "matrix.identity_check", arguments,
                builder.getArrayAttr({take(runtime::decodeAssetReference(
                    &context, "zkc.ring/0", digest))})),
            "structured-data");
  });
  cases.run("numerical masks retain positional ports and actual expression DAG", [&] {
    auto arguments =
        builder.getArrayAttr({builder.getStringAttr("koala-bear"),
                              builder.getDenseBoolArrayAttr({true, false})});
    auto signature = resolveLogicalSignature(
        [&] { return emitError(builder.getUnknownLoc()); }, &context,
        "numerical.map", arguments.getValue());
    require(bool(signature), "valid numerical signature did not form");
    auto numerical = runtime::BindingOp::create(
        operations, module->getLoc(), "map", "numerical.map", arguments, "",
        executableBindingSignature(signature), ArrayAttr{}, ArrayAttr{});
    auto expectedBinding = read(
        R"(["numerical.map",[["domain","Field","koala-bear"],["mask",[true,false]]],"",[["apply","index",[]],["apply","vector",[["domain","Field","koala-bear"]]],["apply","field",[["domain","Field","koala-bear"]]]],[["apply","vector",[["domain","Field","koala-bear"]]]]])");
    accepted(checkBindingData(numerical, expectedBinding));
    (*(*expectedBinding.getAsArray())[1].getAsArray())[1] =
        read(R"(["mask",[false,true]])");
    rejected(checkBindingData(numerical, expectedBinding));
    using N = ring::Node;
    auto expression = take(ring::Expression::create(
        {{"koala-bear"}, {"koala-bear"}},
        {N::slot(0), N::slot(0), N::mul(0, 1), N::slot(1), N::add(2, 3)}, {4}));
    auto native = take(algebra::importRingExpression(&context, expression));
    auto parameters = builder.getArrayAttr({native});
    auto expected = read(
        R"([["expression",["zkc.ring/0",["koala-bear","koala-bear"],[["input",0],["input",0],["mul",0,1],["input",1],["add",2,3]],[4]]]])");
    accepted(checkInvocationParametersData("numerical.map", arguments,
                                           parameters, expected));
    auto old = read(printJson(expected));
    auto &parameter = *(*old.getAsArray())[0].getAsArray();
    parameter[1] = printJson(parameter[1]);
    rejected(checkInvocationParametersData("numerical.map", arguments,
                                           parameters, old));
    auto &body = *(*(*expected.getAsArray())[0].getAsArray())[1].getAsArray();
    (*body[3].getAsArray())[0] = 2;
    rejected(checkInvocationParametersData("numerical.map", arguments,
                                           parameters, expected));
    auto wrongMask = builder.getArrayAttr(
        {builder.getStringAttr("koala-bear"),
         builder.getDenseBoolArrayAttr({true, false, true})});
    refuses(
        exportInvocationParametersData("numerical.map", wrongMask, parameters),
        "structured-data");
    numerical->setAttr("arguments", wrongMask);
    refuses(exportBindingData(numerical), "structured-data");
    numerical.erase();
  });
  cases.run("binary literal bits retain their exact owner spelling", [&] {
    StringRef domain = "gf2-64.pentanomial-4-3-1";
    auto field = cast<algebra::FieldType>(imported(
        R"(["apply","field",[["domain","Field","gf2-64.pentanomial-4-3-1"]]])"));
    auto literal = take(algebra::decodeFieldLiteral(field, "0x2"));
    auto arguments = builder.getArrayAttr({builder.getStringAttr(domain)});
    auto parameters = builder.getArrayAttr({literal});
    auto expected =
        read(R"([["field_literal","gf2-64.pentanomial-4-3-1","bits","0x2"]])");
    accepted(checkInvocationParametersData("field.constant", arguments,
                                           parameters, expected));
    (*(*expected.getAsArray())[0].getAsArray())[2] = "natural";
    rejected(checkInvocationParametersData("field.constant", arguments,
                                           parameters, expected));
  });
  cases.run("participant integer bit patterns, symbols and recursive values", [&] {
    auto signless =
        builder.getIntegerAttr(builder.getIntegerType(8), APInt(8, 255));
    require(equalNaturalJson(take(exportSemanticAttributeData(signless)),
                             read(R"(["integer","signless","8","255"])")),
            "signless value was interpreted as signed");
    auto signedValue = builder.getIntegerAttr(
        IntegerType::get(&context, 8, IntegerType::Signed), APInt(8, 255));
    require(equalNaturalJson(take(exportSemanticAttributeData(signedValue)),
                             read(R"(["integer","signed","8","-1"])")),
            "signed value lost its sign or width");
    auto symbol = SymbolRefAttr::get(
        &context, "root", {FlatSymbolRefAttr::get(&context, "leaf")});
    auto value = builder.getDictionaryAttr(
        {builder.getNamedAttr("a", symbol),
         builder.getNamedAttr("b",
                              builder.getArrayAttr({builder.getBoolAttr(true),
                                                    TypeAttr::get(base)}))});
    auto encoded = take(exportSemanticAttributeData(value));
    require(
        equalNaturalJson(
            encoded,
            read(
                R"(["dictionary",[["a",["symbol",["root","leaf"]]],["b",["array",[["bool",true],["type",["apply","field",[["domain","Field","koala-bear"]]]]]]]]])")),
        "recursive semantic value changed order or kind");
    refuses(exportSemanticAttributeData(builder.getUnitAttr()),
            "structured-data");
    refuses(exportSemanticAttributeData(builder.getF32FloatAttr(1.0)),
            "structured-data");
    refuses(exportSemanticAttributeData(
                builder.getIntegerAttr(builder.getIntegerType(4097), 0)),
            "structured-data");
  });
  cases.run("declaration carrier is structured and rejects old documents", [&] {
    auto expected = read(R"([["record",false,7,null],["protocol",[]]])");
    auto native = take(importDeclarationData(&context, expected));
    require(equalNaturalJson(take(exportDeclarationData(native)), expected),
            "declaration tree lost native kinds");
    refuses(exportDeclarationData(builder.getStringAttr(printJson(expected))),
            "structured-data");
    refuses(importDeclarationData(&context, json::Value(printJson(expected))),
            "structured-data");
    refuses(importDeclarationData(&context, read(R"([{"unknown":true}])")),
            "structured-data");
  });
  return cases.result();
}
