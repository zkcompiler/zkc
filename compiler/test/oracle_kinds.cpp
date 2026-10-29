#include "mlir/AsmParser/AsmParser.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/Diagnostics.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/OracleKinds.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Protocol/IR/ProtocolTypes.h"
#include "zkc/Dialect/Registry.h"
#include <limits>

using namespace llvm;
using namespace mlir;
using namespace zkc::protocol_ir;
using namespace zkc::test;
namespace {
OracleKindAttr kind(StringRef arguments, MLIRContext &context) {
  auto parsed = parseAttribute(
      ("#protocol.oracle_kind<\"table\", " + arguments + ">").str(), &context);
  require(bool(parsed), "valid oracle kind refused");
  return cast<OracleKindAttr>(parsed);
}
template <typename T> std::string printed(T value) {
  std::string text;
  raw_string_ostream out(text);
  out << value;
  return text;
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  zkc::registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run("kind associations reuse complete logical collections", [&] {
    for (const auto &[row, data] :
         std::vector<std::pair<std::string, std::string>>{
             {"!algebra.field<\"koala-bear\">",
              "!algebra.field_vector<\"koala-bear\">"},
             {"!algebra.field<\"koala-bear.ext8-binomial3\">",
              "!algebra.field_vector<\"koala-bear.ext8-binomial3\">"},
             {"!algebra.group<\"bls12-381.g1\">",
              "!algebra.group_vector<\"bls12-381.g1\">"},
             {"ui64", "!algebra.indices"},
             {"i1", "!data.sequence<i1>"},
             {"!data.sequence<i1>", "!data.sequence<!data.sequence<i1>>"}}) {
      auto instance = kind("[" + row + "]", context);
      require(instance.getDataType() == parseType(data, &context) &&
                  instance.getQueryType().isUnsignedInteger(64) &&
                  instance.getAnswerType() == parseType(row, &context) &&
                  !instance.getStaticShape("rows"),
              "kind changed its Data/Query/Answer associations");
      auto logical =
          take(zkc::protocol::encodeBoundType(instance.getDataType(), false));
      require(logical.representation.empty(),
              "oracle kind selects a physical owner");
    }
  });
  cases.run("shared kind formation refuses malformed logical descriptors", [] {
    using namespace zkc::protocol;
    auto row = take(parseBoundType("field:koala-bear", false));
    auto descriptor = TypeArgument::typeArgument(row);
    auto shape = take(oracleKindSignature(
        "table", {descriptor, TypeArgument::naturalArgument(16)}));
    require(shape.answer == row &&
                shape.data.spelling() == "vector:koala-bear" &&
                shape.query.spelling() == "index" &&
                shape.staticShape("rows") == 16,
            "source-independent kind associations differ");
    auto refused = [](Expected<OracleKindSignature> value) {
      require(!value, "invalid logical kind descriptor admitted");
      consumeError(value.takeError());
    };
    refused(oracleKindSignature("table", {}));
    refused(oracleKindSignature("univariate", {descriptor}));
    refused(oracleKindSignature("table",
                                {TypeArgument::domainArgument("koala-bear")}));
    refused(oracleKindSignature("table", {descriptor, descriptor}));
    refused(
        oracleKindSignature("table", {{TypeArgument::Kind::Type, {}, {}, 0}}));
    BoundType malformed{
        "sequence", {}, {}, {{TypeArgument::Kind::Type, {}, {}, 0}}};
    refused(
        oracleKindSignature("table", {TypeArgument::typeArgument(malformed)}));
    BoundType deep{"bool", {}, {}};
    for (unsigned i = 0; i != 70; ++i)
      deep = {
          "sequence", {}, {}, {TypeArgument::typeArgument(std::move(deep))}};
    refused(oracleKindSignature("table", {TypeArgument::typeArgument(deep)}));
    row.representation = "native";
    refused(oracleKindSignature("table", {TypeArgument::typeArgument(row)}));
  });
  cases.run("sized kinds retain zero and full-width cardinalities", [&] {
    auto dynamic = kind("[i1]", context);
    auto empty = kind("[i1, 0 : ui64]", context);
    auto largest = kind("[i1, 18446744073709551615 : ui64]", context);
    require(
        !dynamic.getStaticShape("rows") && empty.getStaticShape("rows") == 0 &&
            largest.getStaticShape("rows") ==
                std::numeric_limits<uint64_t>::max(),
        "static rows were erased, narrowed or confused with an omitted size");
    require(
        dynamic != empty && empty != largest &&
            dynamic.getDataType() == empty.getDataType() &&
            empty.getDataType() == largest.getDataType(),
        "ordinary collection type replaced the kind's cardinality refinement");
  });
  cases.run(
      "logical handles and bounded sequences round trip without codecs", [&] {
        auto instance =
            kind("[!algebra.field<\"koala-bear\">, 16 : ui64]", context);
        require(parseAttribute(printed(instance), &context) == instance,
                "typed kind round trip differs");
        auto handle = OracleHandleType::get(&context, instance);
        for (auto maximum :
             {uint64_t(0), uint64_t(7), std::numeric_limits<uint64_t>::max()}) {
          auto sequence = OracleSequenceType::get(&context, instance, maximum);
          require(sequence.getKind() == instance &&
                      sequence.getMaximum() == maximum &&
                      parseType(printed(sequence), &context) == sequence,
                  "handle sequence lost its kind or bound");
          auto bound = zkc::protocol::encodeBoundType(sequence, false);
          require(!bound,
                  "logical handle sequence acquired an ordinary native codec");
          consumeError(bound.takeError());
        }
        require(parseType(printed(handle), &context) == handle,
                "logical handle round trip differs");
        auto bound = zkc::protocol::encodeBoundType(handle, false);
        require(!bound, "logical handle acquired an ordinary native codec");
        consumeError(bound.takeError());
        ScopedDiagnosticHandler silence(&context,
                                        [](Diagnostic &) { return success(); });
        require(!parseType("!data.sequence<" + printed(handle) + ">", &context),
                "ordinary sequence bypassed bounded oracle ownership");
      });
  cases.run("unknown kinds, malformed statics and nondata rows refuse", [&] {
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    for (
        StringRef invalid :
        {R"(#protocol.oracle_kind<"univariate", [i1, 8 : ui64]>)",
         R"(#protocol.oracle_kind<"multilinear", [i1, 8 : ui64]>)",
         R"(#protocol.oracle_kind<"unknown", [i1]>)",
         R"(#protocol.oracle_kind<"table", []>)",
         R"(#protocol.oracle_kind<"table", [1 : ui64]>)",
         R"(#protocol.oracle_kind<"table", [i1, 4 : i64]>)",
         R"(#protocol.oracle_kind<"table", [i1, 4 : ui32]>)",
         R"(#protocol.oracle_kind<"table", [i1, -1 : ui64]>)",
         R"(#protocol.oracle_kind<"table", [i1, 4 : ui64, 5 : ui64]>)",
         R"(#protocol.oracle_kind<"table", [i64]>)",
         R"(#protocol.oracle_kind<"table", [index]>)",
         R"(#protocol.oracle_kind<"table", [!protocol.service_ref<"randomness">]>)",
         R"(#protocol.oracle_kind<"table", [!protocol.oracle<#protocol.oracle_kind<"table", [i1]>>]>)"})
      require(!parseAttribute(invalid, &context),
              "invalid kind admitted: " + invalid);
    for (StringRef invalid : {"-1", "-18446744073709551615",
                              "18446744073709551616", "0x10000000000000000"})
      require(!parseType(("!protocol.oracle_sequence<#protocol.oracle_kind<"
                          "\"table\", [i1]>, " +
                          invalid + ">")
                             .str(),
                         &context),
              "invalid handle bound admitted: " + invalid);
    std::string nested = "i1";
    for (unsigned i = 0; i != 70; ++i)
      nested = "!data.sequence<" + nested + ">";
    require(!parseAttribute(
                "#protocol.oracle_kind<\"table\", [" + nested + "]>", &context),
            "nested oracle row escaped logical type depth limits");
  });
  return cases.result();
}
