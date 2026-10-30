#include "support/NativeCases.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Runtime/Parameters.h"
#include "zkc/Support/Json.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Builder builder(&context);
  ScopedDiagnosticHandler diagnostics(&context,
                                      [](Diagnostic &) { return success(); });
  auto emit = [&] { return emitError(builder.getUnknownLoc()); };
  auto natural = [&](uint64_t n) {
    return builder.getIntegerAttr(
        IntegerType::get(&context, 64, IntegerType::Unsigned), n);
  };
  auto field = algebra::FieldType::get(&context, "koala-bear");
  auto arguments = builder.getArrayAttr({builder.getStringAttr("koala-bear")});
  auto accepted = [&](StringRef contract, ArrayAttr args,
                      ArrayRef<Attribute> params) {
    return succeeded(verifyInvocationParameters(emit, contract, args,
                                                builder.getArrayAttr(params)));
  };
  auto roundtrip = [&](const BindingApplication &binding,
                       ArrayRef<std::string> text) {
    auto checked = checkParameters(binding, text);
    if (checked)
      throw std::runtime_error(toString(std::move(checked)));
    auto args = take(decodeBindingArguments(&context, binding));
    auto attributes =
        take(decodeInvocationParameters(binding.contract, args, text));
    require(accepted(binding.contract, args, attributes.getValue()),
            "native parameter formation");
    require(ArrayRef<std::string>(take(encodeInvocationParameters(
                binding.contract, args, attributes))) == text,
            "program parameter bytes changed");
    require(invocationParametersMatch(binding.contract, args, attributes, text),
            "independent parameter comparison");
    return attributes;
  };
  Cases cases;
  cases.run(
      "ordinary parameter families agree with independent program admission",
      [&] {
        struct Example {
          const char *contract;
          std::vector<std::string> values;
        };
        for (const auto &example : std::vector<Example>{
                 {"field.add", {}},
                 {"field.constant", {"2130706432"}},
                 {"vector.constant", {}},
                 {"vector.constant", {"0", "1", "123"}},
                 {"matrix.dimension", {"18446744073709551615"}},
                 {"vector.splat", {"1048576"}},
                 {"matrix.shape_check", {"65536", "0"}},
                 {"vector.matvec", {"1048576", "3", "1"}},
                 {"vector.gather", {}},
                 {"vector.gather", {"2", "1048576", "2"}},
                 {"vector.scatter_sum", {"18446744073709551615", "0", "1"}}})
          roundtrip({example.contract, {"koala-bear"}, ""}, example.values);
        roundtrip({"index.constant", {}, ""}, {"18446744073709551615"});
        auto wide =
            roundtrip({"field.constant",
                       {"gf2-64.pentanomial-4-3-1.ext3-trinomial1"},
                       ""},
                      {"0xffffffffffffffffffffffffffffffffffffffffffffffff"});
        require(cast<algebra::FieldLiteralAttr>(wide[0])
                        .getValue()
                        .getValue()
                        .getBitWidth() == 192,
                "binary literal was narrowed");
      });
  cases.run("native kinds and exact fields refuse semantic substitutions", [&] {
    auto one = take(algebra::decodeFieldLiteral(field, "1"));
    auto other = take(algebra::decodeFieldLiteral(
        algebra::FieldType::get(&context, "baby-bear"), "1"));
    require(accepted("field.constant", arguments, {one}) &&
                !accepted("field.constant", arguments, {other}) &&
                !accepted("field.constant", arguments, {natural(1)}) &&
                !accepted("field.constant", arguments,
                          {builder.getStringAttr("1")}),
            "literal identity or kind was coerced");
    require(
        !accepted("field.add", arguments, {one}) &&
            !accepted("vector.splat", arguments, {natural(1048577)}) &&
            !accepted("matrix.shape_check", arguments,
                      {natural(65537), natural(0)}) &&
            !accepted("vector.matvec", arguments,
                      {natural(3), natural(3), natural(2)}) &&
            !accepted("vector.at", arguments, {builder.getI64IntegerAttr(0)}),
        "parameter bounds or signedness were erased");
    require(!invocationParametersMatch("field.constant", arguments,
                                       builder.getArrayAttr({other}), {"1"}),
            "comparison accepted a different field");
    for (StringRef text : {"", "00", "-1", "18446744073709551616"})
      refuses(decodeInvocationParameters(
                  "index.constant", builder.getArrayAttr({}), {text.str()}),
              "expected-natural");
  });
  cases.run(
      "same digest under different asset formats is not interchangeable", [&] {
        std::string digest(64, 'a');
        auto matrix =
            roundtrip({"matrix.identity_check", {"koala-bear"}, ""}, {digest});
        auto ring = roundtrip({"ring.point", {"koala-bear"}, ""}, {digest});
        auto relation = roundtrip(
            {"relation.table_shape", {"koala-bear", "0"}, ""}, {digest});
        require(matrix != ring && ring != relation &&
                    !accepted("matrix.identity_check", arguments,
                              ring.getValue()) &&
                    !accepted("ring.point", arguments, matrix.getValue()),
                "asset format identity was lost");
      });
  cases.run("catalog roles distinguish message origins and query methods", [&] {
    std::string transcript;
    for (const auto &domain : installedDomains().allDomains())
      if (domain.sort == "Transcript" &&
          installedDomains().hasFact("FieldTranscript", {domain.identity}) &&
          installedDomains().hasFact("IndexTranscript", {domain.identity})) {
        transcript = domain.identity;
        break;
      }
    require(!transcript.empty(), "missing transcript fixture");
    auto query = NativeOriginTemplate{
        "entry",
        {},
        NativeQueryOrigin{"main", "coin", 1, "service", "index", "V"}};
    auto index =
        roundtrip({"transcript.native.indexed.index", {transcript}, ""},
                  {take(encodeNativeOriginTemplate(query))});
    auto args = builder.getArrayAttr({builder.getStringAttr(transcript)});
    require(!accepted("transcript.native.indexed.challenge", args,
                      index.getValue()),
            "index query substituted for field draw");
    std::get<NativeQueryOrigin>(query.event).method = "draw";
    roundtrip({"transcript.native.indexed.challenge", {transcript}, ""},
              {take(encodeNativeOriginTemplate(query))});
    auto message = NativeOriginTemplate{
        "entry", {}, NativeMessageOrigin{"main", "msg", "schema", "P", "V"}};
    roundtrip({"transcript.native.indexed.observe.data",
               {transcript, "field:bls12-381.fr"},
               ""},
              {take(encodeNativeOriginTemplate(message))});
  });
  cases.run(
      "numerical graphs preserve exact sharing and positional slots", [&] {
        auto selected = take(ring::Expression::create(
            {{"koala-bear"}, {"koala-bear"}},
            {ring::Node::slot(0), ring::Node::slot(0), ring::Node::add(0, 1)},
            {2}));
        auto native = roundtrip({"numerical.map", {"koala-bear", "01"}, ""},
                                {printJson(selected.encode())});
        auto mask = builder.getDenseBoolArrayAttr({true});
        require(!accepted("numerical.map",
                          builder.getArrayAttr({arguments[0], mask}),
                          native.getValue()),
                "unused positional input was discarded");
        auto malformed = algebra::RingExpressionAttr::get(&context, {}, {},
                                                          DenseI32ArrayAttr{});
        require(
            !accepted("numerical.sum",
                      builder.getArrayAttr(
                          {arguments[0], builder.getDenseBoolArrayAttr({})}),
                      {malformed}),
            "unchecked graph was admitted");
      });
  cases.run(
      "native numerical admission retains exact encoded body ceiling", [&] {
        // Adjust a prime literal to hit each byte boundary in a reachable
        // graph.
        auto boundary = [&](size_t bytes) {
          std::vector<ring::Node> nodes{
              ring::Node::literal("bls12-381.fr", "0")};
          auto expression = [&] {
            return take(ring::Expression::create({}, nodes,
                                                 {uint32_t(nodes.size() - 1)}));
          };
          while (printJson(expression().encode()).size() <= bytes)
            nodes.push_back(ring::Node::neg(nodes.size() - 1));
          nodes.pop_back();
          nodes[0].constant = std::string(
              bytes - printJson(expression().encode()).size() + 1, '1');
          return expression();
        };
        auto args = builder.getArrayAttr({builder.getStringAttr("bls12-381.fr"),
                                          builder.getDenseBoolArrayAttr({})});
        for (size_t count : {4095, 4096, 4097}) {
          auto expression = boundary(count);
          auto native =
              take(algebra::importRingExpression(&context, expression));
          require(take(algebra::ringExpressionByteSize(native)) == count &&
                      accepted("numerical.sum", args, {native}) ==
                          (count <= 4096),
                  "native admission changed the byte-sensitive work boundary");
        }
      });
  return cases.result();
}
