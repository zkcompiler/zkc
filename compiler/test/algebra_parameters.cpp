#include "mlir/AsmParser/AsmParser.h"
#include "mlir/IR/Builders.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::algebra;
int main() {
  DialectRegistry registry;
  registry.insert<AlgebraDialect>();
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  OpBuilder builder(&context);
  auto field = FieldType::get(&context, "koala-bear");
  auto other = FieldType::get(&context, "baby-bear");
  auto extension = FieldType::get(&context, "koala-bear.ext8-binomial3");
  Cases cases;
  auto roundtrip = [&](const ring::Expression &source) {
    auto native = take(importRingExpression(&context, source));
    require(succeeded(RingExpressionAttr::verify(
                [&] { return emitError(builder.getUnknownLoc()); },
                native.getInputs(), native.getNodes(), native.getOutputs())),
            "native formation disagrees with independent Ring reader");
    std::string text;
    raw_string_ostream out(text);
    out << native;
    auto parsed =
        dyn_cast_or_null<RingExpressionAttr>(parseAttribute(text, &context));
    require(parsed == native, "MLIR attribute print/parse changed the graph");
    auto encoded = take(exportRingExpression(parsed));
    require(printJson(encoded.encode()) == printJson(source.encode()) &&
                encoded.identity() == source.identity() &&
                take(encodeRingExpression(native)) ==
                    printJson(source.encode()) &&
                take(ringExpressionByteSize(native)) ==
                    printJson(source.encode()).size(),
            "Ring boundary changed exact bytes or identity");
    return native;
  };
  cases.run("empty graph lists and constant-only expressions roundtrip", [&] {
    roundtrip(take(ring::Expression::create({}, {}, {})));
    roundtrip(take(ring::Expression::create(
        {}, {ring::Node::literal("koala-bear", "1")}, {0})));
  });
  for (StringRef name :
       {"koala-bear", "bls12-381.fr", "gf2-64.pentanomial-4-3-1",
        "gf2-64.pentanomial-4-3-1.ext3-trinomial1"})
    cases.run("canonical literals " + name, [&] {
      auto type = FieldType::get(&context, name);
      for (StringRef value : {"0", "1"}) {
        auto literal = take(decodeFieldLiteral(type, value));
        require(take(encodeFieldLiteral(literal)) == value,
                "literal roundtrip");
        require(succeeded(FieldLiteralAttr::verify(
                    [&] { return emitError(builder.getUnknownLoc()); }, type,
                    literal.getValue())),
                "native literal formation");
      }
      for (StringRef malformed : {"", "00", "01", "-1", "+1", "0x0", "0x01"})
        refuses(decodeFieldLiteral(type, malformed), "field-literal");
    });
  cases.run("field presentations retain exact arbitrary-width values", [&] {
    auto bls = FieldType::get(&context, "bls12-381.fr");
    StringRef large = "340282366920938463463374607431768211456";
    require(take(encodeFieldLiteral(take(decodeFieldLiteral(bls, large)))) ==
                large,
            "wide prime literal was truncated");
    refuses(decodeFieldLiteral(field, "2130706433"), "field-literal");
    refuses(decodeFieldLiteral(field, "0x2"), "field-literal");
    auto binary =
        FieldType::get(&context, "gf2-64.pentanomial-4-3-1.ext3-trinomial1");
    StringRef bits = "0xffffffffffffffffffffffffffffffffffffffffffffffff";
    require(take(encodeFieldLiteral(take(decodeFieldLiteral(binary, bits)))) ==
                bits,
            "wide binary literal was truncated");
    refuses(decodeFieldLiteral(binary, "2"), "field-literal");
    refuses(decodeFieldLiteral(binary, "0xF"), "field-literal");
    refuses(decodeFieldLiteral(
                binary, "0x1000000000000000000000000000000000000000000000000"),
            "field-literal");
  });
  cases.run("native literal width and signedness are not interchangeable", [&] {
    for (auto type : {builder.getI32Type(),
                      IntegerType::get(&context, 31, IntegerType::Signed),
                      IntegerType::get(&context, 32, IntegerType::Unsigned)}) {
      std::string code;
      ScopedDiagnosticHandler diagnostic(&context, [&](Diagnostic &d) {
        auto refusals = diagnostics::refusals(d);
        if (!refusals.empty())
          code = refusals.front().code;
        return success();
      });
      auto literal = FieldLiteralAttr::getChecked(
          [&] { return emitError(builder.getUnknownLoc()); }, &context, field,
          IntegerAttr::get(type, 1));
      require(!literal && code == "field-literal",
              "noncanonical integer type admitted");
    }
  });
  cases.run(
      "selected graphs preserve repeated inputs and exact node order", [&] {
        auto shared = take(ring::Expression::create(
            {{"koala-bear"}, {"koala-bear"}},
            {ring::Node::slot(0), ring::Node::add(0, 0)}, {1}));
        auto repeated = take(ring::Expression::create(
            {{"koala-bear"}, {"koala-bear"}},
            {ring::Node::slot(0), ring::Node::slot(0), ring::Node::add(0, 1)},
            {2}));
        auto left = roundtrip(shared), right = roundtrip(repeated);
        require(left != right && left.getNodes().size() == 2 &&
                    right.getNodes().size() == 3 &&
                    right.getInputs().size() == 2,
                "budget-sensitive graph or unused input slot was collapsed");
        roundtrip(take(ring::Expression::create(
            {{"koala-bear"}},
            {ring::Node::literal("koala-bear", "1"), ring::Node::slot(0),
             ring::Node::mul(0, 1), ring::Node::neg(2)},
            {3})));
      });
  cases.run("declared embedding survives a Ring boundary", [&] {
    roundtrip(take(ring::Expression::create(
        {{"koala-bear"}},
        {ring::Node::slot(0),
         ring::Node::embed(extension.getDomain().str(), 0)},
        {1})));
  });
  auto node = [&](RingNodeKind kind, ArrayRef<int32_t> indices,
                  FieldType target = {}) {
    return RingNodeAttr::get(&context, kind,
                             builder.getDenseI32ArrayAttr(indices),
                             FieldLiteralAttr{}, target);
  };
  auto refuse = [&](StringRef expected, ArrayRef<FieldType> inputs,
                    ArrayRef<RingNodeAttr> nodes, ArrayRef<int32_t> outputs) {
    std::string code;
    ScopedDiagnosticHandler diagnostic(&context, [&](Diagnostic &d) {
      auto refusals = diagnostics::refusals(d);
      if (!refusals.empty())
        code = refusals.front().code;
      return success();
    });
    auto value = RingExpressionAttr::getChecked(
        [&] { return emitError(builder.getUnknownLoc()); }, &context, inputs,
        nodes, builder.getDenseI32ArrayAttr(outputs));
    require(!value && code == expected, "unexpected native refusal: " + code);
  };
  cases.run("actual graph formation checks every structural obligation", [&] {
    refuse("ring-input", {field}, {node(RingNodeKind::Input, {1})}, {0});
    refuse("ring-node-shape", {field}, {node(RingNodeKind::Input, {-1})}, {0});
    refuse("ring-edge", {field},
           {node(RingNodeKind::Input, {0}), node(RingNodeKind::Add, {0, 1})},
           {1});
    refuse("ring-output", {field}, {node(RingNodeKind::Input, {0})}, {1});
    refuse("ring-unreachable-node", {field},
           {node(RingNodeKind::Input, {0}), node(RingNodeKind::Input, {0})},
           {0});
    refuse("ring-field-mismatch", {field, other},
           {node(RingNodeKind::Input, {0}), node(RingNodeKind::Input, {1}),
            node(RingNodeKind::Add, {0, 1})},
           {2});
    refuse(
        "ring-embedding", {field},
        {node(RingNodeKind::Input, {0}), node(RingNodeKind::Embed, {0}, other)},
        {1});
    SmallVector<RingNodeAttr> chain{node(RingNodeKind::Input, {0})};
    for (unsigned i = 1; i <= ring::Limits::depth; ++i)
      chain.push_back(node(RingNodeKind::Negate, {int32_t(i - 1)}));
    refuse("ring-depth", {field}, chain, {int32_t(chain.size() - 1)});
  });
  cases.run("byte publication rechecks unchecked native construction", [&] {
    auto malformed = RingExpressionAttr::get(&context, {field},
                                             {node(RingNodeKind::Add, {0, 0})},
                                             builder.getDenseI32ArrayAttr({0}));
    refuses(exportRingExpression(malformed), "ring-attribute");
    refuses(exportRingExpression({}), "ring-attribute");
    auto wrongArity = RingExpressionAttr::get(
        &context, {field}, {node(RingNodeKind::Add, {})},
        builder.getDenseI32ArrayAttr({0}));
    refuses(exportRingExpression(wrongArity), "ring-attribute");
    auto wrongLiteral =
        FieldLiteralAttr::get(&context, field, builder.getI64IntegerAttr(1));
    refuses(encodeFieldLiteral(wrongLiteral), "field-literal");
    refuses(encodeFieldLiteral({}), "field-literal");
  });
  return cases.result();
}
