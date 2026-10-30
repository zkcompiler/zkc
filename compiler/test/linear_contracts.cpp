#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/LinearContraction.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::protocol;
namespace {
unsigned checks = 0;
void require(bool condition, StringRef detail) {
  ++checks;
  if (!condition) {
    errs() << detail << '\n';
    std::exit(1);
  }
}
template <class T> T accept(Expected<T> result) {
  if (!result)
    require(false, toString(result.takeError()));
  ++checks;
  return std::move(*result);
}
template <class T> void refuse(Expected<T> result, StringRef code) {
  require(!result, "expected refusal");
  require(toString(result.takeError()) == code, code);
}
void refuse(Error result, StringRef code) {
  require(bool(result), "expected refusal");
  require(toString(std::move(result)) == code, code);
}

void catalogAndCarriers(MLIRContext &ctx) {
  const auto &catalog = installedDomains();
  require(catalog.associatedIdentity("ristretto255.group", "Scalar") ==
              "ristretto255.scalar",
          "nominal group scalar association");
  require(catalog.associatedIdentity("merlin3.ristretto255.scalar64le/0",
                                     "ChallengeField") == "ristretto255.scalar",
          "nominal challenge field association");
  for (StringRef fact :
       {"Field", "CommRing", "PrimeField", "CharacteristicNotTwo"})
    require(catalog.hasFact(fact, {"ristretto255.scalar"}),
            "Ristretto field facts");
  require(catalog.hasFact("ScalarAction", {"ristretto255.group"}),
          "Ristretto scalar action");
  for (StringRef identity : {"bls12-381.fr", "ristretto255.scalar"})
    for (StringRef kind :
         {"field", "vector", "polynomial", "round", "rng", "nonce"}) {
      BoundType t{kind.str(), identity.str(), ""};
      auto logical = decodeBoundType(&ctx, t);
      require(accept(encodeBoundType(logical, false)) == t,
              "logical carrier roundtrip");
      auto physical = accept(defaultRepresentation(t));
      require(accept(encodeBoundType(decodeBoundType(&ctx, physical), true)) ==
                  physical,
              "physical carrier roundtrip");
      if (kind == "vector") {
        auto vector = dyn_cast<zkc::algebra::FieldVectorType>(logical);
        require(vector && vector.getDomain() == identity &&
                    vector.getElementType() ==
                        zkc::algebra::FieldType::get(&ctx, identity),
                "vector exact nominal domain and element type");
      } else if (kind == "polynomial")
        require(isa<zkc::poly::UnivariateType>(logical),
                "polynomial has a distinct mathematical carrier");
    }
  for (StringRef identity : {"bls12-381.g1", "ristretto255.group"}) {
    BoundType t{"groups", identity.str(), ""};
    auto logical =
        cast<zkc::algebra::GroupVectorType>(decodeBoundType(&ctx, t));
    require(logical.getElementType() ==
                zkc::algebra::GroupType::get(&ctx, identity),
            "group vector exact elements");
    require(accept(encodeBoundType(logical, false)) == t,
            "groups source spelling roundtrip");
  }
  auto scalar = zkc::algebra::FieldType::get(&ctx, "ristretto255.scalar");
  for (Type type :
       {Type(RankedTensorType::get({}, scalar)),
        Type(UnrankedTensorType::get(scalar)),
        Type(RankedTensorType::get({ShapedType::kDynamic},
                                   IntegerType::get(&ctx, 64))),
        Type(RankedTensorType::get({ShapedType::kDynamic}, scalar,
                                   StringAttr::get(&ctx, "custom")))})
    refuse(encodeBoundType(type, false), "binding-type");
  refuse(parseBoundType("vector:ristretto255.group", false),
         "binding-type-identity");
  refuse(parseBoundType("groups:ristretto255.scalar", false),
         "binding-type-identity");
  refuse(
      parseBoundType("vector:ristretto255.scalar@arkworks.fr-vector/0", true),
      "binding-representation");
  refuse(parseBoundType("polynomial:ristretto255.scalar@dalek.scalar-vector/0",
                        true),
         "binding-representation");
  refuse(parseBoundType("groups:bls12-381.g1@dalek.ristretto-diagonal/0", true),
         "binding-representation");
  refuse(DomainCatalog::create({{"bad.g", "Group", {{"Scalar", "bad.g"}}, {}}},
                               {}, {}, {}),
         "invalid associated identity");
  refuse(DomainCatalog::create({{"bad.f", "Field", {}, {}, "01"}}, {}, {}, {}),
         "invalid field modulus");
  refuse(DomainCatalog::create({{"bad.g", "Group", {}, {}, "7"}}, {}, {}, {}),
         "invalid field modulus");
  refuse(DomainCatalog::create({{"bad.f", "Field", {}, {}}}, {},
                               {{"bad.codec", "groups", "bad.f"}}, {}),
         "invalid codec payload domain");
  refuse(DomainCatalog::create({{"bad.f", "Field", {}, {}}}, {}, {},
                               {{"bad.rep", "groups", "bad.f", true, ""}}),
         "invalid representation domain");

  for (auto [contract, nominal, impl, kind, rep] :
       {std::tuple{"vector.mul", "bls12-381.fr", "arkworks-diagonal/vector.mul",
                   "vector", "arkworks.fr-diagonal/0"},
        std::tuple{"curve.scale_each", "ristretto255.group",
                   "dalek-diagonal/curve.scale_each", "groups",
                   "dalek.ristretto-diagonal/0"}}) {
    protocol::OperationBinding b{"map", {contract, {nominal}, impl}};
    auto physical = accept(resolveBinding(b.application, true));
    require(physical.outputs[0].kind == kind &&
                physical.outputs[0].representation == rep,
            "reserved physical result only");
    require(!isDiagonalRepresentation(physical.inputs[0].representation) &&
                !isDiagonalRepresentation(physical.inputs[1].representation),
            "depth one backing only");
    auto logical = accept(resolveBinding(b.application, false));
    require(logical.outputs[0].representation.empty(),
            "logical producer contract unchanged");
  }
  protocol::OperationBinding msm{
      "msm", {"curve.msm", {"ristretto255.group"}, "dalek-diagonal/curve.msm"}};
  auto physical = accept(resolveBinding(msm.application, true));
  require(physical.inputs[0].identity == "ristretto255.scalar" &&
              physical.inputs[0].representation == "dalek.scalar-vector/0" &&
              physical.inputs[1].representation ==
                  "dalek.ristretto-diagonal/0" &&
              physical.outputs[0].representation == "dalek.ristretto/0",
          "MSM exact domains and operand roles");
  msm.application.arguments[0] = "bls12-381.g1";
  refuse(resolveBinding(msm.application, true), "binding-implementation");
  msm.application.implementation = "arkworks-diagonal/curve.msm";
  refuse(resolveBinding(msm.application, true), "binding-implementation");
  protocol::OperationBinding observe{
      "observe",
      {"transcript.native.indexed.observe.data",
       {"merlin3.ristretto255.scalar64le/0", "rng:ristretto255.scalar"},
       ""}};
  refuse(resolveBinding(observe.application, false), "native-proof-wire-type");
  observe.application.arguments[1] = "vector:ristretto255.scalar";
  require(accept(defaultImplementation(observe.application)) ==
              "dalek/transcript.native.indexed.observe.data",
          "typed Ristretto observation backend");
  refuse(checkImplementation("poly.coefficients",
                             "arkworks-msb/poly.coefficients"),
         "binding-implementation");
  protocol::OperationBinding unknown{
      "unknown",
      {"vector.unknown", {"bls12-381.fr"}, "arkworks/vector.unknown"}};
  refuse(resolveBinding(unknown.application, true), "binding-contract");
  refuse(checkParameters("vector.gather", {"00"}), "noncanonical-natural");
  refuse(checkParameters("vector.matvec", {"1", "2", "01"}),
         "noncanonical-natural");
  refuse(checkParameters("field.constant", {"0"}, "missing.field"),
         "interactive-constant");
}

void scopedRoles(MLIRContext &ctx) {
  OpBuilder builder(&ctx);
  auto loc = builder.getUnknownLoc();
  OwningOpRef<ModuleOp> module(ModuleOp::create(loc));
  builder.setInsertionPointToEnd(module->getBody());
  for (StringRef contract : {"vector.mul", "vector.dot"})
    runtime::BindingOp::create(builder, loc, contract, contract,
                               builder.getStrArrayAttr({"koala-bear"}), "");
  auto vector = algebra::FieldVectorType::get(&ctx, "koala-bear");
  auto field = algebra::FieldType::get(&ctx, "koala-bear");
  auto scope = runtime::ScopeType::get(&ctx);
  auto function = func::FuncOp::create(
      builder, loc, "roles",
      builder.getFunctionType({scope, vector, vector}, {}));
  builder.setInsertionPointToEnd(function.addEntryBlock());
  auto call = [&](StringRef contract, Type output) {
    OperationState state(loc, exec::ApplyOp::getOperationName());
    state.addOperands(function.getArguments());
    state.addTypes(exec::OutcomeType::get(&ctx, {output}));
    state.addAttribute("binding", FlatSymbolRefAttr::get(&ctx, contract));
    state.addAttribute("parameters", builder.getArrayAttr({}));
    state.addAttribute("site", builder.getStringAttr(contract));
    return cast<exec::ApplyOp>(builder.create(state));
  };
  auto multiply = call("vector.mul", vector);
  auto dot = call("vector.dot", field);
  func::ReturnOp::create(builder, loc);
  require(succeeded(verify(*module)),
          "scoped role fixture must be well formed");
  auto producer = cast<DiagonalProducerInterface>(multiply.getOperation());
  auto consumer = cast<DiagonalContractionInterface>(dot.getOperation());
  auto map = producer.getDiagonalProducerRoles();
  auto contraction = consumer.getDiagonalContractionRoles();
  require(map && map->factorsOperand == 0 && map->valuesOperand == 1 &&
              map->result == 0,
          "producer roles index logical inputs and payload, excluding scope");
  require(contraction && contraction->coefficientsOperand == 0 &&
              contraction->valuesOperand == 1,
          "contraction roles exclude the invocation scope");
  require(!multiply.getDiagonalContractionRoles() &&
              !dot.getDiagonalProducerRoles(),
          "shared interfaces do not invent absent catalog facets");
  multiply.setParametersAttr(builder.getStrArrayAttr({"1"}));
  require(!producer.getDiagonalProducerRoles(),
          "malformed application parameters cannot expose semantic roles");
  multiply.setParametersAttr(builder.getArrayAttr({}));
  auto original = multiply.getOutcome().getType();
  multiply.getOutcome().setType(exec::OutcomeType::get(&ctx, {field}));
  require(!producer.getDiagonalProducerRoles(),
          "wrong outcome payload cannot expose producer roles");
  multiply.getOutcome().setType(original);
  function.getArgument(1).setType(
      algebra::FieldVectorType::get(&ctx, "bls12-381.fr"));
  require(!producer.getDiagonalProducerRoles() &&
              !consumer.getDiagonalContractionRoles(),
          "nominal operand mismatch cannot expose semantic roles");
  function.getArgument(1).setType(vector);
  multiply.setBindingAttr(FlatSymbolRefAttr::get(&ctx, "missing"));
  {
    ScopedDiagnosticHandler silence(&ctx,
                                    [](Diagnostic &) { return success(); });
    require(failed(verify(*module)),
            "missing binding must fail symbol-use verification");
  }
  require(!producer.getDiagonalProducerRoles(),
          "unresolved binding has no roles");
  multiply.setBindingAttr(FlatSymbolRefAttr::get(&ctx, "vector.mul"));
  require(succeeded(verify(*module)) && producer.getDiagonalProducerRoles(),
          "restored actual invocation resolves its roles again");
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  catalogAndCarriers(context);
  scopedRoles(context);
  outs() << "linear contracts and domain extensions: " << checks
         << " checks passed\n";
}
