#include "mlir/IR/Builders.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
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

// A test dialect supplies the same narrow optional interfaces under unrelated
// operation names. The shared analysis knows neither these names nor the real
// algebra/curve names. Real planner admission still requires installed
// bindings.
class ModuleMapOp
    : public Op<ModuleMapOp, OpTrait::NOperands<2>::Impl, OpTrait::OneResult,
                DiagonalProducerInterface::Trait> {
public:
  using Op::Op;
  static StringRef getOperationName() { return "extension.map"; }
  static ArrayRef<StringRef> getAttributeNames() { return {}; }
  std::optional<DiagonalProducerRoles> getDiagonalProducerRoles() {
    if ((*this)->hasAttr("unavailable"))
      return {};
    if ((*this)->hasAttr("bad_result"))
      return DiagonalProducerRoles{0, 1, 1};
    if ((*this)->hasAttr("overlapping_roles"))
      return DiagonalProducerRoles{1, 1, 0};
    return DiagonalProducerRoles{0, 1, 0};
  }
};
class ContractOp
    : public Op<ContractOp, OpTrait::NOperands<2>::Impl, OpTrait::OneResult,
                DiagonalContractionInterface::Trait> {
public:
  using Op::Op;
  static StringRef getOperationName() { return "extension.contract"; }
  static ArrayRef<StringRef> getAttributeNames() { return {}; }
  std::optional<DiagonalContractionRoles> getDiagonalContractionRoles() {
    if ((*this)->hasAttr("unavailable"))
      return {};
    if ((*this)->hasAttr("bad_coefficient"))
      return DiagonalContractionRoles{2, 1};
    if ((*this)->hasAttr("swapped_roles"))
      return DiagonalContractionRoles{1, 0};
    return DiagonalContractionRoles{0, 1};
  }
};
class ExtensionDialect : public Dialect {
public:
  explicit ExtensionDialect(MLIRContext *context)
      : Dialect(getDialectNamespace(), context,
                TypeID::get<ExtensionDialect>()) {
    addOperations<ModuleMapOp, ContractOp>();
    allowUnknownOperations();
  }
  static StringRef getDialectNamespace() { return "extension"; }
};

void catalogAndCarriers(MLIRContext &ctx) {
  const auto &catalog = installedDomains();
  require(catalog.associatedIdentity("ristretto255.group", "Scalar") ==
              "ristretto255.scalar",
          "nominal group scalar association");
  require(catalog.associatedIdentity("merlin3.ristretto255.scalar64le/1",
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
        auto tensor = dyn_cast<RankedTensorType>(logical);
        require(tensor && tensor.getRank() == 1 && tensor.isDynamicDim(0) &&
                    tensor.getElementType() == FieldType::get(&ctx, identity),
                "vector exact dynamic nominal element type");
      } else if (kind == "polynomial")
        require(isa<UnivariateType>(logical),
                "polynomial has a distinct mathematical carrier");
    }
  for (StringRef identity : {"bls12-381.g1", "ristretto255.group"}) {
    BoundType t{"groups", identity.str(), ""};
    auto logical = cast<RankedTensorType>(decodeBoundType(&ctx, t));
    require(logical.getElementType() == GroupType::get(&ctx, identity),
            "group tensor exact elements");
    require(accept(encodeBoundType(logical, false)) == t,
            "groups source spelling roundtrip");
  }
  auto scalar = FieldType::get(&ctx, "ristretto255.scalar");
  for (Type type :
       {Type(RankedTensorType::get({4}, scalar)),
        Type(RankedTensorType::get({}, scalar)),
        Type(RankedTensorType::get({ShapedType::kDynamic, ShapedType::kDynamic},
                                   scalar)),
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
      parseBoundType("vector:ristretto255.scalar@arkworks.fr-vector/1", true),
      "binding-representation");
  refuse(parseBoundType("polynomial:ristretto255.scalar@dalek.scalar-vector/1",
                        true),
         "binding-representation");
  refuse(parseBoundType("groups:bls12-381.g1@dalek.ristretto-diagonal/1", true),
         "binding-representation");
  refuse(DomainCatalog::create({{"bad.g", "Group", {{"Scalar", "bad.g"}}, {}}},
                               {}, {}),
         "invalid associated identity");
  refuse(DomainCatalog::create({{"bad.f", "Field", {}, {}, "01"}}, {}, {}),
         "invalid field modulus");
  refuse(DomainCatalog::create({{"bad.g", "Group", {}, {}, "7"}}, {}, {}),
         "invalid field modulus");
  refuse(DomainCatalog::create({{"bad.f", "Field", {}, {}}},
                               {{"bad.codec", "groups", "bad.f"}}, {}),
         "invalid codec payload domain");
  refuse(DomainCatalog::create({{"bad.f", "Field", {}, {}}}, {},
                               {{"bad.rep", "groups", "bad.f", true, ""}}),
         "invalid representation domain");

  for (auto [contract, nominal, impl, kind, rep] :
       {std::tuple{"vector.mul", "bls12-381.fr", "arkworks-diagonal/vector.mul",
                   "vector", "arkworks.fr-diagonal/1"},
        std::tuple{"curve.scale_each", "ristretto255.group",
                   "dalek-diagonal/curve.scale_each", "groups",
                   "dalek.ristretto-diagonal/1"}}) {
    source::OperationBinding b{{}, "map", {contract, {nominal}, impl}};
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
  source::OperationBinding msm{
      {},
      "msm",
      {"curve.msm", {"ristretto255.group"}, "dalek-diagonal/curve.msm"}};
  auto physical = accept(resolveBinding(msm.application, true));
  require(physical.inputs[0].identity == "ristretto255.scalar" &&
              physical.inputs[0].representation == "dalek.scalar-vector/1" &&
              physical.inputs[1].representation ==
                  "dalek.ristretto-diagonal/1" &&
              physical.outputs[0].representation == "dalek.ristretto/1",
          "MSM exact domains and operand roles");
  msm.application.arguments[0] = "bls12-381.g1";
  refuse(resolveBinding(msm.application, true), "binding-implementation");
  msm.application.implementation = "arkworks-diagonal/curve.msm";
  refuse(resolveBinding(msm.application, true), "binding-implementation");
  source::OperationBinding observe{
      {},
      "observe",
      {"transcript.observe.vector",
       {"merlin3.ristretto255.scalar64le/1", "ristretto255.scalar",
        "zkcv.vector.bls12-381.fr/1"},
       ""}};
  refuse(resolveBinding(observe.application, false), "binding-requirement");
  observe.application.arguments[2] = "zkcv.polynomial.ristretto255.scalar/1";
  refuse(resolveBinding(observe.application, false), "binding-requirement");
  observe.application.arguments[2] = "zkcv.vector.ristretto255.scalar/1";
  require(accept(defaultImplementation(observe.application)) ==
              "dalek/transcript.observe.vector",
          "matching Ristretto codec backend");
  refuse(checkImplementation("poly.coefficients",
                             "arkworks-msb/poly.coefficients"),
         "binding-implementation");
  source::OperationBinding unknown{
      {},
      "unknown",
      {"vector.unknown", {"bls12-381.fr"}, "arkworks/vector.unknown"}};
  refuse(resolveBinding(unknown.application, true), "binding-contract");
  refuse(checkParameters("vector.gather", {"00"}), "noncanonical-natural");
  refuse(checkParameters("vector.matvec", {"1", "2", "01"}),
         "noncanonical-natural");
  refuse(checkParameters("field.constant", {"0"}, "missing.field"),
         "interactive-constant");
}

void optionalInterfaces(MLIRContext &ctx) {
  OpBuilder b(&ctx);
  OwningOpRef<ModuleOp> module(ModuleOp::create(b.getUnknownLoc()));
  auto field = RankedTensorType::get(
      {ShapedType::kDynamic}, FieldType::get(&ctx, "ristretto255.scalar"));
  auto group = RankedTensorType::get(
      {ShapedType::kDynamic}, GroupType::get(&ctx, "ristretto255.group"));
  auto resultType = GroupType::get(&ctx, "ristretto255.group");
  auto function = func::FuncOp::create(
      b.getUnknownLoc(), "unrelated",
      b.getFunctionType({field, group, field}, {resultType}));
  module->push_back(function);
  auto *block = function.addEntryBlock();
  b.setInsertionPointToEnd(block);
  auto op = [&](StringRef name, ValueRange operands, Type result) {
    OperationState state(b.getUnknownLoc(), name);
    state.addOperands(operands);
    state.addTypes(result);
    return b.create(state);
  };
  auto *producer = op("extension.map",
                      {block->getArgument(0), block->getArgument(1)}, group);
  auto *consumer =
      op("extension.contract", {block->getArgument(2), producer->getResult(0)},
         resultType);
  auto ret =
      func::ReturnOp::create(b, b.getUnknownLoc(), consumer->getResult(0));
  auto count = [&] {
    LinearContractionStats stats;
    return findLinearContractions(function, stats).size();
  };
  require(count() == 1,
          "shared analysis uses interfaces, not known operation names");
  auto roles =
      cast<DiagonalProducerInterface>(producer).getDiagonalProducerRoles();
  require(roles && roles->factorsOperand == 0 && roles->valuesOperand == 1 &&
              roles->result == 0,
          "synthetic semantic roles need no binding or installed backend");
  for (StringRef attribute : {"bad_result", "overlapping_roles"}) {
    producer->setAttr(attribute, b.getUnitAttr());
    require(count() == 0, "invalid synthetic producer roles refuse grouping");
    producer->removeAttr(attribute);
  }
  for (StringRef attribute : {"bad_coefficient", "swapped_roles"}) {
    consumer->setAttr(attribute, b.getUnitAttr());
    require(count() == 0, "invalid synthetic consumer roles refuse grouping");
    consumer->removeAttr(attribute);
  }
  b.setInsertionPoint(ret);
  auto *second =
      op("extension.contract", {block->getArgument(2), producer->getResult(0)},
         resultType);
  LinearContractionStats shared;
  auto groups = findLinearContractions(function, shared);
  require(groups.size() == 1 && groups[0].uses.size() == 2 &&
              groups[0].uses[0].consumer == consumer &&
              groups[0].uses[1].consumer == second &&
              shared.eligiblePairs == 2 && shared.eligibleProducers == 1,
          "all uses grouped atomically in source order");
  second->setAttr("unavailable", b.getUnitAttr());
  require(count() == 0, "one unavailable use disqualifies the whole producer");
  second->erase();
  producer->setAttr("unavailable", b.getUnitAttr());
  require(count() == 0, "missing optional producer choice retains dense");
  producer->removeAttr("unavailable");
  consumer->setAttr("unavailable", b.getUnitAttr());
  require(count() == 0, "missing optional consumer choice retains dense");
  consumer->removeAttr("unavailable");
  consumer->setOperand(0, producer->getResult(0));
  require(count() == 0, "two operand uses in one consumer are not single-use");
  consumer->setOperand(0, block->getArgument(2));
  block->getArgument(2).setType(RankedTensorType::get(
      {ShapedType::kDynamic}, FieldType::get(&ctx, "bls12-381.fr")));
  require(count() == 0, "mixed nominal coefficient domains refuse selection");
  block->getArgument(2).setType(field);
  b.setInsertionPoint(consumer);
  auto *unknown = op("extension.unknown", {producer->getResult(0)}, resultType);
  require(count() == 0, "unknown extra consumer prevents selection");
  consumer->setOperand(1, block->getArgument(1));
  require(count() == 0, "unknown single consumer lacks the optional interface");
  unknown->erase();
  consumer->setOperand(1, producer->getResult(0));
  ret->setOperand(0, producer->getResult(0));
  require(count() == 0, "function escape is not local single-use");
  consumer->erase();
  require(count() == 0,
          "return-only use cannot select a diagonal representation");
  auto *extra = new Block;
  function.getBody().push_back(extra);
  require(count() == 0,
          "multi-block control never acquires a local lifetime inference");
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  registry.insert<ExtensionDialect>();
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  catalogAndCarriers(context);
  optionalInterfaces(context);
  outs() << "linear interfaces and domain extensions: " << checks
         << " checks passed\n";
}
