#include "zkc/Dialect/Bindings.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Json.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {

StringRef boundOperationName(StringRef contract) {
  if (contract.starts_with("transcript.observe.") &&
      llvm::any_of(kernels(), [&](const Kernel &kernel) {
        return kernel.key == contract;
      }))
    return TranscriptObserveOp::getOperationName();
  static const std::pair<StringRef, StringRef> operations[] = {
      {"resource_unit.create", ResourceUnitCreateOp::getOperationName()},
      {"resource_unit.pass", ResourceUnitPassOp::getOperationName()},
      {"resource_unit.consume", ResourceUnitConsumeOp::getOperationName()},
      {"external.monero.init", ExternalMoneroInitOp::getOperationName()},
      {"external.monero.hash", ExternalMoneroHashOp::getOperationName()},
      {"external.monero.update", ExternalMoneroUpdateOp::getOperationName()},
      {"external.openvm.init", ExternalOpenvmInitOp::getOperationName()},
      {"external.openvm.observe", ExternalOpenvmObserveOp::getOperationName()},
      {"external.openvm.sample", ExternalOpenvmSampleOp::getOperationName()},
      {"external.openvm.sample_ext",
       ExternalOpenvmSampleExtOp::getOperationName()},
      {"external.openvm.sample_bits",
       ExternalOpenvmSampleBitsOp::getOperationName()},
      {"external.openvm.check_witness",
       ExternalOpenvmCheckWitnessOp::getOperationName()},
      {"index.constant", IndexConstantOp::getOperationName()},
      {"index.add", IndexAddOp::getOperationName()},
      {"index.sub", IndexSubOp::getOperationName()},
      {"index.mul", IndexMulOp::getOperationName()},
      {"index.div", IndexDivOp::getOperationName()},
      {"index.mod", IndexModOp::getOperationName()},
      {"index.equal", IndexEqualOp::getOperationName()},
      {"index.less", IndexLessOp::getOperationName()},
      {"indices.empty", IndicesEmptyOp::getOperationName()},
      {"indices.append", IndicesAppendOp::getOperationName()},
      {"indices.at", IndicesAtOp::getOperationName()},
      {"indices.length", IndicesLengthOp::getOperationName()},
      {"vector.get", VectorGetOp::getOperationName()},
      {"vector.slice", VectorSliceOp::getOperationName()},
      {"vector.length", VectorLengthOp::getOperationName()},
      {"vector.rotate", VectorRotateOp::getOperationName()},
      {"vector.interleave", VectorInterleaveOp::getOperationName()},
      {"vector.prefix_product", VectorPrefixProductOp::getOperationName()},
      {"vector.prefix_sum", VectorPrefixSumOp::getOperationName()},
      {"vector.inverse", VectorInverseOp::getOperationName()},
      {"vector.embed", VectorEmbedOp::getOperationName()},
      {"vector.fill", VectorFillOp::getOperationName()},
      {"vector.geometric", VectorGeometricOp::getOperationName()},
      {"field.from_index", FieldFromIndexOp::getOperationName()},
      {"poly.coefficient_count", CoefficientCountOp::getOperationName()},
      {"poly.coset_evaluate", CosetEvaluateOp::getOperationName()},
      {"poly.coset_interpolate", CosetInterpolateOp::getOperationName()},
      {"poly.domain_point", DomainPointOp::getOperationName()},
      {"poly.domain_root", DomainRootOp::getOperationName()},
      {"poly.domain_points", DomainPointsOp::getOperationName()},
      {"poly.even_odd_fold", EvenOddFoldOp::getOperationName()},
      {"poly.divide_opening", DivideOpeningOp::getOperationName()},
      {"poly.opening_quotient", OpeningQuotientOp::getOperationName()},
      {"field.sub", FieldSubtractOp::getOperationName()},
      {"field.neg", FieldNegateOp::getOperationName()},
      {"field.inverse", FieldInverseOp::getOperationName()},
      {"field.embed", FieldEmbedOp::getOperationName()},
      {"matrix.mul_vector", MatrixMulVectorOp::getOperationName()},
      {"matrix.transpose_mul_vector",
       MatrixTransposeMulVectorOp::getOperationName()},
      {"matrix.bilinear", MatrixBilinearOp::getOperationName()},
      {"matrix.shape_check", MatrixShapeCheckOp::getOperationName()},
      {"matrix.identity_check", MatrixIdentityCheckOp::getOperationName()},
      {"vector.constant", VectorConstantOp::getOperationName()},
      {"vector.scatter_sum", VectorScatterSumOp::getOperationName()},
      {"vector.empty", VectorEmptyOp::getOperationName()},
      {"vector.append", VectorAppendOp::getOperationName()},
      {"vector.splat", VectorSplatOp::getOperationName()},
      {"vector.powers", VectorPowersOp::getOperationName()},
      {"vector.add", VectorAddOp::getOperationName()},
      {"vector.sub", VectorSubOp::getOperationName()},
      {"vector.mul", VectorMulOp::getOperationName()},
      {"vector.dot", VectorDotOp::getOperationName()},
      {"vector.concat", VectorConcatOp::getOperationName()},
      {"vector.kronecker", VectorKroneckerOp::getOperationName()},
      {"vector.matvec", VectorMatvecOp::getOperationName()},
      {"vector.scale", VectorScaleOp::getOperationName()},
      {"vector.sum", VectorSumOp::getOperationName()},
      {"vector.split", VectorSplitOp::getOperationName()},
      {"vector.at", VectorAtOp::getOperationName()},
      {"vector.length_check", VectorLengthCheckOp::getOperationName()},
      {"vector.gather", VectorGatherOp::getOperationName()},
      {"vector.from_point", PointToVectorOp::getOperationName()},
      {"vector.from_table", TableToVectorOp::getOperationName()},
      {"vector.to_point", PointFromVectorOp::getOperationName()},
      {"vector.to_table", TableFromVectorOp::getOperationName()},
      {"poly.equality_weights", EqualityWeightsOp::getOperationName()},
      {"poly.from_coefficients", FromCoefficientsOp::getOperationName()},
      {"poly.coefficients", CoefficientsOp::getOperationName()},
      {"poly.degree_check", DegreeCheckOp::getOperationName()},
      {"poly.univariate_evaluate", UnivariateEvaluateOp::getOperationName()},
      {"poly.univariate_boundary", UnivariateBoundaryOp::getOperationName()},
      {"random.vector", RandomVectorOp::getOperationName()},
      {"curve.neg", CurveNegateOp::getOperationName()},
      {"curve.nonidentity", CurveNonidentityOp::getOperationName()},
      {"curve.msm", CurveMSMOp::getOperationName()},
      {"curve.scale_each", CurveScaleEachOp::getOperationName()},
      {"curve.vector_add", CurveVectorAddOp::getOperationName()},
      {"curve.vector_scale", CurveVectorScaleOp::getOperationName()},
      {"curve.split", CurveSplitOp::getOperationName()},
      {"curve.concat", CurveConcatOp::getOperationName()},
      {"pairing.check", PairingCheckOp::getOperationName()},
      {"field.constant", FieldConstantOp::getOperationName()},
      {"field.add", FieldSumOp::getOperationName()},
      {"field.mul", FieldProductOp::getOperationName()},
      {"field.equal", FieldCompareOp::getOperationName()},
      {"bool.and", BooleanAndOp::getOperationName()},
      {"bool.not", BooleanNotOp::getOperationName()},
      {"bool.or", BooleanOrOp::getOperationName()},
      {"control.require", RequireOp::getOperationName()},
      {"poly.product_sum", ProductSumOp::getOperationName()},
      {"poly.product_round", ProductRoundOp::getOperationName()},
      {"poly.boundary", BoundaryOp::getOperationName()},
      {"poly.round_evaluate", RoundEvaluateOp::getOperationName()},
      {"poly.fold", FoldOp::getOperationName()},
      {"poly.evaluate", MLEEvaluateOp::getOperationName()},
      {"poly.empty_point", EmptyPointOp::getOperationName()},
      {"poly.append_point", AppendPointOp::getOperationName()},
      {"oracle.commit", OracleCommitOp::getOperationName()},
      {"oracle.open", OracleOpenOp::getOperationName()},
      {"oracle.check", OracleCheckOp::getOperationName()},
      {"commitments.empty", CommitmentsEmptyOp::getOperationName()},
      {"commitments.append", CommitmentsAppendOp::getOperationName()},
      {"commitments.at", CommitmentsAtOp::getOperationName()},
      {"commitments.length", CommitmentsLengthOp::getOperationName()},
      {"opening_states.empty", OpeningStatesEmptyOp::getOperationName()},
      {"opening_states.append", OpeningStatesAppendOp::getOperationName()},
      {"opening_states.at", OpeningStatesAtOp::getOperationName()},
      {"opening_states.length", OpeningStatesLengthOp::getOperationName()},
      {"pcs.commit", PCSCommitOp::getOperationName()},
      {"pcs.open", PCSOpenOp::getOperationName()},
      {"pcs.check", PCSCheckOp::getOperationName()},
      {"random.index", RandomIndexOp::getOperationName()},
      {"transcript.draw_index", TranscriptDrawIndexOp::getOperationName()},
      {"random.draw", RandomDrawOp::getOperationName()},
      {"pcs.equal", PCSEqualOp::getOperationName()},
      {"curve.generator", CurveGeneratorOp::getOperationName()},
      {"curve.add", CurveAddOp::getOperationName()},
      {"curve.scale", CurveScaleOp::getOperationName()},
      {"curve.equal", CurveEqualOp::getOperationName()},
      {"curve.empty", CurveEmptyOp::getOperationName()},
      {"curve.append", CurveAppendOp::getOperationName()},
      {"curve.at", CurveAtOp::getOperationName()},
      {"curve.get", CurveGetOp::getOperationName()},
      {"curve.length", CurveLengthOp::getOperationName()},
      {"curve.commit", CurveCommitOp::getOperationName()},
      {"curve.response", CurveResponseOp::getOperationName()},
      {"transcript.challenge", TranscriptChallengeOp::getOperationName()},
  };
  for (const auto &[key, name] : operations)
    if (key == contract)
      return name;
  return {};
}

namespace {
// Decoding must not initialize a caller's context. Missing dialects are an
// ordinary translation failure, not a fatal call into an unregistered type.
template <typename T, typename... Args>
Type loadedType(MLIRContext *ctx, Args &&...args) {
  if (!ctx->getLoadedDialect(T::dialectName))
    return {};
  return T::get(ctx, std::forward<Args>(args)...);
}
} // namespace
Type decodeBoundType(MLIRContext *ctx, const BoundType &t) {
  Type result;
  if (t.kind == "variant")
    result = loadedType<VariantType>(ctx, "variant:" + t.identity);
  else if (t.kind == "bool")
    result = IntegerType::get(ctx, 1);
  else if (t.kind == "index")
    result = IntegerType::get(ctx, 64, IntegerType::Unsigned);
  else if (t.kind == "indices")
    result =
        RankedTensorType::get({ShapedType::kDynamic},
                              IntegerType::get(ctx, 64, IntegerType::Unsigned));
  else if (t.kind == "field")
    result = loadedType<FieldType>(ctx, t.identity);
  else if (t.kind == "matrix")
    result = loadedType<MatrixType>(ctx, t.identity);
  else if (t.kind == "table")
    result = loadedType<MultilinearType>(ctx, t.identity);
  else if (t.kind == "point")
    result = loadedType<PointType>(ctx, t.identity);
  else if (t.kind == "round")
    result = loadedType<QuadraticType>(ctx, t.identity);
  else if (t.kind == "group")
    result = loadedType<GroupType>(ctx, t.identity);
  else if (t.kind == "vector" || t.kind == "groups") {
    Type element = t.kind == "vector" ? loadedType<FieldType>(ctx, t.identity)
                                      : loadedType<GroupType>(ctx, t.identity);
    if (!element)
      return {};
    result = RankedTensorType::get({ShapedType::kDynamic}, element);
  } else if (t.kind == "polynomial")
    result = loadedType<UnivariateType>(ctx, t.identity);
  else if (t.kind == "resource_unit" || t.kind == "rng" || t.kind == "nonce" ||
           t.kind == "transcript")
    result = loadedType<CapabilityType>(ctx, t.kind + ":" + t.identity);
  else if (installedDomains().hasFact("VectorCommitment", {t.identity}))
    result = loadedType<OracleObjectType>(ctx, t.identity, t.kind);
  else
    result = loadedType<ObjectType>(ctx, t.identity, t.kind);
  if (!result)
    return {};
  return t.representation.empty()
             ? result
             : loadedType<DataType>(ctx, result, t.representation);
}

Expected<BoundType> encodeBoundType(Type type, bool physical) {
  std::string rep;
  if (auto data = dyn_cast<DataType>(type)) {
    if (!physical)
      return error("binding-physical-type-at-logical-stage");
    rep = data.getRepresentation().str();
    type = data.getLogical();
  } else if (physical)
    return error("binding-logical-type-at-physical-stage");
  BoundType result;
  if (auto t = dyn_cast<VariantType>(type))
    result = {"variant", t.getDescriptor().drop_front(8).str(), {}};
  else if (type.isSignlessInteger(1))
    result.kind = "bool";
  else if (type.isUnsignedInteger(64))
    result.kind = "index";
  else if (auto t = dyn_cast<FieldType>(type))
    result = {"field", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<MatrixType>(type))
    result = {"matrix", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<MultilinearType>(type))
    result = {"table", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<PointType>(type))
    result = {"point", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<QuadraticType>(type))
    result = {"round", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<GroupType>(type))
    result = {"group", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<UnivariateType>(type))
    result = {"polynomial", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<RankedTensorType>(type)) {
    if (t.getRank() != 1 || !t.isDynamicDim(0) || t.getEncoding())
      return error("binding-type");
    if (t.getElementType().isUnsignedInteger(64))
      result.kind = "indices";
    else if (auto f = dyn_cast<FieldType>(t.getElementType()))
      result = {"vector", f.getDomain().str(), {}};
    else if (auto g = dyn_cast<GroupType>(t.getElementType()))
      result = {"groups", g.getDomain().str(), {}};
    else
      return error("binding-type");
  } else if (auto t = dyn_cast<OracleObjectType>(type))
    result = {t.getKind().str(), t.getScheme().str(), {}};
  else if (auto t = dyn_cast<ObjectType>(type))
    result = {t.getKind().str(), t.getScheme().str(), {}};
  else if (auto t = dyn_cast<CapabilityType>(type)) {
    auto [kind, identity] = t.getKind().split(':');
    result = {kind.str(), identity.str(), {}};
  } else
    return error("binding-type");
  result.representation = std::move(rep);
  auto checked = parseBoundType(result.spelling(), physical);
  if (!checked)
    return checked.takeError();
  if (decodeBoundType(type.getContext(), *checked) !=
      (physical ? Type(DataType::get(type.getContext(), type,
                                     checked->representation))
                : type))
    return error("binding-type-identity");
  return checked;
}

Expected<source::OperationBinding> readBinding(Operation *op) {
  auto declaration = dyn_cast_or_null<OperationBindingOp>(op);
  if (!declaration || !isa_and_nonnull<ProtocolModuleOp>(op->getParentOp()))
    return error("binding-declaration-context");
  auto name = declaration.getSymNameAttr();
  auto contract = declaration.getContractAttr();
  auto implementation = declaration.getImplementationAttr();
  auto arguments = declaration.getArgumentsAttr();
  if (!name || !contract || !implementation || !arguments)
    return error("binding-declaration");
  source::Names values;
  for (auto arg : arguments) {
    auto value = dyn_cast<StringAttr>(arg);
    if (!value)
      return error("binding-static-identity");
    values.push_back(value.getValue().str());
  }
  auto root = cast<ProtocolModuleOp>(op->getParentOp());
  bool physical = root.getStageAttr() && root.getStage() == "physical";
  source::OperationBinding binding{{},
                                   name.getValue().str(),
                                   {contract.getValue().str(),
                                    std::move(values),
                                    implementation.getValue().str()}};
  if (auto e =
          checkBindingDeclaration(binding.name, binding.application, physical))
    return e;
  return binding;
}

Expected<source::OperationBinding> operationBinding(Operation *user) {
  auto root = user->getParentOfType<ProtocolModuleOp>();
  auto reference = user->getAttrOfType<FlatSymbolRefAttr>("binding");
  if (!root || !reference)
    return error("binding-reference");
  return readBinding(SymbolTable::lookupSymbolIn(root, reference));
}

LogicalResult verifyBoundOperation(Operation *op, bool physical) {
  auto selected = operationBinding(op);
  if (!selected)
    return diagnostics::emit(op->emitOpError(), selected.takeError());
  auto signature = resolveBinding(selected->application, physical);
  if (!signature)
    return diagnostics::emit(op->emitOpError(), signature.takeError());
  if (physical) {
    auto key = op->getAttrOfType<StringAttr>("kernel");
    if (!isa<ExecuteKernelOp>(op) || !key ||
        key.getValue() != selected->application.implementation)
      return diagnostics::emit(op->emitOpError(), "binding-implementation");
  } else if (op->getName().getStringRef() !=
             boundOperationName(selected->application.contract))
    return diagnostics::emit(op->emitOpError(), "binding-operation");
  auto types = [&](TypeRange actual, ArrayRef<BoundType> expected) {
    if (actual.size() != expected.size())
      return false;
    for (auto [type, target] : zip(actual, expected)) {
      auto value = encodeBoundType(type, physical);
      if (!value) {
        consumeError(value.takeError());
        return false;
      }
      if (!(*value == target))
        return false;
    }
    return true;
  };
  if (!types(op->getOperandTypes(), signature->inputs) ||
      !types(op->getResultTypes(), signature->outputs))
    return diagnostics::emit(op->emitOpError(), "binding-operation-signature");
  auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
  if (!parameters)
    return diagnostics::emit(op->emitOpError(), "binding-parameters");
  source::Names values;
  for (auto p : parameters) {
    auto value = dyn_cast<StringAttr>(p);
    if (!value)
      return diagnostics::emit(op->emitOpError(), "binding-parameters");
    values.push_back(value.getValue().str());
  }
  if (auto e =
          checkParameters(selected->application.contract, values,
                          (selected->application.contract == "field.constant" ||
                           selected->application.contract == "vector.constant")
                              ? signature->outputs[0].identity
                              : ""))
    return diagnostics::emit(op->emitOpError(), std::move(e));
  return success();
}
} // namespace zkc::protocol

namespace zkc {
LogicalResult OperationBindingOp::verify() {
  auto binding = protocol::readBinding(*this);
  if (!binding)
    return diagnostics::emit(emitOpError(), binding.takeError());
  return success();
}
} // namespace zkc
