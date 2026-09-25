#include "zkc/Protocol/Kernels.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Protocol/Bindings.h"
#include "zkc/Protocol/Module.h"
#include "zkc/Protocol/TypeProperties.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;

namespace zkc {
namespace {
LogicalResult verifyKernel(Operation *op, bool physical) {
  auto module = op->getParentOfType<ProtocolModuleOp>();
  auto *owner = op->getParentOp();
  while (owner && isa<LocalIfOp, LocalForOp, LocalMatchOp>(owner))
    owner = owner->getParentOp();
  if (!module || !isa_and_nonnull<func::FuncOp>(owner))
    return op->emitOpError(
        "interactive-kernel-context: expected a local function in pir.module");
  auto stage = module.getStageAttr();
  if (!stage)
    return op->emitOpError("interactive-kernel-context: missing stage");
  if (physical ? stage.getValue() != "physical"
               : stage.getValue() != "common" && stage.getValue() != "logical")
    return op->emitOpError("interactive-kernel-stage");

  return protocol::verifyBoundOperation(op, physical);
}
} // namespace

#define VERIFY_KERNEL(OP)                                                      \
  LogicalResult OP::verify() { return verifyKernel(*this, false); }
VERIFY_KERNEL(ResourceUnitCreateOp)
VERIFY_KERNEL(ResourceUnitPassOp)
VERIFY_KERNEL(ResourceUnitConsumeOp)
VERIFY_KERNEL(ExternalMoneroInitOp)
VERIFY_KERNEL(ExternalMoneroHashOp)
VERIFY_KERNEL(ExternalMoneroUpdateOp)
VERIFY_KERNEL(ExternalOpenvmInitOp)
VERIFY_KERNEL(ExternalOpenvmObserveOp)
VERIFY_KERNEL(ExternalOpenvmSampleOp)
VERIFY_KERNEL(ExternalOpenvmSampleExtOp)
VERIFY_KERNEL(ExternalOpenvmSampleBitsOp)
VERIFY_KERNEL(ExternalOpenvmCheckWitnessOp)
VERIFY_KERNEL(IndexConstantOp)
VERIFY_KERNEL(IndexAddOp)
VERIFY_KERNEL(IndexSubOp)
VERIFY_KERNEL(IndexMulOp)
VERIFY_KERNEL(IndexDivOp)
VERIFY_KERNEL(IndexModOp)
VERIFY_KERNEL(IndexEqualOp)
VERIFY_KERNEL(IndexLessOp)
VERIFY_KERNEL(IndicesEmptyOp)
VERIFY_KERNEL(IndicesAppendOp)
VERIFY_KERNEL(IndicesAtOp)
VERIFY_KERNEL(IndicesLengthOp)
VERIFY_KERNEL(VectorGetOp)
VERIFY_KERNEL(VectorSliceOp)
VERIFY_KERNEL(VectorLengthOp)
VERIFY_KERNEL(VectorRotateOp)
VERIFY_KERNEL(VectorInterleaveOp)
VERIFY_KERNEL(VectorPrefixProductOp)
VERIFY_KERNEL(VectorPrefixSumOp)
VERIFY_KERNEL(VectorInverseOp)
VERIFY_KERNEL(VectorEmbedOp)
VERIFY_KERNEL(VectorFillOp)
VERIFY_KERNEL(VectorGeometricOp)
VERIFY_KERNEL(FieldFromIndexOp)
VERIFY_KERNEL(CoefficientCountOp)
VERIFY_KERNEL(CosetEvaluateOp)
VERIFY_KERNEL(CosetInterpolateOp)
VERIFY_KERNEL(DomainPointOp)
VERIFY_KERNEL(DomainRootOp)
VERIFY_KERNEL(DomainPointsOp)
VERIFY_KERNEL(EvenOddFoldOp)
VERIFY_KERNEL(DivideOpeningOp)
VERIFY_KERNEL(OpeningQuotientOp)
VERIFY_KERNEL(FieldSubtractOp)
VERIFY_KERNEL(FieldNegateOp)
VERIFY_KERNEL(FieldInverseOp)
VERIFY_KERNEL(FieldEmbedOp)
VERIFY_KERNEL(MatrixMulVectorOp)
VERIFY_KERNEL(MatrixTransposeMulVectorOp)
VERIFY_KERNEL(MatrixBilinearOp)
VERIFY_KERNEL(MatrixShapeCheckOp)
VERIFY_KERNEL(MatrixIdentityCheckOp)
VERIFY_KERNEL(VectorConstantOp)
VERIFY_KERNEL(VectorScatterSumOp)
VERIFY_KERNEL(VectorEmptyOp)
VERIFY_KERNEL(VectorAppendOp)
VERIFY_KERNEL(VectorSplatOp)
VERIFY_KERNEL(VectorPowersOp)
VERIFY_KERNEL(VectorAddOp)
VERIFY_KERNEL(VectorSubOp)
VERIFY_KERNEL(VectorMulOp)
VERIFY_KERNEL(VectorDotOp)
VERIFY_KERNEL(VectorConcatOp)
VERIFY_KERNEL(VectorKroneckerOp)
VERIFY_KERNEL(VectorMatvecOp)
VERIFY_KERNEL(VectorScaleOp)
VERIFY_KERNEL(VectorSumOp)
VERIFY_KERNEL(VectorSplitOp)
VERIFY_KERNEL(VectorAtOp)
VERIFY_KERNEL(VectorLengthCheckOp)
VERIFY_KERNEL(VectorGatherOp)
VERIFY_KERNEL(PointToVectorOp)
VERIFY_KERNEL(TableToVectorOp)
VERIFY_KERNEL(PointFromVectorOp)
VERIFY_KERNEL(TableFromVectorOp)
VERIFY_KERNEL(EqualityWeightsOp)
VERIFY_KERNEL(FromCoefficientsOp)
VERIFY_KERNEL(CoefficientsOp)
VERIFY_KERNEL(DegreeCheckOp)
VERIFY_KERNEL(UnivariateEvaluateOp)
VERIFY_KERNEL(UnivariateBoundaryOp)
VERIFY_KERNEL(RandomVectorOp)
VERIFY_KERNEL(CurveNegateOp)
VERIFY_KERNEL(CurveNonidentityOp)
VERIFY_KERNEL(CurveMSMOp)
VERIFY_KERNEL(CurveScaleEachOp)
VERIFY_KERNEL(CurveVectorAddOp)
VERIFY_KERNEL(CurveVectorScaleOp)
VERIFY_KERNEL(CurveSplitOp)
VERIFY_KERNEL(CurveConcatOp)
VERIFY_KERNEL(PairingCheckOp)
VERIFY_KERNEL(FieldConstantOp)
VERIFY_KERNEL(FieldSumOp)
VERIFY_KERNEL(FieldProductOp)
VERIFY_KERNEL(FieldCompareOp)
VERIFY_KERNEL(BooleanAndOp)
VERIFY_KERNEL(BooleanNotOp)
VERIFY_KERNEL(BooleanOrOp)
VERIFY_KERNEL(RequireOp)
VERIFY_KERNEL(ProductSumOp)
VERIFY_KERNEL(ProductRoundOp)
VERIFY_KERNEL(BoundaryOp)
VERIFY_KERNEL(RoundEvaluateOp)
VERIFY_KERNEL(FoldOp)
VERIFY_KERNEL(MLEEvaluateOp)
VERIFY_KERNEL(EmptyPointOp)
VERIFY_KERNEL(AppendPointOp)
VERIFY_KERNEL(OracleCommitOp)
VERIFY_KERNEL(OracleOpenOp)
VERIFY_KERNEL(OracleCheckOp)
VERIFY_KERNEL(CommitmentsEmptyOp)
VERIFY_KERNEL(CommitmentsAppendOp)
VERIFY_KERNEL(CommitmentsAtOp)
VERIFY_KERNEL(CommitmentsLengthOp)
VERIFY_KERNEL(OpeningStatesEmptyOp)
VERIFY_KERNEL(OpeningStatesAppendOp)
VERIFY_KERNEL(OpeningStatesAtOp)
VERIFY_KERNEL(OpeningStatesLengthOp)
VERIFY_KERNEL(PCSCommitOp)
VERIFY_KERNEL(PCSOpenOp)
VERIFY_KERNEL(PCSCheckOp)
VERIFY_KERNEL(RandomIndexOp)
VERIFY_KERNEL(TranscriptDrawIndexOp)
VERIFY_KERNEL(RandomDrawOp)
VERIFY_KERNEL(PCSEqualOp)
VERIFY_KERNEL(TranscriptObserveOp)
VERIFY_KERNEL(TranscriptChallengeOp)
VERIFY_KERNEL(CurveGeneratorOp)
VERIFY_KERNEL(CurveAddOp)
VERIFY_KERNEL(CurveScaleOp)
VERIFY_KERNEL(CurveEqualOp)
VERIFY_KERNEL(CurveEmptyOp)
VERIFY_KERNEL(CurveAppendOp)
VERIFY_KERNEL(CurveAtOp)
VERIFY_KERNEL(CurveGetOp)
VERIFY_KERNEL(CurveLengthOp)
VERIFY_KERNEL(CurveCommitOp)
VERIFY_KERNEL(CurveResponseOp)
#undef VERIFY_KERNEL
LogicalResult ReleaseOp::verify() {
  auto root = (*this)->getParentOfType<ProtocolModuleOp>();
  auto *owner = (*this)->getParentOp();
  while (owner && isa<LocalIfOp, LocalForOp, LocalMatchOp>(owner))
    owner = owner->getParentOp();
  auto function = dyn_cast_or_null<func::FuncOp>(owner);
  if (!root || root.getStage() != "physical" || !function ||
      !llvm::hasSingleElement(function.getBody()))
    return emitOpError("interactive-release-context");
  if (getValues().empty())
    return emitOpError("interactive-release-empty");
  llvm::DenseSet<Value> seen;
  for (auto value : getValues()) {
    if (!seen.insert(value).second)
      return emitOpError("interactive-release-unavailable");
    auto type = protocol::encodeBoundType(value.getType(), true);
    if (!type)
      return emitOpError() << toString(type.takeError());
    bool canDiscard = protocol::discardable(type->spelling());
    if (!canDiscard)
      return emitOpError("interactive-release-resource");
    for (auto &use : value.getUses()) {
      auto *owner = use.getOwner();
      if (owner == getOperation())
        continue;
      if (owner->getBlock() != (*this)->getBlock() ||
          !owner->isBeforeInBlock(getOperation()))
        return emitOpError("interactive-release-live");
    }
  }
  return success();
}
LogicalResult ExecuteKernelOp::verify() { return verifyKernel(*this, true); }
} // namespace zkc
