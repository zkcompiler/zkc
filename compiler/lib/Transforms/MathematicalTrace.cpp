#include "zkc/Transforms/MathematicalTrace.h"
#include "llvm/Support/ErrorHandling.h"

namespace zkc::mathematical {
const char *decisionName(OptimizationStatus value) {
  switch (value) {
  case OptimizationStatus::Succeeded:
    return "succeeded";
  case OptimizationStatus::Unsupported:
    return "unsupported";
  case OptimizationStatus::MissingEvidence:
    return "missing-evidence";
  case OptimizationStatus::Capacity:
    return "capacity";
  case OptimizationStatus::PolicyDisabled:
    return "policy-disabled";
  case OptimizationStatus::ReplacementRestricted:
    return "replacement-restricted";
  case OptimizationStatus::MissingRecipe:
    return "missing-recipe";
  }
  llvm_unreachable("unknown mathematical decision");
}
const char *decisionName(OptimizationReason value) {
  switch (value) {
  case OptimizationReason::None:
    return "none";
  case OptimizationReason::Structure:
    return "structure";
  case OptimizationReason::Equation:
    return "equation";
  case OptimizationReason::EqualExtent:
    return "equal-extent";
  case OptimizationReason::StrictBound:
    return "strict-bound";
  case OptimizationReason::Depth:
    return "depth";
  case OptimizationReason::Cycle:
    return "cycle";
  case OptimizationReason::Replacement:
    return "replacement";
  case OptimizationReason::Recipe:
    return "recipe";
  case OptimizationReason::Policy:
    return "policy";
  case OptimizationReason::OrderedRetry:
    return "ordered-retry";
  case OptimizationReason::LaneFormula:
    return "lane-formula";
  case OptimizationReason::Work:
    return "work";
  case OptimizationReason::ExpansionSize:
    return "expansion-size";
  case OptimizationReason::CallEligibility:
    return "call-eligibility";
  case OptimizationReason::ImplementationRestriction:
    return "implementation-restriction";
  }
  llvm_unreachable("unknown mathematical decision");
}
const char *decisionName(WorkOwner value) {
  switch (value) {
  case WorkOwner::Structural:
    return "structural";
  case WorkOwner::FiniteCallbackStructural:
    return "finite-callback-structural";
  case WorkOwner::Equations:
    return "equations";
  case WorkOwner::Evidence:
    return "evidence";
  case WorkOwner::Lanes:
    return "lanes";
  case WorkOwner::OptionalComparison:
    return "optional-comparison";
  case WorkOwner::RequiredFiniteReader:
    return "required-finite-reader";
  case WorkOwner::HelperOperations:
    return "helper-operations";
  case WorkOwner::HelperSlots:
    return "helper-slots";
  case WorkOwner::Polynomial:
    return "polynomial";
  case WorkOwner::FiniteExpressions:
    return "finite-expressions";
  case WorkOwner::AlgorithmExpansion:
    return "algorithm-expansion";
  case WorkOwner::AlgorithmOriginBytes:
    return "algorithm-origin-bytes";
  case WorkOwner::AlgorithmChecking:
    return "algorithm-checking";
  }
  llvm_unreachable("unknown mathematical decision");
}
const char *decisionName(DecisionFamily value) {
  switch (value) {
  case DecisionFamily::Finite:
    return "finite";
  case DecisionFamily::NestedContraction:
    return "nested-contraction";
  case DecisionFamily::Lanes:
    return "lanes";
  case DecisionFamily::Map:
    return "map";
  case DecisionFamily::MapProduct:
    return "map-product";
  case DecisionFamily::VectorReduction:
    return "vector-reduction";
  }
  llvm_unreachable("unknown mathematical decision");
}
const char *decisionName(RealizationChoice value) {
  switch (value) {
  case RealizationChoice::Ordered:
    return "ordered";
  case RealizationChoice::Bilinear:
    return "bilinear";
  case RealizationChoice::Reduction:
    return "reduction";
  case RealizationChoice::Elementwise:
    return "elementwise";
  case RealizationChoice::NestedContraction:
    return "nested-contraction";
  case RealizationChoice::MapProduct:
    return "map-product";
  case RealizationChoice::MapSum:
    return "map-sum";
  }
  llvm_unreachable("unknown mathematical decision");
}
const char *decisionName(PublicationBoundary value) {
  switch (value) {
  case PublicationBoundary::IncorporatedIntoParent:
    return "incorporated-into-parent";
  case PublicationBoundary::ReturnedCandidate:
    return "returned-candidate";
  case PublicationBoundary::PublishedToCaller:
    return "published-to-caller";
  }
  llvm_unreachable("unknown mathematical decision");
}
const char *decisionName(CompletionKind value) {
  switch (value) {
  case CompletionKind::Completed:
    return "completed";
  case CompletionKind::Unchanged:
    return "unchanged";
  case CompletionKind::Refused:
    return "refused";
  }
  llvm_unreachable("unknown mathematical decision");
}

} // namespace zkc::mathematical
