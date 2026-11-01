#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Runtime/Parameters.h"
#include "zkc/Support/Json.h"

using namespace mlir;
using namespace llvm;
namespace zkc::runtime {
LogicalResult
NumericalPlanAttr::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                          algebra::RingExpressionAttr expression,
                          unsigned lanes, unsigned slots,
                          DenseI32ArrayAttr locations) {
  if (!expression || !locations || !lanes ||
      lanes > protocol::NumericalLimits::lanes || !slots ||
      slots > expression.getNodes().size() ||
      size_t(locations.size()) != expression.getNodes().size() ||
      llvm::any_of(locations.asArrayRef(), [&](int32_t slot) {
        return slot < 0 || unsigned(slot) >= slots;
      }))
    return diagnostics::emit(emit(), "numerical-plan-shape");
  auto size = algebra::ringExpressionByteSize(expression);
  if (!size) {
    consumeError(size.takeError());
    return diagnostics::emit(emit(), "numerical-body-signature");
  }
  if (*size > protocol::NumericalLimits::bodyBytes)
    return diagnostics::emit(emit(), "numerical-plan-bytes");
  return success();
}
Expected<NumericalPlanAttr>
importNumericalPlan(MLIRContext *context, const protocol::NumericalPlan &plan) {
  auto expression = algebra::importRingExpression(context, plan.expression);
  if (!expression)
    return expression.takeError();
  SmallVector<int32_t> locations(plan.locations.begin(), plan.locations.end());
  auto result = NumericalPlanAttr::getChecked(
      [&] { return emitError(UnknownLoc::get(context)); }, context, *expression,
      plan.lanes, plan.slots, DenseI32ArrayAttr::get(context, locations));
  if (!result)
    return error("numerical-plan-shape");
  return result;
}
Expected<protocol::NumericalPlan> exportNumericalPlan(NumericalPlanAttr plan) {
  if (!plan ||
      failed(NumericalPlanAttr::verify(
          [&] { return emitError(UnknownLoc::get(plan.getContext())); },
          plan.getExpression(), plan.getLanes(), plan.getSlots(),
          plan.getLocations())))
    return error("numerical-plan-shape");
  auto expression = algebra::exportRingExpression(plan.getExpression());
  if (!expression)
    return expression.takeError();
  auto locations = plan.getLocations().asArrayRef();
  return protocol::NumericalPlan{std::move(*expression),
                                 plan.getLanes(),
                                 plan.getSlots(),
                                 {locations.begin(), locations.end()}};
}
} // namespace zkc::runtime
