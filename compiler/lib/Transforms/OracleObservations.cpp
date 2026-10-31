#include "OracleSchedule.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/Interactions.h"
#include "zkc/Analysis/ProtocolConstants.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseSet.h"
#include <optional>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
namespace pir = protocol_ir;
using Summary = OracleObservationSummary;
Summary uncertainStop() { return Summary().either(Summary::stop()); }
struct Analysis {
  StringRef observer;
  facts::Work &work;
  MathematicalFactAnalysis &mathematics;
  Error charge() {
    if (!work.charge())
      return error("oracle-observation-limit");
    return Error::success();
  }
  Expected<std::optional<uint64_t>> constant(Value value) {
    auto result = observeProtocolConstant(value, observer, mathematics, work);
    if (result.status == facts::Status::Capacity)
      return error("oracle-observation-limit");
    return result.value;
  }
  bool includes(ArrayAttr roles) {
    return is_contained(roles, StringAttr::get(roles.getContext(), observer));
  }
  Expected<Summary> sequence(const InteractionDeclaration &view,
                             const InteractionSequence &body, unsigned depth) {
    if (!depth) {
      work.exhaust();
      return error("oracle-observation-limit");
    }
    Summary result;
    for (unsigned index : body.getActions()) {
      if (auto e = charge())
        return std::move(e);
      const auto &action = view.getActions()[index];
      auto &op = *action.getOperation();
      Summary step;
      if (isa<pir::ApplyOp>(op))
        return error("oracle-observation-preparation");
      if (auto repeat = dyn_cast<pir::RepeatOp>(op)) {
        if (includes(repeat.getRoles())) {
          auto nested = sequence(
              view, view.getSequence(*action.getRepeatBody()), depth - 1);
          if (!nested)
            return nested.takeError();
          auto count = constant(repeat.getInputs().front());
          if (!count)
            return count.takeError();
          uint64_t maximum = repeat.getMaximum();
          step = *count ? (**count > maximum ? Summary::stop()
                                             : nested->repeat(**count))
                        : nested->repeatAtMost(maximum).either(Summary::stop());
        }
      } else if (auto query = dyn_cast<pir::OracleQueryOp>(op)) {
        if (query.getOwner() == observer)
          step = Summary::query().then(uncertainStop());
      } else if (auto query = dyn_cast<pir::QueryOp>(op)) {
        if (query.getOwner() == observer)
          step = Summary::draw().then(uncertainStop());
      } else if (auto guard = dyn_cast<pir::GuardOp>(op)) {
        if (guard.getOwner() == observer) {
          auto value = constant(guard.getCondition());
          if (!value)
            return value.takeError();
          step = *value ? (**value ? Summary() : Summary::stop())
                        : uncertainStop();
        }
      } else if (auto finish = dyn_cast<pir::FinishIfOp>(op)) {
        if (finish.getOwner() == observer) {
          auto value = constant(finish.getCondition());
          if (!value)
            return value.takeError();
          step = *value ? (**value ? Summary::stop() : Summary())
                        : uncertainStop();
        }
      } else if (auto call = dyn_cast<pir::LocalCallOp>(op)) {
        // Local execution has no protocol draws. Until its explicit outcome
        // is known, neither successful continuation nor stopping is discarded.
        if (call.getRole() == observer)
          step = uncertainStop();
      } else if (isa<pir::OracleSendOp, pir::OracleInputOp,
                     pir::OracleVirtualOp, pir::OracleSequenceAppendOp,
                     pir::OracleSequenceAtOp, pir::ExchangeOp>(op)) {
        step = uncertainStop();
      } else if (!isa<pir::OracleContentsOp, pir::OracleComponentsOp,
                      pir::OracleShapeOp, pir::OracleForgetShapeOp,
                      pir::OracleSequenceEmptyOp, pir::OracleSequenceLengthOp,
                      pir::RestrictRolesOp, pir::AssembleRolesOp,
                      pir::StatementOp, pir::ConstructionStartOp,
                      pir::MathematicalReturnOp, pir::ProtocolYieldOp>(op) &&
                 !mathematical::isTotal(&op))
        return error("oracle-observation-operation");
      result = result.then(step);
    }
    return result;
  }
};
Expected<const InteractionDeclaration *>
structure(InteractionAnalysis &analysis, Operation *program,
          facts::Work &work) {
  // Extraction and observer transfers share the existing cumulative allowance.
  // An incomplete view must never supply a neutral (safe-ordering) summary.
  auto result = analysis.get(program, work);
  if (result)
    return *result;
  return handleErrors(result.takeError(), [](const Refusal &refusal) -> Error {
    if (refusal.code == "interaction-analysis-capacity")
      return error("oracle-observation-limit");
    if (refusal.code == "interaction-analysis-owner")
      return error("oracle-observation-source");
    return error("oracle-observation-operation");
  });
}
Expected<pir::ProtocolModuleOp> admitted(ModuleOp prepared) {
  if (!prepared || failed(zkc::admitStage(prepared)) ||
      !hasSingleElement(prepared.getBody()->getOperations()))
    return error("oracle-observation-source");
  auto module = dyn_cast<pir::ProtocolModuleOp>(prepared.getBody()->front());
  if (!module || module.getProfile() != pir::Profile::Protocol)
    return error("oracle-observation-source");
  return module;
}
} // namespace
Expected<OracleObservationSummary>
analyzeOracleObservations(ModuleOp prepared, StringRef entry,
                          StringRef observer) {
  auto module = admitted(prepared);
  if (!module)
    return module.takeError();
  SymbolTable symbols(*module);
  auto program = symbols.lookup<pir::MathematicalOp>(entry);
  if (!program ||
      !is_contained(program.getRoles(),
                    StringAttr::get(prepared.getContext(), observer)))
    return error("oracle-observation-interface");
  uint64_t remaining = 100000;
  facts::Work work(remaining);
  InteractionAnalysis interactions(prepared);
  MathematicalFactAnalysis mathematics(prepared);
  auto view = structure(interactions, program, work);
  if (!view)
    return view.takeError();
  return Analysis{observer, work, mathematics}.sequence(**view,
                                                        (*view)->getBody(), 64);
}
Error checkOracleFinalDrawSchedule(ModuleOp prepared) {
  auto module = admitted(prepared);
  if (!module)
    return module.takeError();
  uint64_t remaining = 100000;
  facts::Work work(remaining);
  InteractionAnalysis interactions(prepared);
  MathematicalFactAnalysis mathematics(prepared);
  for (auto program : module->getBody().front().getOps<pir::MathematicalOp>()) {
    // Virtual declarations cannot draw. Their nested queries inherit the outer
    // observation; uncalled virtual declarations create no reached event.
    llvm::DenseSet<StringAttr> observers;
    auto view = structure(interactions, program, work);
    if (!view)
      return view.takeError();
    for (const auto &action : (*view)->getActions()) {
      if (!work.charge())
        return error("oracle-observation-limit");
      auto *op = action.getOperation();
      if (isa<pir::ApplyOp>(op))
        return error("oracle-observation-preparation");
      if (auto query = dyn_cast<pir::OracleQueryOp>(op))
        observers.insert(query.getOwnerAttr());
    }
    // Declaration order makes refusal precedence independent of hash order.
    for (Attribute role : program.getRoles()) {
      auto observer = cast<StringAttr>(role);
      if (!observers.contains(observer))
        continue;
      auto summary = Analysis{observer.getValue(), work, mathematics}.sequence(
          **view, (*view)->getBody(), 64);
      if (!summary)
        return summary.takeError();
      if (summary->queryBeforeDraw())
        return error("oracle-realization-query-order");
    }
  }
  return Error::success();
}
} // namespace zkc::protocol
