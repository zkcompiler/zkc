#include "OracleSchedule.h"
#include "mlir/IR/Matchers.h"
#include "mlir/IR/Verifier.h"
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
  unsigned &remaining;
  Error charge() {
    if (!remaining)
      return error("oracle-observation-limit");
    --remaining;
    return Error::success();
  }
  Expected<std::optional<uint64_t>> constant(Value value) {
    while (value) {
      if (auto e = charge())
        return std::move(e);
      if (auto view = value.getDefiningOp<pir::RestrictRolesOp>()) {
        value = view.getInput();
        continue;
      }
      if (auto argument = dyn_cast<BlockArgument>(value)) {
        auto repeat =
            dyn_cast<pir::RepeatOp>(argument.getOwner()->getParentOp());
        // Captures are invariant. Carried values and the induction index are
        // not constants just because their zero-trip initializer is one.
        if (repeat && argument.getArgNumber() > uint64_t(repeat.getCarried())) {
          value = repeat.getInputs()[argument.getArgNumber()];
          continue;
        }
      }
      if (auto index = value.getDefiningOp<data::IndexOp>()) {
        uint64_t number;
        if (!index.getValue().getAsInteger(10, number))
          return std::optional<uint64_t>(number);
      }
      Attribute attr;
      if (matchPattern(value, m_Constant(&attr)))
        if (auto integer = dyn_cast<IntegerAttr>(attr))
          if (integer.getValue().getBitWidth() <= 64)
            return std::optional<uint64_t>(integer.getValue().getZExtValue());
      return std::optional<uint64_t>();
    }
    return std::optional<uint64_t>();
  }
  bool includes(ArrayAttr roles) {
    return is_contained(roles, StringAttr::get(roles.getContext(), observer));
  }
  Expected<Summary> block(Block &body, unsigned depth) {
    if (!depth)
      return error("oracle-observation-limit");
    Summary result;
    for (auto &op : body) {
      if (auto e = charge())
        return std::move(e);
      Summary step;
      if (isa<pir::ApplyOp>(op))
        return error("oracle-observation-preparation");
      if (auto repeat = dyn_cast<pir::RepeatOp>(op)) {
        if (includes(repeat.getRoles())) {
          auto nested = block(repeat.getBody().front(), depth - 1);
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
Expected<pir::ProtocolModuleOp> admitted(ModuleOp prepared) {
  if (!prepared || failed(verify(prepared)) ||
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
  unsigned remaining = 100000;
  return Analysis{observer, remaining}.block(program.getBody().front(), 64);
}
Error checkOracleFinalDrawSchedule(ModuleOp prepared) {
  auto module = admitted(prepared);
  if (!module)
    return module.takeError();
  unsigned remaining = 100000;
  for (auto program : module->getBody().front().getOps<pir::MathematicalOp>()) {
    // Virtual declarations cannot draw. Their nested queries inherit the outer
    // observation; uncalled virtual declarations create no reached event.
    llvm::DenseSet<StringAttr> observers;
    Error failure = Error::success();
    program.walk([&](Operation *op) -> WalkResult {
      if (!remaining)
        failure = error("oracle-observation-limit");
      else if (isa<pir::ApplyOp>(op))
        failure = error("oracle-observation-preparation");
      if (failure)
        return WalkResult::interrupt();
      --remaining;
      if (auto query = dyn_cast<pir::OracleQueryOp>(op))
        observers.insert(query.getOwnerAttr());
      return WalkResult::advance();
    });
    if (failure)
      return failure;
    // Declaration order makes refusal precedence independent of hash order.
    for (Attribute role : program.getRoles()) {
      auto observer = cast<StringAttr>(role);
      if (!observers.contains(observer))
        continue;
      auto summary = Analysis{observer.getValue(), remaining}.block(
          program.getBody().front(), 64);
      if (!summary)
        return summary.takeError();
      if (summary->queryBeforeDraw())
        return error("oracle-realization-query-order");
    }
  }
  return Error::success();
}
} // namespace zkc::protocol
