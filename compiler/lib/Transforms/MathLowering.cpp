#include "Computation/Support.h"
#include "HelperNormalization.h"
#include "MathematicalPassOptions.h"
#include "MathematicalSupport.h"
#include "RealizationTrace.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecDialect.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
class OutlineSymbols {
  llvm::StringSet<> names;
  unsigned next = 0;

public:
  explicit OutlineSymbols(protocol_ir::ProtocolModuleOp unit) {
    for (auto &op : unit.getBody().front())
      if (auto name = SymbolTable::getSymbolName(&op))
        names.insert(name.getValue());
  }
  std::string fresh() {
    std::string name;
    do {
      name = "_calculation_" + std::to_string(next++);
    } while (!names.insert(name).second);
    return name;
  }
};
class Outliner {
  protocol_ir::ProtocolModuleOp unit;
  OutlineSymbols &symbols;
  bool batching;
  OpBuilder builder;
  SmallVector<Attribute> calculations;
  struct Calculation {
    func::FuncOp function;
    std::optional<computation::CalculationGuard> guard;
  };
  SmallVector<Calculation> formed;
  uint64_t remaining = 1000000;

  LogicalResult participant(protocol_ir::ParticipantOp participant) {
    llvm::StringSet<> sites;
    participant.walk([&](Operation *op) {
      if (auto site = op->getAttrOfType<StringAttr>("site"))
        sites.insert(site.getValue());
    });
    unsigned nextSite = 0;
    return block(participant, participant.getBody().front(), sites, nextSite);
  }
  LogicalResult block(protocol_ir::ParticipantOp participant, Block &body,
                      llvm::StringSet<> &sites, unsigned &nextSite) {
    llvm::DenseMap<Operation *, unsigned> order;
    unsigned ordinal = 0;
    for (auto &op : body)
      order[&op] = ordinal++;
    SmallVector<Operation *> cuts;
    for (auto &op : body)
      if (!isTotal(&op))
        cuts.push_back(&op);
    IRMapping computed;
    llvm::DenseSet<Value> realized;
    auto updateOperands = [&](Operation *cut) {
      for (auto &operand : cut->getOpOperands())
        operand.set(computed.lookupOrDefault(operand.get()));
    };
    // Trace mathematical dependencies while keeping concrete values already
    // realized at an earlier action. Formal descriptors are reconstructed at
    // their consumers and never become participant ports.
    auto demand = [&](SmallVector<Value> pending,
                      llvm::DenseSet<Operation *> &needed,
                      SmallVector<Operation *> &operations) -> LogicalResult {
      while (!pending.empty()) {
        auto value = pending.pop_back_val();
        if (!remaining--)
          return diagnostics::emit(participant.emitError(),
                                   "computation-frontier-limit");
        bool formal = mathematical::isFormalType(value.getType());
        if (!formal && realized.contains(value)) {
          if (!computed.contains(value))
            return diagnostics::emit(
                participant.emitError(), "computation-frontier",
                "an earlier concrete coordinate was not exported");
          continue;
        }
        auto *definition = value.getDefiningOp();
        if (!definition || !isTotal(definition) ||
            !needed.insert(definition).second)
          continue;
        operations.push_back(definition);
        auto dependencies = operandDependencies(
            definition, cast<OpResult>(value).getResultNumber());
        if (failed(dependencies))
          return failure();
        for (auto index : *dependencies)
          pending.push_back(definition->getOperand(index));
      }
      return success();
    };
    llvm::DenseSet<Operation *> demanded;
    if (!batching) {
      SmallVector<Value> pending;
      for (auto *cut : cuts)
        append_range(pending, cut->getOperands());
      SmallVector<Operation *> unordered;
      if (failed(demand(std::move(pending), demanded, unordered)))
        return failure();
    }
    for (auto *cut : cuts) {
      if (auto loop = dyn_cast<protocol_ir::ProtocolLoopOp>(cut))
        if (failed(block(participant, loop.getBody().front(), sites, nextSite)))
          return failure();
      llvm::DenseSet<Operation *> needed;
      SmallVector<Operation *> operations;
      SmallVector<Value> pending;
      if (batching) {
        append_range(pending, cut->getOperands());
      } else {
        // Place needed concrete work before the first following action. A
        // formal-only definition has no runtime work to schedule; the demand
        // walk reconstructs it beside each concrete consumer instead.
        for (auto &op : body) {
          if (&op == cut)
            break;
          if (!remaining--)
            return diagnostics::emit(cut->emitError(),
                                     "computation-frontier-limit");
          if (demanded.contains(&op))
            for (auto value : op.getResults())
              if (!mathematical::isFormalType(value.getType()) &&
                  !realized.contains(value))
                pending.push_back(value);
        }
      }
      if (failed(demand(std::move(pending), needed, operations)))
        return failure();
      auto guard = dyn_cast<protocol_ir::GuardOp>(cut);
      if (needed.empty() && !guard) {
        updateOperands(cut);
        continue;
      }
      llvm::sort(operations, [&](Operation *lhs, Operation *rhs) {
        return order.lookup(lhs) < order.lookup(rhs);
      });
      llvm::SetVector<Value> captures;
      SmallVector<Value> results;
      for (auto *op : operations) {
        for (auto value : op->getOperands())
          if (!needed.count(value.getDefiningOp()))
            captures.insert(value);
        for (auto value : op->getResults()) {
          if (mathematical::isFormalType(value.getType()))
            continue;
          // A native dependency may escape only through a reconstructed formal
          // descriptor. Follow descriptor uses transitively, never concrete
          // work: that work is materialized only once at its own demand.
          SmallVector<Value> pending{value};
          llvm::DenseSet<Value> seen;
          bool escapes = false;
          while (!pending.empty()) {
            auto current = pending.pop_back_val();
            if (!seen.insert(current).second)
              continue;
            for (auto *user : current.getUsers()) {
              if (!remaining--)
                return diagnostics::emit(cut->emitError(),
                                         "computation-frontier-limit");
              if (!needed.contains(user) && (!guard || user != cut))
                escapes = true;
              for (auto result : user->getResults())
                if (mathematical::isFormalType(result.getType()))
                  pending.push_back(result);
            }
          }
          if (escapes)
            results.push_back(value);
          realized.insert(value);
        }
      }
      if (guard && !needed.count(guard.getCondition().getDefiningOp()))
        captures.insert(guard.getCondition());
      SmallVector<Type> inputTypes, resultTypes;
      for (auto value : captures)
        inputTypes.push_back(value.getType());
      for (auto value : results)
        resultTypes.push_back(value.getType());
      builder.setInsertionPoint(participant);
      auto function = func::FuncOp::create(
          builder, cut->getLoc(), symbols.fresh(),
          builder.getFunctionType(inputTypes, resultTypes));
      function->setAttr(
          "runtime.origin",
          builder.getArrayAttr({builder.getStringAttr(function.getSymName()),
                                builder.getArrayAttr({})}));
      auto *entry = function.addEntryBlock();
      builder.setInsertionPointToEnd(entry);
      IRMapping mapping;
      for (auto [value, argument] : zip(captures, entry->getArguments()))
        mapping.map(value, argument);
      for (auto *op : operations) {
        auto *copy = builder.clone(*op, mapping);
        copy->removeAttr("site");
      }

      SmallVector<Value> returned;
      for (auto value : results)
        returned.push_back(mapping.lookup(value));
      func::ReturnOp::create(builder, cut->getLoc(), returned);
      std::optional<computation::CalculationGuard> condition;
      if (guard)
        condition = computation::CalculationGuard{
            mapping.lookup(guard.getCondition()), guard.getSiteAttr()};
      formed.push_back({function, condition});
      std::string site;
      if (guard)
        site = guard.getSite().str();
      else {
        do {
          site = "calculation_" + std::to_string(nextSite++);
        } while (!sites.insert(site).second);
      }
      builder.setInsertionPoint(cut);
      SmallVector<Value> arguments;
      for (auto value : captures)
        arguments.push_back(computed.lookupOrDefault(value));
      auto call = protocol_ir::LocalCallOp::create(
          builder, cut->getLoc(), resultTypes, arguments, function.getSymName(),
          site, participant.getRole());
      calculations.push_back(builder.getDictionaryAttr(
          {builder.getNamedAttr(
               "participant", FlatSymbolRefAttr::get(builder.getContext(),
                                                     participant.getSymName())),
           builder.getNamedAttr("callee", call.getCalleeAttr()),
           builder.getNamedAttr("site", call.getSiteAttr())}));
      for (auto [old, replacement] : zip(results, call.getResults()))
        computed.map(old, replacement);
      if (guard)
        guard.erase();
      else
        updateOperands(cut);
      // Keep original total definitions until all cuts have been rewritten.
      // Replacing their earlier uses with this later call result would create
      // a transient dominance violation. Later slices use the explicit map.
    }
    // Original admission happened before DCE. Any remaining total expressions
    // are unobserved and can be removed without creating physical work.
    for (auto &op : make_early_inc_range(reverse(body)))
      if (isTotal(&op) && op.use_empty())
        op.erase();
    return success();
  }

public:
  Outliner(protocol_ir::ProtocolModuleOp unit, OutlineSymbols &symbols,
           bool batching)
      : unit(unit), symbols(symbols), batching(batching),
        builder(unit.getContext()) {}
  LogicalResult run(MathematicalSelectionPolicy policy) {
    SmallVector<protocol_ir::ParticipantOp> participants;
    for (auto value :
         unit.getBody().front().getOps<protocol_ir::ParticipantOp>())
      participants.push_back(value);
    for (auto value : participants)
      if (failed(participant(value)))
        return failure();
    auto records = unit.getBody().front().getOps<protocol_ir::ProjectionOp>();
    if (records.empty())
      return diagnostics::emit(
          unit.emitError(), "mathematical-lowering-profile",
          "lowering requires retained projection metadata");
    auto record = *records.begin();
    record.setCalculationsAttr(builder.getArrayAttr(calculations));
    // Dead original expressions can have kept intermediate result ports alive
    // while outlining. Remove those ports after participant DCE, without
    // removing the invocation or any executable operation in its body.
    SymbolTable outlinedSymbols(unit);
    llvm::DenseSet<Attribute> generatedCallees;
    for (auto item : calculations)
      generatedCallees.insert(cast<DictionaryAttr>(item).get("callee"));
    SmallVector<protocol_ir::LocalCallOp> calls;
    for (auto participant : participants)
      participant.walk(
          [&](protocol_ir::LocalCallOp call) { calls.push_back(call); });
    for (auto call : calls) {
      if (!generatedCallees.contains(call.getCalleeAttr()))
        continue;
      llvm::BitVector unused(call.getNumResults());
      SmallVector<Type> types;
      for (auto [index, result] : enumerate(call.getResults())) {
        if (result.use_empty())
          unused.set(index);
        else
          types.push_back(result.getType());
      }
      if (unused.none())
        continue;
      auto function =
          cast<func::FuncOp>(outlinedSymbols.lookup(call.getCallee()));
      auto returned = cast<func::ReturnOp>(function.getBody().front().back());
      returned->eraseOperands(unused);
      function.setFunctionType(builder.getFunctionType(
          function.getFunctionType().getInputs(), types));
      builder.setInsertionPoint(call);
      auto replacement = protocol_ir::LocalCallOp::create(
          builder, call.getLoc(), types, call.getInputs(), call.getCalleeAttr(),
          call.getSiteAttr(), call.getRoleAttr());
      unsigned next = 0;
      for (auto [index, result] : enumerate(call.getResults()))
        if (!unused[index])
          result.replaceAllUsesWith(replacement.getResult(next++));
      call.erase();
    }
    for (auto &calculation : formed)
      if (failed(computation::formCalculation(calculation.function, unit,
                                              policy, calculation.guard)))
        return failure();
    return success();
  }
};
template <bool CloseDeployment>
struct LowerMathPass
    : PassWrapper<LowerMathPass<CloseDeployment>, OperationPass<ModuleOp>> {
  using Base =
      PassWrapper<LowerMathPass<CloseDeployment>, OperationPass<ModuleOp>>;
  using Base::getOperation;
  using Base::signalPassFailure;
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(LowerMathPass)
  MathematicalPassOptions selection{*this};
  LowerMathPass() = default;
  RealizationTrace *observer = nullptr;
  explicit LowerMathPass(MathematicalSelectionPolicy policy,
                         RealizationTrace *trace)
      : observer(trace) {
    selection.set(policy);
  }
  LowerMathPass(const LowerMathPass &other)
      : Base(other), selection(*this, other.selection.get()),
        observer(other.observer) {}
  typename Base::template Option<bool> traceMathematics{
      *this, "trace-mathematics",
      llvm::cl::desc("Report mathematical decisions and stages"),
      llvm::cl::init(false)};
  typename Base::template Option<bool> dumpMathematics{
      *this, "dump-mathematics",
      llvm::cl::desc("Dump mathematical lowering diagnostics and IR"),
      llvm::cl::init(false)};
  void getDependentDialects(DialectRegistry &registry) const final {
    registry.insert<runtime::RuntimeDialect, algebra::AlgebraDialect,
                    exec::ExecDialect, func::FuncDialect,
                    cf::ControlFlowDialect, arith::ArithDialect>();
  }
  StringRef getArgument() const final {
    return CloseDeployment ? "zkc-lower-closed-participant" : "zkc-lower-math";
  }
  StringRef getDescription() const final {
    return CloseDeployment
               ? "Close participant helpers and form demanded computations"
               : "Form scoped computations at participant mathematics demands";
  }
  void runOnOperation() final {
    auto source = getOperation();
    RealizationTrace diagnosticTrace;
    diagnosticTrace.remarks = traceMathematics;
    diagnosticTrace.ir = dumpMathematics ? &llvm::errs() : nullptr;
    auto *trace = observer
                      ? observer
                      : (traceMathematics || dumpMathematics ? &diagnosticTrace
                                                             : nullptr);
    auto policy = selection.get();
    RealizationScope scope(
        trace, CloseDeployment ? "lower-closed-participant" : "lower-math",
        source, policy);
    if (trace && trace->ir) {
      *trace->ir << "// Before mathematical demand lowering\n";
      source.print(*trace->ir);
      *trace->ir << "\n";
    }
    if (failed(zkc::admitStage(source)) || !hasSingleElement(*source.getBody()))
      return signalPassFailure();
    auto original =
        dyn_cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
    if (!original ||
        original.getProfile() != protocol_ir::Profile::Participant) {
      diagnostics::emit(source.emitError(), "mathematical-lowering-profile",
                        "expected the 'participant' profile");
      return signalPassFailure();
    }
    scope.propose(policy);
    auto expanded = protocol::expandScopedHelpers(source);
    if (!expanded)
      return signalPassFailure();
    if constexpr (CloseDeployment) {
      auto reachable = protocol::pruneParticipantHelpers(*expanded);
      if (!reachable)
        return signalPassFailure();
      expanded = std::move(reachable);
    }
    OwningOpRef<ModuleOp> candidate(cast<ModuleOp>((*expanded)->clone()));
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
    OutlineSymbols symbols(unit);
    if (failed(Outliner(unit, symbols, policy.calculationBatching).run(policy)))
      return signalPassFailure();
    unit.setProfile(protocol_ir::Profile::Exec);
    if (failed(zkc::admitStage(*candidate)) ||
        failed(verifyProjectionPreserved(*expanded, *candidate, policy)))
      return signalPassFailure();
    source->setAttrs(candidate->getOperation()->getAttrs());
    source.getBodyRegion().takeBody(candidate->getBodyRegion());
    scope.publish(PublicationBoundary::PublishedToCaller);
    if (trace && trace->ir) {
      *trace->ir << "// After mathematical demand lowering\n";
      source.print(*trace->ir);
      *trace->ir << "\n";
    }
  }
};
} // namespace
} // namespace zkc::mathematical
std::unique_ptr<mlir::Pass>
zkc::protocol::createLowerMathPass(MathematicalSelectionPolicy policy,
                                   mathematical::RealizationTrace *trace) {
  return std::make_unique<mathematical::LowerMathPass<false>>(policy, trace);
}
std::unique_ptr<mlir::Pass> zkc::protocol::createLowerClosedParticipantPass(
    MathematicalSelectionPolicy policy, mathematical::RealizationTrace *trace) {
  return std::make_unique<mathematical::LowerMathPass<true>>(policy, trace);
}
