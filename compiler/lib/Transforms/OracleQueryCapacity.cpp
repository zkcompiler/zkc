#include "OracleQueryCapacity.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/Interactions.h"
#include "zkc/Analysis/ProtocolConstants.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Refusal.h"
#include <limits>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
namespace pir = protocol_ir;
OracleQuerySize joined(OracleQuerySize a, OracleQuerySize b) {
  return {std::max(a.leaves, b.leaves), std::max(a.nodes, b.nodes)};
}
struct Analysis {
  Block *entry;
  uint64_t remaining;
  facts::Work work;
  InteractionAnalysis interactions;
  MathematicalFactAnalysis mathematics;
  Analysis(ModuleOp module, Block &body, uint64_t allowance)
      : entry(&body), remaining(allowance), work(remaining),
        interactions(module), mathematics(module) {}
  OracleQueryCapacity result;
  llvm::DenseMap<Value, OracleQuerySize> values;
  static bool logical(Type type) {
    return isa<pir::OracleHandleType, pir::OracleSequenceType>(type);
  }
  Error charge(uint64_t amount) {
    if (!work.charge(amount))
      return error("oracle-query-capacity-limit");
    return Error::success();
  }
  Expected<const InteractionDeclaration *> structure(Operation *declaration) {
    auto view = interactions.get(declaration, work);
    if (view)
      return *view;
    consumeError(view.takeError());
    return error(work.exhausted() ? "oracle-query-capacity-limit"
                                  : "oracle-query-capacity-source");
  }
  Error sum(OracleQuerySize &target, OracleQuerySize source) {
    if (target.leaves > std::numeric_limits<uint64_t>::max() - source.leaves ||
        target.nodes > std::numeric_limits<uint64_t>::max() - source.nodes)
      return error("oracle-query-capacity-overflow");
    target.leaves += source.leaves;
    target.nodes += source.nodes;
    return Error::success();
  }
  void record(Operation *op, OracleQuerySize size, bool query = false) {
    auto &inventory = query ? result.queries : result.constructors;
    inventory[op] = joined(inventory.lookup(op), size);
  }
  Expected<OracleQuerySize> get(Value value) {
    if (!logical(value.getType()))
      return OracleQuerySize{};
    auto found = values.find(value);
    if (found == values.end())
      return error("oracle-query-capacity-source");
    return found->second;
  }
  Error repeat(pir::RepeatOp loop, const InteractionDeclaration &view,
               const InteractionSequence &sequence) {
    SmallVector<OracleQuerySize> carried, captures;
    for (auto [i, input] : enumerate(loop.getInputs().drop_front())) {
      auto size = get(input);
      if (!size)
        return size.takeError();
      (i < unsigned(loop.getCarried()) ? carried : captures).push_back(*size);
    }
    auto &body = loop.getBody().front();
    uint64_t maximum = loop.getMaximum();
    auto count = observeProtocolConstant(loop.getInputs().front(), "",
                                         mathematics, work);
    if (count.status == facts::Status::Capacity)
      return error("oracle-query-capacity-limit");
    // A common value may tighten the maximum. A participant-specific count,
    // backedge or out-of-range value supplies no common iteration bound.
    if (count.status == facts::Status::Proven && count.value &&
        *count.value <= maximum)
      maximum = *count.value;
    for (uint64_t iteration = 0; iteration < maximum; ++iteration) {
      if (auto e = charge(1 + body.getNumArguments()))
        return e;
      for (auto [argument, size] :
           zip(body.getArguments().drop_front(), carried))
        values[argument] = size;
      for (auto [argument, size] :
           zip(body.getArguments().drop_front(1 + carried.size()), captures))
        values[argument] = size;
      if (auto e = block(view, sequence))
        return e;
      bool changed = false;
      for (auto [i, value] : enumerate(body.back().getOperands())) {
        auto size = get(value);
        if (!size)
          return size.takeError();
        auto bound = joined(carried[i], *size);
        changed |= !(bound == carried[i]);
        carried[i] = bound;
      }
      // A post-fixed point covers every remaining iteration, including a
      // very large maximum. Otherwise retain the zero-trip values in the join.
      if (!changed)
        break;
    }
    for (auto [value, size] : zip(loop.getResults(), carried))
      values[value] = size;
    return Error::success();
  }
  Error block(const InteractionDeclaration &view,
              const InteractionSequence &sequence) {
    for (unsigned ordinal : sequence.getActions()) {
      const auto &action = view.getActions()[ordinal];
      auto *op = action.getOperation();
      if (auto e = charge(1 + op->getNumOperands() + op->getNumResults()))
        return e;
      if (op->hasTrait<OpTrait::IsTerminator>())
        continue;
      if (auto loop = dyn_cast<pir::RepeatOp>(op)) {
        if (auto e =
                repeat(loop, view, view.getSequence(*action.getRepeatBody())))
          return e;
        continue;
      }
      OracleQuerySize size;
      if (isa<pir::OracleSendOp>(op)) {
        size = {1, 1};
        record(op, size);
      } else if (auto input = dyn_cast<pir::OracleInputOp>(op)) {
        auto actual = get(input.getAnchor());
        if (!actual)
          return actual.takeError();
        size = *actual;
        Value anchor = input.getAnchor();
        while (auto view = anchor.getDefiningOp<pir::RestrictRolesOp>()) {
          if (auto e = charge(1))
            return e;
          anchor = view.getInput();
        }
        auto argument = dyn_cast<BlockArgument>(anchor);
        if (argument && argument.getOwner() == entry)
          record(op, size);
      } else if (auto created = dyn_cast<pir::OracleVirtualOp>(op)) {
        auto definition = dyn_cast_or_null<pir::OracleDefinitionOp>(
            action.getReferencedSymbol());
        if (!definition)
          return error("oracle-query-capacity-source");
        auto definitionView = structure(definition);
        if (!definitionView)
          return definitionView.takeError();
        size.nodes = 1;
        for (const auto &nested : (*definitionView)->getActions()) {
          if (auto e = charge(1))
            return e;
          auto query = dyn_cast<pir::OracleQueryOp>(nested.getOperation());
          if (!query)
            continue;
          auto ordinal = cast<BlockArgument>(query.getHandle()).getArgNumber();
          auto child = get(created.getInputs()[ordinal]);
          if (!child)
            return child.takeError();
          if (auto e = sum(size, *child))
            return e;
        }
        record(op, size);
      } else if (auto query = dyn_cast<pir::OracleQueryOp>(op)) {
        auto actual = get(query.getHandle());
        if (!actual)
          return actual.takeError();
        record(op, *actual, true);
      } else if (isa<pir::OracleSequenceEmptyOp>(op)) {
        size = {};
      } else if (isa<pir::OracleSequenceAppendOp, pir::OracleSequenceAtOp,
                     pir::OracleForgetShapeOp, pir::OracleComponentsOp,
                     pir::RestrictRolesOp>(op)) {
        for (Value input : op->getOperands()) {
          auto actual = get(input);
          if (!actual)
            return actual.takeError();
          size = joined(size, *actual);
        }
      } else if (any_of(op->getResultTypes(), logical) ||
                 isa<pir::ApplyOp>(op)) {
        return error("oracle-query-capacity-source");
      }
      for (Value value : op->getResults())
        if (logical(value.getType()))
          values[value] = size;
    }
    return Error::success();
  }
};
} // namespace
Expected<OracleQueryCapacity>
analyzeOracleQueryCapacity(ModuleOp prepared, StringRef entry, uint64_t work) {
  if (!prepared || failed(zkc::admitStage(prepared)) ||
      !hasSingleElement(prepared.getBody()->getOperations()))
    return error("oracle-query-capacity-source");
  auto unit = dyn_cast<pir::ProtocolModuleOp>(prepared.getBody()->front());
  auto program = unit ? dyn_cast_or_null<pir::MathematicalOp>(
                            SymbolTable::lookupSymbolIn(unit, entry))
                      : pir::MathematicalOp{};
  if (!program || unit.getProfile() != pir::Profile::Protocol)
    return error("oracle-query-capacity-source");
  Analysis analysis(prepared, program.getBody().front(), work);
  auto view = analysis.structure(program);
  if (!view)
    return view.takeError();
  for (auto argument : program.getBody().front().getArguments()) {
    if (isa<pir::OracleHandleType>(argument.getType()))
      analysis.values[argument] = {1, 1};
    else if (auto sequence =
                 dyn_cast<pir::OracleSequenceType>(argument.getType()))
      // Cover every possible source element, including repeated occurrences.
      // This structural bound grants no Host sequence-ingress capability.
      analysis.values[argument] = {sequence.getMaximum(),
                                   sequence.getMaximum()};
  }
  if (auto e = analysis.block(**view, (*view)->getBody()))
    return std::move(e);
  return std::move(analysis.result);
}
} // namespace zkc::protocol
