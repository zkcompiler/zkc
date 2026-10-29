#include "OracleQueryCapacity.h"
#include "mlir/IR/Verifier.h"
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
  Analysis(Block &body, uint64_t work) : entry(&body), remaining(work) {}
  OracleQueryCapacity result;
  llvm::DenseMap<Value, OracleQuerySize> values;
  SymbolTableCollection symbols;
  static bool logical(Type type) {
    return isa<pir::OracleHandleType, pir::OracleSequenceType>(type);
  }
  Error charge(uint64_t work) {
    if (work > remaining)
      return error("oracle-query-capacity-limit");
    remaining -= work;
    return Error::success();
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
  Error repeat(pir::RepeatOp loop) {
    SmallVector<OracleQuerySize> carried, captures;
    for (auto [i, input] : enumerate(loop.getInputs().drop_front())) {
      auto size = get(input);
      if (!size)
        return size.takeError();
      (i < unsigned(loop.getCarried()) ? carried : captures).push_back(*size);
    }
    auto &body = loop.getBody().front();
    for (uint64_t iteration = 0; iteration < uint64_t(loop.getMaximum());
         ++iteration) {
      if (auto e = charge(1 + body.getNumArguments()))
        return e;
      for (auto [argument, size] :
           zip(body.getArguments().drop_front(), carried))
        values[argument] = size;
      for (auto [argument, size] :
           zip(body.getArguments().drop_front(1 + carried.size()), captures))
        values[argument] = size;
      if (auto e = block(body))
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
  Error block(Block &body) {
    for (auto &operation : body.without_terminator()) {
      auto *op = &operation;
      if (auto e = charge(1 + op->getNumOperands() + op->getNumResults()))
        return e;
      if (auto loop = dyn_cast<pir::RepeatOp>(op)) {
        if (auto e = repeat(loop))
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
        auto definition =
            symbols.lookupNearestSymbolFrom<pir::OracleDefinitionOp>(
                created, created.getCalleeAttr());
        if (!definition)
          return error("oracle-query-capacity-source");
        size.nodes = 1;
        for (auto query :
             definition.getBody().front().getOps<pir::OracleQueryOp>()) {
          if (auto e = charge(1))
            return e;
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
  if (!prepared || failed(verify(prepared)) ||
      !hasSingleElement(prepared.getBody()->getOperations()))
    return error("oracle-query-capacity-source");
  auto unit = dyn_cast<pir::ProtocolModuleOp>(prepared.getBody()->front());
  auto program = unit ? dyn_cast_or_null<pir::MathematicalOp>(
                            SymbolTable::lookupSymbolIn(unit, entry))
                      : pir::MathematicalOp{};
  if (!program || unit.getProfile() != pir::Profile::Protocol)
    return error("oracle-query-capacity-source");
  Analysis analysis(program.getBody().front(), work);
  for (auto argument : program.getBody().front().getArguments()) {
    if (isa<pir::OracleHandleType>(argument.getType()))
      analysis.values[argument] = {1, 1};
    else if (isa<pir::OracleSequenceType>(argument.getType()))
      return error("oracle-query-capacity-source");
  }
  if (auto e = analysis.block(program.getBody().front()))
    return std::move(e);
  return std::move(analysis.result);
}
} // namespace zkc::protocol
