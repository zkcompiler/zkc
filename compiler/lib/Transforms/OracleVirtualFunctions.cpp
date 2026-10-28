#include "OracleVirtualFunctions.h"
#include "MathematicalSupport.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseSet.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
Expected<OracleVirtualFunctions>
emitOracleVirtualFunctions(ModuleOp candidate,
                           protocol_ir::OracleDefinitionOp source,
                           OracleVirtualFunctionWork &work) {
  auto sourceUnit =
      source ? dyn_cast<protocol_ir::ProtocolModuleOp>(source->getParentOp())
             : protocol_ir::ProtocolModuleOp{};
  if (!candidate || !sourceUnit ||
      source.getContext() != candidate.getContext() ||
      sourceUnit.getProfile() != protocol_ir::Profile::Protocol ||
      failed(verify(sourceUnit)) || failed(verify(candidate)) ||
      !hasSingleElement(candidate.getBody()->getOperations()))
    return error("oracle-virtual-functions");
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol ||
      unit == sourceUnit)
    return error("oracle-virtual-functions");
  // Expand actual helper returns before slicing: an unused helper argument may
  // mention an earlier answer without making its position depend on that
  // answer.
  if (failed(mathematical::chargeHelperOperations(source, work.operations,
                                                  work.slots)))
    return error("oracle-virtual-function-limit");
  OwningOpRef<protocol_ir::OracleDefinitionOp> expanded(
      cast<protocol_ir::OracleDefinitionOp>(source->clone()));
  SymbolTableCollection symbols;
  if (failed(mathematical::inlineHelpers(*expanded, work.operations, work.slots,
                                         symbols, sourceUnit)))
    return error("oracle-virtual-function-limit");
  auto &body = expanded->getBody().front();
  unsigned sources = source.getNumSources();
  SmallVector<Value> arguments(body.getArguments().drop_front(sources));
  llvm::DenseMap<Operation *, unsigned> order;
  for (auto [i, operation] : enumerate(body))
    order[&operation] = i;
  auto queries = SmallVector<protocol_ir::OracleQueryOp>(
      body.getOps<protocol_ir::OracleQueryOp>());
  auto emit = [&](StringRef suffix, Value result,
                  bool answers) -> Expected<func::FuncOp> {
    SmallVector<Value> formals(arguments);
    if (answers)
      for (auto query : queries)
        formals.push_back(query.getAnswer());
    if (formals.size() + 1 > work.slots || !work.operations)
      return error("oracle-virtual-function-limit");
    --work.operations;
    work.slots -= formals.size() + 1;
    SmallVector<Type> inputs(ValueRange(formals).getTypes());
    OpBuilder builder(candidate.getContext());
    std::string prefix =
        "_oracle_virtual_" + source.getSymName().str() + "_" + suffix.str();
    std::string name = prefix;
    for (unsigned n = 0; SymbolTable::lookupSymbolIn(unit, name); ++n)
      name = prefix + "_" + std::to_string(n);
    builder.setInsertionPointToEnd(&unit.getBody().front());
    auto helper =
        func::FuncOp::create(builder, source.getLoc(), name,
                             builder.getFunctionType(inputs, result.getType()));
    helper.setPrivate();
    auto *target = helper.addEntryBlock();
    IRMapping mapping;
    for (auto [from, to] : zip(formals, target->getArguments()))
      mapping.map(from, to);
    SmallVector<Value> pending{result};
    llvm::DenseSet<Operation *> needed;
    while (!pending.empty()) {
      if (!work.slots)
        return error("oracle-virtual-function-limit");
      --work.slots;
      Value value = pending.pop_back_val();
      if (mapping.contains(value))
        continue;
      auto *op = value.getDefiningOp();
      if (!op || op->getBlock() != &body || !mathematical::isTotal(op))
        return error("oracle-virtual-functions");
      if (needed.insert(op).second)
        append_range(pending, op->getOperands());
    }
    SmallVector<Operation *> sorted(needed.begin(), needed.end());
    llvm::sort(sorted,
               [&](Operation *a, Operation *b) { return order[a] < order[b]; });
    builder.setInsertionPointToEnd(target);
    for (auto *op : sorted) {
      auto slots = uint64_t(op->getNumOperands()) + op->getNumResults();
      if (!work.operations || slots > work.slots)
        return error("oracle-virtual-function-limit");
      --work.operations;
      work.slots -= slots;
      if (any_of(op->getOperands(),
                 [&](Value input) { return !mapping.contains(input); }))
        return error("oracle-virtual-functions");
      builder.clone(*op, mapping);
    }
    func::ReturnOp::create(builder, source.getLoc(), mapping.lookup(result));
    return helper;
  };
  OracleVirtualFunctions result;
  for (auto [i, query] : enumerate(queries)) {
    auto function =
        emit("position_" + std::to_string(i), query.getPosition(), false);
    if (!function)
      return function.takeError();
    auto input = cast<BlockArgument>(query.getHandle());
    result.queries.push_back({input.getArgNumber(), query.getSite().str(),
                              query.getHandle().getType().getKind(),
                              *function});
  }
  auto answer =
      emit("answer", cast<protocol_ir::OracleYieldOp>(body.back()).getAnswer(),
           true);
  if (!answer)
    return answer.takeError();
  result.answer = *answer;
  return result;
}
} // namespace zkc::protocol
