#include "OracleQueryBlocks.h"
#include "zkc/Support/Refusal.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
namespace pir = protocol_ir;
Error charge(unsigned &remaining) {
  if (!remaining)
    return error("oracle-query-block-limit");
  --remaining;
  return Error::success();
}
} // namespace
Expected<OracleQueryWindowSelection>
selectOracleQueryWindow(pir::OracleQueryOp first,
                        OracleAuthentication authentication,
                        const OracleQueryCapacity &capacity,
                        DominanceInfo &dominance, unsigned &remaining) {
  if (!first || !first.getOwner() ||
      !first->getParentOfType<pir::MathematicalOp>() ||
      (authentication != OracleAuthentication::PerQuery &&
       authentication != OracleAuthentication::AtomicBlocks))
    return error("oracle-query-block-source");
  OracleQueryWindowSelection result;
  auto *operation = first.getOperation();
  while (operation && result.queries.size() < 32) {
    if (auto e = charge(remaining))
      return std::move(e);
    auto query = dyn_cast<pir::OracleQueryOp>(operation);
    if (!query || query.getOwner() != first.getOwner())
      break;
    // Compare actual SSA against the first source occurrence. In particular,
    // a preceding answer, loop-carried alias or freshly selected handle cannot
    // be replaced by a structurally similar earlier value.
    bool available = true;
    for (Value operand : query->getOperands()) {
      if (auto e = charge(remaining))
        return std::move(e);
      available &= dominance.properlyDominates(operand, first);
    }
    if (!available)
      break;
    uint64_t leaves = capacity.queries.lookup(query).leaves;
    if (leaves > 1048576 || result.leaves > 1048576 - leaves)
      return error("oracle-query-block-limit");
    result.leaves += leaves;
    result.queries.push_back(query);
    if (authentication == OracleAuthentication::PerQuery)
      break;
    operation = operation->getNextNode();
  }
  if (result.queries.empty())
    return error("oracle-query-block-source");
  return result;
}
} // namespace zkc::protocol
