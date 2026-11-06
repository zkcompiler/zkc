#ifndef ZKC_TRANSFORMS_ORACLEVIRTUALFUNCTIONS_H
#define ZKC_TRANSFORMS_ORACLEVIRTUALFUNCTIONS_H
#include "OracleNativeCommon.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <string>
#include <vector>
namespace zkc::protocol {
class OraclePrivateComposite;
class OracleOwnedRealization;
struct OracleVirtualQueryFunction {
  unsigned source;
  std::string site;
  protocol_ir::OracleKindAttr kind;
  mlir::func::FuncOp position;
};
struct OracleVirtualFunctions {
  // Declaration order, including duplicates and queries with unused answers.
  std::vector<OracleVirtualQueryFunction> queries;
  mlir::func::FuncOp answer;
};
struct OracleVirtualFunctionWork {
private:
  friend class OraclePrivateComposite;
  friend class OracleOwnedRealization;
  mlir::ModuleOp scratch;
  const OracleNativeSourcePreflight *source = nullptr;

public:
  unsigned operations = 100000;
  uint64_t slots = 1000000;
  // Raw primitive callers own one allowance. Nested producers/readers borrow
  // the enclosing allowance; copies and rollback never refund native work.
  std::shared_ptr<OracleNativeWork> owned =
      std::make_shared<OracleNativeWork>();
  OracleNativeWork *common = nullptr;
  bool ownsScratch(mlir::ModuleOp candidate) const {
    return scratch && scratch == candidate;
  }
  OracleNativeWork &getWork() const { return common ? *common : *owned; }
  bool reserveCapacity(uint64_t operationCount, uint64_t slotCount) {
    if (!getWork().charge(0) || operationCount > operations ||
        slotCount > slots)
      return false;
    operations -= operationCount;
    slots -= slotCount;
    return true;
  }
  // Exact recipe/copy work is reserved before that work. Primitive planners use
  // reserveCapacity for their upper bounds and an actual insertion listener for
  // generation, so unused conservative slots do not masquerade as native work.
  bool reserve(uint64_t operationCount, uint64_t slotCount) {
    if (operationCount > operations || slotCount > slots)
      return false;
    if (!getWork().charge(slotCount) ||
        !getWork().traversal(operationCount, unsigned(operationCount)))
      return false;
    operations -= operationCount;
    slots -= slotCount;
    return true;
  }
  // Private scratch generation is completed by the mandatory independent pair
  // check. Never create/reuse an immutable index for that mutating candidate.
  mlir::LogicalResult checkSubject(mlir::Operation *subject) const {
    if (!getWork().charge(0))
      return mlir::failure();
    if (scratch && subject == scratch.operator->())
      return mlir::success();
    auto module = mlir::dyn_cast_or_null<mlir::ModuleOp>(subject);
    if (!module && subject)
      module = subject->getParentOfType<mlir::ModuleOp>();
    if (source && source->matches(module, getWork()))
      return source->admit();
    auto bounded = OracleNativeSourcePreflight::read(module, getWork());
    if (!bounded) {
      llvm::consumeError(bounded.takeError());
      return mlir::failure();
    }
    return bounded->admit();
  }
};
// Split one admitted virtual declaration into ordinary total functions. Every
// position function takes its ordinary parameters followed by the outer query
// position. The answer function adds every query answer in declaration order.
// No function performs a query, checks a domain or acquires a logical handle.
// The control lowering must execute all recorded queries in order, validating
// each reached domain at its occurrence, before invoking the answer function.
// The producer modifies only candidate; discard it on failure. Work is shared
// across the complete realization, rather than reset for each declaration.
llvm::Expected<OracleVirtualFunctions>
emitOracleVirtualFunctions(mlir::ModuleOp candidate,
                           protocol_ir::OracleDefinitionOp source,
                           OracleVirtualFunctionWork &work);
// Independently compare actual helper closures against the frozen declaration.
// This checks pure substitution and the ordered query inventory, not the
// surrounding continuation machine, its actual anchor bindings or simulation.
llvm::Error checkOracleVirtualFunctions(mlir::ModuleOp candidate,
                                        protocol_ir::OracleDefinitionOp source,
                                        const OracleVirtualFunctions &actual);
} // namespace zkc::protocol
#endif
