#ifndef ZKC_TRANSFORMS_ORACLEVIRTUALFUNCTIONS_H
#define ZKC_TRANSFORMS_ORACLEVIRTUALFUNCTIONS_H
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <string>
#include <vector>
namespace zkc::protocol {
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
  unsigned operations = 100000;
  uint64_t slots = 1000000;
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
