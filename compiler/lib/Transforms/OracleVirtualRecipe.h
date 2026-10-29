#ifndef ZKC_TRANSFORMS_ORACLEVIRTUALRECIPE_H
#define ZKC_TRANSFORMS_ORACLEVIRTUALRECIPE_H
#include "OracleVirtualFunctions.h"
#include <memory>
namespace zkc::protocol {
// Source-derived substitution recipe. It contains no candidate operations or
// emitter callbacks. Nested total regions retain lexical scopes and order.
struct OracleVirtualBlock;
struct OracleVirtualInstruction {
  mlir::Operation *source;
  std::vector<unsigned> inputs, outputs;
  std::vector<std::shared_ptr<OracleVirtualBlock>> regions;
};
struct OracleVirtualBlock {
  std::vector<unsigned> arguments;
  std::vector<mlir::Type> types;
  std::vector<OracleVirtualInstruction> instructions;
};
struct OracleVirtualBody {
  OracleVirtualBlock block;
  unsigned result;
  mlir::Type resultType;
};
struct OracleVirtualQueryRecipe {
  unsigned source;
  std::string site;
  protocol_ir::OracleKindAttr kind;
  OracleVirtualBody position;
};
struct OracleVirtualRecipe {
  std::vector<OracleVirtualQueryRecipe> queries;
  OracleVirtualBody answer;
};
llvm::Expected<OracleVirtualRecipe>
planOracleVirtualFunctions(protocol_ir::OracleDefinitionOp,
                           OracleVirtualFunctionWork &);
} // namespace zkc::protocol
#endif
