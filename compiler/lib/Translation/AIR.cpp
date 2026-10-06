#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Relations.h"
#include "llvm/ADT/StringExtras.h"
using namespace llvm;
using namespace mlir;
namespace zkc::relation {
Expected<OwningOpRef<ModuleOp>> importAIR(const AIR &relation, StringRef symbol,
                                          MLIRContext &context) {
  if (symbol.empty() || symbol.size() > 128 ||
      !(isAlpha(symbol.front()) || symbol.front() == '_') ||
      !all_of(symbol, [](char c) { return isAlnum(c) || c == '_'; }))
    return zkc::error("air-ir-symbol");
  context.getOrLoadDialect<zkc::relation::RelationDialect>();
  OpBuilder b(&context);
  OwningOpRef<ModuleOp> module = ModuleOp::create(b.getUnknownLoc());
  b.setInsertionPointToStart(module->getBody());
  OperationState state(b.getUnknownLoc(),
                       zkc::relation::AIRRelationOp::getOperationName());
  state.addAttribute("sym_name", b.getStringAttr(symbol));
  state.addAttributes(encodeAIRAttributes(b, relation).getValue());
  b.create(state);
  if (failed(verify(*module)))
    return zkc::error("air-ir");
  return module;
}
} // namespace zkc::relation
