#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Relations.h"
#include "llvm/ADT/StringExtras.h"
using namespace llvm;
using namespace mlir;
namespace zkc::relation {
Expected<OwningOpRef<ModuleOp>> importR1CS(const R1CS &relation, StringRef name,
                                           MLIRContext &context) {
  if (name.empty() || name.size() > 128 ||
      !(isAlpha(name.front()) || name.front() == '_') ||
      !all_of(name, [](char c) { return isAlnum(c) || c == '_'; }))
    return zkc::error("relation-symbol");
  context.getOrLoadDialect<zkc::relation::RelationDialect>();
  OpBuilder b(&context);
  OwningOpRef<ModuleOp> module = ModuleOp::create(b.getUnknownLoc());
  b.setInsertionPointToStart(module->getBody());
  OperationState state(b.getUnknownLoc(),
                       zkc::relation::R1CSRelationOp::getOperationName());
  state.addAttribute("sym_name", b.getStringAttr(name));
  state.addAttribute("field", b.getStringAttr(relation.field()));
  state.addAttribute("columns", b.getI64IntegerAttr(relation.columns()));
  state.addAttribute("public_outputs",
                     b.getI64IntegerAttr(relation.publicOutputs()));
  state.addAttribute("public_inputs",
                     b.getI64IntegerAttr(relation.publicInputs()));
  state.addAttribute("constraints", encodeR1CSConstraints(b, relation));
  b.create(state);
  if (failed(verify(*module)))
    return zkc::error("relation-ir");
  return module;
}

} // namespace zkc::relation
