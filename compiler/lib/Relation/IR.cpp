#include "zkc/Relation/IR.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Target/Json.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/ADT/StringExtras.h"

using namespace llvm;
using namespace mlir;
namespace zkc::relation {
namespace {
ArrayAttr constraints(Builder &b, const R1CS &relation) {
  SmallVector<Attribute> rows;
  for (const auto &row : relation.constraints()) {
    SmallVector<Attribute> forms;
    for (const auto &form : row) {
      SmallVector<Attribute> terms;
      for (const auto &term : form)
        terms.push_back(b.getArrayAttr({b.getI64IntegerAttr(term.column),
                                        b.getStringAttr(term.coefficient)}));
      forms.push_back(b.getArrayAttr(terms));
    }
    rows.push_back(b.getArrayAttr(forms));
  }
  return b.getArrayAttr(rows);
}
Expected<uint32_t> readDimension(Operation *op, StringRef name) {
  auto value = op->getAttrOfType<IntegerAttr>(name);
  if (!value || !value.getType().isInteger(64) ||
      value.getValue().isNegative() || value.getValue().ugt(Limits::columns))
    return zkc::error("relation-dimension");
  return value.getValue().getZExtValue();
}
} // namespace

Expected<R1CS> readR1CSOperation(Operation *op) {
  if (!isa<R1CSRelationOp>(op))
    return zkc::error("relation-operation");
  for (const auto &attr : op->getAttrs())
    if (attr.getName() != "sym_name" && attr.getName() != "field" &&
        attr.getName() != "columns" && attr.getName() != "public_outputs" &&
        attr.getName() != "public_inputs" && attr.getName() != "constraints")
      return zkc::error("relation-attribute");
  auto field = op->getAttrOfType<StringAttr>("field");
  auto name = op->getAttrOfType<StringAttr>("sym_name");
  auto rows = op->getAttrOfType<ArrayAttr>("constraints");
  if (!field || !name || name.getValue().empty() || !rows ||
      rows.size() > Limits::rows)
    return zkc::error("relation-format");
  auto columns = readDimension(op, "columns");
  if (!columns)
    return columns.takeError();
  auto outputs = readDimension(op, "public_outputs");
  if (!outputs)
    return outputs.takeError();
  auto inputs = readDimension(op, "public_inputs");
  if (!inputs)
    return inputs.takeError();
  std::vector<Constraint> decoded;
  size_t count = 0;
  for (Attribute item : rows) {
    auto row = dyn_cast<ArrayAttr>(item);
    if (!row || row.size() != 3)
      return zkc::error("relation-row");
    Constraint constraint;
    for (unsigned k = 0; k < 3; ++k) {
      auto form = dyn_cast<ArrayAttr>(row[k]);
      if (!form || form.size() > Limits::terms - count)
        return zkc::error("relation-term-limit");
      count += form.size();
      for (auto item : form) {
        auto pair = dyn_cast<ArrayAttr>(item);
        if (!pair || pair.size() != 2)
          return zkc::error("relation-term");
        auto column = dyn_cast<IntegerAttr>(pair[0]);
        auto coefficient = dyn_cast<StringAttr>(pair[1]);
        if (!column || !column.getType().isInteger(64) || !coefficient ||
            column.getValue().isNegative() || column.getValue().uge(*columns))
          return zkc::error("relation-column");
        constraint[k].push_back({uint32_t(column.getValue().getZExtValue()),
                                 coefficient.getValue().str()});
      }
    }
    decoded.push_back(std::move(constraint));
  }
  auto result = R1CS::create(field.getValue().str(), *columns, *outputs,
                             *inputs, std::move(decoded));
  if (!result)
    return result.takeError();
  Builder b(op->getContext());
  if (constraints(b, *result) != rows)
    return zkc::error("relation-noncanonical");
  return result;
}

Expected<OwningOpRef<ModuleOp>> importR1CS(const R1CS &relation, StringRef name,
                                           MLIRContext &context) {
  if (name.empty() || name.size() > 128 ||
      !(isAlpha(name.front()) || name.front() == '_') ||
      !all_of(name, [](char c) { return isAlnum(c) || c == '_'; }))
    return zkc::error("relation-symbol");
  context.getOrLoadDialect<RelationDialect>();
  OpBuilder b(&context);
  OwningOpRef<ModuleOp> module = ModuleOp::create(b.getUnknownLoc());
  b.setInsertionPointToStart(module->getBody());
  OperationState state(b.getUnknownLoc(), R1CSRelationOp::getOperationName());
  state.addAttribute("sym_name", b.getStringAttr(name));
  state.addAttribute("field", b.getStringAttr(relation.field()));
  state.addAttribute("columns", b.getI64IntegerAttr(relation.columns()));
  state.addAttribute("public_outputs",
                     b.getI64IntegerAttr(relation.publicOutputs()));
  state.addAttribute("public_inputs",
                     b.getI64IntegerAttr(relation.publicInputs()));
  state.addAttribute("constraints", constraints(b, relation));
  b.create(state);
  if (failed(verify(*module)))
    return zkc::error("relation-ir");
  return module;
}

namespace {
struct DeduplicateRelationsPass
    : PassWrapper<DeduplicateRelationsPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(DeduplicateRelationsPass)
  StringRef getArgument() const final { return "zkc-deduplicate-relations"; }
  StringRef getDescription() const final {
    return "Remove exact duplicate rank-one constraint rows";
  }
  void runOnOperation() final {
    for (auto op : getOperation().getOps<R1CSRelationOp>()) {
      auto relation = readR1CSOperation(op);
      if (!relation) {
        op.emitOpError(toString(relation.takeError()));
        signalPassFailure();
        return;
      }
      Builder b(op.getContext());
      op->setAttr("constraints", constraints(b, relation->deduplicate()));
    }
  }
};
} // namespace
std::unique_ptr<Pass> createDeduplicateRelationsPass() {
  return std::make_unique<DeduplicateRelationsPass>();
}
} // namespace zkc::relation

LogicalResult zkc::R1CSRelationOp::verify() {
  auto relation = relation::readR1CSOperation(getOperation());
  if (!relation)
    return emitOpError(toString(relation.takeError()));
  return success();
}
