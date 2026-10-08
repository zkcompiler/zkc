#include "zkc/Dialect/Relation/Formula.h"
#include "zkc/Dialect/Printing.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/FramedHash.h"
using namespace llvm;
namespace zkc::relation {
Expected<const FormulaIdentities::Definition *>
FormulaIdentities::definition(mlir::func::FuncOp helper) {
  if (auto found = definitions.find(helper); found != definitions.end())
    return &found->second;
  if (helper.isExternal())
    return error("relation.formula", "predicate helper has no body");
  Definition result;
  bool limited = false, missing = false;
  helper.walk([&](mlir::Operation *op) {
    uint64_t work = 1 + op->getNumOperands() + op->getNumResults();
    if (work > remaining) {
      limited = true;
      return mlir::WalkResult::interrupt();
    }
    remaining -= work;
    if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op)) {
      auto callee = symbols.lookupNearestSymbolFrom<mlir::func::FuncOp>(
          call, call.getCalleeAttr());
      if (!callee) {
        missing = true;
        return mlir::WalkResult::interrupt();
      }
      result.dependencies.push_back(callee);
    }
    return mlir::WalkResult::advance();
  });
  if (limited)
    return error("source.limit", "formula closure work limit exceeded");
  if (missing)
    return error("relation.formula", "predicate helper is absent");
  std::string text;
  BoundedStream body(text, std::min(byteLimit, remaining));
  helper->print(body, canonicalPrintingFlags(true));
  if (body.overflow())
    return error("source.limit", "formula definition byte limit exceeded");
  FramedHash hash(remaining);
  hash.frame("zkc.language.formula-helper/1");
  hash.frame(text);
  auto digest = hash.finish();
  if (!digest)
    return digest.takeError();
  result.digest = std::move(*digest);
  return &definitions.emplace(helper, std::move(result)).first->second;
}
Expected<std::string>
FormulaIdentities::get(mlir::func::FuncOp predicate,
                       ArrayRef<std::string> logicalInputs,
                       ArrayRef<std::string> purposes) {
  if (!predicate || logicalInputs.size() != purposes.size())
    return error("relation.formula", "invalid predicate definition");
  std::map<std::string, const Definition *> closure;
  SmallVector<mlir::func::FuncOp> pending{predicate};
  while (!pending.empty()) {
    auto helper = pending.pop_back_val();
    if (!remaining)
      return error("source.limit", "formula closure work limit exceeded");
    --remaining;
    if (closure.count(helper.getSymName().str()))
      continue;
    auto value = definition(helper);
    if (!value)
      return value.takeError();
    closure.emplace(helper.getSymName().str(), *value);
    append_range(pending, (*value)->dependencies);
  }
  FramedHash hash(remaining);
  hash.frame("zkc.language.formula/1");
  hash.frame(predicate.getSymName());
  hash.frame(std::to_string(logicalInputs.size()));
  for (auto [identity, purpose] : zip(logicalInputs, purposes)) {
    hash.frame(identity);
    hash.frame(purpose);
  }
  hash.frame(std::to_string(closure.size()));
  for (auto &[name, definition] : closure) {
    hash.frame(name);
    hash.frame(definition->digest);
  }
  return hash.finish();
}
} // namespace zkc::relation
