#include "zkc/Analysis/FiniteClosure.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "llvm/ADT/ScopeExit.h"

using namespace mlir;
namespace zkc::finite {
namespace {
// Only references with a defined executable meaning are interchangeable.
bool executableEdge(Operation *op, StringRef key) {
  if (isa<func::CallOp>(op))
    return key == "callee";
  return isComputation(op) && (key == "domain" || key == "step" ||
                               key == "body" || key == "predicate");
}
} // namespace

LogicalResult
ClosureClasses::resolveEdges(Operation *op, NamedAttrList &attributes,
                             SymbolTableCollection &symbols,
                             llvm::function_ref<bool(uint64_t)> charge) {
  for (NamedAttribute attribute : op->getAttrs()) {
    if (!charge(1))
      return failure();
    auto key = attribute.getName();
    if (!executableEdge(op, key.getValue())) {
      // The meaning of another symbol-bearing property can depend on the
      // surrounding module. Preserve that boundary conservatively.
      if (attribute.getValue()
              .walk([&](Attribute a) {
                return !charge(1) || isa<SymbolRefAttr>(a)
                           ? WalkResult::interrupt()
                           : WalkResult::advance();
              })
              .wasInterrupted())
        return failure();
      continue;
    }
    auto ref = dyn_cast<FlatSymbolRefAttr>(attribute.getValue());
    if (!ref)
      return failure();
    auto id =
        classify(symbols.lookupNearestSymbolFrom(op, ref), symbols, charge);
    if (failed(id))
      return failure();
    attributes.set(
        key, FlatSymbolRefAttr::get(op->getContext(), std::to_string(*id)));
  }
  return success();
}

FailureOr<unsigned>
ClosureClasses::classify(Operation *definition, SymbolTableCollection &symbols,
                         llvm::function_ref<bool(uint64_t)> charge) {
  if (!charge(1) || !definition)
    return failure();
  if (auto found = known.find(definition); found != known.end())
    return found->second;
  if (!isa<func::FuncOp, data::DomainOp>(definition) ||
      definition->getNumRegions() != 1 || definition->getRegion(0).empty() ||
      active.size() >= 64 || !active.insert(definition).second)
    return failure();
  auto leave = llvm::scope_exit([&] { active.erase(definition); });

  // Resolve each edge at its original use. Charge the whole tree before
  // cloning it. Walking both trees in the same order preserves SSA use and
  // region structure, including repeated or permuted callback arguments.
  SmallVector<DictionaryAttr> normalized;
  uint64_t size = 0;
  auto walked = definition->walk<WalkOrder::PreOrder>([&](Operation *nested) {
    uint64_t weight = uint64_t(1) + nested->getNumOperands() +
                      nested->getNumResults() + nested->getNumRegions();
    for (Region &region : nested->getRegions())
      for (Block &block : region)
        weight += 1 + block.getNumArguments();
    if (!charge(weight))
      return WalkResult::interrupt();
    size += weight;
    NamedAttrList attributes(nested->getAttrs());
    if (failed(resolveEdges(nested, attributes, symbols, charge)))
      return WalkResult::interrupt();
    if (nested == definition && SymbolTable::getSymbolVisibility(nested) ==
                                    SymbolTable::Visibility::Private)
      attributes.set(SymbolTable::getSymbolAttrName(),
                     StringAttr::get(nested->getContext(), "definition"));
    normalized.push_back(attributes.getDictionary(nested->getContext()));
    return WalkResult::advance();
  });
  if (walked.wasInterrupted())
    return failure();

  OwningOpRef<Operation *> copy(definition->clone());
  constexpr auto flags = OperationEquivalence::IgnoreLocations |
                         OperationEquivalence::IgnoreCommutativity;
  size_t index = 0;
  llvm::hash_code hash = llvm::hash_value(size);
  copy->walk<WalkOrder::PreOrder>([&](Operation *nested) {
    nested->setAttrs(normalized[index++]);
    hash = llvm::hash_combine(
        hash, OperationEquivalence::computeHash(
                  nested, OperationEquivalence::ignoreHashValue,
                  OperationEquivalence::ignoreHashValue, flags));
  });
  auto &bucket = classes[static_cast<size_t>(hash)];
  for (auto &other : bucket) {
    if (!charge(size + other.size))
      return failure();
    if (OperationEquivalence::isEquivalentTo(*copy, *other.definition, flags)) {
      known[definition] = other.id;
      return other.id;
    }
  }
  unsigned id = next++;
  bucket.push_back({std::move(copy), size, id});
  known[definition] = id;
  return id;
}
} // namespace zkc::finite
