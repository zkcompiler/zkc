#include "RealizationEmission.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
RealizationEmitter::RealizationEmitter(
    Operation *candidate, StringRef bindingPrefix,
    std::function<void(uint64_t)> reserve,
    std::function<Operation *(StringRef)> liveLookup)
    : unit(candidate), reserve(std::move(reserve)),
      liveLookup(std::move(liveLookup)) {
  assert(unit && unit->hasTrait<OpTrait::SymbolTable>() &&
         unit->getNumRegions() == 1 && unit->getRegion(0).hasOneBlock() &&
         "realization requires a single-block symbol table");
  if (this->reserve)
    this->reserve(bindingPrefix.size());
  prefix = bindingPrefix.str();
  reserveNames(unit);
}
void RealizationEmitter::reserveNames(Operation *source) {
  for (auto &op : source->getRegion(0).front()) {
    if (reserve)
      reserve(2 + 2 * uint64_t(op.getAttrDictionary().size()));
    if (auto name = SymbolTable::getSymbolName(&op)) {
      if (reserve)
        reserve(name.getValue().size());
      names.insert(name.getValue());
    }
  }
}

FlatSymbolRefAttr
RealizationEmitter::binding(OpBuilder &builder, Location location,
                            const NativeBindingApplication &application) {
  auto charge = [&](uint64_t amount) {
    if (reserve)
      reserve(amount);
    return true;
  };
  return *bindingWithWork(builder, location, application,
                          reserve ? llvm::function_ref<bool(uint64_t)>(charge)
                                  : llvm::function_ref<bool(uint64_t)>{});
}
FailureOr<FlatSymbolRefAttr>
RealizationEmitter::bindingWithWork(OpBuilder &builder, Location location,
                                    const NativeBindingApplication &application,
                                    llvm::function_ref<bool(uint64_t)> charge) {
  if (charge &&
      !charge(2 + application.contract.size() +
              application.implementation.size() + application.arguments.size()))
    return failure();
  auto arguments = builder.getArrayAttr(application.arguments);
  auto &instances =
      bindings[{application.contract, application.implementation}];
  auto found = instances.find(arguments);
  auto lookup = [&](StringRef name) -> FailureOr<Operation *> {
    if (!liveLookup && charge && !charge(1 + name.size()))
      return failure();
    if (!liveLookup && charge)
      for (auto &declaration : unit->getRegion(0).front()) {
        auto attributes = declaration.getAttrDictionary().size();
        if (!charge(2) || !charge(attributes) || !charge(attributes))
          return failure();
      }
    return liveLookup ? liveLookup(name)
                      : SymbolTable::lookupSymbolIn(unit, name);
  };
  if (found == instances.end()) {
    std::string name;
    do {
      if (charge && !charge(prefix.size() + 11))
        return failure();
      name = prefix + std::to_string(next++);
      if (!names.insert(name).second)
        continue;
      auto live = lookup(name);
      if (failed(live))
        return failure();
      if (!*live)
        break;
    } while (true);
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToStart(&unit->getRegion(0).front());
    auto binding = runtime::BindingOp::create(builder, location, name,
                                              application.contract, arguments,
                                              application.implementation);
    found = instances
                .try_emplace(arguments,
                             CreatedBinding{std::move(name), binding,
                                            binding->getAttrDictionary()})
                .first;
  } else {
    // Never dereference the retained address until charged live lookup proves
    // it is still the exact declaration with its complete original attributes.
    auto live = lookup(found->second.name);
    if (charge && !charge(1))
      return failure();
    if (failed(live) || *live != found->second.operation ||
        (*live)->getAttrDictionary() != found->second.attributes)
      return failure();
  }
  return FlatSymbolRefAttr::get(builder.getContext(), found->second.name);
}

} // namespace zkc::mathematical
