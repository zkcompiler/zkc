#include "RealizationEmission.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
RealizationEmitter::RealizationEmitter(Operation *candidate,
                                       StringRef bindingPrefix)
    : unit(candidate), prefix(bindingPrefix.str()) {
  assert(unit && unit->hasTrait<OpTrait::SymbolTable>() &&
         unit->getNumRegions() == 1 && unit->getRegion(0).hasOneBlock() &&
         "realization requires a single-block symbol table");
  reserveNames(unit);
}
void RealizationEmitter::reserveNames(Operation *source) {
  for (auto &op : source->getRegion(0).front())
    if (auto name = SymbolTable::getSymbolName(&op))
      names.insert(name.getValue());
}

FlatSymbolRefAttr
RealizationEmitter::binding(OpBuilder &builder, Location location,
                            const NativeBindingApplication &application) {
  auto arguments = builder.getArrayAttr(application.arguments);
  auto &instances =
      bindings[{application.contract, application.implementation}];
  auto found = instances.find(arguments);
  if (found == instances.end()) {
    std::string name;
    do {
      name = prefix + std::to_string(next++);
    } while (!names.insert(name).second ||
             SymbolTable::lookupSymbolIn(unit, name));
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToStart(&unit->getRegion(0).front());
    runtime::BindingOp::create(builder, location, name, application.contract,
                               arguments, application.implementation);
    found = instances.try_emplace(arguments, name).first;
  }
  return FlatSymbolRefAttr::get(builder.getContext(), found->second);
}

} // namespace zkc::mathematical
