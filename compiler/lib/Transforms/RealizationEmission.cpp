#include "RealizationEmission.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
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
                            const protocol::BindingApplication &application) {
  Key key{application.contract, application.arguments,
          application.implementation};
  auto found = bindings.find(key);
  if (found == bindings.end()) {
    std::string name;
    do {
      name = prefix + std::to_string(next++);
    } while (!names.insert(name).second ||
             SymbolTable::lookupSymbolIn(unit, name));
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToStart(&unit->getRegion(0).front());
    SmallVector<Attribute> arguments;
    for (const auto &argument : application.arguments)
      arguments.push_back(builder.getStringAttr(argument));
    runtime::BindingOp::create(builder, location, name, application.contract,
                               builder.getArrayAttr(arguments),
                               application.implementation, mlir::ArrayAttr{});
    found = bindings.emplace(std::move(key), name).first;
  }
  return FlatSymbolRefAttr::get(builder.getContext(), found->second);
}

Operation *
RealizationEmitter::emit(OpBuilder &builder, Location location, StringRef site,
                         const protocol::BindingApplication &application,
                         ValueRange inputs, TypeRange outputs,
                         ArrayRef<std::string> parameters) {
  auto operation = protocol::boundOperationName(application.contract);
  assert(!operation.empty() && "realization requires an installed contract");
  OperationState state(location, operation);
  state.addOperands(inputs);
  state.addTypes(outputs);
  state.addAttribute("binding", binding(builder, location, application));
  state.addAttribute("site", builder.getStringAttr(site));
  SmallVector<Attribute> attributes;
  for (const auto &parameter : parameters)
    attributes.push_back(builder.getStringAttr(parameter));
  state.addAttribute("parameters", builder.getArrayAttr(attributes));
  return builder.create(state);
}
} // namespace zkc::mathematical
