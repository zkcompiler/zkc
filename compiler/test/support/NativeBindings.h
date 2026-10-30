#ifndef ZKC_TEST_SUPPORT_NATIVE_BINDINGS_H
#define ZKC_TEST_SUPPORT_NATIVE_BINDINGS_H

#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/IR/ExecTypes.h"
#include "llvm/ADT/STLExtras.h"
#include <cstdint>
#include <initializer_list>
#include <stdexcept>

namespace zkc::test {
/// Import textual fixtures once at the test input boundary. Production policy
/// and plan checks receive only native attributes and complete native ports.
inline NativeBindingApplication
nativeRequest(mlir::MLIRContext &context,
              const protocol::BindingApplication &fixture) {
  NativeBindingApplication result{
      fixture.contract, {}, fixture.implementation, {}, &context};
  const generic::Operation *operation = nullptr;
  for (const auto &entry : protocol::executableOperationContracts())
    if (entry.name == fixture.contract)
      operation = &entry;
  if (!operation && protocol::resourceUnitContract(fixture.contract)) {
    for (const auto &argument : fixture.arguments)
      result.arguments.push_back(mlir::StringAttr::get(&context, argument));
    return result;
  }
  if (!operation)
    throw std::runtime_error("unknown native binding fixture");
  unsigned next = 0;
  for (auto [index, term] : llvm::enumerate(operation->signature.scope.terms)) {
    if (term.parent || term.arguments ||
        operation->signature.scope.constants.count(index))
      continue;
    if (next == fixture.arguments.size())
      break;
    llvm::StringRef text = fixture.arguments[next++];
    auto sort = operation->signature.scope.sorts[index];
    mlir::Attribute argument;
    if (sort == "Type") {
      auto parsed = protocol::parseBoundType(text, false);
      if (!parsed)
        throw std::runtime_error(llvm::toString(parsed.takeError()));
      auto type = protocol::decodeBoundType(&context, *parsed);
      if (!type)
        throw std::runtime_error("invalid native type fixture");
      argument = mlir::TypeAttr::get(type);
    } else if (sort == "Nat") {
      uint64_t value;
      if (!text.getAsInteger(10, value))
        argument = mlir::IntegerAttr::get(
            mlir::IntegerType::get(&context, 64, mlir::IntegerType::Unsigned),
            value);
    }
    result.arguments.push_back(
        argument ? argument : mlir::StringAttr::get(&context, text));
  }
  if (operation->numerical && next < fixture.arguments.size()) {
    llvm::SmallVector<bool> mask;
    for (char bit : fixture.arguments[next++])
      mask.push_back(bit == '1');
    result.arguments.push_back(mlir::DenseBoolArrayAttr::get(&context, mask));
  }
  if (fixture.contract != "table.relayout")
    for (; next < fixture.arguments.size(); ++next)
      result.arguments.push_back(
          mlir::StringAttr::get(&context, fixture.arguments[next]));
  if (!fixture.physicalArguments.empty() ||
      fixture.contract == "table.relayout") {
    auto abi = protocol::bindingSignature(&context, fixture, true);
    if (!abi)
      throw std::runtime_error(llvm::toString(abi.takeError()));
    result.valueType = mlir::FunctionType::get(
        &context, abi->getInputs().drop_front(),
        mlir::cast<exec::OutcomeType>(abi->getResult(0)).getPayload());
  }
  return result;
}
inline mlir::Type nativeType(mlir::MLIRContext &context,
                             const protocol::BoundType &fixture) {
  auto type = protocol::decodeBoundType(&context, fixture);
  if (!type)
    throw std::runtime_error("invalid native type fixture");
  return type;
}
inline bool
hasNativeArguments(const NativeBindingApplication &application,
                   std::initializer_list<llvm::StringRef> identities) {
  if (application.arguments.size() != identities.size())
    return false;
  for (auto [argument, identity] :
       llvm::zip(application.arguments, identities)) {
    auto value = mlir::dyn_cast<mlir::StringAttr>(argument);
    if (!value || value.getValue() != identity)
      return false;
  }
  return true;
}
} // namespace zkc::test
#endif
