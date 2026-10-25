#include "zkc/Dialect/Bindings.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringSet.h"
#include <array>

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {

namespace {
struct ContractAssociation {
  StringLiteral key;
  StringLiteral value;
};

#include "zkc/Dialect/ContractMappings.cpp.inc"

// The installed contract set has static lifetime. Build its membership index
// once without adding MLIR knowledge or generated adapter data to Contracts.
bool installedContract(StringRef contract) {
  static const llvm::StringSet<> installed = [] {
    llvm::StringSet<> result;
    for (const auto &application : operationShapes())
      result.insert(application.key);
    return result;
  }();
  return installed.contains(contract);
}

auto associationBegin(ArrayRef<ContractAssociation> rows, StringRef key) {
  return llvm::lower_bound(rows, key, [](const auto &row, StringRef value) {
    return row.key < value;
  });
}

const ContractAssociation *contractAssociation(StringRef key) {
  ArrayRef<ContractAssociation> rows = contractAssociations;
  auto found = associationBegin(rows, key);
  return found != rows.end() && found->key == key ? found : nullptr;
}
} // namespace

StringRef boundOperationName(StringRef contract) {
  if (!installedContract(contract))
    return {};
  if (const auto *exact = contractAssociation(contract))
    return exact->value;
  return {};
}

bool operationSupportsContract(StringRef operationName, StringRef contract) {
  if (!installedContract(contract))
    return false;
  ArrayRef<ContractAssociation> rows = operationAssociations;
  for (auto found = associationBegin(rows, operationName);
       found != rows.end() && found->key == operationName; ++found)
    if (contract == found->value)
      return true;
  return false;
}

Type decodeBoundType(MLIRContext *ctx, const BoundType &t) {
  if (!ctx)
    return {};
  auto checked = parseBoundType(t.spelling(), !t.representation.empty());
  if (!checked) {
    consumeError(checked.takeError());
    return {};
  }
  if (!(*checked == t))
    return {};
  const auto *adapter = type_adapters::findAdapter(t.kind);
  if (!adapter)
    return {};
  Type result = adapter->decode(ctx, t);
  if (!result)
    return {};
  if (t.representation.empty())
    return result;
  SmallVector<Type> children;
  if (t.physicalChildren)
    for (const auto &child : *t.physicalChildren) {
      auto decoded = decodeBoundType(ctx, child);
      if (!decoded)
        return {};
      children.push_back(decoded);
    }
  return type_adapters::loadedType<zkc::runtime::RepresentedType>(
      ctx, result, t.representation, children);
}

Expected<BoundType> encodeBoundType(Type type, bool physical) {
  if (!type)
    return error("binding-type");
  Type original = type;
  std::string rep;
  if (auto data = dyn_cast<zkc::runtime::RepresentedType>(type)) {
    if (!physical)
      return error("binding-physical-type-at-logical-stage");
    rep = data.getRepresentation().str();
    type = data.getLogical();
  } else if (physical)
    return error("binding-logical-type-at-physical-stage");
  auto result = type_adapters::encodeLogicalType(type);
  if (!result)
    return result.takeError();
  if (physical) {
    std::vector<BoundType> children;
    for (auto child :
         cast<zkc::runtime::RepresentedType>(original).getChildren()) {
      auto encoded = encodeBoundType(child, true);
      if (!encoded)
        return encoded.takeError();
      children.push_back(std::move(*encoded));
    }
    result = physicalType(*result, rep, std::move(children));
    if (!result)
      return result.takeError();
  }
  auto checked = parseBoundType(result->spelling(), physical);
  if (!checked)
    return checked.takeError();
  // Compare the original carrier, including its exact physical wrapper.
  if (decodeBoundType(original.getContext(), *checked) != original)
    return error("binding-type-identity");
  return checked;
}

Expected<protocol::OperationBinding> readBinding(Operation *op) {
  auto declaration = dyn_cast_or_null<zkc::local::OperationBindingOp>(op);
  if (!declaration ||
      !isa_and_nonnull<zkc::protocol_ir::ProtocolModuleOp, mlir::ModuleOp>(
          op->getParentOp()))
    return error("binding-declaration-context");
  auto name = declaration.getSymNameAttr();
  auto contract = declaration.getContractAttr();
  auto implementation = declaration.getImplementationAttr();
  auto arguments = declaration.getArgumentsAttr();
  if (!name || !contract || !implementation || !arguments)
    return error("binding-declaration");
  std::vector<std::string> values;
  for (auto arg : arguments) {
    auto value = dyn_cast<StringAttr>(arg);
    if (!value)
      return error("binding-static-identity");
    values.push_back(value.getValue().str());
  }
  auto root = dyn_cast<zkc::protocol_ir::ProtocolModuleOp>(op->getParentOp());
  bool physical = root && root.getProfileAttr() &&
                  root.getProfile() == zkc::protocol_ir::Profile::Physical;
  protocol::OperationBinding binding{name.getValue().str(),
                                     {contract.getValue().str(),
                                      std::move(values),
                                      implementation.getValue().str()}};
  if (auto parameters = declaration.getPhysicalArgumentsAttr()) {
    for (auto parameter : parameters) {
      auto value = dyn_cast<StringAttr>(parameter);
      if (!value)
        return error("binding-representation");
      binding.application.physicalArguments.push_back(value.getValue().str());
    }
  }
  if (auto e =
          checkBindingDeclaration(binding.name, binding.application, physical))
    return e;
  return binding;
}

Expected<protocol::OperationBinding> operationBinding(Operation *user) {
  // Resolve in this lexical symbol table only. Compiler schedules use a
  // builtin module; executable profile admission owns its closed vocabulary.
  auto *root = SymbolTable::getNearestSymbolTable(user);
  auto reference = user->getAttrOfType<FlatSymbolRefAttr>("binding");
  if (!root || !reference)
    return error("binding-reference");
  return readBinding(SymbolTable::lookupSymbolIn(root, reference));
}

LogicalResult verifyBoundOperation(Operation *op, bool physical) {
  auto selected = operationBinding(op);
  if (!selected)
    return diagnostics::emit(op->emitOpError(), selected.takeError());
  auto signature = resolveBinding(selected->application, physical);
  if (!signature)
    return diagnostics::emit(op->emitOpError(), signature.takeError());
  if (physical) {
    auto key = op->getAttrOfType<StringAttr>("implementation");
    if (!isa<zkc::plan::ApplyOp>(op) || !key ||
        key.getValue() != selected->application.implementation)
      return diagnostics::emit(op->emitOpError(), "binding-implementation");
  } else if (!operationSupportsContract(op->getName().getStringRef(),
                                        selected->application.contract))
    return diagnostics::emit(op->emitOpError(), "binding-operation");
  auto types = [&](TypeRange actual, ArrayRef<BoundType> expected) {
    if (actual.size() != expected.size())
      return false;
    for (auto [type, target] : zip(actual, expected)) {
      auto value = encodeBoundType(type, physical);
      if (!value) {
        consumeError(value.takeError());
        return false;
      }
      if (!(*value == target))
        return false;
    }
    return true;
  };
  if (!types(op->getOperandTypes(), signature->inputs) ||
      !types(op->getResultTypes(), signature->outputs))
    return diagnostics::emit(op->emitOpError(), "binding-operation-signature");
  auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
  if (!parameters)
    return diagnostics::emit(op->emitOpError(), "binding-parameters");
  std::vector<std::string> values;
  for (auto p : parameters) {
    auto value = dyn_cast<StringAttr>(p);
    if (!value)
      return diagnostics::emit(op->emitOpError(), "binding-parameters");
    values.push_back(value.getValue().str());
  }
  if (auto e = checkParameters(selected->application, values))
    return diagnostics::emit(op->emitOpError(), std::move(e));
  return success();
}
} // namespace zkc::protocol

namespace zkc {
LogicalResult zkc::local::OperationBindingOp::verify() {
  auto binding = protocol::readBinding(*this);
  if (!binding)
    return diagnostics::emit(emitOpError(), binding.takeError());
  return success();
}
} // namespace zkc
