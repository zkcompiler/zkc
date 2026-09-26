#include "zkc/Dialect/Bindings.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
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
  bool family;
};

#include "zkc/Dialect/ContractMappings.cpp.inc"

// The installed contract set has static lifetime. Build its membership index
// once without adding MLIR knowledge or generated adapter data to Contracts.
bool installedContract(StringRef contract) {
  static const llvm::StringSet<> installed = [] {
    llvm::StringSet<> result;
    for (const auto &kernel : kernels())
      result.insert(kernel.key);
    return result;
  }();
  return installed.contains(contract);
}

auto associationBegin(ArrayRef<ContractAssociation> rows, StringRef key) {
  return llvm::lower_bound(rows, key, [](const auto &row, StringRef value) {
    return row.key < value;
  });
}

const ContractAssociation *contractAssociation(StringRef key, bool family) {
  ArrayRef<ContractAssociation> rows = contractAssociations;
  auto found = associationBegin(rows, key);
  return found != rows.end() && found->key == key && found->family == family
             ? found
             : nullptr;
}
} // namespace

StringRef boundOperationName(StringRef contract) {
  if (!installedContract(contract))
    return {};
  if (const auto *exact = contractAssociation(contract, false))
    return exact->value;
  // Families are explicit dotted prefixes, not guessed mnemonic rewrites.
  // Each candidate uses the generated index; overlapping rules fail generation.
  for (size_t dot = contract.rfind('.'); dot != StringRef::npos;
       dot = contract.take_front(dot).rfind('.'))
    if (const auto *family =
            contractAssociation(contract.take_front(dot + 1), true))
      return family->value;
  return {};
}

bool operationSupportsContract(StringRef operationName, StringRef contract) {
  if (!installedContract(contract))
    return false;
  ArrayRef<ContractAssociation> rows = operationAssociations;
  for (auto found = associationBegin(rows, operationName);
       found != rows.end() && found->key == operationName; ++found)
    if (found->family ? contract.starts_with(found->value)
                      : contract == found->value)
      return true;
  return false;
}

namespace {
// Decoding must not initialize a caller's context. Missing dialects are an
// ordinary translation failure, not a fatal call into an unregistered type.
template <typename T, typename... Args>
Type loadedType(MLIRContext *ctx, Args &&...args) {
  if (!ctx->getLoadedDialect(T::dialectName))
    return {};
  return T::get(ctx, std::forward<Args>(args)...);
}
} // namespace
Type decodeBoundType(MLIRContext *ctx, const BoundType &t) {
  Type result;
  if (t.kind == "variant")
    result = loadedType<VariantType>(ctx, "variant:" + t.identity);
  else if (t.kind == "bool")
    result = IntegerType::get(ctx, 1);
  else if (t.kind == "index")
    result = IntegerType::get(ctx, 64, IntegerType::Unsigned);
  else if (t.kind == "indices")
    result =
        RankedTensorType::get({ShapedType::kDynamic},
                              IntegerType::get(ctx, 64, IntegerType::Unsigned));
  else if (t.kind == "field")
    result = loadedType<FieldType>(ctx, t.identity);
  else if (t.kind == "matrix")
    result = loadedType<MatrixType>(ctx, t.identity);
  else if (t.kind == "table")
    result = loadedType<MultilinearType>(ctx, t.identity);
  else if (t.kind == "point")
    result = loadedType<PointType>(ctx, t.identity);
  else if (t.kind == "round")
    result = loadedType<QuadraticType>(ctx, t.identity);
  else if (t.kind == "group")
    result = loadedType<GroupType>(ctx, t.identity);
  else if (t.kind == "vector" || t.kind == "groups") {
    Type element = t.kind == "vector" ? loadedType<FieldType>(ctx, t.identity)
                                      : loadedType<GroupType>(ctx, t.identity);
    if (!element)
      return {};
    result = RankedTensorType::get({ShapedType::kDynamic}, element);
  } else if (t.kind == "polynomial")
    result = loadedType<UnivariateType>(ctx, t.identity);
  else if (t.kind == "resource_unit" || t.kind == "rng" || t.kind == "nonce" ||
           t.kind == "transcript")
    result = loadedType<CapabilityType>(ctx, t.kind + ":" + t.identity);
  else if (installedDomains().hasFact("VectorCommitment", {t.identity}))
    result = loadedType<OracleObjectType>(ctx, t.identity, t.kind);
  else
    result = loadedType<ObjectType>(ctx, t.identity, t.kind);
  if (!result)
    return {};
  return t.representation.empty()
             ? result
             : loadedType<DataType>(ctx, result, t.representation);
}

Expected<BoundType> encodeBoundType(Type type, bool physical) {
  std::string rep;
  if (auto data = dyn_cast<DataType>(type)) {
    if (!physical)
      return error("binding-physical-type-at-logical-stage");
    rep = data.getRepresentation().str();
    type = data.getLogical();
  } else if (physical)
    return error("binding-logical-type-at-physical-stage");
  BoundType result;
  if (auto t = dyn_cast<VariantType>(type))
    result = {"variant", t.getDescriptor().drop_front(8).str(), {}};
  else if (type.isSignlessInteger(1))
    result.kind = "bool";
  else if (type.isUnsignedInteger(64))
    result.kind = "index";
  else if (auto t = dyn_cast<FieldType>(type))
    result = {"field", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<MatrixType>(type))
    result = {"matrix", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<MultilinearType>(type))
    result = {"table", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<PointType>(type))
    result = {"point", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<QuadraticType>(type))
    result = {"round", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<GroupType>(type))
    result = {"group", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<UnivariateType>(type))
    result = {"polynomial", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<RankedTensorType>(type)) {
    if (t.getRank() != 1 || !t.isDynamicDim(0) || t.getEncoding())
      return error("binding-type");
    if (t.getElementType().isUnsignedInteger(64))
      result.kind = "indices";
    else if (auto f = dyn_cast<FieldType>(t.getElementType()))
      result = {"vector", f.getDomain().str(), {}};
    else if (auto g = dyn_cast<GroupType>(t.getElementType()))
      result = {"groups", g.getDomain().str(), {}};
    else
      return error("binding-type");
  } else if (auto t = dyn_cast<OracleObjectType>(type))
    result = {t.getKind().str(), t.getScheme().str(), {}};
  else if (auto t = dyn_cast<ObjectType>(type))
    result = {t.getKind().str(), t.getScheme().str(), {}};
  else if (auto t = dyn_cast<CapabilityType>(type)) {
    auto [kind, identity] = t.getKind().split(':');
    result = {kind.str(), identity.str(), {}};
  } else
    return error("binding-type");
  result.representation = std::move(rep);
  auto checked = parseBoundType(result.spelling(), physical);
  if (!checked)
    return checked.takeError();
  if (decodeBoundType(type.getContext(), *checked) !=
      (physical ? Type(DataType::get(type.getContext(), type,
                                     checked->representation))
                : type))
    return error("binding-type-identity");
  return checked;
}

Expected<source::OperationBinding> readBinding(Operation *op) {
  auto declaration = dyn_cast_or_null<OperationBindingOp>(op);
  if (!declaration || !isa_and_nonnull<ProtocolModuleOp>(op->getParentOp()))
    return error("binding-declaration-context");
  auto name = declaration.getSymNameAttr();
  auto contract = declaration.getContractAttr();
  auto implementation = declaration.getImplementationAttr();
  auto arguments = declaration.getArgumentsAttr();
  if (!name || !contract || !implementation || !arguments)
    return error("binding-declaration");
  source::Names values;
  for (auto arg : arguments) {
    auto value = dyn_cast<StringAttr>(arg);
    if (!value)
      return error("binding-static-identity");
    values.push_back(value.getValue().str());
  }
  auto root = cast<ProtocolModuleOp>(op->getParentOp());
  bool physical = root.getStageAttr() && root.getStage() == "physical";
  source::OperationBinding binding{{},
                                   name.getValue().str(),
                                   {contract.getValue().str(),
                                    std::move(values),
                                    implementation.getValue().str()}};
  if (auto e =
          checkBindingDeclaration(binding.name, binding.application, physical))
    return e;
  return binding;
}

Expected<source::OperationBinding> operationBinding(Operation *user) {
  auto root = user->getParentOfType<ProtocolModuleOp>();
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
    auto key = op->getAttrOfType<StringAttr>("kernel");
    if (!isa<ExecuteKernelOp>(op) || !key ||
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
  source::Names values;
  for (auto p : parameters) {
    auto value = dyn_cast<StringAttr>(p);
    if (!value)
      return diagnostics::emit(op->emitOpError(), "binding-parameters");
    values.push_back(value.getValue().str());
  }
  if (auto e =
          checkParameters(selected->application.contract, values,
                          (selected->application.contract == "field.constant" ||
                           selected->application.contract == "vector.constant")
                              ? signature->outputs[0].identity
                              : ""))
    return diagnostics::emit(op->emitOpError(), std::move(e));
  return success();
}
} // namespace zkc::protocol

namespace zkc {
LogicalResult OperationBindingOp::verify() {
  auto binding = protocol::readBinding(*this);
  if (!binding)
    return diagnostics::emit(emitOpError(), binding.takeError());
  return success();
}
} // namespace zkc
