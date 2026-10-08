#include "../../Verification.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;

namespace zkc {
namespace {
// Symbol verification may inspect a sibling before its own verifier runs.
// Validate nested attributes and signatures before using generated accessors.
using Bindings = llvm::StringMap<Attribute>;
LogicalResult bindings(Operation *user, ArrayAttr array, bool symbols,
                       Bindings &out) {
  if (!array)
    return diagnostics::emit(user->emitOpError(),
                             "interactive-binding-attribute");
  for (auto item : array) {
    auto pair = dyn_cast<ArrayAttr>(item);
    if (!pair || pair.size() != 2 || !isa<StringAttr>(pair[0]) ||
        (symbols ? !isa<FlatSymbolRefAttr>(pair[1])
                 : !isa<StringAttr>(pair[1])))
      return diagnostics::emit(user->emitOpError(),
                               "interactive-binding-attribute");
    auto alias = cast<StringAttr>(pair[0]).getValue();
    if (!out.try_emplace(alias, pair[1]).second)
      return diagnostics::emit(user->emitOpError(),
                               "interactive-binding-attribute",
                               "duplicate binding " + alias);
  }
  return success();
}
LogicalResult names(Operation *user, ArrayAttr array, llvm::StringSet<> &out) {
  if (!array)
    return diagnostics::emit(user->emitOpError(), "interactive-role-attribute");
  for (auto item : array) {
    auto name = dyn_cast<StringAttr>(item);
    if (!name || !out.insert(name.getValue()).second)
      return diagnostics::emit(user->emitOpError(),
                               "interactive-role-attribute");
  }
  return success();
}
FunctionType signature(Operation *definition) {
  auto attr = definition->getAttrOfType<TypeAttr>("function_type");
  return attr ? dyn_cast<FunctionType>(attr.getValue()) : FunctionType();
}
template <typename Op>
Op resolve(Operation *user, FlatSymbolRefAttr ref,
           SymbolTableCollection &tables, Operation *scope = nullptr) {
  auto found =
      ref ? tables.lookupNearestSymbolFrom(scope ? scope : user, ref) : nullptr;
  auto result = dyn_cast_or_null<Op>(found);
  if (!result) {
    std::string detail;
    raw_string_ostream(detail)
        << "expected " << Op::getOperationName() << " for " << ref;
    diagnostics::emit(user->emitOpError(), "interactive-symbol-kind", detail);
  }
  return result;
}
LogicalResult callSignature(Operation *call, Operation *definition) {
  auto ft = signature(definition);
  if (!ft || call->getOperandTypes() != ft.getInputs() ||
      call->getResultTypes() != ft.getResults()) {
    std::string detail;
    raw_string_ostream(detail)
        << "operands/results must match " << definition->getAttr("sym_name")
        << " function_type";
    return diagnostics::emit(call->emitOpError(), "interactive-call-signature",
                             detail);
  }
  return success();
}
LogicalResult callableBody(Operation *op, Region &body, FunctionType type) {
  if (!llvm::hasSingleElement(body) || body.front().empty())
    return diagnostics::emit(op->emitOpError(), "interactive-callable-body");
  if (body.front().getArgumentTypes() != type.getInputs())
    return diagnostics::emit(op->emitOpError(),
                             "interactive-callable-arguments");
  auto *end = body.front().getTerminator();
  if (isa<zkc::protocol_ir::FinishOp, zkc::protocol_ir::MathematicalReturnOp>(
          end)) {
    if (end->getOperandTypes() != type.getResults())
      return diagnostics::emit(end->emitOpError(),
                               "interactive-return-signature");
  } else
    return diagnostics::emit(op->emitOpError(),
                             "interactive-callable-terminator");
  return success();
}
} // namespace

LogicalResult zkc::protocol_ir::ParticipantOp::verifyRegions() {
  return callableBody(*this, getBody(), getFunctionType());
}

LogicalResult zkc::protocol_ir::RepeatOp::verifyRegions() {
  if (getInputs().empty() ||
      !getInputs().front().getType().isUnsignedInteger(64) ||
      getCarried() < 0 || uint64_t(getCarried()) >= getNumOperands() ||
      uint64_t(getCarried()) != getNumResults() || getMaximum() < 0 ||
      getMaximum() > 1048576 || getCarriedRoles().size() != getNumResults() ||
      getOperands().slice(1, getCarried()).getTypes() != getResultTypes())
    return diagnostics::emit(
        emitOpError(), "mathematical-formation",
        "invalid repeat count, bound or carried interface");
  if (!llvm::hasSingleElement(getBody()) || getBody().front().empty() ||
      getBody().front().getArgumentTypes() != getOperandTypes())
    return diagnostics::emit(
        emitOpError(), "mathematical-formation",
        "repeat arguments must be index, carried values and captures");
  auto yield = dyn_cast<ProtocolYieldOp>(getBody().front().back());
  if (!yield || yield.getOperandTypes() != getResultTypes())
    return diagnostics::emit(emitOpError(), "mathematical-formation",
                             "repeat must yield its carried interface");
  return success();
}

LogicalResult zkc::protocol_ir::ProtocolLoopOp::verifyRegions() {
  auto carried = getCarried();
  constexpr unsigned offset = 1;
  if (!getMaximum() || *getMaximum() > 1048576 || getInputs().empty() ||
      getParameter() || !getCount().empty())
    return diagnostics::emit(emitOpError(), "interactive-loop-count");
  Type type = getInputs().front().getType();
  if (auto physical = dyn_cast<plan::DataType>(type))
    type = physical.getLogical();
  if (!type.isUnsignedInteger(64))
    return diagnostics::emit(emitOpError(), "interactive-loop-count");
  if (carried < 0 || size_t(carried) + offset > getNumOperands() ||
      size_t(carried) != getNumResults() ||
      getOperands().slice(offset, carried).getTypes() != getResultTypes())
    return diagnostics::emit(emitOpError(), "interactive-loop-carried");
  if (getBody().empty() || getBody().front().empty() ||
      getBody().front().getArgumentTypes() != getOperandTypes())
    return diagnostics::emit(emitOpError(), "interactive-loop-arguments");
  auto *end = getBody().front().getTerminator();
  if (auto yield = dyn_cast<zkc::protocol_ir::ProtocolYieldOp>(end)) {
    if (yield.getOperandTypes() != getResultTypes())
      return diagnostics::emit(yield.emitOpError(), "interactive-loop-yield");
  } else
    return diagnostics::emit(emitOpError(), "interactive-loop-terminator");
  return success();
}

LogicalResult
zkc::protocol_ir::LocalCallOp::verifySymbolUses(SymbolTableCollection &tables) {
  auto *callee = tables.lookupNearestSymbolFrom(*this, getCalleeAttr());
  if (!callee || !isa<zkc::local::FuncOp, zkc::poly::RealizeOp>(callee))
    return diagnostics::emit(
        emitOpError(), "interactive-symbol-kind",
        "expected a local definition or checked polynomial realization");
  if (auto caller =
          (*this)->getParentOfType<zkc::protocol_ir::MathematicalOp>()) {
    llvm::StringSet<> roles;
    if (failed(names(*this, caller.getRolesAttr(), roles)))
      return failure();
    if (!getRoleAttr() || !roles.contains(getRoleAttr().getValue()))
      return diagnostics::emit(emitOpError(), "interactive-local-role");
  } else {
    return diagnostics::emit(emitOpError(), "interactive-local-role",
                             "expected a common protocol owner");
  }
  return callSignature(*this, callee);
}

LogicalResult zkc::protocol_ir::ProtocolEntryOp::verifySymbolUses(
    SymbolTableCollection &tables) {
  auto module = (*this)->getParentOfType<zkc::protocol_ir::ProtocolModuleOp>();
  auto targets = getTargetsAttr();
  if (!module || !module.getProfileAttr() || !targets || targets.empty())
    return diagnostics::emit(emitOpError(), "interactive-entry-targets");
  Bindings selected;
  if (failed(bindings(*this, targets, true, selected)))
    return failure();
  StringAttr instance;
  for (const auto &target : selected) {
    auto participant = resolve<zkc::protocol_ir::ParticipantOp>(
        *this, cast<FlatSymbolRefAttr>(target.second), tables);
    if (!participant)
      return failure();
    if (!signature(participant))
      return diagnostics::emit(emitOpError(), "interactive-callable-type");
    if (!participant.getRoleAttr() || participant.getRole() != target.getKey())
      return diagnostics::emit(emitOpError(), "interactive-entry-role");
    if (!participant.getInstanceAttr() ||
        (instance && instance != participant.getInstanceAttr()))
      return diagnostics::emit(emitOpError(), "interactive-entry-instance");
    instance = participant.getInstanceAttr();
  }
  return success();
}
} // namespace zkc

mlir::LogicalResult zkc::protocol_ir::ProtocolModuleOp::verifyRegions() {
  if (isMathematicalProfile(getProfile()))
    return mathematical::verifyModule(*this);
  mathematical::NativeTypePolicies types(*this);
  if (failed(mathematical::verifyProjectionMetadata(*this, types)))
    return failure();
  if (failed(mathematical::verifyNativeExecution(*this, types)))
    return failure();
  return protocol::verifyModule(*this);
}

LogicalResult zkc::protocol_ir::FinishIfOp::verify() {
  auto reject = [&](StringRef detail) {
    return diagnostics::emit(emitOpError(), "interactive-return-type", detail);
  };
  Type condition = getCondition().getType();
  if (auto wrapper = dyn_cast<plan::DataType>(condition))
    condition = wrapper.getLogical();
  if (!condition.isSignlessInteger(1))
    return reject("conditional completion requires a Boolean condition");
  SmallVector<Type> expected;
  if (auto common = (*this)->getParentOfType<MathematicalOp>()) {
    auto type = common->getAttrOfType<TypeAttr>("function_type");
    auto function =
        type ? dyn_cast<FunctionType>(type.getValue()) : FunctionType();
    auto owners = common->getAttrOfType<ArrayAttr>("output_roles");
    auto roles = common->getAttrOfType<ArrayAttr>("roles");
    if (!function || !owners || owners.size() != function.getNumResults() ||
        !roles || !is_contained(roles, getOwnerAttr()))
      return reject("conditional completion requires a declared entry owner");
    for (auto [type, outputOwners] : zip(function.getResults(), owners)) {
      auto set = dyn_cast<ArrayAttr>(outputOwners);
      if (!set)
        return reject("invalid entry output owners");
      if (is_contained(set, getOwnerAttr()))
        expected.push_back(type);
    }
  } else if (auto participant = (*this)->getParentOfType<ParticipantOp>()) {
    auto type = participant->getAttrOfType<TypeAttr>("function_type");
    auto function =
        type ? dyn_cast<FunctionType>(type.getValue()) : FunctionType();
    if (!function || participant->getAttr("role") != getOwnerAttr())
      return reject("conditional completion requires its participant owner");
    append_range(expected, function.getResults());
  } else
    return reject("conditional completion requires an entry participant");
  if (getValues().getTypes() != TypeRange(expected))
    return reject(
        "conditional completion must return every owner result in order");
  mathematical::NativeTypePolicies policies(*this);
  SmallVector<Type> affine;
  for (Type type : expected) {
    auto logical = type;
    if (auto wrapper = dyn_cast<plan::DataType>(logical))
      logical = wrapper.getLogical();
    auto policy = policies.get(logical);
    if (!policy)
      return reject("conditional completion requires admitted result types");
    if (policy->affine)
      affine.push_back(type);
  }
  if (getResultTypes() != TypeRange(affine))
    return reject(
        "conditional completion requires each affine continuation in order");
  return success();
}
