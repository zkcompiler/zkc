#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "../Verification.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Plan/IR/PlanOps.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Protocol/Semantics.h"
using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "native-local-policy", detail);
}
} // namespace
std::optional<NativeTypePolicy> nativeTypePolicy(Type type) {
  if (isa<poly::PolynomialType>(type))
    return NativeTypePolicy{true, false, false, false, false};
  auto logical = protocol::encodeBoundType(type, false);
  if (!logical) {
    consumeError(logical.takeError());
    return std::nullopt;
  }
  return protocol::nativeTypePolicy(*logical);
}
std::optional<NativeTypePolicy> NativeTypePolicies::get(Type type) {
  if (isa<poly::PolynomialType>(type))
    return NativeTypePolicy{true, false, false, false, false};
  if (auto found = cache.find(type); found != cache.end())
    return found->second;
  if (limited)
    return std::nullopt;
  auto logical = protocol::encodeBoundType(type, false);
  if (!logical) {
    consumeError(logical.takeError());
    cache[type] = std::nullopt;
    return std::nullopt;
  }
  size_t bytes = logical->spelling().size();
  std::optional<NativeTypePolicy> result;
  if (bytes > remainingBytes)
    limited = true;
  else {
    remainingBytes -= bytes;
    result = protocol::nativeTypePolicy(*logical, remaining, limited);
  }
  if (limited)
    (void)diagnostics::emit(owner->emitOpError(), "native-type-policy-limit",
                            "closed type analysis exceeds its node, depth or "
                            "distinct spelling budget");
  cache[type] = result;
  return result;
}
LogicalResult verifyNativeLocals(Operation *unit, bool allowApply) {
  NativeTypePolicies types(unit);
  return verifyNativeLocals(unit, allowApply, types);
}
LogicalResult verifyNativeLocals(Operation *unit, bool allowApply,
                                 NativeTypePolicies &types) {
  auto root = cast<protocol_ir::ProtocolModuleOp>(unit);
  const bool physical = root.getProfile() == protocol_ir::Profile::Physical;
  auto admitted = [&](Type type) {
    if (physical) {
      auto selected = dyn_cast<plan::DataType>(type);
      if (!selected)
        return false;
      type = selected.getLogical();
    }
    return !isa<poly::PolynomialType>(type) && bool(types.get(type));
  };
  unsigned remaining = 100000;
  for (auto &op : unit->getRegion(0).front()) {
    auto function = dyn_cast<local::FuncOp>(op);
    if (!function)
      continue;
    if (function.isExternal() || function->hasAttr("relation") ||
        function->hasAttr("relation_view"))
      return refuse(function, "expected a closed executable definition");
    for (auto type : function.getArgumentTypes())
      if (!admitted(type))
        return refuse(function, "unsupported local input type");
    for (auto type : function.getResultTypes())
      if (!admitted(type))
        return refuse(function, "unsupported local result type");
    auto result = function.walk([&](Operation *nested) -> WalkResult {
      if (!remaining--) {
        (void)refuse(nested, "local definition work limit");
        return WalkResult::interrupt();
      }
      if (!allowApply && isa<local::ApplyOp>(nested)) {
        (void)refuse(nested, "local.apply requires common preparation");
        return WalkResult::interrupt();
      }
      for (auto type : nested->getResultTypes())
        if (!admitted(type)) {
          (void)refuse(nested, "unsupported local result type");
          return WalkResult::interrupt();
        }
      for (auto &region : nested->getRegions())
        for (auto &block : region)
          for (auto argument : block.getArguments())
            if (!admitted(argument.getType())) {
              (void)refuse(nested, "unsupported local block type");
              return WalkResult::interrupt();
            }
      return WalkResult::advance();
    });
    if (result.wasInterrupted())
      return failure();
  }
  // Reuse the installed executable grammar, binding signatures, control and
  // affine-use admission for every definition, including unreferenced ones.
  // Executable profiles receive full source admission immediately afterwards
  // in ProtocolModuleOp verification, including selected representations.
  return protocol_ir::isExecutableProfile(root.getProfile())
             ? success()
             : protocol::verifyLocalDefinitions(unit);
}
LogicalResult verifyNativeExecution(Operation *unit) {
  NativeTypePolicies types(unit);
  return verifyNativeExecution(unit, types);
}
LogicalResult verifyNativeExecution(Operation *unit,
                                    NativeTypePolicies &types) {
  if (failed(verifyNativeLocals(unit, false, types)))
    return failure();
  const bool physical =
      cast<protocol_ir::ProtocolModuleOp>(unit).getProfile() ==
      protocol_ir::Profile::Physical;
  auto logical = [&](Type type) -> Type {
    if (!physical)
      return type;
    auto selected = dyn_cast<plan::DataType>(type);
    return selected ? selected.getLogical() : Type{};
  };
  unsigned remaining = 100000;
  for (auto endpoint :
       unit->getRegion(0).front().getOps<protocol_ir::ParticipantOp>()) {
    auto port = [&](Type type) -> LogicalResult {
      auto t = logical(type);
      auto policy = t ? types.get(t) : std::nullopt;
      if (!policy)
        return refuse(endpoint, "unsupported native endpoint port");
      if (!policy->protocolPort)
        return diagnostics::emit(endpoint.emitOpError(), "variant-boundary");
      return success();
    };
    for (auto type : endpoint.getFunctionType().getInputs())
      if (failed(port(type)))
        return failure();
    for (auto type : endpoint.getFunctionType().getResults())
      if (failed(port(type)))
        return failure();
    auto result = endpoint.walk([&](Operation *op) -> WalkResult {
      if (!remaining--) {
        (void)refuse(op, "native endpoint work limit");
        return WalkResult::interrupt();
      }
      for (auto type : op->getResultTypes())
        if (!logical(type) || isa<poly::PolynomialType>(logical(type)) ||
            !types.get(logical(type))) {
          (void)refuse(op, "unsupported native endpoint value");
          return WalkResult::interrupt();
        }
      if (isa<protocol_ir::EmitOp, protocol_ir::AwaitOp>(op)) {
        auto type = isa<protocol_ir::EmitOp>(op) ? op->getOperand(0).getType()
                                                 : op->getResult(0).getType();
        auto policy = types.get(logical(type));
        bool representation = true;
        if (physical && algebra::isFieldArray(logical(type))) {
          auto selected = cast<plan::DataType>(type);
          representation =
              selected.getRepresentation() == "arkworks.field-array/1";
        }
        if (!policy || !policy->wire || !representation) {
          (void)refuse(op, "unsupported native wire type");
          return WalkResult::interrupt();
        }
      }
      return WalkResult::advance();
    });
    if (result.wasInterrupted())
      return failure();
  }
  return success();
}
} // namespace zkc::mathematical
