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
#include "llvm/ADT/StringSwitch.h"
using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
std::optional<NativeTypePolicy> policy(const protocol::BoundType &type,
                                       unsigned depth, unsigned &remaining,
                                       bool &limited, bool &copy) {
  if (!remaining || depth > 64) {
    limited = true;
    return std::nullopt;
  }
  --remaining;
  StringRef kind = type.kind;
  bool total = kind == "bool" || kind == "field" || kind == "group" ||
               kind == "field_array" || kind == "index" || kind == "indices" ||
               kind == "vector" || kind == "matrix" || kind == "groups";
  bool shared =
      total ||
      llvm::StringSwitch<bool>(kind)
          .Cases({"index", "indices", "vector", "matrix"}, true)
          .Cases({"polynomial", "table", "point", "round"}, true)
          .Cases({"groups", "commitment", "commitments", "proof"}, true)
          .Default(false);
  bool local = llvm::StringSwitch<bool>(kind)
                   .Cases({"opening_states", "prover_key", "verifier_key",
                           "opening_state"},
                          true)
                   .Cases({"rng", "nonce", "transcript", "resource_unit"}, true)
                   .Cases({"fixed_vector", "variant"}, true)
                   .Default(false);
  if (!shared && !local && kind != "sequence")
    return std::nullopt;
  // Accumulate custody and boundary facts once per child. Do not stringify
  // and reparse every subtree through the generic custody helpers.
  bool childrenCopy = true, childrenTotal = true, childrenShared = true,
       protocolPort = true;
  auto include = [&](const protocol::BoundType &child) {
    bool childCopy = false;
    auto facts = policy(child, depth + 1, remaining, limited, childCopy);
    if (!facts)
      return false;
    childrenCopy &= childCopy;
    childrenTotal &= facts->total;
    childrenShared &= facts->shared;
    protocolPort &= facts->protocolPort;
    return true;
  };
  for (const auto &argument : type.arguments)
    if (argument.kind == protocol::TypeArgument::Kind::Type &&
        !include(*argument.type))
      return std::nullopt;
  if (kind == "sequence") {
    copy = childrenCopy;
    return NativeTypePolicy{copy && childrenTotal, copy && childrenShared,
                            !copy, copy && protocolPort,
                            protocol::nativeMessageData(type)};
  }
  if (kind == "variant") {
    auto descriptor = protocol::decodeVariant(type.spelling());
    if (!descriptor)
      return std::nullopt;
    for (const auto &arm : descriptor->alternatives)
      for (const auto &leaf : arm.payload) {
        auto parsed = protocol::parseBoundType(leaf, false);
        if (!parsed) {
          consumeError(parsed.takeError());
          return std::nullopt;
        }
        if (!include(*parsed))
          return std::nullopt;
      }
    copy = childrenCopy;
    return NativeTypePolicy{copy && childrenTotal, copy && childrenShared,
                            !copy, copy && protocolPort,
                            protocol::nativeMessageData(type)};
  }
  const auto *permissions = protocol::typePermissions(kind);
  if (!permissions)
    return std::nullopt;
  copy = permissions->copy && childrenCopy;
  bool affine =
      permissions->custody == protocol::Custody::Affine || !childrenCopy;
  // A structural application does not inherit its nominal head's wire codec.
  bool wire = shared && type.arguments.empty() &&
              permissions->custody == protocol::Custody::PublicValue &&
              !protocol::defaultCodec(type).empty();
  if (kind == "field_array")
    wire = protocol::nativeFieldArrayWire(type);
  return NativeTypePolicy{total, shared, affine, protocolPort, wire};
}
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
  unsigned remaining = 200000;
  bool limited = false;
  bool copy = false;
  return policy(*logical, 0, remaining, limited, copy);
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
    bool copy = false;
    result = policy(*logical, 0, remaining, limited, copy);
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
