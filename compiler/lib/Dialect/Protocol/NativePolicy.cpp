#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "../Verification.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/DenseSet.h"
using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "native-local-policy", detail);
}
} // namespace
LogicalResult verifyNativeExecution(Operation *unit) {
  NativeTypePolicies types(unit);
  return verifyNativeExecution(unit, types);
}
LogicalResult verifyNativeExecution(Operation *unit,
                                    NativeTypePolicies &types) {
  const bool physical =
      cast<protocol_ir::ProtocolModuleOp>(unit).getProfile() ==
      protocol_ir::Profile::Physical;
  auto logical = [&](Type type) -> Type {
    if (!physical)
      return type;
    auto selected = dyn_cast<runtime::RepresentedType>(type);
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
        if (!logical(type) || mathematical::isFormalType(logical(type)) ||
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
          auto selected = cast<runtime::RepresentedType>(type);
          representation =
              selected.getRepresentation() == "arkworks.field-array/0";
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
