#include "ProtocolApplications.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "llvm/ADT/StringMap.h"
using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
LogicalResult expandApplications(protocol_ir::ProtocolModuleOp module) {
  if (failed(verifyApplications(module)))
    return failure();
  // Snapshot definitions: expanding one caller never changes a later callee's
  // meaning or site prefix. The bounded queue expands each call occurrence.
  OwningOpRef<protocol_ir::ProtocolModuleOp> source(
      cast<protocol_ir::ProtocolModuleOp>(module->clone()));
  SymbolTable symbols(*source);
  NativeTypePolicies policies(module);
  for (auto function :
       module.getBody().front().getOps<protocol_ir::MathematicalOp>()) {
    SmallVector<protocol_ir::ApplyOp> pending;
    function.walk([&](protocol_ir::ApplyOp call) { pending.push_back(call); });
    while (!pending.empty()) {
      auto call = pending.pop_back_val();
      auto callee =
          cast<protocol_ir::MathematicalOp>(symbols.lookup(call.getCallee()));
      StringMap<Attribute> roles;
      for (auto [original, replacement] :
           zip(callee.getRoles(), call.getRoles()))
        roles[cast<StringAttr>(original).getValue()] = replacement;
      auto mapped = [&](ArrayAttr set) {
        SmallVector<Attribute> values;
        for (auto role : set)
          values.push_back(roles.lookup(cast<StringAttr>(role).getValue()));
        return ArrayAttr::get(module.getContext(), values);
      };
      OpBuilder builder(call);
      IRMapping values;
      auto restrict = [&](Value value, ArrayAttr owners) -> Value {
        // Owner-local inputs already have exactly one role; services remain
        // the original caller block arguments, so query state is shared.
        if (isa<protocol_ir::ServiceReferenceType>(value.getType()))
          return value;
        auto policy = policies.get(value.getType());
        if (!policy || !policy->shared)
          return value;
        return protocol_ir::RestrictRolesOp::create(
                   builder, call.getLoc(), value.getType(), value, owners)
            .getOutput();
      };
      for (auto [argument, input, owners] :
           zip(callee.getBody().front().getArguments(), call.getInputs(),
               callee.getInputRoles()))
        values.map(argument, restrict(input, mapped(cast<ArrayAttr>(owners))));
      for (auto &op : callee.getBody().front().without_terminator()) {
        auto *copy = builder.clone(op, values);
        auto renamed = copy->walk<WalkOrder::PreOrder>([&](Operation *copy)
                                                           -> WalkResult {
          copy->setLoc(CallSiteLoc::get(copy->getLoc(), call.getLoc()));
          auto role = [&](StringAttr name) {
            return cast<StringAttr>(roles.lookup(name.getValue()));
          };
          // Use typed accessors so renaming an ODS role attribute cannot
          // silently skip substitution when caller and callee rosters overlap.
          if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(copy)) {
            repeat.setRolesAttr(mapped(repeat.getRoles()));
            SmallVector<Attribute> carried;
            for (auto owners : repeat.getCarriedRoles())
              carried.push_back(mapped(cast<ArrayAttr>(owners)));
            repeat.setCarriedRolesAttr(builder.getArrayAttr(carried));
          } else if (auto exchange = dyn_cast<protocol_ir::ExchangeOp>(copy)) {
            exchange.setSenderAttr(role(exchange.getSenderAttr()));
            exchange.setReceiverAttr(role(exchange.getReceiverAttr()));
          } else if (auto guard = dyn_cast<protocol_ir::GuardOp>(copy)) {
            guard.setOwnerAttr(role(guard.getOwnerAttr()));
          } else if (auto query = dyn_cast<protocol_ir::QueryOp>(copy)) {
            query.setOwnerAttr(role(query.getOwnerAttr()));
          } else if (auto local = dyn_cast<protocol_ir::LocalCallOp>(copy)) {
            local.setRoleAttr(role(local.getRoleAttr()));
          } else if (auto view = dyn_cast<protocol_ir::RestrictRolesOp>(copy)) {
            view.setRolesAttr(mapped(view.getRoles()));
          } else if (auto nested = dyn_cast<protocol_ir::ApplyOp>(copy)) {
            nested.setRolesAttr(mapped(nested.getRoles()));
          }
          if (auto attr = copy->getAttrOfType<StringAttr>("site")) {
            auto site =
                expandedApplicationSite(call.getSite(), attr.getValue());
            if (site.size() > 4096)
              return WalkResult(
                  diagnostics::emit(call.emitOpError(), "protocol-application",
                                    "expanded site exceeds 4096 bytes"));
            copy->setAttr("site", builder.getStringAttr(site));
          }
          if (auto nested = dyn_cast<protocol_ir::ApplyOp>(copy))
            pending.push_back(nested);
          return WalkResult::advance();
        });
        if (renamed.wasInterrupted())
          return failure();
      }
      for (auto [result, returned, owners] :
           zip(call.getOutputs(), callee.getBody().front().back().getOperands(),
               callee.getOutputRoles()))
        result.replaceAllUsesWith(
            restrict(values.lookup(returned), mapped(cast<ArrayAttr>(owners))));
      call.erase();
    }
  }
  return success();
}
} // namespace zkc::mathematical
