#include "ProtocolApplications.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "llvm/ADT/StringMap.h"
#include <map>
#include <set>
using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
LogicalResult expandApplications(protocol_ir::ProtocolModuleOp module,
                                 ArrayRef<ApplicationStart> starts) {
  auto fail = [&]() {
    return diagnostics::emit(module.emitError(), "protocol-construction-start",
                             "invalid selected application start");
  };
  std::map<std::pair<std::string, std::string>, const ApplicationStart *>
      selected;
  unsigned work = 1000000;
  if (starts.size() > 2048)
    return fail();
  for (const auto &start : starts) {
    auto size = start.protocol.size() + start.site.size() + start.inputs.size();
    if (start.protocol.empty() || start.protocol.size() > 4096 ||
        start.site.empty() || start.site.size() > 4096 ||
        start.inputs.size() > 1024 || size > work ||
        !selected.emplace(std::make_pair(start.protocol, start.site), &start)
             .second)
      return fail();
    work -= size;
  }
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
      auto start =
          selected.find({function.getSymName().str(), call.getSite().str()});
      if (start != selected.end()) {
        if (callee.getRoles().size() != 2)
          return fail();
        SmallVector<Value> inputs;
        std::set<unsigned> seen;
        for (unsigned port : start->second->inputs) {
          if (port >= callee.getFunctionType().getNumInputs() ||
              !seen.insert(port).second)
            return fail();
          auto owners = cast<ArrayAttr>(callee.getInputRoles()[port]);
          auto argument = callee.getBody().front().getArgument(port);
          if (owners.size() != callee.getRoles().size() ||
              isa<protocol_ir::ServiceReferenceType>(argument.getType()) ||
              !all_of(callee.getRoles(),
                      [&](Attribute r) { return is_contained(owners, r); }))
            return fail();
          inputs.push_back(values.lookup(argument));
        }
        protocol_ir::ConstructionStartOp::create(
            builder, call.getLoc(), inputs, call.getRoles(), call.getSite());
        selected.erase(start);
      }
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
          } else if (auto constructed =
                         dyn_cast<protocol_ir::OracleVirtualOp>(copy)) {
            constructed.setHolderAttr(role(constructed.getHolderAttr()));
            constructed.setReceiversAttr(mapped(constructed.getReceivers()));
          } else if (auto send = dyn_cast<protocol_ir::OracleSendOp>(copy)) {
            send.setSenderAttr(role(send.getSenderAttr()));
            send.setReceiversAttr(mapped(send.getReceivers()));
          } else if (auto append =
                         dyn_cast<protocol_ir::OracleSequenceAppendOp>(copy)) {
            append.setRolesAttr(mapped(append.getRoles()));
          } else if (auto at =
                         dyn_cast<protocol_ir::OracleSequenceAtOp>(copy)) {
            at.setRolesAttr(mapped(at.getRoles()));
          } else if (auto contents =
                         dyn_cast<protocol_ir::OracleContentsOp>(copy)) {
            contents.setOwnerAttr(role(contents.getOwnerAttr()));
          } else if (auto query = dyn_cast<protocol_ir::OracleQueryOp>(copy)) {
            query.setOwnerAttr(role(query.getOwnerAttr()));
          } else if (auto guard = dyn_cast<protocol_ir::GuardOp>(copy)) {
            guard.setOwnerAttr(role(guard.getOwnerAttr()));
          } else if (auto query = dyn_cast<protocol_ir::QueryOp>(copy)) {
            query.setOwnerAttr(role(query.getOwnerAttr()));
          } else if (auto local = dyn_cast<protocol_ir::LocalCallOp>(copy)) {
            local.setRoleAttr(role(local.getRoleAttr()));
          } else if (auto view = dyn_cast<protocol_ir::RestrictRolesOp>(copy)) {
            view.setRolesAttr(mapped(view.getRoles()));
          } else if (auto start =
                         dyn_cast<protocol_ir::ConstructionStartOp>(copy)) {
            start.setRolesAttr(mapped(start.getRoles()));
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
  return selected.empty() ? success() : fail();
}
} // namespace zkc::mathematical
