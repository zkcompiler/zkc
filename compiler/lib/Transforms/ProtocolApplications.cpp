#include "ProtocolApplications.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/IR/RoleAttributes.h"
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
      StringMap<StringAttr> roles;
      for (auto [original, replacement] :
           zip(callee.getRoles(), call.getRoles()))
        roles[cast<StringAttr>(original).getValue()] =
            cast<StringAttr>(replacement);
      // Verified callee role uses name only callee roles, so every role use
      // has a caller replacement.
      auto rename = [&](StringAttr role) {
        auto replacement = roles.lookup(role.getValue());
        return replacement ? replacement : role;
      };
      auto mapped = [&](Attribute set) {
        return cast<ArrayAttr>(protocol_ir::renameRoles(
            set, protocol_ir::RoleShape::RoleSet, rename));
      };
      OpBuilder builder(call);
      IRMapping values;
      auto restrict = [&](Value value, ArrayAttr owners) -> Value {
        // Owner-local inputs already have exactly one role; services remain
        // the original caller block arguments, so query state is shared.
        if (isa<protocol_ir::ServiceReferenceType>(value.getType()))
          return value;
        auto policy = policies.get(value.getType());
        if ((!policy || !policy->shared) &&
            !isa<protocol_ir::OracleHandleType,
                 protocol_ir::OracleSequenceType>(value.getType()))
          return value;
        return protocol_ir::RestrictRolesOp::create(
                   builder, call.getLoc(), value.getType(), value, owners)
            .getOutput();
      };
      for (auto [argument, input, owners] :
           zip(callee.getBody().front().getArguments(), call.getInputs(),
               callee.getInputRoles()))
        values.map(argument, restrict(input, mapped(owners)));
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
        auto renamed =
            copy->walk<WalkOrder::PreOrder>([&](Operation *copy) -> WalkResult {
              copy->setLoc(CallSiteLoc::get(copy->getLoc(), call.getLoc()));
              // Every declared role use, and nothing else, takes the caller
              // role.
              protocol_ir::renameRoleUses(copy, rename);
              if (auto attr = copy->getAttrOfType<StringAttr>("site")) {
                auto site =
                    expandedApplicationSite(call.getSite(), attr.getValue());
                if (site.size() > 4096)
                  return WalkResult(diagnostics::emit(
                      call.emitOpError(), "protocol-application",
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
            restrict(values.lookup(returned), mapped(owners)));
      call.erase();
    }
  }
  return selected.empty() ? success() : fail();
}
} // namespace zkc::mathematical
