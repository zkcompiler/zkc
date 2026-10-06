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
LogicalResult declarations(Operation *user, ArrayAttr array, Bindings &out) {
  if (!array)
    return diagnostics::emit(user->emitOpError(),
                             "interactive-binding-attribute");
  for (auto item : array) {
    auto record = dyn_cast<ArrayAttr>(item);
    if (!record || record.size() != 3 || !isa<StringAttr>(record[0]) ||
        !isa<FlatSymbolRefAttr>(record[1]) || !isa<ArrayAttr>(record[2]))
      return diagnostics::emit(user->emitOpError(),
                               "interactive-binding-attribute",
                               "expected dependency alias, symbol, agreements");
    Bindings agreements;
    if (failed(bindings(user, cast<ArrayAttr>(record[2]), false, agreements)))
      return failure();
    if (!out.try_emplace(cast<StringAttr>(record[0]).getValue(), record[1])
             .second)
      return diagnostics::emit(user->emitOpError(),
                               "interactive-binding-attribute",
                               "duplicate dependency alias");
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
LogicalResult argumentNames(Operation *definition, FunctionType type) {
  auto attr = definition->getAttrOfType<ArrayAttr>("argument_names");
  if (!attr && !definition->hasAttr("argument_names"))
    return success();
  llvm::StringSet<> seen;
  if (!attr || attr.size() != type.getNumInputs())
    return diagnostics::emit(definition->emitOpError(),
                             "interactive-family-argument-names");
  for (auto item : attr) {
    auto name = dyn_cast<StringAttr>(item);
    if (!name || name.getValue().empty() ||
        !seen.insert(name.getValue()).second)
      return diagnostics::emit(definition->emitOpError(),
                               "interactive-family-argument-names");
  }
  return success();
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
LogicalResult callableBody(Operation *op, Region &body, FunctionType type,
                           bool external) {
  if (external)
    return body.empty() ? success()
                        : diagnostics::emit(op->emitOpError(),
                                            "interactive-external-body");
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
  } else if (isa<zkc::protocol_ir::ParticipantOp>(op)
                 ? !isa<zkc::local::StopOp, zkc::protocol_ir::IncompleteOp>(end)
                 : !isa<zkc::protocol_ir::HaltOp>(end))
    return diagnostics::emit(op->emitOpError(),
                             "interactive-callable-terminator");
  return success();
}
LogicalResult sharedRoles(Operation *user, zkc::protocol_ir::ExecFuncOp caller,
                          zkc::protocol_ir::ExecFuncOp callee) {
  llvm::StringSet<> parent, child;
  if (failed(names(user, caller.getRolesAttr(), parent)) ||
      failed(names(user, callee.getRolesAttr(), child)))
    return failure();
  for (const auto &role : child)
    if (!parent.contains(role.getKey()))
      return diagnostics::emit(
          user->emitOpError(), "interactive-dependency-role",
          "child formal role is absent in caller: " + role.getKey());
  return success();
}

// Only the MLIR symbol boundary is checked here. Whole-body, dependency and
// bundle consistency checks remain in Source admission through module export.
struct SelectorOwner {
  Operation *definition;
  // Common input_roles are formal; selector roles are actual instance roles.
  StringRef formal;
};
using SelectorOwners = llvm::StringMap<SelectorOwner>;
bool canonicalNatural(Attribute attr) {
  auto text = dyn_cast<StringAttr>(attr);
  if (!text)
    return false;
  auto s = text.getValue();
  return !s.empty() && (s.size() == 1 || s.front() != '0') &&
         llvm::all_of(s, [](char c) { return isDigit(c); });
}
// A canonical natural within the family bound.
bool familyBound(Attribute attr) {
  uint64_t n;
  return !cast<StringAttr>(attr).getValue().getAsInteger(10, n) && n <= 1048576;
}
bool familyNatural(Attribute attr) {
  return canonicalNatural(attr) && familyBound(attr);
}
LogicalResult selectorInputs(Operation *user, ArrayAttr arguments,
                             const SelectorOwner &owner,
                             SmallVectorImpl<Type> &inputs) {
  auto *definition = owner.definition;
  auto ft = signature(definition);
  if (!ft)
    return diagnostics::emit(user->emitOpError(), "interactive-callable-type");
  if (failed(argumentNames(definition, ft)))
    return failure();
  auto ports = definition->getAttrOfType<ArrayAttr>("argument_names");
  if (!ports)
    return diagnostics::emit(user->emitOpError(),
                             "interactive-family-argument-names");
  auto roles = definition->getAttrOfType<ArrayAttr>("input_roles");
  if (!owner.formal.empty() && (!roles || roles.size() != ports.size()))
    return diagnostics::emit(user->emitOpError(), "interactive-port-roles");
  llvm::StringSet<> seen;
  for (auto item : arguments) {
    auto name = dyn_cast<StringAttr>(item);
    if (!name || name.getValue().empty() ||
        !seen.insert(name.getValue()).second)
      return diagnostics::emit(user->emitOpError(),
                               "interactive-family-argument");
    auto found = llvm::find(ports, name);
    if (found == ports.end())
      return diagnostics::emit(user->emitOpError(),
                               "interactive-family-argument");
    unsigned i = found - ports.begin();
    if (!owner.formal.empty() &&
        roles[i] != StringAttr::get(user->getContext(), owner.formal))
      return diagnostics::emit(user->emitOpError(), "interactive-family-input");
    Type type = ft.getInput(i);
    auto bound =
        protocol::encodeBoundType(type, isa<zkc::plan::DataType>(type));
    if (!bound) {
      llvm::consumeError(bound.takeError());
      return diagnostics::emit(user->emitOpError(), "interactive-family-input");
    }
    if (!protocol::serializable(bound->spelling()))
      return diagnostics::emit(user->emitOpError(), "interactive-family-input");
    inputs.push_back(type);
  }
  return success();
}
LogicalResult familyParameters(Operation *user, ArrayAttr parameters,
                               const SelectorOwners &owners,
                               SymbolTableCollection &tables,
                               const llvm::StringSet<> *declared = nullptr) {
  if (!parameters)
    return diagnostics::emit(user->emitOpError(), "interactive-family-binding");
  llvm::StringSet<> keys;
  for (auto item : parameters) {
    auto pair = dyn_cast<ArrayAttr>(item);
    if (!pair || pair.size() != 2 || !isa<StringAttr>(pair[0]))
      return diagnostics::emit(user->emitOpError(),
                               "interactive-family-binding");
    auto key = cast<StringAttr>(pair[0]).getValue();
    if (key.empty() || !keys.insert(key).second ||
        (declared && !declared->contains(key)))
      return diagnostics::emit(user->emitOpError(),
                               "interactive-parameter-binding");
    if (isa<StringAttr>(pair[1])) {
      if (!familyNatural(pair[1]))
        return diagnostics::emit(user->emitOpError(),
                                 "interactive-family-binding");
      continue;
    }
    auto ingress = dyn_cast<ArrayAttr>(pair[1]);
    if (!ingress || ingress.size() != 3 ||
        ingress[0] != StringAttr::get(user->getContext(), "ingress") ||
        !canonicalNatural(ingress[1]) || !isa<ArrayAttr>(ingress[2]))
      return diagnostics::emit(user->emitOpError(),
                               "interactive-family-binding");
    if (!familyBound(ingress[1]))
      return diagnostics::emit(user->emitOpError(), "interactive-family-bound");
    auto selectors = cast<ArrayAttr>(ingress[2]);
    llvm::StringSet<> selected;
    if (selectors.empty() || selectors.size() != owners.size())
      return diagnostics::emit(user->emitOpError(), "interactive-family-roles");
    for (auto item : selectors) {
      auto selector = dyn_cast<ArrayAttr>(item);
      if (!selector || selector.size() != 3 || !isa<StringAttr>(selector[0]) ||
          !isa<FlatSymbolRefAttr>(selector[1]) || !isa<ArrayAttr>(selector[2]))
        return diagnostics::emit(user->emitOpError(),
                                 "interactive-family-binding");
      auto role = cast<StringAttr>(selector[0]).getValue();
      auto owner = owners.find(role);
      if (owner == owners.end() || !selected.insert(role).second)
        return diagnostics::emit(user->emitOpError(),
                                 "interactive-family-roles");
      auto function =
          dyn_cast_or_null<zkc::local::FuncOp>(tables.lookupNearestSymbolFrom(
              user, cast<FlatSymbolRefAttr>(selector[1])));
      if (!function || function->getNumRegions() != 1 ||
          function->getRegion(0).empty())
        return diagnostics::emit(user->emitOpError(),
                                 "interactive-family-selector");
      auto ft = signature(function);
      if (!ft || ft.getNumResults() != 1)
        return diagnostics::emit(user->emitOpError(),
                                 "interactive-family-signature");
      Type result = ft.getResult(0);
      if (auto data = dyn_cast<zkc::plan::DataType>(result))
        result = data.getLogical();
      if (!result.isUnsignedInteger(64))
        return diagnostics::emit(user->emitOpError(),
                                 "interactive-family-signature");
      SmallVector<Type> inputs;
      if (failed(selectorInputs(user, cast<ArrayAttr>(selector[2]),
                                owner->second, inputs)))
        return failure();
      if (ft.getInputs() != ArrayRef<Type>(inputs))
        return diagnostics::emit(user->emitOpError(),
                                 "interactive-family-signature");
    }
  }
  if (declared && keys.size() != declared->size())
    return diagnostics::emit(user->emitOpError(),
                             "interactive-parameter-binding");
  return success();
}
} // namespace

LogicalResult zkc::protocol_ir::ExecFuncOp::verifyRegions() {
  if (failed(argumentNames(*this, getFunctionType())))
    return failure();
  if (getInputRoles().size() != getFunctionType().getNumInputs() ||
      getOutputRoles().size() != getFunctionType().getNumResults())
    return diagnostics::emit(emitOpError(), "interactive-port-roles");
  return callableBody(*this, getBody(), getFunctionType(), getExternal());
}

LogicalResult zkc::protocol_ir::ParticipantOp::verifyRegions() {
  if (failed(argumentNames(*this, getFunctionType())))
    return failure();
  return callableBody(*this, getBody(), getFunctionType(), false);
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
  bool dynamic = bool(getMaximum());
  unsigned offset = dynamic ? 1 : 0;
  if ((dynamic && *getMaximum() > 1048576) ||
      (dynamic &&
       (getInputs().empty() || getParameter() || !getCount().empty())))
    return diagnostics::emit(emitOpError(), "interactive-loop-count");
  if (dynamic) {
    Type type = getInputs().front().getType();
    if (auto physical = dyn_cast<plan::DataType>(type))
      type = physical.getLogical();
    if (!type.isUnsignedInteger(64))
      return diagnostics::emit(emitOpError(), "interactive-loop-count");
  }
  if (carried < 0 || size_t(carried) + offset > getNumOperands() ||
      size_t(carried) != getNumResults() ||
      getOperands().slice(offset, carried).getTypes() != getResultTypes())
    return diagnostics::emit(emitOpError(), "interactive-loop-carried");
  auto count = getCount();
  if (getParameter()) {
    if (count.empty() || !(isAlpha(count.front()) || count.front() == '_') ||
        !all_of(count, [](char c) {
          return isAlnum(c) || c == '_' || c == '.' || c == '-';
        }))
      return diagnostics::emit(emitOpError(), "interactive-loop-count");
    Operation *owner = (*this)->getParentOp();
    while (owner && isa<zkc::protocol_ir::ProtocolLoopOp>(owner))
      owner = owner->getParentOp();
    auto parameters =
        owner ? owner->getAttrOfType<ArrayAttr>("parameters") : ArrayAttr();
    bool declared = parameters && llvm::any_of(parameters, [&](Attribute a) {
                      if (auto pair = dyn_cast<ArrayAttr>(a))
                        return pair.size() == 2 &&
                               pair[0] == StringAttr::get(getContext(), count);
                      return a == StringAttr::get(getContext(), count);
                    });
    if (!declared)
      return diagnostics::emit(emitOpError(), "interactive-loop-parameter");
  } else if (!dynamic) {
    uint64_t value;
    if (count.empty() || (count.size() > 1 && count.front() == '0') ||
        !all_of(count, [](char c) { return isDigit(c); }) ||
        count.getAsInteger(10, value) || value > 1048576)
      return diagnostics::emit(emitOpError(), "interactive-loop-count");
  }
  if (getBody().empty() || getBody().front().empty() ||
      getBody().front().getArgumentTypes() != getOperandTypes())
    return diagnostics::emit(emitOpError(), "interactive-loop-arguments");
  auto *end = getBody().front().getTerminator();
  if (auto yield = dyn_cast<zkc::protocol_ir::ProtocolYieldOp>(end)) {
    if (yield.getOperandTypes() != getResultTypes())
      return diagnostics::emit(yield.emitOpError(), "interactive-loop-yield");
  } else if ((*this)->getParentOfType<zkc::protocol_ir::ParticipantOp>()
                 ? !isa<zkc::local::StopOp, zkc::protocol_ir::IncompleteOp>(end)
                 : !isa<zkc::protocol_ir::HaltOp>(end))
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
  if (auto caller = (*this)->getParentOfType<zkc::protocol_ir::ExecFuncOp>()) {
    llvm::StringSet<> roles;
    if (failed(names(*this, caller.getRolesAttr(), roles)))
      return failure();
    if (!getRoleAttr() || !roles.contains(getRoleAttr().getValue()))
      return diagnostics::emit(emitOpError(), "interactive-local-role");
  } else if (auto caller =
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

LogicalResult zkc::protocol_ir::ParticipantCallOp::verifySymbolUses(
    SymbolTableCollection &tables) {
  auto callee =
      resolve<zkc::protocol_ir::ParticipantOp>(*this, getCalleeAttr(), tables);
  if (!callee)
    return failure();
  auto caller = (*this)->getParentOfType<zkc::protocol_ir::ParticipantOp>();
  if (!caller || !caller.getRoleAttr() || !callee.getRoleAttr() ||
      caller.getRoleAttr() != callee.getRoleAttr())
    return diagnostics::emit(emitOpError(), "interactive-call-role");
  // Supplied participants may call another instance at the same actual role.
  // Generated selected-dependency correspondence belongs to the source checker.
  return callSignature(*this, callee);
}

LogicalResult
zkc::protocol_ir::ExecFuncOp::verifySymbolUses(SymbolTableCollection &tables) {
  Bindings dependencies;
  if (failed(declarations(*this, getDependenciesAttr(), dependencies)))
    return failure();
  for (const auto &binding : dependencies) {
    auto callee = resolve<zkc::protocol_ir::ExecFuncOp>(
        *this, cast<FlatSymbolRefAttr>(binding.second), tables);
    if (!callee)
      return failure();
    if (!signature(callee))
      return diagnostics::emit(emitOpError(), "interactive-callable-type");
    if (failed(sharedRoles(*this, *this, callee)))
      return failure();
  }
  return success();
}

LogicalResult zkc::protocol_ir::ProtocolCallOp::verifySymbolUses(
    SymbolTableCollection &tables) {
  auto caller = (*this)->getParentOfType<zkc::protocol_ir::ExecFuncOp>();
  if (!caller)
    return diagnostics::emit(emitOpError(), "interactive-dependency",
                             "expected enclosing protocol.exec_func");
  Bindings dependencies;
  if (failed(declarations(*this, caller.getDependenciesAttr(), dependencies)))
    return failure();
  // The call's string is a local alias. The declaration owns the real
  // SymbolRef.
  auto selected = dependencies.find(getDependency());
  if (selected == dependencies.end())
    return diagnostics::emit(emitOpError(), "interactive-dependency",
                             "undeclared alias " + getDependency());
  auto callee = resolve<zkc::protocol_ir::ExecFuncOp>(
      *this, cast<FlatSymbolRefAttr>(selected->second), tables, caller);
  if (!callee || failed(sharedRoles(*this, caller, callee)))
    return failure();
  return callSignature(*this, callee);
}

LogicalResult
zkc::protocol_ir::InstanceOp::verifySymbolUses(SymbolTableCollection &tables) {
  auto definition =
      resolve<zkc::protocol_ir::ExecFuncOp>(*this, getProtocolAttr(), tables);
  if (!definition)
    return failure();
  if (!signature(definition))
    return diagnostics::emit(emitOpError(), "interactive-callable-type");
  Bindings expected, actual, roles;
  llvm::StringSet<> formal;
  if (failed(declarations(*this, definition.getDependenciesAttr(), expected)) ||
      failed(bindings(*this, getDependenciesAttr(), true, actual)) ||
      failed(bindings(*this, getRolesAttr(), false, roles)) ||
      failed(names(*this, definition.getRolesAttr(), formal)))
    return failure();
  llvm::StringSet<> assigned;
  if (roles.size() != formal.size())
    return diagnostics::emit(emitOpError(), "interactive-role-binding");
  for (const auto &binding : roles)
    if (!formal.contains(binding.getKey()) ||
        !assigned.insert(cast<StringAttr>(binding.second).getValue()).second)
      return diagnostics::emit(emitOpError(), "interactive-role-binding");
  llvm::StringSet<> parameters;
  if (failed(names(*this, definition.getParametersAttr(), parameters)))
    return failure();
  SelectorOwners owners;
  for (const auto &binding : roles)
    owners.try_emplace(cast<StringAttr>(binding.second).getValue(),
                       SelectorOwner{definition, binding.getKey()});
  if (failed(familyParameters(*this, getParametersAttr(), owners, tables,
                              &parameters)))
    return failure();
  if (expected.size() != actual.size())
    return diagnostics::emit(emitOpError(), "interactive-dependency-binding");
  for (const auto &binding : expected) {
    auto selection = actual.find(binding.getKey());
    if (selection == actual.end())
      return diagnostics::emit(emitOpError(), "interactive-dependency-binding",
                               "missing alias " + binding.getKey());
    auto expectedDef = resolve<zkc::protocol_ir::ExecFuncOp>(
        *this, cast<FlatSymbolRefAttr>(binding.second), tables, definition);
    auto child = resolve<zkc::protocol_ir::InstanceOp>(
        *this, cast<FlatSymbolRefAttr>(selection->second), tables);
    if (!expectedDef || !child)
      return failure();
    auto actualDef = resolve<zkc::protocol_ir::ExecFuncOp>(
        child, child.getProtocolAttr(), tables);
    if (!actualDef)
      return diagnostics::emit(emitOpError(), "interactive-dependency-protocol",
                               "invalid selected instance");
    if (actualDef != expectedDef)
      return diagnostics::emit(emitOpError(),
                               "interactive-dependency-protocol");
    Bindings childRoles;
    if (failed(bindings(*this, child.getRolesAttr(), false, childRoles)))
      return failure();
    for (const auto &role : childRoles) {
      auto parent = roles.find(role.getKey());
      if (parent == roles.end() || parent->second != role.second)
        return diagnostics::emit(emitOpError(), "interactive-dependency-role");
    }
  }
  return success();
}

LogicalResult zkc::protocol_ir::ParticipantOp::verifySymbolUses(
    SymbolTableCollection &tables) {
  // Projection retains the complete selection bundle. Resolve each actual
  // role's arguments at its sibling, never against this role's SSA ports.
  SelectorOwners owners;
  auto parameters = getParametersAttr();
  bool hasSelectors =
      parameters && llvm::any_of(parameters, [](Attribute item) {
        auto pair = dyn_cast<ArrayAttr>(item);
        return pair && pair.size() == 2 && !isa<StringAttr>(pair[1]);
      });
  // Static participants have no selector symbol uses and need no sibling
  // bundle. Keep their existing independent callable verification unchanged.
  if (!hasSelectors)
    return familyParameters(*this, parameters, owners, tables);
  auto instance = getInstanceAttr();
  auto *scope = SymbolTable::getNearestSymbolTable(*this);
  if (!instance || !scope || scope->getNumRegions() != 1)
    return diagnostics::emit(emitOpError(), "interactive-family-roles");
  for (auto &block : scope->getRegion(0))
    for (auto &op : block)
      if (isa<zkc::protocol_ir::ParticipantOp>(op) &&
          op.getAttrOfType<StringAttr>("instance") == instance) {
        auto role = op.getAttrOfType<StringAttr>("role");
        if (!role || role.getValue().empty() ||
            !owners.try_emplace(role.getValue(), SelectorOwner{&op, {}}).second)
          return diagnostics::emit(emitOpError(), "interactive-family-roles");
      }
  return familyParameters(*this, parameters, owners, tables);
}

LogicalResult zkc::protocol_ir::ProtocolEntryOp::verifySymbolUses(
    SymbolTableCollection &tables) {
  auto module = (*this)->getParentOfType<zkc::protocol_ir::ProtocolModuleOp>();
  auto targets = getTargetsAttr();
  if (!module || !module.getProfileAttr() || !targets || targets.empty())
    return diagnostics::emit(emitOpError(), "interactive-entry-targets");
  if (module.getProfile() == zkc::protocol_ir::Profile::ProtocolExec) {
    if (targets.size() != 1 || !isa<FlatSymbolRefAttr>(targets[0]))
      return diagnostics::emit(emitOpError(), "interactive-entry-targets");
    return success(bool(resolve<zkc::protocol_ir::InstanceOp>(
        *this, cast<FlatSymbolRefAttr>(targets[0]), tables)));
  }
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
  if (getExecutionContract() && isProgram(*getExecutionContract()) &&
      failed(mathematical::verifyNativeExecution(*this, types)))
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
