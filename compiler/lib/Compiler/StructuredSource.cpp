#include "zkc/Compiler/StructuredSource.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Operations.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
using namespace mlir;

namespace zkc::protocol {
namespace {
constexpr unsigned signatureLimit = 512;
constexpr unsigned instructionLimit = 4096;
constexpr unsigned depthLimit = 64;
constexpr uint64_t staticVisitLimit = 100000;
constexpr size_t effectiveSiteByteLimit = 4096;
constexpr uint64_t staticSiteByteLimit = 16 * 1024 * 1024;

// This profile is deliberately smaller than the installed native catalogue.
// Catalogue resolution below still owns nominal arguments, full ordered ports,
// and parameters; membership alone never authorizes an execution.
bool primitiveContract(StringRef contract) {
  return llvm::is_contained(
      ArrayRef<StringRef>{"index.constant", "index.add", "index.sub",
                          "index.mul", "index.div", "index.mod", "index.equal",
                          "index.less", "vector.empty", "vector.length",
                          "vector.sum", "vector.split", "vector.append",
                          "vector.equal", "field.equal"},
      contract);
}

Expected<OperationBinding> primitiveBinding(Operation *op) {
  auto binding = readBinding(op);
  if (!binding)
    return binding.takeError();
  const auto &application = binding->application;
  if (!primitiveContract(application.contract) ||
      (StringRef(application.contract).starts_with("index.")
           ? !application.arguments.empty()
           : application.arguments != std::vector<std::string>{"bls12-381.fr"}))
    return error("structured-source-binding");
  if (!application.implementation.empty())
    return error("structured-source-implementation");
  auto resolved = resolveLogicalBinding(application);
  if (!resolved)
    return resolved.takeError();
  return std::move(*binding);
}

Error attributes(Operation &op, ArrayRef<StringRef> allowed) {
  for (NamedAttribute attr : op.getAttrs()) {
    if (!llvm::is_contained(allowed, attr.getName().getValue()))
      return error("structured-source-attribute", attr.getName().getValue());
    bool valid = true, bounded = true;
    attr.getValue().walk([&](StringAttr string) {
      valid &= json::isUTF8(string.getValue());
      bounded &= string.getValue().size() <= 512;
    });
    // MLIR strings can contain arbitrary bytes. LLVM's JSON constructor
    // asserts or repairs invalid UTF-8; neither is a faithful source export.
    if (!valid)
      return error("structured-source-string");
    if (!bounded)
      return error("structured-source-limit");
  }
  return Error::success();
}

// Called only for the dialect-verified, bounded declaration contract layout.
json::Value contractValue(Attribute attr) {
  if (isa<UnitAttr>(attr))
    return nullptr;
  if (auto text = dyn_cast<StringAttr>(attr))
    return text.getValue();
  if (auto symbol = dyn_cast<FlatSymbolRefAttr>(attr))
    return symbol.getValue();
  if (auto index = dyn_cast<IntegerAttr>(attr))
    return index.getInt();
  json::Array values;
  for (Attribute value : cast<ArrayAttr>(attr))
    values.push_back(contractValue(value));
  return values;
}

Expected<json::Value> sort(Type type) {
  if (type.isSignlessInteger(1))
    return json::Array{"bool"};
  if (type.isUnsignedInteger(64))
    return json::Array{"index"};
  if (auto field = dyn_cast<algebra::FieldType>(type)) {
    if (field.getDomain() == "bls12-381.fr")
      return json::Array{"field", field.getDomain()};
  }
  if (auto vector = dyn_cast<algebra::FieldVectorType>(type)) {
    if (vector.getDomain() == "bls12-381.fr")
      return json::Array{"vector", vector.getDomain()};
  }
  if (auto group = dyn_cast<algebra::GroupType>(type)) {
    if (group.getDomain() == "bls12-381.g1")
      return json::Array{"group", group.getDomain()};
  }
  if (auto service = dyn_cast<protocol_ir::ServiceReferenceType>(type)) {
    if (service.getContract() == "random.bls12-381.fr/0")
      return json::Array{"service", service.getContract()};
  }
  return error("structured-source-type");
}

Expected<json::Array> sorts(TypeRange types, bool services = false) {
  if (types.size() > signatureLimit)
    return error("structured-source-limit");
  json::Array result;
  for (Type type : types) {
    if (!services && isa<protocol_ir::ServiceReferenceType>(type))
      return error("structured-source-service");
    auto encoded = sort(type);
    if (!encoded)
      return encoded.takeError();
    result.push_back(std::move(*encoded));
  }
  return result;
}

// Count lexical JSON arrays, rather than only native region nesting. A native
// region contributes several wire arrays. Strings are checked as UTF-8 bytes.
bool boundedWire(const json::Value &value, unsigned depth = 0) {
  if (auto string = value.getAsString())
    return string->size() <= 512;
  if (auto array = value.getAsArray()) {
    if (++depth > depthLimit)
      return false;
    return llvm::all_of(*array, [&](const json::Value &child) {
      return boundedWire(child, depth);
    });
  }
  return true;
}

FunctionType signature(Operation &op) {
  auto attr = op.getAttrOfType<TypeAttr>("function_type");
  return attr ? dyn_cast<FunctionType>(attr.getValue()) : FunctionType();
}

StringRef kind(Operation &op) {
  if (isa<protocol_ir::MathematicalOp>(op))
    return "protocol";
  if (isa<func::FuncOp>(op))
    return "math";
  if (isa<local::FuncOp>(op))
    return "local";
  if (isa<local::FiniteFoldOp>(op))
    return "finite";
  if (isa<local::RealizeOp>(op))
    return "realize";
  if (isa<algebra::MapRealizeOp>(op))
    return "map";
  if (isa<data::DomainOp>(op))
    return "domain";
  return "";
}

Expected<StringRef> visibility(Operation &op) {
  auto attr = op.getAttrOfType<StringAttr>("sym_visibility");
  if (!attr)
    return StringRef("public");
  if (attr.getValue() != "public" && attr.getValue() != "private")
    return error("structured-source-visibility");
  return attr.getValue();
}

class Exporter {
  protocol_ir::ProtocolModuleOp unit;
  protocol_ir::MathematicalOp selected;
  SymbolTable symbols;
  ArrayAttr roles;
  Operation *definition = nullptr;
  llvm::StringSet<> sites;
  llvm::DenseMap<Operation *, SmallVector<Operation *>> dependencies;
  unsigned instructions = 0;

  Expected<StringRef> reference(Operation &op, StringRef attribute,
                                ArrayRef<StringRef> allowedKinds,
                                bool optional = false) {
    if (optional && !op.hasAttr(attribute))
      return StringRef("");
    auto ref = op.getAttrOfType<FlatSymbolRefAttr>(attribute);
    Operation *callee = ref ? symbols.lookup(ref.getValue()) : nullptr;
    if (!callee || callee == selected.getOperation() ||
        !llvm::is_contained(allowedKinds, kind(*callee)))
      return error("structured-source-reference");
    dependencies[definition].push_back(callee);
    return ref.getValue();
  }

  Expected<StringRef> site(Operation &op) {
    auto attr = op.getAttrOfType<StringAttr>("site");
    if (!attr || attr.getValue().empty() ||
        !sites.insert(attr.getValue()).second)
      return error("structured-source-site");
    return attr.getValue();
  }

  bool hasRole(StringRef role) const {
    return roles &&
           llvm::is_contained(roles, StringAttr::get(roles.getContext(), role));
  }

  json::Array names(ArrayAttr values) {
    json::Array result;
    for (Attribute value : values)
      result.push_back(cast<StringAttr>(value).getValue());
    return result;
  }

  Expected<json::Array> interface(protocol_ir::MathematicalOp function) {
    roles = function.getRoles();
    // Native verification owns uniqueness, nonempty scopes and port shape.
    if (roles.empty() || roles.size() > 16)
      return error("structured-source-role");
    json::Array inputs, outputs;
    for (Attribute scope : function.getInputRoles())
      inputs.push_back(names(cast<ArrayAttr>(scope)));
    for (Attribute scope : function.getOutputRoles())
      outputs.push_back(names(cast<ArrayAttr>(scope)));
    return json::Array{"protocol", names(roles), std::move(inputs),
                       std::move(outputs)};
  }

  Expected<json::Array> fold(Operation &op) {
    auto domain = reference(op, "domain", {"domain"});
    if (!domain)
      return domain.takeError();
    StringRef helperKind = isa<local::FiniteFoldOp>(op) ? "local" : "math";
    auto step = reference(op, "step", {helperKind});
    if (!step)
      return step.takeError();
    auto predicate = reference(op, "predicate", {helperKind}, true);
    if (!predicate)
      return predicate.takeError();
    return json::Array{*domain, *step, *predicate};
  }

  Expected<json::Value> descriptor(Operation &op, StringRef owner) {
    // Each branch checks exactly the attributes represented by its descriptor.
    // Inherent attributes and discardable attributes share this whitelist.
    auto field = [&]() {
      return cast<algebra::FieldType>(op.getOperand(0).getType()).getDomain();
    };
    if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(op)) {
      // Native formation already checked nested active rosters and state
      // scopes.
      if (auto e = attributes(
              op, {"site", "carried", "maximum", "roles", "carried_roles"}))
        return std::move(e);
      if (owner != "protocol")
        return error("structured-source-operation");
      json::Array scopes;
      for (Attribute scope : repeat.getCarriedRoles())
        scopes.push_back(names(cast<ArrayAttr>(scope)));
      return json::Array{"protocol_repeat", repeat.getCarried(),
                         repeat.getMaximum(), names(repeat.getRoles()),
                         std::move(scopes)};
    }
    if (auto application = dyn_cast<protocol_ir::ApplyOp>(op)) {
      if (auto e = attributes(op, {"callee", "roles", "site"}))
        return std::move(e);
      auto callee =
          symbols.lookup<protocol_ir::MathematicalOp>(application.getCallee());
      if (owner != "protocol" || !callee || op.getNumRegions())
        return error("structured-source-reference");
      auto type = callee.getFunctionType();
      if (op.getOperandTypes() != type.getInputs() ||
          op.getResultTypes() != type.getResults() ||
          application.getRoles().size() != callee.getRoles().size())
        return error("structured-source-application");
      llvm::StringSet<> mapped;
      for (Attribute role : application.getRoles()) {
        auto name = cast<StringAttr>(role).getValue();
        if (!hasRole(name) || !mapped.insert(name).second)
          return error("structured-source-application");
      }
      if (!callee.getBody().front().getOps<protocol_ir::StatementOp>().empty())
        return error("structured-source-application");
      // Selection is an observation root, not a helper kind. A different,
      // acyclic protocol may invoke the selected statement-free protocol.
      dependencies[definition].push_back(callee);
      return json::Array{"protocol_apply", application.getCallee(),
                         names(application.getRoles())};
    }
    if (isa<data::IndexOp, data::EqualOp>(op)) {
      bool constant = isa<data::IndexOp>(op);
      if (owner != "protocol" && owner != "math")
        return error("structured-source-operation");
      if (auto e = attributes(op, constant ? ArrayRef<StringRef>{"value"}
                                           : ArrayRef<StringRef>{}))
        return std::move(e);
      if (constant)
        return json::Array{"index.constant",
                           cast<data::IndexOp>(op).getValue()};
      return json::Array{"index.equal"};
    }
    StringRef operation = op.getName().getStringRef();
    if (operation.starts_with("algebra.exec.")) {
      if (owner != "local")
        return error("structured-source-operation");
      if (auto e = attributes(op, {"binding", "parameters", "site"}))
        return std::move(e);
      auto ref = op.getAttrOfType<FlatSymbolRefAttr>("binding");
      auto binding =
          primitiveBinding(ref ? symbols.lookup(ref.getValue()) : nullptr);
      if (!binding)
        return binding.takeError();
      std::string expected = "algebra.exec." + binding->application.contract;
      std::replace(expected.begin() + StringRef("algebra.exec.").size(),
                   expected.end(), '.', '_');
      if (operation != expected ||
          operation != boundOperationName(binding->application.contract) ||
          !operationSupportsContract(operation, binding->application.contract))
        return error("structured-source-binding");
      auto resolved = resolveLogicalBinding(binding->application);
      if (!resolved)
        return resolved.takeError();
      auto ports = [&](TypeRange types, ArrayRef<BoundType> expected) -> Error {
        if (types.size() != expected.size())
          return error("structured-source-binding");
        for (auto [type, port] : llvm::zip(types, expected)) {
          auto encoded = encodeBoundType(type, false);
          if (!encoded)
            return encoded.takeError();
          if (!(*encoded == port))
            return error("structured-source-binding");
        }
        return Error::success();
      };
      if (auto e = ports(op.getOperandTypes(), resolved->inputs))
        return std::move(e);
      if (auto e = ports(op.getResultTypes(), resolved->outputs))
        return std::move(e);
      auto parameters = op.getAttrOfType<ArrayAttr>("parameters");
      if (!parameters)
        return error("structured-source-binding");
      std::vector<std::string> values;
      for (Attribute parameter : parameters) {
        auto text = dyn_cast<StringAttr>(parameter);
        if (!text)
          return error("structured-source-binding");
        values.push_back(text.getValue().str());
      }
      if (auto e = checkParameters(binding->application, values))
        return std::move(e);
      return json::Array{"exec", operation, binding->name, names(parameters)};
    }
    if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op)) {
      if (auto e = attributes(op, {"value"}))
        return std::move(e);
      return json::Array{
          "field.constant",
          cast<algebra::FieldType>(constant.getResult().getType()).getDomain(),
          constant.getValue()};
    }
    StringRef fieldOpcode;
    if (isa<algebra::FieldAddOp>(op))
      fieldOpcode = "field.add";
    else if (isa<algebra::SubtractFieldOp>(op))
      fieldOpcode = "field.subtract";
    else if (isa<algebra::FieldMultiplyOp>(op))
      fieldOpcode = "field.multiply";
    else if (isa<algebra::FieldEqualOp>(op))
      fieldOpcode = "field.equal";
    if (!fieldOpcode.empty()) {
      if (auto e = attributes(op, {}))
        return std::move(e);
      return json::Array{fieldOpcode, field()};
    }
    if (isa<algebra::GroupIdentityOp, algebra::GroupAddOp,
            algebra::GroupScaleOp, algebra::GroupEqualOp>(op)) {
      if (auto e = attributes(op, {}))
        return std::move(e);
      bool identity = isa<algebra::GroupIdentityOp>(op);
      auto group = cast<algebra::GroupType>(
          identity ? op.getResult(0).getType() : op.getOperand(0).getType());
      StringRef opcode = identity                         ? "group.identity"
                         : isa<algebra::GroupAddOp>(op)   ? "group.add"
                         : isa<algebra::GroupEqualOp>(op) ? "group.equal"
                                                          : "group.scale";
      json::Array result{opcode, group.getDomain()};
      if (isa<algebra::GroupScaleOp>(op))
        result.push_back(
            cast<algebra::FieldType>(op.getOperand(1).getType()).getDomain());
      return result;
    }
    if (auto restrict = dyn_cast<protocol_ir::RestrictRolesOp>(op)) {
      if (auto e = attributes(op, {"roles"}))
        return std::move(e);
      return json::Array{"restrict", names(restrict.getRoles())};
    }
    if (auto exchange = dyn_cast<protocol_ir::ExchangeOp>(op)) {
      if (auto e = attributes(op, {"sender", "receiver", "site"}))
        return std::move(e);
      return json::Array{"exchange", exchange.getSender(),
                         exchange.getReceiver()};
    }
    if (auto query = dyn_cast<protocol_ir::QueryOp>(op)) {
      if (auto e = attributes(op, {"owner", "method", "site"}))
        return std::move(e);
      auto result = dyn_cast<algebra::FieldType>(op.getResult(0).getType());
      if (query.getMethod() != "draw" || op.getNumOperands() != 1 || !result ||
          result.getDomain() != "bls12-381.fr")
        return error("structured-source-service");
      return json::Array{"draw", query.getOwner(), result.getDomain()};
    }
    if (auto statement = dyn_cast<protocol_ir::StatementOp>(op)) {
      if (auto e =
              attributes(op, {"relation", "selectors", "acceptance", "target"}))
        return std::move(e);
      return json::Array{"statement", statement.getRelation(),
                         names(statement.getSelectors()),
                         statement.getAcceptance(),
                         statement.getTargetAttr()
                             ? json::Value(statement.getTargetAttr().getValue())
                             : json::Value(nullptr)};
    }
    if (auto constant = dyn_cast<arith::ConstantOp>(op)) {
      if (auto e = attributes(op, {"value"}))
        return std::move(e);
      if (!constant.getType().isSignlessInteger(1))
        return error("structured-source-operation");
      return json::Array{"bool.constant",
                         cast<IntegerAttr>(constant.getValue()).getInt() != 0};
    }
    if (auto constant = dyn_cast<local::BoolConstantOp>(op)) {
      if (auto e = attributes(op, {"value", "site"}))
        return std::move(e);
      return json::Array{"bool.constant", constant.getValue()};
    }
    StringRef boolOpcode;
    if (isa<arith::AndIOp>(op))
      boolOpcode = "bool.and";
    else if (isa<arith::OrIOp>(op))
      boolOpcode = "bool.or";
    else if (isa<arith::XOrIOp>(op))
      boolOpcode = "bool.xor";
    if (!boolOpcode.empty()) {
      if (auto e = attributes(op, {}))
        return std::move(e);
      if (!op.getResult(0).getType().isSignlessInteger(1))
        return error("structured-source-operation");
      return json::Array{boolOpcode};
    }
    if (auto compare = dyn_cast<arith::CmpIOp>(op)) {
      if (auto e = attributes(op, {"predicate"}))
        return std::move(e);
      if (!compare.getLhs().getType().isSignlessInteger(1) ||
          (compare.getPredicate() != arith::CmpIPredicate::eq &&
           compare.getPredicate() != arith::CmpIPredicate::ne))
        return error("structured-source-operation");
      return json::Array{compare.getPredicate() == arith::CmpIPredicate::eq
                             ? "bool.equal"
                             : "bool.not_equal"};
    }
    if (isa<arith::SelectOp>(op)) {
      if (auto e = attributes(op, {}))
        return std::move(e);
      auto type = sort(op.getResult(0).getType());
      if (!type)
        return type.takeError();
      return json::Array{"select", std::move(*type)};
    }
    if (isa<data::BoundedAtOp>(op)) {
      if (auto e = attributes(op, {}))
        return std::move(e);
      auto vector =
          dyn_cast<algebra::FieldVectorType>(op.getOperand(0).getType());
      if (!vector)
        return error("structured-source-type");
      return json::Array{"bounded_at", vector.getDomain()};
    }
    if (isa<func::CallOp, local::ApplyOp, protocol_ir::LocalCallOp>(op)) {
      bool math = isa<func::CallOp>(op);
      bool participant = isa<protocol_ir::LocalCallOp>(op);
      if (auto e = attributes(
              op, math          ? ArrayRef<StringRef>{"callee"}
                  : participant ? ArrayRef<StringRef>{"callee", "site", "role"}
                                : ArrayRef<StringRef>{"callee", "site"}))
        return std::move(e);
      if ((math && owner != "math" && owner != "protocol") ||
          (!math && !participant && owner != "local"))
        return error("structured-source-reference");
      auto callee =
          reference(op, "callee",
                    math          ? ArrayRef<StringRef>{"math"}
                    : participant ? ArrayRef<StringRef>{"local"}
                                  : ArrayRef<StringRef>{"local", "finite",
                                                        "realize", "map"});
      if (!callee)
        return callee.takeError();
      auto *target = symbols.lookup(*callee);
      auto type = signature(*target);
      if (!type || op.getOperandTypes() != type.getInputs() ||
          op.getResultTypes() != type.getResults() ||
          (math && !cast<func::FuncOp>(target).isPrivate()))
        return error("structured-source-reference");
      if (participant) {
        auto ownerRole = op.getAttrOfType<StringAttr>("role");
        if (owner != "protocol" || !ownerRole || !hasRole(ownerRole.getValue()))
          return error("structured-source-role");
        return json::Array{"local_call", *callee, ownerRole.getValue()};
      }
      return json::Array{math ? "call" : "apply", *callee};
    }
    if (isa<algebra::FiniteFoldOp>(op)) {
      if (auto e = attributes(op, {"domain", "step", "predicate"}))
        return std::move(e);
      auto refs = fold(op);
      if (!refs)
        return refs.takeError();
      return json::Array{"fold", std::move((*refs)[0]), std::move((*refs)[1]),
                         std::move((*refs)[2])};
    }
    if (isa<protocol_ir::GuardOp>(op)) {
      if (auto e = attributes(op, {"site", "owner"}))
        return std::move(e);
      auto guardOwner = op.getAttrOfType<StringAttr>("owner");
      if (owner != "protocol" || !guardOwner || !hasRole(guardOwner.getValue()))
        return error("structured-source-role");
      return json::Array{"guard", guardOwner.getValue()};
    }
    if (isa<local::LocalIfOp, local::LocalForOp>(op)) {
      if (auto e = attributes(op, {"site"}))
        return std::move(e);
      if (owner != "local")
        return error("structured-source-operation");
      if (isa<local::LocalIfOp>(op))
        return json::Array{"if"};
      return json::Array{
          isa<local::LocalConditionOp>(op.getRegion(0).front().back())
              ? "for_condition"
              : "for"};
    }
    return error("structured-source-operation", op.getName().getStringRef());
  }

  // A fresh context for every closed block is essential: two equal types (or
  // even two aliased actual arguments) still occupy distinct formal positions.
  Expected<json::Value> block(Region &region, TypeRange outputs,
                              StringRef owner, StringRef terminator,
                              unsigned depth = 0) {
    if (depth > depthLimit)
      return error("structured-source-limit");
    if (!llvm::hasSingleElement(region) || region.front().empty())
      return error("structured-source-region");
    Block &body = region.front();
    if (body.getNumArguments() > signatureLimit)
      return error("structured-source-limit");
    llvm::DenseMap<Value, unsigned> refs;
    for (auto [i, arg] : llvm::enumerate(body.getArguments()))
      refs[arg] = i;
    auto operands = [&](Operation &op) -> Expected<json::Array> {
      json::Array result;
      for (Value value : op.getOperands()) {
        auto found = refs.find(value);
        if (found == refs.end())
          return error("structured-source-reference");
        if (found->second > instructionLimit)
          return error("structured-source-limit");
        result.push_back(found->second);
      }
      return result;
    };
    json::Array encoded;
    for (Operation &op : body) {
      auto args = operands(op);
      if (!args)
        return args.takeError();
      if (&op == &body.back()) {
        if (isa<local::StopOp>(op)) {
          if (auto e = attributes(op, {"reason", "site"}))
            return std::move(e);
          if (owner != "local")
            return error("structured-source-operation");
          auto occurrence = site(op);
          if (!occurrence)
            return occurrence.takeError();
          auto reason = op.getAttrOfType<StringAttr>("reason");
          if (!reason)
            return error("structured-source-operation");
          return json::Array{
              "block", std::move(encoded),
              json::Array{"stop", reason.getValue(), *occurrence}};
        }
        bool valid =
            terminator == "return"
                ? (owner == "math" ? isa<func::ReturnOp>(op)
                   : owner == "local"
                       ? isa<local::ReturnOp>(op)
                       : isa<protocol_ir::MathematicalReturnOp>(op))
            : terminator == "condition" ? isa<local::LocalConditionOp>(op)
            : owner == "protocol"       ? isa<protocol_ir::ProtocolYieldOp>(op)
                                        : isa<local::LocalYieldOp>(op);
        if (!valid || op.getOperandTypes() != outputs)
          return error("structured-source-region");
        if (auto e = attributes(op, {}))
          return std::move(e);
        return json::Array{"block", std::move(encoded),
                           json::Array{terminator, std::move(*args)}};
      }
      if (++instructions > instructionLimit)
        return error("structured-source-limit");
      auto inputs = sorts(op.getOperandTypes(),
                          isa<protocol_ir::QueryOp, protocol_ir::ApplyOp,
                              protocol_ir::RepeatOp>(op));
      if (!inputs)
        return inputs.takeError();
      auto results = sorts(op.getResultTypes());
      if (!results)
        return results.takeError();
      auto desc = descriptor(op, owner);
      if (!desc)
        return desc.takeError();
      StringRef occurrence;
      if (op.hasAttr("site") ||
          op.getName().getStringRef().starts_with("algebra.exec.") ||
          isa<protocol_ir::ExchangeOp, protocol_ir::QueryOp,
              protocol_ir::GuardOp, protocol_ir::LocalCallOp,
              protocol_ir::RepeatOp, local::ApplyOp, local::LocalIfOp,
              local::LocalForOp, local::BoolConstantOp>(op)) {
        auto checked = site(op);
        if (!checked)
          return checked.takeError();
        occurrence = *checked;
      }
      json::Array regions;
      if (op.getNumRegions()) {
        bool loop = isa<local::LocalForOp>(op);
        bool repeat = isa<protocol_ir::RepeatOp>(op);
        if ((!loop && !repeat && !isa<local::LocalIfOp>(op)) ||
            op.getNumRegions() != (loop || repeat ? 1u : 2u))
          return error("structured-source-region");
        for (Region &nested : op.getRegions()) {
          if (!llvm::hasSingleElement(nested) || nested.front().empty())
            return error("structured-source-region");
          Block &inner = nested.front();
          SmallVector<Type> expectedInputs;
          SmallVector<Type> expectedOutputs(op.getResultTypes());
          StringRef end = "yield";
          if (repeat) {
            // The count operand becomes the induction argument; state and
            // immutable captures retain their ordered types, not their SSA.
            llvm::append_range(expectedInputs, op.getOperandTypes());
          } else if (loop) {
            expectedInputs.push_back(
                IntegerType::get(unit.getContext(), 64, IntegerType::Unsigned));
            llvm::append_range(expectedInputs,
                               op.getOperands().drop_front(2).getTypes());
            auto captures = op.getOperands().drop_front(2 + op.getNumResults());
            llvm::append_range(expectedOutputs, captures.getTypes());
            Operation &last = inner.back();
            bool conditional = isa<local::LocalConditionOp>(last);
            if (conditional) {
              end = "condition";
              expectedOutputs.insert(expectedOutputs.begin(),
                                     IntegerType::get(unit.getContext(), 1));
            }
            if (!isa<local::StopOp>(last)) {
              if (last.getNumOperands() != expectedOutputs.size() ||
                  inner.getNumArguments() != expectedInputs.size())
                return error("structured-source-region");
              for (unsigned i = 0; i < captures.size(); ++i)
                if (last.getOperand(conditional + op.getNumResults() + i) !=
                    inner.getArgument(1 + op.getNumResults() + i))
                  return error("structured-source-capture");
            }
          } else {
            llvm::append_range(expectedInputs,
                               op.getOperands().drop_front().getTypes());
          }
          if (inner.getArgumentTypes() != TypeRange(expectedInputs))
            return error("structured-source-region");
          auto in = sorts(expectedInputs, repeat);
          if (!in)
            return in.takeError();
          auto out = sorts(expectedOutputs);
          if (!out)
            return out.takeError();
          auto content = block(nested, expectedOutputs, owner, end, depth + 1);
          if (!content)
            return content.takeError();
          regions.push_back(json::Array{std::move(*in), std::move(*out),
                                        std::move(*content)});
        }
      }
      encoded.push_back(json::Array{std::move(*desc), std::move(*args),
                                    std::move(*results), std::move(regions),
                                    occurrence});
      // Prepend the complete result list once. Incremental single-result
      // insertion would reverse a multi-result operation's coordinates.
      for (auto &entry : refs)
        entry.second += op.getNumResults();
      for (auto [i, result] : llvm::enumerate(op.getResults()))
        refs[result] = i;
    }
    return error("structured-source-region");
  }

  Expected<json::Value> domain(data::DomainOp op) {
    if (auto e =
            attributes(*op, {"sym_name", "sym_visibility", "function_type"}))
      return std::move(e);
    if (op.getSymVisibility() != "private" ||
        !llvm::hasSingleElement(op.getBody()))
      return error("structured-source-domain");
    Block &body = op.getBody().front();
    if (body.getOperations().size() != 2)
      return error("structured-source-domain");
    Operation &constructor = body.front();
    Operation &yield = body.back();
    bool indices = isa<data::DomainIndicesOp>(constructor);
    if ((!indices && !isa<data::DomainElementsOp>(constructor)) ||
        !isa<data::DomainYieldOp>(yield) ||
        yield.getOperand(0) != constructor.getResult(0))
      return error("structured-source-domain");
    if (auto e = attributes(constructor, indices ? ArrayRef<StringRef>{"axis"}
                                                 : ArrayRef<StringRef>{}))
      return std::move(e);
    if (auto e = attributes(yield, {}))
      return std::move(e);
    auto arg = dyn_cast<BlockArgument>(constructor.getOperand(0));
    auto vector =
        dyn_cast<algebra::FieldVectorType>(constructor.getOperand(0).getType());
    if (!arg || arg.getOwner() != &body || !vector ||
        (indices &&
         constructor.getAttrOfType<IntegerAttr>("axis").getInt() != 0))
      return error("structured-source-domain");
    auto items = cast<data::DomainType>(constructor.getResult(0).getType())
                     .getItemTypes();
    Type item = indices ? Type(IntegerType::get(unit.getContext(), 64,
                                                IntegerType::Unsigned))
                        : Type(algebra::FieldType::get(unit.getContext(),
                                                       vector.getDomain()));
    if (items.size() != 1 || items[0] != item)
      return error("structured-source-domain");
    auto inputs = sorts(signature(*op).getInputs());
    if (!inputs)
      return inputs.takeError();
    json::Array desc{indices ? "indices" : "elements", arg.getArgNumber()};
    if (indices)
      desc.push_back(0);
    return json::Array{"domain", op.getSymName(), std::move(*inputs),
                       std::move(desc)};
  }

  Expected<json::Value> preparation(Operation &op) {
    bool map = isa<algebra::MapRealizeOp>(op);
    StringRef code =
        map ? "structured-source-map" : "structured-source-realization";
    if (auto e = attributes(
            op,
            map ? ArrayRef<StringRef>{"sym_name", "function_type", "helper",
                                      "rowwise"}
                : ArrayRef<StringRef>{"sym_name", "function_type", "helper"}))
      return std::move(e);
    if (op.getNumOperands() || op.getNumResults() || op.getNumRegions())
      return error(code);
    if (++instructions > instructionLimit)
      return error("structured-source-limit");
    auto type = signature(op);
    if (!type)
      return error(code);
    auto inputs = sorts(type.getInputs());
    if (!inputs)
      return inputs.takeError();
    auto outputs = sorts(type.getResults());
    if (!outputs)
      return outputs.takeError();
    auto helperName = reference(op, "helper", {"math"});
    if (!helperName)
      return helperName.takeError();
    auto helper = cast<func::FuncOp>(symbols.lookup(*helperName));
    if (!helper.isPrivate() || helper.isExternal() ||
        helper->getParentOp() != op.getParentOp())
      return error(code, "private sibling helper required");
    json::Array rowwise;
    if (map) {
      auto mask = op.getAttrOfType<DenseBoolArrayAttr>("rowwise");
      Type field = algebra::FieldType::get(op.getContext(), "bls12-381.fr");
      Type vector =
          algebra::FieldVectorType::get(op.getContext(), "bls12-381.fr");
      if (!mask || mask.size() != type.getNumInputs() ||
          !llvm::is_contained(mask.asArrayRef(), true) ||
          type.getNumResults() != 1 || type.getResult(0) != vector ||
          helper.getFunctionType() !=
              FunctionType::get(op.getContext(),
                                SmallVector<Type>(mask.size(), field), {field}))
        return error(code, "scalar helper ABI or row mask");
      for (auto [input, row] : llvm::zip(type.getInputs(), mask.asArrayRef())) {
        if (input != (row ? vector : field))
          return error(code, "lifted input type");
        rowwise.push_back(row);
      }
    } else if (helper.getFunctionType() != type) {
      return error(code, "full helper ABI");
    }
    json::Array result{map ? "map" : "realize",
                       SymbolTable::getSymbolName(&op).getValue(),
                       std::move(*inputs), std::move(*outputs), *helperName};
    if (map)
      result.push_back(std::move(rowwise));
    return result;
  }

  // Whole-unit bodies have already passed ordinary instruction admission and
  // cycle/depth checks. These two memoized profiles additionally constrain
  // every transitive instruction, including unused calls and discarded results.
  Error preparationProfiles() {
    llvm::DenseSet<Operation *> totalChecked, ringChecked;
    std::function<Error(Operation *, bool)> check = [&](Operation *op,
                                                        bool ring) -> Error {
      auto &checked = ring ? ringChecked : totalChecked;
      if (checked.contains(op))
        return Error::success();
      StringRef code =
          ring ? "structured-source-map" : "structured-source-realization";
      auto helper = dyn_cast<func::FuncOp>(op);
      if (!helper || helper.isExternal() || !helper.isPrivate() ||
          helper->getParentOp() != unit.getOperation())
        return error(code, "private Math closure required");
      if (auto premises =
              helper->getAttrOfType<ArrayAttr>("data.preconditions");
          premises && !premises.empty())
        return error(code, "helper preconditions");
      if (ring) {
        Type field = algebra::FieldType::get(op->getContext(), "bls12-381.fr");
        auto type = helper.getFunctionType();
        for (Type port :
             llvm::concat<const Type>(type.getInputs(), type.getResults()))
          if (port != field)
            return error(code, "scalar closure ABI");
      }
      for (Operation &instruction : helper.getBody().front()) {
        if (auto call = dyn_cast<func::CallOp>(instruction)) {
          if (auto e = check(symbols.lookup(call.getCallee()), ring))
            return e;
          continue;
        }
        bool allowed = isa<algebra::ConstantFieldOp, algebra::FieldAddOp,
                           algebra::SubtractFieldOp, algebra::FieldMultiplyOp,
                           func::ReturnOp>(instruction);
        if (!ring)
          allowed |=
              isa<algebra::FieldEqualOp, algebra::GroupIdentityOp,
                  algebra::GroupAddOp, algebra::GroupScaleOp,
                  algebra::GroupEqualOp, data::IndexOp, data::EqualOp,
                  arith::ConstantOp, arith::AndIOp, arith::OrIOp, arith::XOrIOp,
                  arith::CmpIOp, arith::SelectOp>(instruction);
        if (!allowed || instruction.getNumRegions())
          return error(code, instruction.getName().getStringRef());
      }
      checked.insert(op);
      return Error::success();
    };
    for (Operation &op : unit.getBody().front())
      if (isa<local::RealizeOp, algebra::MapRealizeOp>(op))
        if (auto e = check(
                symbols.lookup(
                    op.getAttrOfType<FlatSymbolRefAttr>("helper").getValue()),
                isa<algebra::MapRealizeOp>(op)))
          return e;
    return Error::success();
  }

  Expected<json::Value> function(Operation &op) {
    if (isa<local::RealizeOp, algebra::MapRealizeOp>(op))
      return preparation(op);
    StringRef owner = kind(op);
    SmallVector<StringRef> allowed{"sym_name", "sym_visibility",
                                   "function_type"};
    if (owner == "math")
      allowed.push_back("data.preconditions");
    else if (owner == "local")
      allowed.push_back("logical_origin");
    else if (owner == "protocol")
      llvm::append_range(allowed,
                         ArrayRef<StringRef>{"roles", "input_roles",
                                             "output_roles", "contracts"});
    else if (owner == "finite")
      llvm::append_range(allowed,
                         ArrayRef<StringRef>{"domain", "step", "predicate"});
    else
      return error("structured-source-operation", op.getName().getStringRef());
    if (auto e = attributes(op, allowed))
      return std::move(e);
    auto type = signature(op);
    if (!type)
      return error("structured-source-region");
    auto inputs = sorts(type.getInputs(), owner == "protocol");
    if (!inputs)
      return inputs.takeError();
    auto outputs = sorts(type.getResults());
    if (!outputs)
      return outputs.takeError();
    auto visible = visibility(op);
    if (!visible)
      return visible.takeError();
    StringRef name = SymbolTable::getSymbolName(&op).getValue();
    if (owner == "finite") {
      // The declaration lowers to one owned fold instruction in the reader.
      if (++instructions > instructionLimit)
        return error("structured-source-limit");
      auto refs = fold(op);
      if (!refs)
        return refs.takeError();
      return json::Array{"finite",
                         name,
                         *visible,
                         std::move(*inputs),
                         std::move(*outputs),
                         std::move((*refs)[0]),
                         std::move((*refs)[1]),
                         std::move((*refs)[2])};
    }
    json::Array ports;
    roles = {};
    if (auto protocol = dyn_cast<protocol_ir::MathematicalOp>(op)) {
      auto encoded = interface(protocol);
      if (!encoded)
        return encoded.takeError();
      ports = std::move(*encoded);
    }
    json::Array preconditions;
    if (op.hasAttr("data.preconditions")) {
      auto attrs = op.getAttrOfType<ArrayAttr>("data.preconditions");
      if (!attrs)
        return error("structured-source-precondition");
      if (attrs.size() > signatureLimit)
        return error("structured-source-limit");
      for (Attribute attr : attrs) {
        auto bound = dyn_cast<data::IndexBoundAttr>(attr);
        if (!bound || bound.getAxis() != 0 ||
            bound.getIndexArg() >= type.getNumInputs() ||
            bound.getContainerArg() >= type.getNumInputs() ||
            !type.getInput(bound.getIndexArg()).isUnsignedInteger(64) ||
            !isa<algebra::FieldVectorType>(
                type.getInput(bound.getContainerArg())))
          return error("structured-source-precondition");
        preconditions.push_back(json::Array{"index_bound", bound.getIndexArg(),
                                            bound.getContainerArg(), 0});
      }
    }
    json::Array origin;
    if (owner == "local") {
      auto attr = op.getAttrOfType<ArrayAttr>("logical_origin");
      if (!attr || attr.size() != 2 || !isa<StringAttr>(attr[0]) ||
          !isa<ArrayAttr>(attr[1]))
        return error("structured-source-origin");
      json::Array bindings;
      for (Attribute component : cast<ArrayAttr>(attr[1])) {
        auto pair = dyn_cast<ArrayAttr>(component);
        if (!pair || pair.size() != 2 || !isa<StringAttr>(pair[0]) ||
            !isa<StringAttr>(pair[1]))
          return error("structured-source-origin");
        bindings.push_back(json::Array{cast<StringAttr>(pair[0]).getValue(),
                                       cast<StringAttr>(pair[1]).getValue()});
      }
      origin.push_back(cast<StringAttr>(attr[0]).getValue());
      origin.push_back(std::move(bindings));
    }
    if (op.getNumRegions() != 1 || !llvm::hasSingleElement(op.getRegion(0)) ||
        op.getRegion(0).front().getArgumentTypes() != type.getInputs())
      return error("structured-source-region");
    auto body = block(op.getRegion(0), type.getResults(), owner, "return");
    if (!body)
      return body.takeError();
    return json::Array{"function",
                       name,
                       owner,
                       *visible,
                       std::move(*inputs),
                       std::move(*outputs),
                       std::move(ports),
                       std::move(preconditions),
                       std::move(origin),
                       std::move(*body)};
  }

  Error closure() {
    // Height is the longest reference path in edges; a leaf has height zero.
    // Memoize heights, not only colors: a shared helper encountered first on a
    // short path must still count its whole suffix on a later, longer path.
    llvm::DenseMap<Operation *, unsigned> heights;
    llvm::DenseSet<Operation *> active;
    std::function<Expected<unsigned>(Operation *, unsigned)> visit =
        [&](Operation *op, unsigned depth) -> Expected<unsigned> {
      if (depth > depthLimit)
        return error("structured-source-limit");
      if (auto found = heights.find(op); found != heights.end())
        return found->second;
      if (!active.insert(op).second)
        return error("structured-source-cycle");
      unsigned height = 0;
      for (Operation *callee : dependencies[op]) {
        auto nested = visit(callee, depth + 1);
        if (!nested)
          return nested.takeError();
        height = std::max(height, *nested + 1);
        if (height > depthLimit)
          return error("structured-source-limit");
      }
      active.erase(op);
      heights[op] = height;
      return height;
    };
    for (Operation &op : unit.getBody().front()) {
      auto checked = visit(&op, 0);
      if (!checked)
        return checked.takeError();
    }
    return Error::success();
  }

  Error effectiveSites() {
    // Native verification already checks its conservative application/Math
    // expansion budget. Independently check final protocol-site collisions,
    // without cloning syntax or entering the separate closed helper namespace.
    uint64_t visits = 0, bytes = 0;
    llvm::StringSet<> effective;
    std::function<Error(Block &, StringRef, unsigned, unsigned)> visit =
        [&](Block &body, StringRef prefix, unsigned applicationDepth,
            unsigned repeatDepth) -> Error {
      if (applicationDepth > depthLimit || repeatDepth > depthLimit)
        return error("structured-source-limit");
      for (Operation &op : body) {
        if (++visits > staticVisitLimit)
          return error("structured-source-limit");
        auto site = op.getAttrOfType<StringAttr>("site");
        if (!site)
          continue;
        StringRef leaf = site.getValue();
        auto length = std::to_string(prefix.size());
        size_t overhead =
            prefix.empty() ? 0 : 8 + length.size() + prefix.size();
        if (overhead > effectiveSiteByteLimit ||
            leaf.size() > effectiveSiteByteLimit - overhead)
          return error("structured-source-limit");
        size_t size = overhead + leaf.size();
        if (size > staticSiteByteLimit - bytes)
          return error("structured-source-limit");
        bytes += size;
        std::string rendered =
            prefix.empty()
                ? leaf.str()
                : "apply_" + length + "_" + prefix.str() + "_" + leaf.str();
        if (auto call = dyn_cast<protocol_ir::ApplyOp>(op)) {
          // Headers disappear, but their rendered labels advance the context
          // and count toward metadata work. Revisit each static occurrence.
          if (auto e = visit(
                  symbols.lookup<protocol_ir::MathematicalOp>(call.getCallee())
                      .getBody()
                      .front(),
                  rendered, applicationDepth + 1, repeatDepth))
            return e;
        } else if (!effective.insert(rendered).second) {
          return error("structured-source-site", "expanded protocol collision");
        }
        if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(op))
          // A repeat header survives expansion. Its body has the same static
          // prefix and is visited once, even when maximum is zero.
          if (auto e = visit(repeat.getBody().front(), prefix, applicationDepth,
                             repeatDepth + 1))
            return e;
      }
      return Error::success();
    };
    for (auto function :
         unit.getBody().front().getOps<protocol_ir::MathematicalOp>()) {
      effective.clear();
      if (auto e = visit(function.getBody().front(), {}, 1, 0))
        return e;
    }
    return Error::success();
  }

public:
  Exporter(protocol_ir::ProtocolModuleOp unit,
           protocol_ir::MathematicalOp selected)
      : unit(unit), selected(selected), symbols(unit) {}

  Expected<json::Value> run(StringRef bytes) {
    if (auto e = attributes(*unit, {"profile"}))
      return std::move(e);
    json::Array domains, relations, bindings, definitions, contracts;
    llvm::StringSet<> symbolsSeen;
    for (Operation &op : unit.getBody().front()) {
      // MLIR permits an empty quoted symbol. The wire vocabulary uses the
      // empty string only for absent predicates and sites, never a declaration.
      if (auto name = op.getAttrOfType<StringAttr>("sym_name");
          !name || name.getValue().empty() ||
          !symbolsSeen.insert(name.getValue()).second)
        return error("structured-source-symbol");
      definition = &op;
      sites.clear();
      dependencies.try_emplace(&op);
      if (auto declaration = dyn_cast<data::DomainOp>(op)) {
        if (domains.size() == 128)
          return error("structured-source-limit");
        auto encoded = domain(declaration);
        if (!encoded)
          return encoded.takeError();
        domains.push_back(std::move(*encoded));
      } else if (auto declaration = dyn_cast<relation::DeclareOp>(op)) {
        if (relations.size() == 128)
          return error("structured-source-limit");
        if (auto e = attributes(op, {"sym_name", "sym_visibility", "kind",
                                     "key", "revision", "signature", "purposes",
                                     "formula"}))
          return std::move(e);
        auto visible = visibility(op);
        if (!visible)
          return visible.takeError();
        auto type = declaration.getSignature();
        auto inputs = sorts(type.getInputs());
        if (!inputs)
          return inputs.takeError();
        auto outputs = sorts(type.getResults());
        if (!outputs)
          return outputs.takeError();
        relations.push_back(json::Array{
            "relation", declaration.getSymName(), *visible,
            declaration.getKind(), declaration.getKey(),
            declaration.getRevision(), std::move(*inputs), std::move(*outputs),
            names(declaration.getPurposes()),
            declaration.getFormulaAttr()
                ? json::Value(declaration.getFormulaAttr().getValue())
                : json::Value(nullptr)});
      } else if (isa<local::OperationBindingOp>(op)) {
        if (bindings.size() == 128)
          return error("structured-source-limit");
        if (auto e = attributes(
                op, {"sym_name", "contract", "arguments", "implementation"}))
          return std::move(e);
        auto binding = primitiveBinding(&op);
        if (!binding)
          return binding.takeError();
        bindings.push_back(
            json::Array{"binding", binding->name, binding->application.contract,
                        names(op.getAttrOfType<ArrayAttr>("arguments")),
                        binding->application.implementation});
      } else {
        if (definitions.size() == 128)
          return error("structured-source-limit");
        auto encoded = function(op);
        if (!encoded)
          return encoded.takeError();
        definitions.push_back(std::move(*encoded));
        if (auto protocol = dyn_cast<protocol_ir::MathematicalOp>(op)) {
          if (protocol.getContractsAttr() &&
              protocol.getContractsAttr().size() > signatureLimit)
            return error("structured-source-limit");
          contracts.push_back(
              json::Array{protocol.getSymName(),
                          protocol.getContractsAttr()
                              ? contractValue(protocol.getContractsAttr())
                              : json::Value(json::Array{})});
        }
      }
    }
    if (auto e = closure())
      return std::move(e);
    if (auto e = preparationProfiles())
      return std::move(e);
    if (auto e = effectiveSites())
      return std::move(e);
    // Multi-role Math finite work needs separate partial-component semantics.
    // Follow only Math calls: owned Local finite work keeps its closed ABI.
    llvm::DenseSet<Operation *> checked;
    std::function<Error(Operation *)> scalarMath =
        [&](Operation *function) -> Error {
      if (!checked.insert(function).second)
        return Error::success();
      SmallVector<Operation *> operations;
      function->getRegion(0).walk<WalkOrder::PreOrder>(
          [&](Operation *op) { operations.push_back(op); });
      for (Operation *operation : operations) {
        Operation &op = *operation;
        if (isa<algebra::FiniteFoldOp, data::BoundedAtOp>(op))
          return error("structured-source-multirole-math");
        if (auto call = dyn_cast<func::CallOp>(op))
          if (auto e = scalarMath(symbols.lookup(call.getCallee())))
            return e;
      }
      return Error::success();
    };
    for (auto protocol :
         unit.getBody().front().getOps<protocol_ir::MathematicalOp>())
      if (protocol.getRoles().size() > 1)
        if (auto e = scalarMath(protocol))
          return std::move(e);
    auto digest = SHA256::hash(arrayRefFromStringRef(bytes));
    return json::Array{"zkc.structured-source/0",
                       "original",
                       "sha256:" + toHex(digest, true),
                       selected.getSymName(),
                       std::move(domains),
                       std::move(relations),
                       std::move(bindings),
                       std::move(definitions),
                       std::move(contracts)};
  }
};
} // namespace

Expected<std::string> exportStructuredSource(StringRef bytes, StringRef name,
                                             MLIRContext &context) {
  if (bytes.size() > 16 * 1024 * 1024 || !mlirNestingWithinLimit(bytes))
    return error("structured-source-limit");
  auto original = parseSourceString<ModuleOp>(bytes, &context);
  if (!original || failed(verify(*original)))
    return error("structured-source-original");
  if (auto e = attributes(**original, {}))
    return std::move(e);
  if (!llvm::hasSingleElement(original->getBody()->getOperations()))
    return error("structured-source-module");
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(original->getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
    return error("structured-source-profile");
  SymbolTable symbols(unit);
  auto selected = symbols.lookup<protocol_ir::MathematicalOp>(name);
  if (!selected)
    return error("structured-source-symbol");
  auto exported = Exporter(unit, selected).run(bytes);
  if (!exported)
    return exported.takeError();
  if (!boundedWire(*exported))
    return error("structured-source-limit");
  // Own framing and its byte budget together: callers emit these exact bytes.
  auto serialized = printJson(*exported) + '\n';
  if (serialized.size() > 1024 * 1024)
    return error("structured-source-limit");
  return serialized;
}
} // namespace zkc::protocol
