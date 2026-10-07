#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Interfaces/Mathematical.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Translation/Language.h"
#include <set>

using namespace llvm;
namespace zkc::language {
namespace {
bool sameType(const Type &source, mlir::Type actual) {
  if (source.kind == Type::Kind::Boolean)
    return actual.isSignlessInteger(1);
  auto field = mlir::dyn_cast<algebra::FieldType>(actual);
  return field && field.getDomain() == source.domain;
}
bool attributes(mlir::Operation &op, std::initializer_list<StringRef> names) {
  if (op.getAttrs().size() != names.size())
    return false;
  return llvm::all_of(names,
                      [&](StringRef name) { return bool(op.getAttr(name)); });
}
bool string(mlir::Operation &op, StringRef name, StringRef value) {
  auto attr = op.getAttrOfType<mlir::StringAttr>(name);
  return attr && attr.getValue() == value;
}
bool roleSet(mlir::Attribute actual, const Declaration &decl,
             ArrayRef<unsigned> expected) {
  auto array = mlir::dyn_cast_if_present<mlir::ArrayAttr>(actual);
  if (!array || array.size() != expected.size())
    return false;
  for (unsigned i = 0; i < expected.size(); ++i) {
    auto role = mlir::dyn_cast<mlir::StringAttr>(array[i]);
    if (!role || role.getValue() != decl.roles[expected[i]])
      return false;
  }
  return true;
}
} // namespace
Expected<Correspondence> compareOriginal(const CheckedProject &project,
                                         mlir::ModuleOp module,
                                         const Limits &limits) {
  if (auto error = checkLimits(limits))
    return std::move(error);
  if (project.installationIdentity() != installedCatalogIdentity())
    return error("source.environment",
                 "source was checked against another installed catalog");
  if (!module || mlir::failed(mlir::verify(module)))
    return error("target.admission",
                 "original failed mathematical IR admission");
  auto mismatch = [](StringRef detail) {
    return error("source.correspondence", detail);
  };
  if (!module || !module->getAttrs().empty() ||
      !llvm::hasSingleElement(*module.getBody()))
    return mismatch("expected one unadorned protocol module");
  auto native =
      mlir::dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  if (!native || !attributes(*native, {"profile"}) ||
      native.getProfile() != protocol_ir::Profile::Protocol ||
      !llvm::hasSingleElement(native.getBody()))
    return mismatch("unexpected original profile or module structure");
  auto &definitions = native.getBody().front();
  auto current = definitions.begin();
  Correspondence report;
  auto record = [&](mlir::Operation &operation, Span source) -> bool {
    auto location = mlir::dyn_cast<mlir::FileLineColLoc>(operation.getLoc());
    if (!location)
      return true; // In-memory callers can omit serialized source positions.
    if (report.locations.size() >=
        limits.locationBytes / (5 * sizeof(uint64_t)))
      return false;
    report.locations.push_back(
        {location.getLine(), location.getColumn(), source});
    return true;
  };
  uint64_t work = 0;
  mlir::SymbolTableCollection tables;
  for (const auto &decl : project.declarations()) {
    if (!decl.body)
      continue;
    if (++report.declarations > limits.declarations)
      return error("source.limit",
                   "comparison declaration count limit exceeded");
    if (current == definitions.end())
      return mismatch("original omitted a definition");
    auto &function = *current++;
    bool protocol = decl.kind == Declaration::Kind::Protocol;
    if (function.getName().getStringRef() !=
            (protocol ? "protocol.func" : "func.func") ||
        !string(function, "sym_name", decl.symbol) ||
        function.getNumRegions() != 1 ||
        !llvm::hasSingleElement(function.getRegion(0)))
      return mismatch("definition identity, order, or structure differs");
    if (protocol ? !attributes(function, {"sym_name", "function_type", "roles",
                                          "input_roles", "output_roles"})
                 : !attributes(function, {"sym_name", "function_type",
                                          "sym_visibility"}) ||
                       !string(function, "sym_visibility", "private"))
      return mismatch("unexpected definition attributes");
    auto typeAttr = function.getAttrOfType<mlir::TypeAttr>("function_type");
    auto signature =
        typeAttr ? mlir::dyn_cast<mlir::FunctionType>(typeAttr.getValue())
                 : mlir::FunctionType();
    if (!signature || signature.getNumInputs() != decl.inputs.size() ||
        signature.getNumResults() != decl.outputs.size())
      return mismatch("definition signature differs");
    for (unsigned i = 0; i < decl.inputs.size(); ++i)
      if (!sameType(decl.inputs[i].type, signature.getInput(i)))
        return mismatch("input type differs");
    for (unsigned i = 0; i < decl.outputs.size(); ++i)
      if (!sameType(decl.outputs[i].type, signature.getResult(i)))
        return mismatch("output type differs");
    mathematical::Availability availability;
    if (protocol) {
      auto roster = function.getAttrOfType<mlir::ArrayAttr>("roles");
      if (roster.size() != decl.roles.size())
        return mismatch("participant roster differs");
      for (unsigned i = 0; i < decl.roles.size(); ++i)
        if (mlir::cast<mlir::StringAttr>(roster[i]).getValue() != decl.roles[i])
          return mismatch("participant order differs");
      for (bool input : {true, false}) {
        auto ports = function.getAttrOfType<mlir::ArrayAttr>(
            input ? "input_roles" : "output_roles");
        const auto &expected = input ? decl.inputs : decl.outputs;
        if (ports.size() != expected.size())
          return mismatch("port count differs");
        for (unsigned i = 0; i < expected.size(); ++i)
          if (!roleSet(ports[i], decl, expected[i].roles))
            return mismatch("port role set differs");
      }
      if (mlir::failed(mathematical::analyze(
              mlir::cast<protocol_ir::MathematicalOp>(function), availability,
              tables)))
        return mismatch(
            "actual participant availability could not be analyzed");
    }
    if (!record(function, decl.span))
      return error("source.limit", "source location map limit exceeded");
    const auto &source = *decl.body;
    auto &block = function.getRegion(0).front();
    if (block.getNumArguments() != decl.inputs.size())
      return mismatch("block signature differs");
    DenseMap<mlir::Value, unsigned> values;
    auto bind = [&](mlir::Value actual, unsigned index) {
      if (index >= source.values.size() ||
          !sameType(source.values[index].type, actual.getType()) ||
          !values.try_emplace(actual, index).second)
        return false;
      if (protocol) {
        auto found = availability.values.find(actual);
        if (found == availability.values.end() ||
            found->second.count() != source.values[index].components.size())
          return false;
        for (unsigned role : source.values[index].components)
          if (role >= found->second.size() || !found->second[role])
            return false;
      }
      return true;
    };
    for (unsigned i = 0; i < block.getNumArguments(); ++i)
      if (!bind(block.getArgument(i), i))
        return mismatch("input availability differs");
    auto operands = [&](mlir::Operation &actual, ArrayRef<ValueId> expected) {
      if (actual.getNumOperands() != expected.size())
        return false;
      for (unsigned i = 0; i < expected.size(); ++i) {
        auto found = values.find(actual.getOperand(i));
        if (found == values.end() || found->second != expected[i].index)
          return false;
      }
      return true;
    };
    auto operation = block.begin();
    for (const auto &expected : source.operations) {
      if (++report.operations > limits.operations)
        return error("source.limit",
                     "comparison operation count limit exceeded");
      if (operation == block.end())
        return mismatch("original omitted an operation");
      auto &actual = *operation++;
      if (!record(actual, expected.span))
        return error("source.limit", "source location map limit exceeded");
      if (actual.getNumRegions() || actual.getNumSuccessors() ||
          actual.getNumResults() != 1 ||
          (!std::holds_alternative<Exchange>(expected.action) &&
           !bind(actual.getResult(0), expected.result.index)))
        return error("source.correspondence",
                     "operation result type or availability differs: " +
                         actual.getName().getStringRef() + " in " +
                         decl.qualifiedName + " value " +
                         Twine(expected.result.index));
      uint64_t cost = actual.getNumOperands() +
                      source.values[expected.result.index].components.size() +
                      1;
      if (cost > limits.work - work)
        return error("source.limit", "comparison work limit exceeded");
      work += cost;
      if (const auto *math = std::get_if<MathValue>(&expected.action)) {
        auto interface = mlir::dyn_cast<MathematicalOpInterface>(actual);
        if (!interface ||
            interface.getMathematicalIdentity() != math->identity ||
            !operands(actual, math->operands))
          return mismatch("mathematical identity or ordered operands differ");
        auto dependencies = interface.getOperandDependencies(0);
        if (dependencies.size() != math->operands.size())
          return mismatch("mathematical dependency contract differs");
        for (unsigned i = 0; i < dependencies.size(); ++i)
          if (dependencies[i] != i)
            return mismatch("mathematical dependency order differs");
        if (math->identity == MathematicalIdentity::FieldConstant) {
          if (!attributes(actual, {"value"}) ||
              !string(actual, "value", math->literal))
            return mismatch("field literal differs");
        } else if (math->identity == MathematicalIdentity::BooleanConstant) {
          auto value = actual.getAttrOfType<mlir::IntegerAttr>("value");
          if (!attributes(actual, {"value"}) || !value ||
              value.getValue().getBoolValue() != (math->literal == "true"))
            return mismatch("Boolean literal differs");
        } else if (math->identity == MathematicalIdentity::BooleanEqual) {
          auto comparison = mlir::dyn_cast<mlir::arith::CmpIOp>(actual);
          if (!attributes(actual, {"predicate"}) || !comparison ||
              comparison.getPredicate() != mlir::arith::CmpIPredicate::eq)
            return mismatch("unexpected Boolean comparison attributes");
        } else if (!attributes(actual, {}))
          return mismatch("unexpected mathematical attributes");
      } else if (const auto *call = std::get_if<HelperCall>(&expected.action)) {
        auto callee = actual.getAttrOfType<mlir::FlatSymbolRefAttr>("callee");
        if (actual.getName().getStringRef() != "func.call" ||
            !attributes(actual, {"callee"}) || !callee ||
            callee.getValue() !=
                project.declarations()[call->callee.index].symbol ||
            !operands(actual, call->operands))
          return mismatch("helper target or ordered arguments differ");
      } else if (const auto *exchange =
                     std::get_if<Exchange>(&expected.action)) {
        if (actual.getName().getStringRef() != "protocol.exchange" ||
            !attributes(actual, {"sender", "receiver", "site"}) ||
            !string(actual, "sender", decl.roles[exchange->sender]) ||
            !string(actual, "receiver", decl.roles[exchange->receiver]) ||
            !string(actual, "site", "s" + std::to_string(expected.statement)) ||
            !operands(actual, {exchange->payload}))
          return mismatch("message identity, order, or payload differs");
        if (++report.operations > limits.operations)
          return error("source.limit",
                       "comparison operation count limit exceeded");
        if (!sameType(source.values[expected.result.index].type,
                      actual.getResult(0).getType()) ||
            operation == block.end())
          return mismatch("message is missing its receiver restriction");
        auto available = availability.values.find(actual.getResult(0));
        if (available == availability.values.end() ||
            available->second.count() != 2 ||
            !available->second[exchange->sender] ||
            !available->second[exchange->receiver])
          return mismatch("exchange components differ");
        auto &received = *operation++;
        if (!record(received, expected.span))
          return error("source.limit", "source location map limit exceeded");
        if (received.getName().getStringRef() != "protocol.restrict_roles" ||
            !attributes(received, {"roles"}) ||
            !roleSet(received.getAttr("roles"), decl, {exchange->receiver}) ||
            received.getNumOperands() != 1 ||
            received.getOperand(0) != actual.getResult(0) ||
            received.getNumResults() != 1 || received.getNumRegions() ||
            !bind(received.getResult(0), expected.result.index))
          return mismatch("message receiver restriction differs");
      } else {
        const auto &restriction = std::get<Restriction>(expected.action);
        if (actual.getName().getStringRef() != "protocol.restrict_roles" ||
            !attributes(actual, {"roles"}) ||
            !roleSet(actual.getAttr("roles"), decl, restriction.roles) ||
            !operands(actual, {restriction.input}))
          return mismatch("explicit role restriction differs");
      }
    }
    if (operation == block.end())
      return mismatch("missing return");
    auto &result = *operation++;
    if (!record(result, decl.span))
      return error("source.limit", "source location map limit exceeded");
    if (result.getName().getStringRef() !=
            (protocol ? "protocol.return" : "func.return") ||
        !attributes(result, {}) || result.getNumResults() ||
        result.getNumRegions() || !operands(result, source.results) ||
        operation != block.end())
      return mismatch("return operands or remaining operations differ");
  }
  if (current != definitions.end())
    return mismatch("original contains an extra definition");
  llvm::sort(report.locations, [](const auto &a, const auto &b) {
    return std::tie(a.line, a.column) < std::tie(b.line, b.column);
  });
  return report;
}
} // namespace zkc::language
