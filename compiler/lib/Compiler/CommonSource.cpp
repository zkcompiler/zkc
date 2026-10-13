#include "zkc/Compiler/CommonSource.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
using namespace mlir;

namespace zkc::protocol {
namespace {
bool boundedStrings(const json::Value &value) {
  if (auto string = value.getAsString())
    return string->size() <= 512;
  if (auto array = value.getAsArray())
    return llvm::all_of(*array, boundedStrings);
  return true;
}

Expected<json::Value> sort(Type type) {
  if (type.isInteger(1))
    return json::Array{"bool"};
  if (auto field = dyn_cast<algebra::FieldType>(type))
    return json::Array{"field", field.getDomain()};
  if (auto group = dyn_cast<algebra::GroupType>(type))
    return json::Array{"group", group.getDomain()};
  if (auto service = dyn_cast<protocol_ir::ServiceReferenceType>(type))
    return json::Array{"service", service.getContract()};
  return error("common-source-type");
}

Expected<json::Value> operation(Operation &op) {
  auto field = [&]() {
    return cast<algebra::FieldType>(op.getOperand(0).getType()).getDomain();
  };
  auto group = [&]() {
    return cast<algebra::GroupType>(op.getOperand(0).getType()).getDomain();
  };
  if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op))
    return json::Array{
        "field.constant",
        cast<algebra::FieldType>(constant.getResult().getType()).getDomain(),
        constant.getValue()};
  if (isa<algebra::FieldAddOp>(op))
    return json::Array{"field.add", field()};
  if (isa<algebra::SubtractFieldOp>(op))
    return json::Array{"field.subtract", field()};
  if (isa<algebra::FieldMultiplyOp>(op))
    return json::Array{"field.multiply", field()};
  if (isa<algebra::FieldEqualOp>(op))
    return json::Array{"field.equal", field()};
  if (auto identity = dyn_cast<algebra::GroupIdentityOp>(op))
    return json::Array{
        "group.identity",
        cast<algebra::GroupType>(identity.getValue().getType()).getDomain()};
  if (isa<algebra::GroupAddOp>(op))
    return json::Array{"group.add", group()};
  if (isa<algebra::GroupScaleOp>(op))
    return json::Array{
        "group.scale", group(),
        cast<algebra::FieldType>(op.getOperand(1).getType()).getDomain()};
  if (isa<algebra::GroupEqualOp>(op))
    return json::Array{"group.equal", group()};
  if (auto constant = dyn_cast<arith::ConstantOp>(op))
    return json::Array{"bool.constant",
                       cast<IntegerAttr>(constant.getValue()).getInt() != 0};
  if (isa<arith::AndIOp>(op))
    return json::Array{"bool.and"};
  if (isa<arith::OrIOp>(op))
    return json::Array{"bool.or"};
  if (isa<arith::XOrIOp>(op))
    return json::Array{"bool.xor"};
  if (auto compare = dyn_cast<arith::CmpIOp>(op)) {
    if (compare.getPredicate() != arith::CmpIPredicate::eq &&
        compare.getPredicate() != arith::CmpIPredicate::ne)
      return error("common-source-operation", op.getName().getStringRef());
    return json::Array{compare.getPredicate() == arith::CmpIPredicate::eq
                           ? "bool.equal"
                           : "bool.not_equal"};
  }
  if (isa<arith::SelectOp>(op)) {
    if (isa<protocol_ir::ServiceReferenceType>(op.getResult(0).getType()))
      return error("common-source-operation", op.getName().getStringRef());
    auto type = sort(op.getResult(0).getType());
    if (!type)
      return type.takeError();
    return json::Array{"select", std::move(*type)};
  }
  return error("common-source-operation", op.getName().getStringRef());
}

class Exporter {
  protocol_ir::MathematicalOp selected;
  func::FuncOp formula;
  SymbolTable symbols;
  llvm::DenseMap<Value, unsigned> refs;
  json::Array instructions;
  unsigned work = 0;

  Expected<unsigned> ref(Value value) {
    auto found = refs.find(value);
    if (found == refs.end())
      return error("common-source-reference");
    return found->second;
  }
  Error bind(Value value) {
    if (instructions.size() >= 1024)
      return error("common-source-limit");
    for (auto &entry : refs)
      ++entry.second;
    refs[value] = 0;
    return Error::success();
  }
  Expected<json::Array> roles(ArrayAttr values) {
    json::Array result;
    for (Attribute value : values) {
      auto found = llvm::find(selected.getRoles(), value);
      if (found == selected.getRoles().end())
        return error("common-source-role");
      result.push_back(unsigned(found - selected.getRoles().begin()));
    }
    return result;
  }
  Expected<unsigned> role(StringRef name) {
    for (auto [index, value] : llvm::enumerate(selected.getRoles()))
      if (cast<StringAttr>(value).getValue() == name)
        return index;
    return error("common-source-role");
  }

  Expected<SmallVector<unsigned>> body(Block &block, unsigned depth) {
    if (depth > 64)
      return error("common-source-limit");
    for (Operation &op : block) {
      if (++work > 4096 || instructions.size() > 1024)
        return error("common-source-limit");
      if (isa<func::ReturnOp, protocol_ir::MathematicalReturnOp>(op)) {
        SmallVector<unsigned> returned;
        for (Value operand : op.getOperands()) {
          auto value = ref(operand);
          if (!value)
            return value.takeError();
          returned.push_back(*value);
        }
        return returned;
      }
      if (auto call = dyn_cast<func::CallOp>(op)) {
        auto helper = symbols.lookup<func::FuncOp>(call.getCallee());
        if (!helper || helper.isExternal() || !helper.isPrivate() ||
            !llvm::hasSingleElement(helper.getBody()))
          return error("common-source-helper");
        for (auto [formal, actual] :
             llvm::zip(helper.getArguments(), call.getOperands())) {
          auto value = ref(actual);
          if (!value)
            return value.takeError();
          refs[formal] = *value;
        }
        auto returned = body(helper.getBody().front(), depth + 1);
        if (!returned)
          return returned.takeError();
        if (returned->size() != call.getNumResults())
          return error("common-source-helper");
        for (auto [value, index] : llvm::zip(call.getResults(), *returned))
          refs[value] = index;
        continue;
      }
      if (!selected && isa<protocol_ir::StatementOp, protocol_ir::GuardOp,
                           protocol_ir::ExchangeOp, protocol_ir::QueryOp,
                           protocol_ir::RestrictRolesOp>(op))
        return error("common-source-formula-effect");
      json::Array args;
      for (Value operand : op.getOperands()) {
        auto value = ref(operand);
        if (!value)
          return value.takeError();
        args.push_back(*value);
      }
      if (auto statement = dyn_cast<protocol_ir::StatementOp>(op)) {
        if (statement.getAcceptance() != 0 || statement.getNumOperands() > 512)
          return error("common-source-statement");
        json::Array types;
        for (Type type : statement.getOperandTypes()) {
          auto encoded = sort(type);
          if (!encoded)
            return encoded.takeError();
          types.push_back(std::move(*encoded));
        }
        auto selectors = roles(statement.getSelectors());
        if (!selectors)
          return selectors.takeError();
        instructions.push_back(
            json::Array{"statement", statement.getRelation(), std::move(types),
                        std::move(*selectors), std::move(args)});
        continue;
      }
      if (auto guard = dyn_cast<protocol_ir::GuardOp>(op)) {
        auto owner = role(guard.getOwner());
        if (!owner)
          return owner.takeError();
        instructions.push_back(
            json::Array{"guard", guard.getSite(), *owner, std::move(args[0])});
        continue;
      }
      if (op.getNumResults() != 1 || op.getNumRegions())
        return error("common-source-operation", op.getName().getStringRef());
      auto type = sort(op.getResult(0).getType());
      if (!type)
        return type.takeError();
      json::Value instruction = nullptr;
      if (auto exchange = dyn_cast<protocol_ir::ExchangeOp>(op)) {
        auto sender = role(exchange.getSender());
        if (!sender)
          return sender.takeError();
        auto receiver = role(exchange.getReceiver());
        if (!receiver)
          return receiver.takeError();
        instruction =
            json::Array{"exchange", exchange.getSite(), *sender,
                        *receiver,  std::move(*type),   std::move(args[0])};
      } else if (auto query = dyn_cast<protocol_ir::QueryOp>(op)) {
        auto result =
            dyn_cast<algebra::FieldType>(query.getOutputs()[0].getType());
        auto contract = cast<protocol_ir::ServiceReferenceType>(
                            query.getReference().getType())
                            .getContract();
        if (!result || query.getMethod() != "draw" || args.size() != 1 ||
            contract != ("random." + result.getDomain() + "/0").str())
          return error("common-source-service");
        auto owner = role(query.getOwner());
        if (!owner)
          return owner.takeError();
        instruction = json::Array{"draw", query.getSite(), *owner,
                                  result.getDomain(), std::move(args[0])};
      } else if (auto restrict = dyn_cast<protocol_ir::RestrictRolesOp>(op)) {
        auto scope = roles(restrict.getRoles());
        if (!scope)
          return scope.takeError();
        instruction = json::Array{"restrict", std::move(*scope),
                                  std::move(*type), std::move(args[0])};
      } else {
        auto descriptor = operation(op);
        if (!descriptor)
          return descriptor.takeError();
        instruction =
            json::Array{"pure", std::move(*descriptor), std::move(args)};
      }
      if (auto failure = bind(op.getResult(0)))
        return std::move(failure);
      instructions.push_back(std::move(instruction));
    }
    return error("common-source-return");
  }

public:
  Exporter(protocol_ir::MathematicalOp selected, Operation *module)
      : selected(selected), symbols(module) {}
  Exporter(func::FuncOp formula, Operation *module)
      : formula(formula), symbols(module) {}

  Expected<json::Value> run(StringRef bytes) {
    auto type =
        selected ? selected.getFunctionType() : formula.getFunctionType();
    auto &block =
        selected ? selected.getBody().front() : formula.getBody().front();
    if (type.getNumResults() != 1 || type.getNumInputs() > 512 ||
        (selected && selected.getRoles().size() > 16))
      return error("common-source-signature");
    json::Array names, inputs, inputRoles;
    if (selected) {
      for (Attribute name : selected.getRoles())
        names.push_back(cast<StringAttr>(name).getValue());
    } else {
      names.push_back("formula");
    }
    for (auto [index, argument] : llvm::enumerate(block.getArguments())) {
      auto ty = sort(argument.getType());
      if (!ty)
        return ty.takeError();
      inputs.push_back(std::move(*ty));
      refs[argument] = index;
    }
    if (selected) {
      for (Attribute attr : selected.getInputRoles()) {
        auto scope = roles(cast<ArrayAttr>(attr));
        if (!scope)
          return scope.takeError();
        inputRoles.push_back(std::move(*scope));
      }
    } else {
      for (unsigned index = 0; index < type.getNumInputs(); ++index)
        inputRoles.push_back(json::Array{0});
    }
    auto result = sort(type.getResult(0));
    if (!result)
      return result.takeError();
    Expected<json::Array> outputRoles =
        selected ? roles(cast<ArrayAttr>(selected.getOutputRoles()[0]))
                 : Expected<json::Array>(json::Array{0});
    if (!outputRoles)
      return outputRoles.takeError();
    auto returned = body(block, 0);
    if (!returned)
      return returned.takeError();
    auto digest = SHA256::hash(arrayRefFromStringRef(bytes));
    return json::Array{"zkc.common-source/0",
                       "sha256:" + toHex(digest, true),
                       selected ? selected.getSymName() : formula.getSymName(),
                       std::move(names),
                       std::move(inputs),
                       std::move(inputRoles),
                       std::move(*result),
                       std::move(*outputRoles),
                       std::move(instructions),
                       returned->front()};
  }
};
} // namespace

Expected<json::Value> exportCommonSource(StringRef bytes, StringRef name,
                                         MLIRContext &context) {
  if (bytes.size() > 16 * 1024 * 1024 || !mlirNestingWithinLimit(bytes))
    return error("common-source-limit");
  auto original = parseSourceString<ModuleOp>(bytes, &context);
  if (!original || failed(verify(*original)))
    return error("common-source-original");
  if (!llvm::hasSingleElement(original->getBody()->getOperations()))
    return error("common-source-module");
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(original->getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
    return error("common-source-profile");
  SymbolTable symbols(unit);
  auto selected = symbols.lookup<protocol_ir::MathematicalOp>(name);
  auto formula = symbols.lookup<func::FuncOp>(name);
  if (!selected && (!formula || formula.isExternal() || !formula.isPrivate() ||
                    !llvm::hasSingleElement(formula.getBody())))
    return error("common-source-symbol");
  auto exported = selected ? Exporter(selected, unit).run(bytes)
                           : Exporter(formula, unit).run(bytes);
  if (!exported)
    return exported.takeError();
  if (!boundedStrings(*exported) || printJson(*exported).size() > 1024 * 1024)
    return error("common-source-limit");
  return exported;
}
} // namespace zkc::protocol
