// Independent finite reference evaluation of actual admitted native SSA.
// This reader does not consume the exporter or its instruction descriptors.
// Scalar/group values use the explicit additive Z/97 model, not native curves.
#include "../lib/Support/Input.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;
namespace {
using Scalar = std::optional<uint64_t>;

bool taggedArrayJson(const json::Value &value) {
  if (value.getAsObject())
    return false;
  if (auto items = value.getAsArray())
    for (const auto &item : *items)
      if (!taggedArrayJson(item))
        return false;
  return true;
}

json::Value typeJson(Type type) {
  if (type.isInteger(1))
    return json::Array{"bool"};
  if (auto field = dyn_cast<algebra::FieldType>(type))
    return json::Array{"field", field.getDomain()};
  if (auto group = dyn_cast<algebra::GroupType>(type))
    return json::Array{"group", group.getDomain()};
  if (auto service = dyn_cast<protocol_ir::ServiceReferenceType>(type))
    return json::Array{"service", service.getContract()};
  return nullptr;
}
json::Value encode(Type type, Scalar value) {
  if (!value)
    return nullptr;
  if (type.isInteger(1))
    return bool(*value);
  return *value;
}
Expected<Scalar> decode(Type type, const json::Value &json) {
  if (type.isInteger(1)) {
    auto value = json.getAsBoolean();
    if (!value)
      return error("common-run-boolean");
    return Scalar(*value);
  }
  auto value = json.getAsUINT64();
  if (!value || (isa<protocol_ir::ServiceReferenceType>(type) ? *value > 65535
                                                              : *value >= 97))
    return error("common-run-scalar");
  if (typeJson(type).getAsNull())
    return error("common-source-type");
  return Scalar(*value);
}

class Reference {
  protocol_ir::MathematicalOp source;
  SymbolTable symbols;
  StringRef self;
  llvm::DenseMap<Value, Scalar> values;
  const json::Array &replies;
  unsigned position = 0, work = 0;
  json::Array events;
  std::string stopped;

  unsigned role(StringRef name) {
    for (auto [index, value] : llvm::enumerate(source.getRoles()))
      if (cast<StringAttr>(value).getValue() == name)
        return index;
    llvm_unreachable("admitted role");
  }
  bool at(ArrayAttr roles) {
    return llvm::any_of(roles, [&](Attribute role) {
      return cast<StringAttr>(role).getValue() == self;
    });
  }
  Expected<Scalar> read(Value value) {
    auto it = values.find(value);
    if (it == values.end())
      return error("common-source-reference");
    return it->second;
  }
  Scalar action(json::Value request, Type result = {}) {
    if (position == replies.size()) {
      events.push_back(json::Array{std::move(request), json::Array{"missing"}});
      stopped = "incomplete";
      return {};
    }
    const auto &entry = replies[position++];
    events.push_back(json::Array{request, entry});
    auto fields = entry.getAsArray();
    if (!fields || fields->size() != 2 || (*fields)[0] != request) {
      stopped = "refused";
      return {};
    }
    auto reply = (*fields)[1].getAsArray();
    if (!reply || reply->size() != 2) {
      stopped = "refused";
      return {};
    }
    if ((*reply)[0].getAsString() == "stop") {
      auto reason = (*reply)[1].getAsString();
      if (reason && (*reason == "reject" || *reason == "abort" ||
                     *reason == "exhausted" || *reason == "incomplete" ||
                     *reason == "refused"))
        stopped = reason->str();
      else
        stopped = "refused";
      return {};
    }
    if ((*reply)[0].getAsString() != "return") {
      stopped = "refused";
      return {};
    }
    if (!result) {
      if (!(*reply)[1].getAsNull())
        stopped = "refused";
      return 0;
    }
    auto value = decode(result, (*reply)[1]);
    if (!value) {
      consumeError(value.takeError());
      stopped = "refused";
      return {};
    }
    return *value;
  }

  Expected<SmallVector<Scalar>> block(Block &body, unsigned depth) {
    if (depth > 64)
      return error("common-source-limit");
    for (Operation &op : body) {
      if (!stopped.empty())
        return SmallVector<Scalar>{};
      if (++work > 4096)
        return error("common-source-limit");
      SmallVector<Scalar> args;
      for (Value operand : op.getOperands()) {
        auto value = read(operand);
        if (!value)
          return value.takeError();
        args.push_back(*value);
      }
      if (isa<func::ReturnOp, protocol_ir::MathematicalReturnOp>(op))
        return args;
      if (isa<protocol_ir::StatementOp>(op))
        continue;
      if (auto call = dyn_cast<func::CallOp>(op)) {
        auto helper = symbols.lookup<func::FuncOp>(call.getCallee());
        if (!helper || helper.isExternal())
          return error("common-source-helper");
        for (auto [argument, value] : llvm::zip(helper.getArguments(), args))
          values[argument] = value;
        auto result = block(helper.getBody().front(), depth + 1);
        if (!result)
          return result.takeError();
        if (!stopped.empty())
          return SmallVector<Scalar>{};
        for (auto [output, value] : llvm::zip(call.getResults(), *result))
          values[output] = value;
        continue;
      }
      if (auto guard = dyn_cast<protocol_ir::GuardOp>(op)) {
        if (guard.getOwner() == self) {
          if (!args[0])
            stopped = "incomplete";
          else if (!*args[0])
            stopped = "reject";
        }
        continue;
      }
      if (op.getNumResults() != 1 || op.getNumRegions())
        return error("common-source-operation");
      Type type = op.getResult(0).getType();
      Scalar result;
      if (auto exchange = dyn_cast<protocol_ir::ExchangeOp>(op)) {
        if (exchange.getSender() == self) {
          if (!args[0])
            stopped = "incomplete";
          else {
            action(json::Array{"send", exchange.getSite(),
                               role(exchange.getReceiver()), typeJson(type),
                               encode(type, args[0])});
            result = args[0];
          }
        } else if (exchange.getReceiver() == self)
          result =
              action(json::Array{"receive", exchange.getSite(),
                                 role(exchange.getSender()), typeJson(type)},
                     type);
      } else if (auto query = dyn_cast<protocol_ir::QueryOp>(op)) {
        auto field = dyn_cast<algebra::FieldType>(type);
        if (!field || query.getMethod() != "draw" || args.size() != 1)
          return error("common-source-service");
        if (query.getOwner() == self) {
          if (!args[0])
            stopped = "incomplete";
          else
            result = action(json::Array{"draw", query.getSite(),
                                        field.getDomain(), *args[0]},
                            type);
        }
      } else if (auto restriction =
                     dyn_cast<protocol_ir::RestrictRolesOp>(op)) {
        if (at(restriction.getRoles()))
          result = args[0];
      } else {
        // Validate the operation even when its component is absent.
        bool supported =
            isa<algebra::ConstantFieldOp, algebra::FieldAddOp,
                algebra::SubtractFieldOp, algebra::FieldMultiplyOp,
                algebra::FieldEqualOp, algebra::GroupIdentityOp,
                algebra::GroupAddOp, algebra::GroupScaleOp,
                algebra::GroupEqualOp, arith::ConstantOp, arith::AndIOp,
                arith::OrIOp, arith::XOrIOp, arith::CmpIOp, arith::SelectOp>(
                op);
        if (!supported)
          return error("common-source-operation");
        if (auto compare = dyn_cast<arith::CmpIOp>(op))
          if (compare.getPredicate() != arith::CmpIPredicate::eq &&
              compare.getPredicate() != arith::CmpIPredicate::ne)
            return error("common-source-operation");
        if (llvm::all_of(args,
                         [](Scalar value) { return value.has_value(); })) {
          if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op)) {
            uint64_t value = 0;
            for (char digit : constant.getValue())
              value = (value * 10 + unsigned(digit - '0')) % 97;
            result = value;
          } else if (isa<algebra::GroupIdentityOp>(op))
            result = 0;
          else if (auto constant = dyn_cast<arith::ConstantOp>(op))
            result = cast<IntegerAttr>(constant.getValue()).getInt() != 0;
          else if (isa<algebra::FieldAddOp, algebra::GroupAddOp>(op))
            result = (*args[0] + *args[1]) % 97;
          else if (isa<algebra::SubtractFieldOp>(op))
            result = (*args[0] + 97 - *args[1]) % 97;
          else if (isa<algebra::FieldMultiplyOp, algebra::GroupScaleOp>(op))
            result = (*args[0] * *args[1]) % 97;
          else if (isa<algebra::FieldEqualOp, algebra::GroupEqualOp>(op))
            result = *args[0] == *args[1];
          else if (isa<arith::AndIOp>(op))
            result = *args[0] && *args[1];
          else if (isa<arith::OrIOp>(op))
            result = *args[0] || *args[1];
          else if (isa<arith::XOrIOp>(op))
            result = *args[0] != *args[1];
          else if (auto compare = dyn_cast<arith::CmpIOp>(op))
            result = compare.getPredicate() == arith::CmpIPredicate::eq
                         ? *args[0] == *args[1]
                         : *args[0] != *args[1];
          else if (isa<arith::SelectOp>(op))
            result = *args[0] ? *args[1] : *args[2];
        }
      }
      values[op.getResult(0)] = result;
    }
    return error("common-source-return");
  }

public:
  Reference(protocol_ir::MathematicalOp source, Operation *module,
            StringRef self, const json::Array &replies)
      : source(source), symbols(module), self(self), replies(replies) {}
  Expected<json::Value> run(const json::Array &inputs) {
    auto &body = source.getBody().front();
    if (body.getNumArguments() != inputs.size())
      return error("common-run-inputs");
    for (auto [index, input] : llvm::enumerate(inputs)) {
      auto argument = body.getArgument(index);
      bool present = !input.getAsNull();
      if (present != at(cast<ArrayAttr>(source.getInputRoles()[index])))
        return error("common-run-input-scopes");
      if (present) {
        auto value = decode(argument.getType(), input);
        if (!value)
          return value.takeError();
        values[argument] = *value;
      } else
        values[argument] = {};
    }
    auto returned = block(body, 0);
    if (!returned)
      return returned.takeError();
    json::Value outcome = nullptr;
    if (!stopped.empty())
      outcome = json::Array{"stopped", stopped};
    else {
      if (returned->size() != 1)
        return error("common-source-signature");
      auto value = at(cast<ArrayAttr>(source.getOutputRoles()[0]))
                       ? returned->front()
                       : Scalar{};
      outcome = json::Array{
          "returned", encode(source.getFunctionType().getResult(0), value)};
    }
    return json::Array{"zkc.common-result/0", std::move(outcome), position,
                       std::move(events)};
  }
};
} // namespace

int main(int argc, char **argv) {
  auto fail = [](Error failure) {
    errs() << toString(std::move(failure)) << '\n';
    return 1;
  };
  if (argc != 4)
    return fail(error("common-reference-arguments"));
  auto source = readInput(argv[1], 16 * 1024 * 1024);
  if (!source)
    return fail(source.takeError());
  if (!mlirNestingWithinLimit(*source))
    return fail(error("common-source-limit"));
  auto request = readInput(argv[3], 1024 * 1024);
  if (!request)
    return fail(request.takeError());
  auto json = parseNaturalJson(*request, 1024 * 1024, 64, "common-run-format",
                               "common-run-limit");
  if (!json)
    return fail(json.takeError());
  if (!taggedArrayJson(*json))
    return fail(error("common-run-format"));
  auto fields = json->getAsArray();
  if (!fields || fields->size() != 4 ||
      (*fields)[0].getAsString() != "zkc.common-run/0" ||
      !(*fields)[1].getAsUINT64() || !(*fields)[2].getAsArray() ||
      !(*fields)[3].getAsArray())
    return fail(error("common-run-format"));
  if ((*fields)[3].getAsArray()->size() > 2048)
    return fail(error("common-run-limit"));
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  auto module = parseSourceString<ModuleOp>(*source, &context);
  if (!module || failed(verify(*module)) ||
      !llvm::hasSingleElement(module->getBody()->getOperations()))
    return fail(error("common-source-original"));
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(module->getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
    return fail(error("common-source-profile"));
  SymbolTable symbols(unit);
  auto selected = symbols.lookup<protocol_ir::MathematicalOp>(argv[2]);
  auto self = *(*fields)[1].getAsUINT64();
  if (!selected || self >= selected.getRoles().size())
    return fail(error("common-run-role"));
  if (selected.getFunctionType().getNumResults() != 1 ||
      selected.getFunctionType().getNumInputs() > 512 ||
      selected.getRoles().size() > 16)
    return fail(error("common-source-signature"));
  auto result =
      Reference(selected, unit,
                cast<StringAttr>(selected.getRoles()[self]).getValue(),
                *(*fields)[3].getAsArray())
          .run(*(*fields)[2].getAsArray());
  if (!result)
    return fail(result.takeError());
  outs() << printJson(*result) << '\n';
}
