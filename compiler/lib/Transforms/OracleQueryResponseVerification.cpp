#include "NativeBindingApplication.h"
#include "OracleQueryResponse.h"
#include "OracleVerificationContext.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Refusal.h"
#include <set>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
using Controller = OracleQueryController;
// Independently derive the logical layout from the supplied checked helper
// model. This reader neither invokes the producer nor checks helper bodies on
// behalf of the enclosing caller. All helper handles must resolve in this
// immutable context, including after a textual round trip.
bool layout(const OracleVerificationContext &context,
            const OracleQueryExchange &model,
            const OracleQueryResponse &actual) {
  auto unit = context.getUnit();
  auto *ctx = unit.getContext();
  auto index = IntegerType::get(ctx, 64, IntegerType::Unsigned);
  if (model.arms.empty() || model.arms.size() > 32 ||
      model.state.size() < Controller::HeaderSize || model.state.size() > 505 ||
      model.receiverStores.size() > 505 ||
      !all_of(ArrayRef<Type>(model.state).take_front(Controller::HeaderSize),
              [&](Type type) { return type == index; }))
    return false;
  for (auto types :
       {ArrayRef<Type>(model.state), ArrayRef<Type>(model.receiverStores)})
    if (!all_of(types,
                [&](Type type) { return type && type.getContext() == ctx; }))
      return false;
  auto request = dyn_cast_or_null<data::VariantType>(model.request);
  auto response = dyn_cast_or_null<data::VariantType>(model.response);
  if (!request || !response || request.getContext() != ctx ||
      response.getContext() != ctx || request.getAlternatives().size() != 1 ||
      request.getAlternatives()[0].getLabel().getValue() != "Record" ||
      !equal(request.getAlternatives()[0].getPayload(), Types(3, index)) ||
      response.getAlternatives().size() != model.arms.size())
    return false;
  auto signature = [&](func::FuncOp function) -> FunctionType {
    if (!function || function->getParentOp() != unit || !function.isPrivate() ||
        function->hasAttr("runtime.region") ||
        !context.getClosure().bodies.count(function.getSymName().str()))
      return {};
    return scopedDataSignature(function);
  };
  SmallVector<data::AlternativeAttr> alternatives;
  std::set<unsigned> constructors, slots;
  std::set<std::string> names;
  for (auto [ordinal, arm] : enumerate(model.arms)) {
    auto alternative = response.getAlternatives()[ordinal];
    auto reference = dyn_cast_or_null<data::VariantType>(arm.reference);
    if (!constructors.insert(arm.constructor).second ||
        !slots.insert(arm.receiverSlot).second ||
        !names.insert(arm.alternative).second || arm.opened.size() != 2 ||
        alternative.getLabel().getValue() != arm.alternative ||
        !equal(alternative.getPayload(), arm.opened) || !reference ||
        reference.getAlternatives().size() != 1 ||
        reference.getAlternatives()[0].getLabel().getValue() != "Record" ||
        !equal(reference.getAlternatives()[0].getPayload(), Types(2, index)) ||
        arm.receiverSlot >= model.receiverStores.size())
      return false;
    auto lookup = signature(arm.receiverLookup);
    auto authenticate = signature(arm.authenticate);
    auto resume = signature(arm.resume);
    if (!lookup || !authenticate || !resume || lookup.getNumResults() > 512 ||
        !equal(lookup.getInputs(),
               Types{arm.reference, model.receiverStores[arm.receiverSlot]}) ||
        arm.root >= lookup.getNumResults() ||
        arm.receiverRows >= lookup.getNumResults() ||
        lookup.getResult(arm.receiverRows) != index ||
        !equal(authenticate.getInputs(),
               Types{lookup.getResult(arm.root), index, index, arm.opened[0],
                     arm.opened[1]}) ||
        authenticate.getNumResults() != 1 ||
        arm.kind >= model.state.size() - Controller::HeaderSize)
      return false;
    auto answer = authenticate.getResult(0);
    auto arena = dyn_cast<data::SequenceType>(
        model.state[Controller::HeaderSize + arm.kind]);
    Types resumed(model.state.begin(), model.state.end());
    append_range(resumed, Types(5, index));
    resumed.push_back(answer);
    if (!arena || arena.getElementType() != answer ||
        !equal(resume.getInputs(), resumed) ||
        !equal(resume.getResults(), model.state))
      return false;
    alternatives.push_back(data::AlternativeAttr::get(
        ctx, StringAttr::get(ctx, arm.alternative), ArrayRef<Type>{answer}));
  }
  auto identity = data::importVariantIdentity(
      ctx, json::Array{"zkc.oracle.checked-answer/0",
                       data::exportVariantIdentity(response.getIdentity())});
  if (!identity)
    return false;
  auto answer = data::VariantType::getChecked(
      unit.getLoc(), ctx, identity,
      ArrayRef<data::AlternativeAttr>(alternatives));
  return answer && actual.answer == answer && actual.authenticate &&
         actual.resume && actual.authenticate != actual.resume;
}
struct Reader {
  const OracleVerificationContext &context;
  const OracleQueryResponse &response;
  const OracleQueryExchange &model;
  protocol_ir::ProtocolModuleOp unit;
  const SourceExecutionClosure &closure;
  Type index, scope, boolean;
  bool valid = true;
  Reader(const OracleVerificationContext &context,
         const OracleQueryExchange &model, const OracleQueryResponse &response)
      : context(context), response(response), model(model),
        unit(context.getUnit()), closure(context.getClosure()),
        index(IntegerType::get(unit.getContext(), 64, IntegerType::Unsigned)),
        scope(runtime::ScopeType::get(unit.getContext())),
        boolean(IntegerType::get(unit.getContext(), 1)) {}
  bool expect(bool value) {
    valid &= value;
    return valid;
  }
  struct Cursor {
    Reader &reader;
    ArrayRef<SourceExecutionStep> steps;
    unsigned offset = 0;
    const SourceExecutionStep *take(StringRef operation, StringRef site) {
      if (!reader.valid)
        return nullptr;
      if (!reader.expect(offset < steps.size()))
        return nullptr;
      const auto &step = steps[offset++];
      auto actual = step.operation->getAttrOfType<StringAttr>(
          operation == "func.call" ? "runtime.site" : "site");
      if (!reader.expect(step.operation->getName().getStringRef() ==
                             operation &&
                         actual && actual.getValue() == site))
        return nullptr;
      return &step;
    }
    Values result(const SourceExecutionStep *step, TypeRange types,
                  ValueRange inputs, unsigned regions = 0) {
      if (!reader.valid || !step)
        return Values(types.size());
      if (!reader.expect(equal(step->inputs, inputs) &&
                         step->regions.size() == regions &&
                         equal(ValueRange(step->outputs).getTypes(), types)))
        return Values(types.size());
      return step->outputs;
    }
    Values apply(StringRef contract, TypeRange outputs, ValueRange inputs,
                 StringRef site, ArrayRef<std::string> statics = {},
                 ArrayRef<std::string> parameters = {}) {
      auto *step = take("exec.apply", site);
      auto values = result(step, outputs, inputs);
      if (!reader.valid)
        return values;
      auto op = cast<exec::ApplyOp>(step->operation);
      auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
          op, op.getBindingAttr());
      if (!reader.expect(binding && binding.getContract() == contract &&
                         binding.getImplementation().empty() &&
                         binding.getArguments().size() == statics.size() &&
                         op.getParameters().size() == parameters.size()))
        return values;
      SmallVector<Attribute> arguments;
      for (const auto &identity : statics)
        arguments.push_back(StringAttr::get(op.getContext(), identity));
      reader.expect(matchesNativeBinding(
          binding, {contract.str(), std::move(arguments), {}}));
      reader.expect(
          invocationParametersMatch(contract, binding.getArgumentsAttr(),
                                    op.getParametersAttr(), parameters));
      return values;
    }
    Value number(uint64_t value, StringRef site) {
      return apply("index.constant", reader.index, {}, site, {},
                   {std::to_string(value)})
          .front();
    }
    Values local(ValueRange inputs, TypeRange outputs, StringRef site,
                 func::FuncOp &callee) {
      auto *step = take("func.call", site);
      auto values = result(step, outputs, inputs);
      if (reader.valid) {
        auto call = cast<func::CallOp>(step->operation);
        callee = dyn_cast_or_null<func::FuncOp>(
            SymbolTable::lookupSymbolIn(reader.unit, call.getCallee()));
        reader.expect(bool(callee));
      }
      return values;
    }
    Values call(func::FuncOp expected, ValueRange inputs, StringRef site) {
      if (!reader.valid)
        return Values(
            expected ? cast<exec::OutcomeType>(expected.getResultTypes()[0])
                           .getPayload()
                           .size()
                     : 0);
      func::FuncOp actual;
      auto types =
          cast<exec::OutcomeType>(expected.getResultTypes()[0]).getPayload();
      auto values = local(inputs, types, site, actual);
      reader.expect(actual == expected);
      return values;
    }
    Value pack(Type type, StringRef alternative, ValueRange fields,
               StringRef site) {
      auto *step = take("exec.variant", site);
      auto values = result(step, type, fields);
      if (reader.valid)
        reader.expect(cast<exec::VariantOp>(step->operation).getAlternative() ==
                      alternative);
      return values.front();
    }
    Values match(Value input, ValueRange captures, TypeRange outputs,
                 ArrayRef<std::string> alternatives, StringRef site,
                 llvm::function_ref<void(unsigned, func::FuncOp)> check) {
      auto *step = take("exec.match", site);
      Values inputs{input};
      append_range(inputs, captures);
      auto values = result(step, outputs, inputs, alternatives.size());
      if (!reader.valid)
        return values;
      auto actual = cast<exec::MatchOp>(step->operation).getAlternatives();
      if (!reader.expect(actual.size() == alternatives.size()))
        return values;
      for (auto [i, name] : enumerate(alternatives)) {
        if (!reader.expect(cast<StringAttr>(actual[i]).getValue() == name))
          return values;
        check(i, step->regions[i]);
      }
      return values;
    }
    void finish(ValueRange values, bool region = false) {
      if (!reader.valid)
        return;
      if (!reader.expect(offset + 1 == steps.size()))
        return;
      const auto &last = steps[offset++];
      reader.expect((region ? isa<exec::CompleteOp>(last.operation)
                            : isa<exec::ReturnOp>(last.operation)) &&
                    last.regions.empty() && last.outputs.empty() &&
                    equal(last.inputs, values));
    }
  };
  void body(func::FuncOp function, TypeRange inputs, TypeRange outputs,
            bool region, llvm::function_ref<void(Cursor &, ValueRange)> check) {
    if (!valid)
      return;
    Types arguments{scope};
    append_range(arguments, inputs);
    if (!expect(function && function->getParentOp() == unit &&
                function.isPrivate() &&
                !function->hasAttr("data.preconditions") &&
                function->getAttrOfType<UnitAttr>("no_inline") &&
                function->hasAttr("runtime.region") == region &&
                equal(function.getArgumentTypes(), arguments) &&
                function.getResultTypes().size() == 1))
      return;
    auto outcome = dyn_cast<exec::OutcomeType>(function.getResultTypes()[0]);
    if (!expect(outcome && equal(outcome.getPayload(), outputs)))
      return;
    if (region) {
      if (!expect(function->getAttrOfType<UnitAttr>("runtime.region") &&
                  !function->hasAttr("runtime.origin")))
        return;
    } else {
      auto origin = function->getAttrOfType<ArrayAttr>("runtime.origin");
      auto expected = ArrayAttr::get(
          unit.getContext(),
          {StringAttr::get(unit.getContext(), function.getSymName()),
           ArrayAttr::get(unit.getContext(), {})});
      if (!expect(origin == expected))
        return;
    }
    auto found = closure.bodies.find(function.getSymName().str());
    if (!expect(found != closure.bodies.end()))
      return;
    Cursor cursor{*this, found->second};
    check(cursor, function.getArguments().drop_front());
    expect(cursor.offset == cursor.steps.size());
  }

  void requireEqual(Cursor &c, Value left, Value right, StringRef site) {
    auto predicate = c.apply("index.equal", boolean, {left, right},
                             site.str() + "_equal")[0];
    c.apply("control.require", {}, predicate, site);
  }
  void requireNumber(Cursor &c, Value actual, unsigned expected,
                     StringRef site) {
    auto constant = c.number(expected, site.str() + "_expected");
    requireEqual(c, actual, constant, site);
  }
  std::vector<std::string> alternatives() {
    std::vector<std::string> names;
    for (const auto &arm : model.arms)
      names.push_back(arm.alternative);
    return names;
  }
  void authenticate() {
    Types inputs{model.request, model.response};
    append_range(inputs, model.receiverStores);
    body(response.authenticate, inputs, response.answer, false,
         [&](Cursor &c, ValueRange args) {
           c.finish(c.match(
               args[0], args.drop_front(), response.answer, {"Record"},
               "authenticate_request", [&](unsigned, func::FuncOp request) {
                 Types types(3, index);
                 types.push_back(model.response);
                 append_range(types, model.receiverStores);
                 body(request, types, response.answer, true,
                      [&](Cursor &unpacked, ValueRange fields) {
                        Values captures(fields.take_front(3));
                        append_range(captures, fields.drop_front(4));
                        unpacked.finish(
                            unpacked.match(
                                fields[3], captures, response.answer,
                                alternatives(), "authenticate_response",
                                [&](unsigned ordinal, func::FuncOp selected) {
                                  const auto &arm = model.arms[ordinal];
                                  Types types(arm.opened.begin(), arm.opened.end());
                                  append_range(types, Types(3, index));
                                  append_range(types, model.receiverStores);
                                  body(selected, types, response.answer, true,
                                       [&](Cursor &c, ValueRange a) {
                                         std::string prefix =
                                             "constructor_" +
                                             std::to_string(arm.constructor) +
                                             "_";
                                         requireNumber(
                                             c, a[2], arm.constructor,
                                             prefix + "request_constructor");
                                         auto reference = c.pack(
                                             arm.reference, "Record",
                                             a.slice(2, 2), prefix + "anchor");
                                         auto stored =
                                             c.call(arm.receiverLookup,
                                                    {reference,
                                                     a[5 + arm.receiverSlot]},
                                                    prefix + "load_anchor");
                                         auto answer =
                                             c.call(arm.authenticate,
                                                    {stored[arm.root],
                                                     stored[arm.receiverRows],
                                                     a[4], a[0], a[1]},
                                                    prefix + "authenticate");
                                         c.finish(
                                             c.pack(response.answer,
                                                    arm.alternative, answer,
                                                    prefix + "checked_answer"),
                                             true);
                                       });
                                }),
                            true);
                      });
               }));
         });
  }
  void resume() {
    Types inputs{model.request, response.answer};
    append_range(inputs, model.state);
    body(response.resume, inputs, model.state, false,
         [&](Cursor &c, ValueRange args) {
           c.finish(c.match(
               args[0], args.drop_front(), model.state, {"Record"},
               "resume_request", [&](unsigned, func::FuncOp request) {
                 Types types(3, index);
                 types.push_back(response.answer);
                 append_range(types, model.state);
                 body(request, types, model.state, true,
                      [&](Cursor &unpacked, ValueRange fields) {
                        Values captures(fields.take_front(3));
                        append_range(captures, fields.drop_front(4));
                        unpacked.finish(
                            unpacked.match(
                                fields[3], captures, model.state,
                                alternatives(), "resume_answer",
                                [&](unsigned ordinal, func::FuncOp selected) {
                                  const auto &arm = model.arms[ordinal];
                                  auto answer =
                                      scopedDataSignature(arm.authenticate)
                                          .getResult(0);
                                  Types types{answer};
                                  append_range(types, Types(3, index));
                                  append_range(types, model.state);
                                  body(selected, types, model.state, true,
                                       [&](Cursor &c, ValueRange a) {
                                         auto state = a.drop_front(4);
                                         std::string prefix =
                                             "constructor_" +
                                             std::to_string(arm.constructor) +
                                             "_";
                                         requireNumber(
                                             c, state[Controller::Phase],
                                             Controller::Request,
                                             prefix + "request_phase");
                                         requireNumber(
                                             c, state[Controller::Constructor],
                                             arm.constructor,
                                             prefix + "state_constructor");
                                         requireNumber(
                                             c, state[Controller::Kind],
                                             arm.kind, prefix + "request_kind");
                                         for (unsigned field = 0; field < 3;
                                              ++field)
                                           requireEqual(
                                               c, state[field], a[1 + field],
                                               prefix + "request_field_" +
                                                   std::to_string(field));
                                         Values resumed(state);
                                         append_range(resumed,
                                                      state.take_front(5));
                                         resumed.push_back(a[0]);
                                         c.finish(c.call(arm.resume, resumed,
                                                         prefix + "resume"),
                                                  true);
                                       });
                                }),
                            true);
                      });
               }));
         });
  }
};
} // namespace
Error checkOracleQueryResponse(const OracleVerificationContext &context,
                               const OracleQueryExchange &model,
                               const OracleQueryResponse &actual) {
  if (!layout(context, model, actual))
    return error("oracle-response-body");
  Reader reader(context, model, actual);
  reader.authenticate();
  reader.resume();
  return reader.valid ? Error::success() : error("oracle-response-body");
}
} // namespace zkc::protocol
