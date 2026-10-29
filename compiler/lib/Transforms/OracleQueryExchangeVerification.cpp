#include "OracleQueryExchange.h"
#include "OracleVerificationContext.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
struct Reader {
  const OracleVerificationContext &context;
  const OracleExchangeRecipe &recipe;
  const OracleQueryExchange &model;
  protocol_ir::ProtocolModuleOp unit;
  const SourceExecutionClosure &closure;
  Type index, scope, boolean;
  bool valid = true;
  Reader(const OracleVerificationContext &context,
         const OracleExchangeRecipe &recipe)
      : context(context), recipe(recipe), model(*recipe.exchange),
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
      for (auto [actual, expected] : zip(binding.getArguments(), statics))
        reader.expect(cast<StringAttr>(actual).getValue() == expected);
      for (auto [actual, expected] : zip(op.getParameters(), parameters))
        reader.expect(cast<StringAttr>(actual).getValue() == expected);
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
    Values conditional(Value condition, ValueRange captures, TypeRange outputs,
                       StringRef site,
                       llvm::function_ref<void(unsigned, func::FuncOp)> check) {
      auto *step = take("exec.test", site);
      Values inputs{condition};
      append_range(inputs, captures);
      auto values = result(step, outputs, inputs, 2);
      if (reader.valid)
        for (unsigned branch = 0; branch < 2; ++branch)
          check(branch, step->regions[branch]);
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
                function->hasAttr("runtime.region") == region &&
                equal(function.getArgumentTypes(), arguments) &&
                function.getResultTypes().size() == 1))
      return;
    auto outcome = dyn_cast<exec::OutcomeType>(function.getResultTypes()[0]);
    if (!expect(outcome && equal(outcome.getPayload(), outputs)))
      return;
    auto found = closure.bodies.find(function.getSymName().str());
    if (!expect(found != closure.bodies.end()))
      return;
    Cursor cursor{*this, found->second};
    check(cursor, function.getArguments().drop_front());
    expect(cursor.offset == cursor.steps.size());
  }

  Value equalIndex(Cursor &c, Value actual, unsigned expected, StringRef site) {
    auto constant = c.number(expected, site.str() + "_expected");
    return c.apply("index.equal", boolean, {actual, constant}, site)[0];
  }
  void require(Cursor &c, Value actual, unsigned expected, StringRef site) {
    c.apply("control.require", {}, equalIndex(c, actual, expected, site),
            site.str() + "_guard");
  }
  Value opening(Cursor &c, ValueRange inputs, unsigned ordinal) {
    const auto &arm = model.arms[ordinal];
    std::string prefix = "constructor_" + std::to_string(arm.constructor) + "_";
    auto reference = c.pack(arm.reference, "Record", inputs.take_front(2),
                            prefix + "anchor");
    auto stored = c.call(arm.holderLookup, {reference, inputs[3 + ordinal]},
                         prefix + "load_anchor");
    auto opened = c.call(
        arm.open, {stored[arm.openingState], stored[arm.holderRows], inputs[2]},
        prefix + "open");
    return c.pack(model.response, arm.alternative, opened, prefix + "response");
  }
  Value dispatch(Cursor &c, ValueRange inputs, unsigned ordinal) {
    const auto &arm = model.arms[ordinal];
    std::string prefix = "constructor_" + std::to_string(arm.constructor) + "_";
    auto selected = equalIndex(c, inputs[0], arm.constructor,
                               prefix + "select_constructor");
    if (ordinal + 1 == model.arms.size()) {
      c.apply("control.require", {}, selected, prefix + "admit_constructor");
      return opening(c, inputs, ordinal);
    }
    return c.conditional(selected, inputs, model.response, prefix + "dispatch",
                         [&](unsigned branch, func::FuncOp function) {
                           body(function, inputs.getTypes(), model.response,
                                true, [&](Cursor &region, ValueRange args) {
                                  region.finish(
                                      branch == 0
                                          ? opening(region, args, ordinal)
                                          : dispatch(region, args, ordinal + 1),
                                      true);
                                });
                         })[0];
  }
  bool check(func::FuncOp function) {
    if (!expect(function && function.getSymName() == recipe.name))
      return false;
    body(function, recipe.inputs, recipe.outputs, false,
         [&](Cursor &c, ValueRange inputs) {
           if (recipe.action == OracleExchangeAction::Open) {
             Types captures(3, index);
             append_range(captures, model.holderStores);
             auto output = c.match(
                 inputs[0], inputs.drop_front(), model.response, {"Record"},
                 "request", [&](unsigned, func::FuncOp function) {
                   body(function, captures, model.response, true,
                        [&](Cursor &region, ValueRange args) {
                          region.finish(dispatch(region, args, 0), true);
                        });
                 });
             c.finish(output);
             return;
           }
           std::vector<std::string> alternatives;
           for (const auto &arm : model.arms)
             alternatives.push_back(arm.alternative);
           auto output = c.match(
               inputs[0], inputs.drop_front(), model.state, alternatives,
               "response", [&](unsigned ordinal, func::FuncOp function) {
                 const auto &arm = model.arms[ordinal];
                 Types types(arm.opened.begin(), arm.opened.end());
                 append_range(types, model.state);
                 append_range(types, model.receiverStores);
                 body(function, types, model.state, true,
                      [&](Cursor &region, ValueRange args) {
                        using C = OracleQueryController;
                        std::string prefix = "constructor_" +
                                             std::to_string(arm.constructor) +
                                             "_";
                        auto state =
                            args.drop_front(2).take_front(model.state.size());
                        auto stores = args.drop_front(2 + model.state.size());
                        require(region, state[C::Phase], C::Request,
                                prefix + "request_phase");
                        require(region, state[C::Constructor], arm.constructor,
                                prefix + "request_constructor");
                        require(region, state[C::Kind], arm.kind,
                                prefix + "request_kind");
                        auto reference = region.pack(
                            arm.reference, "Record",
                            {state[C::Constructor], state[C::Instance]},
                            prefix + "anchor");
                        auto stored =
                            region.call(arm.receiverLookup,
                                        {reference, stores[arm.receiverSlot]},
                                        prefix + "load_anchor");
                        auto answer = region.call(
                            arm.authenticate,
                            {stored[arm.root], stored[arm.receiverRows],
                             state[C::Position], args[0], args[1]},
                            prefix + "authenticate");
                        Values resumed(state.begin(), state.end());
                        append_range(resumed, state.take_front(5));
                        resumed.push_back(answer[0]);
                        region.finish(
                            region.call(arm.resume, resumed, prefix + "resume"),
                            true);
                      });
               });
           c.finish(output);
         });
    return valid;
  }
};
} // namespace
bool checkOracleQueryExchange(const OracleVerificationContext &context,
                              func::FuncOp actual,
                              const OracleExchangeRecipe &recipe) {
  return Reader(context, recipe).check(actual);
}
} // namespace zkc::protocol
