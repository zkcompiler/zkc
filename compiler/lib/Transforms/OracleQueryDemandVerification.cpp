#include "NativeBindingApplication.h"
#include "OracleQueryDemand.h"
#include "OracleVerificationContext.h"
#include "OracleVirtualRecipe.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include <map>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
namespace pir = protocol_ir;
using Demand = OracleQueryDemand;
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
// Layout is derived independently of the producer and carries no candidate
// transition inventory. The controller itself is checked against source first.
Error layout(const OracleVerificationContext &target,
             const OracleVerificationContext &source,
             const OracleAnchorStorage &storage,
             const OracleQueryController &controller, pir::OracleKindAttr root,
             const Demand &actual, unsigned &rootKind,
             std::vector<OracleVirtualRecipe> &recipes) {
  auto refuse = [] { return error("oracle-demand-body"); };
  if (!root || !any_of(controller.kinds, [&](auto kind) {
        return sameOracleReferenceKind(kind, root);
      }))
    return refuse();
  rootKind =
      find_if(controller.kinds,
              [&](auto kind) { return sameOracleReferenceKind(kind, root); }) -
      controller.kinds.begin();
  auto *context = target.getModule().getContext();
  auto index = IntegerType::get(context, 64, IntegerType::Unsigned);
  VariantDescriptor descriptor{
      json::Array{"zkc.oracle.demand-frame/0", toHex(storage.entry, true),
                  toHex(controller.role, true)},
      {{"Record", std::vector<std::string>(Demand::FrameSize, "index")}}};
  auto spelling = encodeVariant(descriptor);
  if (!spelling || spelling->size() > 4 * 1024 * 1024)
    return refuse();
  auto nominal = data::importVariantIdentity(context, descriptor.nominal);
  auto arm =
      data::AlternativeAttr::get(context, StringAttr::get(context, "Record"),
                                 Types(Demand::FrameSize, index));
  Type frame = nominal ? data::VariantType::getChecked(
                             target.getModule().getLoc(), context, nominal,
                             ArrayRef<data::AlternativeAttr>{arm})
                       : data::VariantType{};
  if (!frame)
    return refuse();
  auto sequence = constructLogicalType(
      [&] { return emitError(target.getModule().getLoc()); }, context,
      {"sequence", {TypeAttr::get(frame)}});
  std::vector<Type> state(Demand::HeaderSize, index);
  state.push_back(sequence);
  if (!sequence || actual.frame != frame || actual.sequence != sequence ||
      actual.state != state)
    return refuse();
  // Re-read source order, including duplicate and unused queries. The neutral
  // source recipe expands total calls; it emits no helper and evaluates none.
  OracleVirtualFunctionWork work;
  for (const auto &item : controller.constructors) {
    const auto &anchor = storage.constructors[item.source];
    OracleVirtualRecipe recipe;
    if (anchor.constructor == OracleAnchorConstructor::Kind::Virtual) {
      auto definition = dyn_cast_or_null<pir::OracleDefinitionOp>(
          SymbolTable::lookupSymbolIn(source.getUnit(), anchor.declaration));
      if (!definition)
        return refuse();
      auto planned = planOracleVirtualFunctions(definition, work);
      if (!planned)
        return planned.takeError();
      recipe = std::move(*planned);
    }
    if (recipe.queries.size() != item.functions.queries.size())
      return refuse();
    recipes.push_back(std::move(recipe));
  }
  return Error::success();
}
struct Reader {
  const OracleVerificationContext &context;
  const OracleAnchorStorage &storage;
  const OracleQueryController &controller;
  const Demand &model;
  const std::vector<OracleVirtualRecipe> &recipes;
  unsigned rootKind;
  pir::ProtocolModuleOp unit;
  const SourceExecutionClosure &closure;
  Type index, scope, boolean;
  bool valid = true;
  Reader(const OracleVerificationContext &context,
         const OracleAnchorStorage &storage,
         const OracleQueryController &controller, const Demand &model,
         const std::vector<OracleVirtualRecipe> &recipes, unsigned rootKind)
      : context(context), storage(storage), controller(controller),
        model(model), recipes(recipes), rootKind(rootKind),
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
    std::map<uint64_t, Value> constants{};
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
                 StringRef site, ArrayRef<Attribute> statics = {},
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
      reader.expect(matchesNativeBinding(
          binding, {contract.str(), SmallVector<Attribute>(statics), {}}));
      reader.expect(
          invocationParametersMatch(contract, binding.getArgumentsAttr(),
                                    op.getParametersAttr(), parameters));
      return values;
    }
    Value number(uint64_t value, StringRef site) {
      // Only a previously read exact constant in this successful body may
      // be reused. Each outlined body has a fresh cursor and literal table.
      auto found = constants.find(value);
      if (found != constants.end())
        return found->second;
      auto literal = apply("index.constant", reader.index, {}, site, {},
                           {std::to_string(value)})
                         .front();
      constants.emplace(value, literal);
      return literal;
    }
    Value compare(StringRef contract, Value left, Value right, StringRef site) {
      return apply(contract, reader.boolean, {left, right}, site).front();
    }
    void require(Value predicate, StringRef site) {
      apply("control.require", {}, predicate, site);
    }
    void equalTo(Value value, uint64_t expected, StringRef site) {
      auto constant = number(expected, site.str() + "_expected");
      auto equality =
          compare("index.equal", value, constant, site.str() + "_equal");
      require(equality, site);
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
    Value compute(func::FuncOp expected, ValueRange inputs, StringRef site) {
      auto *step = take("exec.compute", site);
      auto values = result(step, expected.getResultTypes(), inputs);
      if (reader.valid) {
        auto op = cast<exec::ComputeOp>(step->operation);
        auto actual = SymbolTable::lookupSymbolIn(reader.unit, op.getCallee());
        reader.expect(actual == expected.getOperation());
      }
      return values.front();
    }
    Value pack(Type type, ValueRange fields, StringRef site) {
      auto *step = take("exec.variant", site);
      auto values = result(step, type, fields);
      if (reader.valid)
        reader.expect(cast<exec::VariantOp>(step->operation).getAlternative() ==
                      "Record");
      return values.front();
    }
    Values unpack(Value value, TypeRange fields, StringRef site) {
      auto *step = take("exec.match", site);
      auto values = result(step, fields, value, 1);
      if (!reader.valid)
        return values;
      auto op = cast<exec::MatchOp>(step->operation);
      if (!reader.expect(op.getAlternatives().size() == 1 &&
                         cast<StringAttr>(op.getAlternatives()[0]).getValue() ==
                             "Record"))
        return values;
      reader.body(step->regions[0], fields, fields, true,
                  [&](Cursor &body, ValueRange arguments) {
                    body.finish(arguments, true);
                  });
      return values;
    }
    Value empty(Type sequence, StringRef site) {
      return apply("sequence.empty", sequence, {}, site,
                   {reader.element(sequence)})
          .front();
    }
    Value append(Type sequence, Value previous, Value value, StringRef site) {
      return apply("sequence.append", sequence, {previous, value}, site,
                   {reader.element(sequence)})
          .front();
    }
    Value at(Type sequence, Type element, Value values, Value offset,
             StringRef site) {
      return apply("sequence.at", element, {values, offset}, site,
                   {reader.element(sequence)})
          .front();
    }
    Value length(Type sequence, Value values, StringRef site) {
      return apply("sequence.length", reader.index, values, site,
                   {reader.element(sequence)})
          .front();
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
    Values loop(Value lower, Value upper, ValueRange state, ValueRange stores,
                TypeRange outputs, bool conditional, StringRef site,
                llvm::function_ref<void(func::FuncOp)> check) {
      auto *step = take("exec.range", site);
      Values inputs{lower, upper};
      append_range(inputs, state);
      append_range(inputs, stores);
      auto values = result(step, outputs, inputs, 1);
      if (reader.valid && reader.expect(step->conditional == conditional))
        check(step->regions[0]);
      return values;
    }
    Values loop(Value lower, Value upper, ValueRange state, ValueRange stores,
                StringRef site, llvm::function_ref<void(func::FuncOp)> check) {
      return loop(lower, upper, state, stores, reader.model.state, true, site,
                  check);
    }
    void reject(StringRef reason, StringRef site) {
      auto *step = take("exec.reject", site);
      if (!reader.valid)
        return;
      reader.expect(cast<exec::RejectOp>(step->operation).getReason() ==
                        reason &&
                    step->inputs.empty() && step->outputs.empty() &&
                    step->regions.empty() && offset == steps.size());
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
  Attribute element(Type sequence) {
    return TypeAttr::get(cast<data::SequenceType>(sequence).getElementType());
  }
  Types allTypes() {
    Types types(model.state.begin(), model.state.end());
    append_range(types, controller.stores);
    return types;
  }
  Values state(ValueRange values) {
    return Values(values.take_front(model.state.size()));
  }
  ValueRange stores(ValueRange values) {
    return values.drop_front(model.state.size());
  }
  unsigned kindNumber(pir::OracleKindAttr kind) {
    for (auto [i, current] : enumerate(controller.kinds))
      if (sameOracleReferenceKind(current, kind))
        return i;
    llvm_unreachable("validated controller kind inventory");
  }
  unsigned field(unsigned constructor, StringRef name) {
    const auto &item = controller.constructors[constructor];
    const auto &fields =
        storage.constructors[item.source].roles[item.role].fields;
    for (auto [i, f] : enumerate(fields))
      if (f.name == name)
        return i;
    llvm_unreachable("derived anchor field inventory");
  }
  Values load(Cursor &c, unsigned constructor, Value tag, Value instance,
              Value store) {
    auto &item = controller.constructors[constructor];
    return c.call(item.lookup, {tag, instance, store}, "load_anchor");
  }
  Values parameters(unsigned constructor, ValueRange record, Value position) {
    Values inputs;
    const auto &item = controller.constructors[constructor];
    const auto &fields =
        storage.constructors[item.source].roles[item.role].fields;
    for (auto [i, f] : enumerate(fields))
      if (StringRef(f.name).starts_with("parameter."))
        inputs.push_back(record[i]);
    inputs.push_back(position);
    return inputs;
  }
  void child(Cursor &c, Values &values, unsigned constructor, unsigned query,
             ValueRange record) {
    const auto &expected = recipes[constructor].queries[query];
    auto offset =
        c.length(model.sequence, values[Demand::Frames], "frame_index");
    auto nextChild = c.number(query + 1, "next_child");
    Values saved{values[Demand::Constructor], values[Demand::Instance],
                 values[Demand::Position], nextChild,
                 values[Demand::Continuation]};
    auto packed = c.pack(model.frame, saved, "frame_record");
    values[Demand::Frames] =
        c.append(model.sequence, values[Demand::Frames], packed, "save_frame");
    auto one = c.number(1, "continuation_offset");
    auto continuation =
        c.apply("index.add", index, {offset, one}, "child_continuation")
            .front();
    auto position = c.compute(
        controller.constructors[constructor].functions.queries[query].position,
        parameters(constructor, record, values[Demand::Position]),
        "child_position");
    auto reference = c.unpack(
        record[field(constructor, "source." + std::to_string(expected.source))],
        TypeRange{index, index}, "child_reference");
    values[Demand::Constructor] = reference[0];
    values[Demand::Instance] = reference[1];
    values[Demand::Position] = position;
    values[Demand::Kind] = c.number(kindNumber(expected.kind), "child_kind");
    values[Demand::Continuation] = continuation;
    values[Demand::Phase] = c.number(0, "enter_child");
  }
  void enter(func::FuncOp function, unsigned constructor) {
    body(function, allTypes(), model.state, false,
         [&](Cursor &c, ValueRange inputs) {
           auto values = state(inputs);
           const auto &item = controller.constructors[constructor];
           c.equalTo(values[Demand::Kind], item.kind, "kind");
           auto record =
               load(c, constructor, values[Demand::Constructor],
                    values[Demand::Instance], stores(inputs)[constructor]);
           auto predicate =
               c.compare("index.less", values[Demand::Position],
                         record[field(constructor, "shape.rows")], "domain");
           Types captureTypes = allTypes();
           for (const auto &field :
                storage.constructors[item.source].roles[item.role].fields)
             captureTypes.push_back(field.type);
           Values captures(inputs);
           append_range(captures, record);
           auto result = c.conditional(
               predicate, captures, model.state, "domain_branch",
               [&](unsigned branch, func::FuncOp region) {
                 body(
                     region, captureTypes, model.state, true,
                     [&](Cursor &body, ValueRange arguments) {
                       auto next = state(arguments);
                       if (branch == 1)
                         next[Demand::Phase] = body.number(3, "domain_cut");
                       else if (storage.constructors[item.source].constructor !=
                                OracleAnchorConstructor::Kind::Virtual)
                         next[Demand::Phase] = body.number(2, "request");
                       else if (recipes[constructor].queries.empty())
                         next[Demand::Phase] = body.number(1, "empty_return");
                       else
                         child(body, next, constructor, 0,
                               arguments.drop_front(allTypes().size()));
                       body.finish(next, true);
                     });
               });
           c.finish(result);
         });
  }
  Types returnTypes() {
    auto types = allTypes();
    types.push_back(index);
    return types;
  }
  void parent(func::FuncOp function, unsigned constructor) {
    SmallVector<unsigned> cases;
    for (unsigned i = 1; i <= recipes[constructor].queries.size(); ++i)
      cases.push_back(i);
    dispatch(function, returnTypes().size() - 1, cases, returnTypes(),
             model.state, [&](unsigned nextChild, func::FuncOp leaf) {
               body(leaf, returnTypes(), model.state, false,
                    [&](Cursor &c, ValueRange inputs) {
                      auto values = state(inputs);
                      const auto &item = controller.constructors[constructor];
                      c.equalTo(
                          values[Demand::Kind],
                          kindNumber(
                              recipes[constructor].queries[nextChild - 1].kind),
                          "returned_kind");
                      values[Demand::Kind] = c.number(item.kind, "parent_kind");
                      if (nextChild == recipes[constructor].queries.size())
                        values[Demand::Phase] = c.number(1, "return_parent");
                      else {
                        auto record =
                            load(c, constructor, values[Demand::Constructor],
                                 values[Demand::Instance],
                                 inputs[model.state.size() + constructor]);
                        child(c, values, constructor, nextChild, record);
                      }
                      c.finish(values);
                    });
             });
  }
  void returned(func::FuncOp function) {
    body(function, allTypes(), model.state, false,
         [&](Cursor &c, ValueRange inputs) {
           auto zero = c.number(0, "root_continuation");
           auto root = c.compare("index.equal", inputs[Demand::Continuation],
                                 zero, "is_root");
           auto result = c.conditional(
               root, inputs, model.state, "return",
               [&](unsigned branch, func::FuncOp region) {
                 body(region, allTypes(), model.state, true,
                      [&](Cursor &body, ValueRange captured) {
                        auto values = state(captured);
                        if (branch == 0) {
                          body.equalTo(values[Demand::Kind], rootKind,
                                       "root_kind");
                          values[Demand::Phase] = body.number(4, "completed");
                          body.finish(values, true);
                          return;
                        }
                        auto one = body.number(1, "continuation_offset");
                        auto offset =
                            body.apply("index.sub", index,
                                       {values[Demand::Continuation], one},
                                       "frame_index")
                                .front();
                        auto packed = body.at(model.sequence, model.frame,
                                              values[Demand::Frames], offset,
                                              "load_frame");
                        auto saved = body.unpack(
                            packed, Types(Demand::FrameSize, index), "frame");
                        values[Demand::Constructor] = saved[0];
                        values[Demand::Instance] = saved[1];
                        values[Demand::Position] = saved[2];
                        values[Demand::Continuation] = saved[4];
                        append_range(values, stores(captured));
                        values.push_back(saved[3]);
                        func::FuncOp select;
                        auto result = body.local(values, model.state,
                                                 "restore_parent", select);
                        SmallVector<unsigned> cases;
                        for (auto [ordinal, item] :
                             enumerate(controller.constructors))
                          if (!recipes[ordinal].queries.empty())
                            cases.push_back(item.source);
                        dispatch(select, Demand::Constructor, cases,
                                 returnTypes(), model.state,
                                 [&](unsigned source, func::FuncOp leaf) {
                                   auto item =
                                       find_if(controller.constructors,
                                               [&](const auto &item) {
                                                 return item.source == source;
                                               });
                                   parent(leaf,
                                          item -
                                              controller.constructors.begin());
                                 });
                        body.finish(result, true);
                      });
               });
           c.finish(result);
         });
  }
  enum class DispatchCheck { Explicit, Anchor };
  void dispatch(func::FuncOp function, unsigned selector,
                ArrayRef<unsigned> cases, TypeRange formals, TypeRange outputs,
                llvm::function_ref<void(unsigned, func::FuncOp)> leaf,
                DispatchCheck check = DispatchCheck::Explicit,
                bool region = false, StringRef prefix = {}) {
    body(function, formals, outputs, region, [&](Cursor &c, ValueRange inputs) {
      if (cases.empty()) {
        c.reject("refused", prefix.str() + "no_constructor");
        return;
      }
      if (cases.size() == 1) {
        // The Anchor policy is chosen below only for independently checked
        // leaves whose actual lookup checks this exact constructor selector.
        if (check == DispatchCheck::Explicit)
          c.equalTo(inputs[selector], cases.front(), prefix.str() + "selected");
        func::FuncOp selected;
        auto values = c.local(inputs, outputs, prefix.str() + "case", selected);
        if (valid)
          leaf(cases.front(), selected);
        c.finish(values, region);
        return;
      }
      auto middle = cases.size() / 2;
      auto pivot = c.number(cases[middle], prefix.str() + "pivot");
      auto left = c.compare("index.less", inputs[selector], pivot,
                            prefix.str() + "partition");
      auto values = c.conditional(
          left, inputs, outputs, prefix.str() + "dispatch",
          [&](unsigned branch, func::FuncOp selected) {
            auto subset = branch == 0 ? cases.take_front(middle)
                                      : cases.drop_front(middle);
            dispatch(selected, selector, subset, formals, outputs, leaf, check,
                     true, prefix.str() + (branch == 0 ? "left_" : "right_"));
          });
      c.finish(values, region);
    });
  }
  void dispatch(func::FuncOp function, unsigned selector,
                ArrayRef<unsigned> cases,
                llvm::function_ref<void(unsigned, func::FuncOp)> leaf,
                DispatchCheck check = DispatchCheck::Explicit) {
    dispatch(function, selector, cases, allTypes(), model.state, leaf, check);
  }
  void initialize(pir::OracleKindAttr root) {
    auto reference = cantFail(oracleReferenceType(root));
    body(model.initialize, TypeRange{reference, index}, model.state, false,
         [&](Cursor &c, ValueRange inputs) {
           auto coordinates =
               c.unpack(inputs[0], TypeRange{index, index}, "root");
           auto zero = c.number(0, "initial");
           auto kind = c.number(rootKind, "root_kind");
           Values expected{coordinates[0], coordinates[1], inputs[1],
                           kind,           zero,           zero};
           expected.push_back(c.empty(model.sequence, "empty_frames"));
           c.finish(expected);
         });
    body(model.consume, model.state, model.state, false,
         [&](Cursor &c, ValueRange inputs) {
           c.equalTo(inputs[Demand::Phase], 2, "suspended");
           auto expected = state(inputs);
           expected[Demand::Phase] = c.number(1, "consumed");
           c.finish(expected);
         });
  }
  Values step(Cursor &c, ValueRange inputs) {
    auto zero = c.number(0, "enter_phase");
    auto entering =
        c.compare("index.equal", inputs[Demand::Phase], zero, "phase");
    auto result = c.conditional(
        entering, inputs, model.state, "step",
        [&](unsigned branch, func::FuncOp region) {
          body(region, allTypes(), model.state, true,
               [&](Cursor &body, ValueRange captured) {
                 func::FuncOp transition;
                 auto result = body.local(captured, model.state,
                                          branch == 0 ? "enter_transition"
                                                      : "return_transition",
                                          transition);
                 if (branch == 0) {
                   SmallVector<unsigned> cases;
                   for (const auto &item : controller.constructors)
                     cases.push_back(item.source);
                   dispatch(
                       transition, Demand::Constructor, cases,
                       [&](unsigned source, func::FuncOp leaf) {
                         auto item = find_if(controller.constructors,
                                             [&](const auto &item) {
                                               return item.source == source;
                                             });
                         enter(leaf, item - controller.constructors.begin());
                       },
                       DispatchCheck::Anchor);
                 } else
                   returned(transition);
                 body.finish(result, true);
               });
        });
    return result;
  }

  void advance() {
    body(model.advance, allTypes(), model.state, false,
         [&](Cursor &c, ValueRange inputs) {
           auto zero = c.number(0, "lower");
           auto two = c.number(2, "suspension_phase");
           auto allowed = c.compare("index.less", inputs[Demand::Phase], two,
                                    "can_advance");
           c.require(allowed, "admit_advance");
           auto upper =
               c.number(controller.capacity.nodes * 2 + 1, "transition_bound");
           auto values =
               c.loop(zero, upper, state(inputs), stores(inputs), "advance",
                      [&](func::FuncOp region) {
                        Types inputs{index};
                        append_range(inputs, allTypes());
                        Types outputs{boolean};
                        append_range(outputs, model.state);
                        body(region, inputs, outputs, true,
                             [&](Cursor &body, ValueRange captures) {
                               auto values = step(body, captures.drop_front());
                               auto threshold =
                                   body.number(2, "iteration_suspension_phase");
                               auto proceed = body.compare(
                                   "index.less", values[Demand::Phase],
                                   threshold, "continuing");
                               Values yielded{proceed};
                               append_range(yielded, values);
                               body.finish(yielded, true);
                             });
                      });
           auto one = c.number(1, "return_phase");
           auto stopped = c.compare("index.less", one, values[Demand::Phase],
                                    "stopped_advancing");
           c.require(stopped, "complete_advance");
           c.finish(values);
         });
  }
};
} // namespace
Error checkOracleQueryDemand(ModuleOp candidate, ModuleOp prepared,
                             const OracleAnchorStorage &storage,
                             const OracleQueryController &controller,
                             pir::OracleKindAttr root, const Demand &actual) {
  auto refuse = [] { return error("oracle-demand-body"); };
  auto target = OracleVerificationContext::read(candidate);
  if (!target) {
    consumeError(target.takeError());
    return refuse();
  }
  auto source = OracleVerificationContext::read(prepared);
  if (!source) {
    consumeError(source.takeError());
    return refuse();
  }
  return checkOracleQueryDemand(*target, *source, storage, controller, root,
                                actual);
}
Error checkOracleQueryDemand(const OracleVerificationContext &target,
                             const OracleVerificationContext &source,
                             const OracleAnchorStorage &storage,
                             const OracleQueryController &controller,
                             pir::OracleKindAttr root, const Demand &actual) {
  auto refuse = [] { return error("oracle-demand-body"); };
  if (target.getUnit() == source.getUnit() ||
      target.getModule().getContext() != source.getModule().getContext() ||
      controller.kinds.empty())
    return refuse();
  // A demand root may have any checked kind number. Revalidate the evaluator
  // with its own original root, rather than changing its kind enumeration.
  if (auto e = checkOracleQueryController(
          target, source, storage, controller.role, controller.kinds.front(),
          controller.capacity, controller, controller.access)) {
    consumeError(std::move(e));
    return refuse();
  }
  unsigned rootKind = 0;
  std::vector<OracleVirtualRecipe> recipes;
  if (auto e = layout(target, source, storage, controller, root, actual,
                      rootKind, recipes)) {
    consumeError(std::move(e));
    return refuse();
  }
  Reader reader(target, storage, controller, actual, recipes, rootKind);
  reader.initialize(root);
  reader.advance();
  return reader.valid ? Error::success() : refuse();
}
} // namespace zkc::protocol
