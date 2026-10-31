#include "NativeBindingApplication.h"
#include "OracleQueryWindow.h"
#include "OracleVerificationContext.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Refusal.h"
#include <set>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using Demand = OracleQueryDemand;
using Controller = OracleQueryController;
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
// This reader consumes actual SSA/control associations, not an emitted expected
// module or a producer recipe. Source correspondence of demand/controller is
// a separate caller obligation; exact response semantics are checked below.
bool layout(const OracleVerificationContext &context,
            const Controller &controller, const Demand &demand,
            const OracleQueryExchange &exchange,
            const OracleQueryResponse &response,
            const OracleQueryWindow &actual) {
  auto unit = context.getUnit();
  auto *ctx = unit.getContext();
  Type index = IntegerType::get(ctx, 64, IntegerType::Unsigned);
  if (!actual.capacity || actual.capacity >= 1048576 ||
      controller.state.size() < Controller::HeaderSize ||
      controller.state.size() > 504 || controller.stores.size() > 504 ||
      demand.state.size() != Demand::HeaderSize + 1 ||
      std::max(controller.state.size() + 4, demand.state.size() + 2) +
              controller.stores.size() + 8 >
          512 ||
      controller.kinds.empty() || controller.kinds.size() > 504 ||
      controller.continuations.size() > 504 || !controller.capacity.nodes ||
      controller.capacity.leaves > controller.capacity.nodes ||
      controller.capacity.nodes > (1048576 - 1) / 2 ||
      controller.capacity.leaves >= 1048576 ||
      controller.answers.size() != controller.kinds.size() ||
      controller.resume.size() != controller.kinds.size() ||
      controller.constructors.size() != controller.stores.size() ||
      exchange.state != controller.state ||
      exchange.receiverStores != controller.stores ||
      controller.state.size() != Controller::HeaderSize +
                                     controller.kinds.size() +
                                     controller.continuations.size())
    return false;
  for (auto types :
       {ArrayRef<Type>(controller.state), ArrayRef<Type>(controller.stores),
        ArrayRef<Type>(demand.state)})
    if (!all_of(types,
                [&](Type type) { return type && type.getContext() == ctx; }))
      return false;
  if (!all_of(
          ArrayRef<Type>(controller.state).take_front(Controller::HeaderSize),
          [&](Type type) { return type == index; }) ||
      !all_of(ArrayRef<Type>(demand.state).take_front(Demand::HeaderSize),
              [&](Type type) { return type == index; }))
    return false;
  auto frames = dyn_cast_or_null<data::SequenceType>(demand.sequence);
  auto frame = dyn_cast_or_null<data::VariantType>(demand.frame);
  auto requests = dyn_cast_or_null<data::SequenceType>(actual.requestSequence);
  auto answers = dyn_cast_or_null<data::SequenceType>(actual.answerSequence);
  if (!frame || !frames || demand.state.back() != frames ||
      frames.getElementType() != frame || frame.getAlternatives().size() != 1 ||
      frame.getAlternatives()[0].getLabel().getValue() != "Record" ||
      !equal(frame.getAlternatives()[0].getPayload(),
             Types(Demand::FrameSize, index)) ||
      !requests || !answers || requests.getContext() != ctx ||
      answers.getContext() != ctx ||
      requests.getElementType() != exchange.request ||
      answers.getElementType() != response.answer)
    return false;
  auto signature = [&](func::FuncOp helper) -> FunctionType {
    if (!helper || helper->getParentOp() != unit || !helper.isPrivate() ||
        helper->hasAttr("runtime.region") ||
        !context.getClosure().bodies.count(helper.getSymName().str()))
      return {};
    return scopedDataSignature(helper);
  };
  auto has = [&](func::FuncOp helper, TypeRange inputs, TypeRange outputs) {
    auto type = signature(helper);
    return type && equal(type.getInputs(), inputs) &&
           equal(type.getResults(), outputs);
  };
  Types discovery(demand.state.begin(), demand.state.end()),
      evaluation(controller.state.begin(), controller.state.end());
  append_range(discovery, controller.stores);
  append_range(evaluation, controller.stores);
  auto initialized = signature(controller.initialize);
  auto discoveryInitial = signature(demand.initialize);
  auto finished = signature(controller.finish);
  if (!has(demand.advance, discovery, demand.state) ||
      !has(demand.consume, demand.state, demand.state) ||
      !has(controller.advance, evaluation, controller.state) || !initialized ||
      !discoveryInitial || !finished || initialized.getNumInputs() != 2 ||
      discoveryInitial.getNumInputs() != 2 ||
      initialized.getInput(1) != index ||
      discoveryInitial.getInput(1) != index ||
      !equal(initialized.getResults(), controller.state) ||
      !equal(discoveryInitial.getResults(), demand.state) ||
      !equal(finished.getInputs(), controller.state) ||
      finished.getNumResults() != 1)
    return false;
  SmallVector<Type> references;
  for (auto [i, kind] : enumerate(controller.kinds)) {
    auto arena = dyn_cast_or_null<data::SequenceType>(controller.answers[i]);
    if (!kind || kind.getContext() != ctx || kind.getIdentity() != "table" ||
        !arena || arena.getElementType() != kind.getAnswerType() ||
        controller.state[Controller::HeaderSize + i] != arena)
      return false;
    auto reference = oracleReferenceType(kind);
    if (!reference) {
      consumeError(reference.takeError());
      return false;
    }
    references.push_back(*reference);
  }
  if (!is_contained(references, initialized.getInput(0)) ||
      !is_contained(references, discoveryInitial.getInput(0)))
    return false;
  for (auto [i, continuation] : enumerate(controller.continuations))
    if (controller.state[Controller::HeaderSize + controller.kinds.size() +
                         i] != continuation.sequence)
      return false;
  for (const auto &arm : exchange.arms) {
    if (arm.receiverSlot >= controller.constructors.size() ||
        arm.kind >= controller.kinds.size())
      return false;
    const auto &item = controller.constructors[arm.receiverSlot];
    auto reference = oracleReferenceType(controller.kinds[arm.kind]);
    if (!reference) {
      consumeError(reference.takeError());
      return false;
    }
    if (item.source != arm.constructor || item.kind != arm.kind ||
        item.lookup != arm.receiverLookup ||
        controller.resume[arm.kind] != arm.resume ||
        *reference != arm.reference)
      return false;
  }
  if (!actual.collect || !actual.replay || !actual.finish ||
      actual.collect == actual.replay || actual.collect == actual.finish ||
      actual.replay == actual.finish)
    return false;
  // This establishes the request/answer/state checks and use of the actual
  // continuation coordinates, without granting authentication to replay.
  if (auto e = checkOracleQueryResponse(context, exchange, response)) {
    consumeError(std::move(e));
    return false;
  }
  return true;
}
struct Reader {
  const OracleVerificationContext &context;
  const Controller &controller;
  const Demand &demand;
  const OracleQueryExchange &exchange;
  const OracleQueryResponse &response;
  const OracleQueryWindow &model;
  protocol_ir::ProtocolModuleOp unit;
  Type index, boolean, scope;
  bool valid = true;
  std::set<Operation *> visited;
  Reader(const OracleVerificationContext &context, const Controller &controller,
         const Demand &demand, const OracleQueryExchange &exchange,
         const OracleQueryResponse &response, const OracleQueryWindow &model)
      : context(context), controller(controller), demand(demand),
        exchange(exchange), response(response), model(model),
        unit(context.getUnit()),
        index(IntegerType::get(unit.getContext(), 64, IntegerType::Unsigned)),
        boolean(IntegerType::get(unit.getContext(), 1)),
        scope(runtime::ScopeType::get(unit.getContext())) {}
  bool expect(bool value) {
    valid &= value;
    return valid;
  }
  struct Cursor {
    Reader &reader;
    ArrayRef<SourceExecutionStep> steps;
    unsigned offset = 0;
    const SourceExecutionStep *take(StringRef operation, StringRef site) {
      if (!reader.valid || !reader.expect(offset < steps.size()))
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
      if (!reader.expect(matchesNativeBinding(
              binding, {contract.str(), SmallVector<Attribute>(statics), {}})))
        return values;
      reader.expect(
          invocationParametersMatch(contract, binding.getArgumentsAttr(),
                                    op.getParametersAttr(), parameters));
      return values;
    }
    Value number(uint64_t value, StringRef site) {
      return apply("index.constant", reader.index, {}, site, {},
                   {std::to_string(value)})[0];
    }
    Value predicate(StringRef contract, ValueRange inputs, StringRef site) {
      return apply(contract, reader.boolean, inputs, site)[0];
    }
    void require(Value predicate, StringRef site) {
      apply("control.require", {}, predicate, site);
    }
    Attribute element(Type sequence) {
      return TypeAttr::get(cast<data::SequenceType>(sequence).getElementType());
    }
    Value length(Type sequence, Value value, StringRef site) {
      return apply("sequence.length", reader.index, value, site,
                   {element(sequence)})[0];
    }
    Values call(func::FuncOp expected, ValueRange inputs, StringRef site) {
      auto types = scopedDataSignature(expected).getResults();
      auto *step = take("func.call", site);
      auto values = result(step, types, inputs);
      if (reader.valid) {
        auto call = cast<func::CallOp>(step->operation);
        reader.expect(
            SymbolTable::lookupSymbolIn(reader.unit, call.getCallee()) ==
            expected.getOperation());
      }
      return values;
    }
    Values conditional(Value predicate, ValueRange captures, TypeRange outputs,
                       StringRef site,
                       llvm::function_ref<void(unsigned, func::FuncOp)> check) {
      auto *step = take("exec.test", site);
      Values inputs{predicate};
      append_range(inputs, captures);
      auto values = result(step, outputs, inputs, 2);
      if (reader.valid)
        for (unsigned branch = 0; branch < 2; ++branch)
          check(branch, step->regions[branch]);
      return values;
    }
    Values loop(Value lower, Value upper, ValueRange seeds, ValueRange captures,
                TypeRange outputs, bool conditional, StringRef site,
                llvm::function_ref<void(func::FuncOp)> check) {
      auto *step = take("exec.range", site);
      Values inputs{lower, upper};
      append_range(inputs, seeds);
      append_range(inputs, captures);
      auto values = result(step, outputs, inputs, 1);
      if (reader.valid && reader.expect(step->conditional == conditional))
        check(step->regions[0]);
      return values;
    }
    Value pack(Type type, ValueRange fields, StringRef site) {
      auto *step = take("exec.variant", site);
      auto values = result(step, type, fields);
      if (reader.valid)
        reader.expect(cast<exec::VariantOp>(step->operation).getAlternative() ==
                      "Record");
      return values[0];
    }
    void finish(ValueRange values, bool region = false) {
      if (!reader.valid || !reader.expect(offset + 1 == steps.size()))
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
    Types formals{scope};
    append_range(formals, inputs);
    if (!expect(function && function->getParentOp() == unit &&
                function.isPrivate() &&
                visited.insert(function.getOperation()).second &&
                !function->hasAttr("data.preconditions") &&
                function->getAttrOfType<UnitAttr>("no_inline") &&
                function->hasAttr("runtime.region") == region &&
                equal(function.getArgumentTypes(), formals) &&
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
      auto origin = ArrayAttr::get(
          unit.getContext(),
          {StringAttr::get(unit.getContext(), function.getSymName()),
           ArrayAttr::get(unit.getContext(), {})});
      if (!expect(function->getAttr("runtime.origin") == origin))
        return;
    }
    auto found = context.getClosure().bodies.find(function.getSymName().str());
    if (!expect(found != context.getClosure().bodies.end()))
      return;
    Cursor cursor{*this, found->second};
    check(cursor, function.getArguments().drop_front());
    expect(cursor.offset == cursor.steps.size());
  }
  Types collectedTypes() {
    Types types(demand.state.begin(), demand.state.end());
    append_range(types, Types{model.requestSequence, boolean});
    return types;
  }
  Types collectInputs() {
    auto types = collectedTypes();
    append_range(types, controller.stores);
    return types;
  }
  Values branch(Cursor &c, Value predicate, ValueRange inputs, StringRef site,
                llvm::function_ref<void(Cursor &, ValueRange)> yes,
                llvm::function_ref<void(Cursor &, ValueRange)> no) {
    return c.conditional(predicate, inputs, collectedTypes(), site,
                         [&](unsigned branch, func::FuncOp region) {
                           body(region, collectInputs(), collectedTypes(), true,
                                [&](Cursor &body, ValueRange a) {
                                  (branch == 0 ? yes : no)(body, a);
                                });
                         });
  }
  void identity(Cursor &c, ValueRange a) {
    c.finish(a.take_front(collectedTypes().size()), true);
  }
  void iteration(func::FuncOp function) {
    Types inputs{index};
    append_range(inputs, collectInputs());
    Types outputs{boolean};
    append_range(outputs, collectedTypes());
    body(function, inputs, outputs, true, [&](Cursor &c, ValueRange args) {
      auto a = args.drop_front();
      unsigned n = demand.state.size();
      Values inputs(a.take_front(n));
      append_range(inputs, a.drop_front(n + 2));
      auto advanced = c.call(demand.advance, inputs, "window_discover");
      auto requestPhase = c.number(Demand::Request, "window_request_phase");
      auto reached =
          c.predicate("index.equal", {advanced[Demand::Phase], requestPhase},
                      "window_is_request");
      Values captures(advanced);
      append_range(captures, a.drop_front(n));
      auto collected = branch(
          c, reached, captures, "window_leaf",
          [&](Cursor &leaf, ValueRange state) {
            auto request = leaf.pack(exchange.request, state.take_front(3),
                                     "window_request");
            auto appended = leaf.apply(
                "sequence.append", model.requestSequence, {state[n], request},
                "window_append", {leaf.element(model.requestSequence)})[0];
            auto consumed = leaf.call(demand.consume, state.take_front(n),
                                      "window_consume");
            consumed.push_back(appended);
            consumed.push_back(state[n + 1]);
            leaf.finish(consumed, true);
          },
          [&](Cursor &terminal, ValueRange state) {
            auto cut = terminal.number(Demand::DomainCut, "window_cut_phase");
            auto blocked =
                terminal.predicate("index.equal", {state[Demand::Phase], cut},
                                   "window_reached_cut");
            Values values(state.take_front(n + 1));
            values.push_back(blocked);
            terminal.finish(values, true);
          });
      auto threshold = c.number(Demand::Request, "window_active_phase");
      auto active = c.predicate(
          "index.less", {collected[Demand::Phase], threshold}, "window_active");
      auto size = c.length(model.requestSequence, collected[n],
                           "window_collected_length");
      auto maximum = c.number(model.capacity, "window_packet_capacity");
      auto room = c.predicate("index.less", {size, maximum}, "window_has_room");
      auto proceed = c.predicate("bool.and", {active, room}, "window_continue");
      Values yielded{proceed};
      append_range(yielded, collected);
      c.finish(yielded, true);
    });
  }
  void collect() {
    body(
        model.collect, collectInputs(), collectedTypes(), false,
        [&](Cursor &c, ValueRange a) {
          unsigned n = demand.state.size();
          auto size =
              c.length(model.requestSequence, a[n], "window_prefix_length");
          auto bound = c.number(model.capacity + 1, "window_prefix_bound");
          c.require(
              c.predicate("index.less", {size, bound}, "window_prefix_fits"),
              "window_admit_prefix");
          auto phaseBound =
              c.number(Demand::Completed + 1, "window_phase_bound");
          c.require(c.predicate("index.less", {a[Demand::Phase], phaseBound},
                                "window_phase_valid"),
                    "window_admit_phase");
          auto request = c.number(Demand::Request, "window_entry_request");
          auto suspended =
              c.predicate("index.equal", {a[Demand::Phase], request},
                          "window_entry_suspended");
          c.require(c.predicate("bool.not", suspended, "window_entry_consumed"),
                    "window_admit_consumed");
          c.finish(branch(
              c, a[n + 1], a, "window_blocked",
              [&](Cursor &blocked, ValueRange retained) {
                identity(blocked, retained);
              },
              [&](Cursor &unblocked, ValueRange current) {
                auto cut = unblocked.number(Demand::DomainCut,
                                            "window_pending_cut_phase");
                auto pending = unblocked.predicate(
                    "index.equal", {current[Demand::Phase], cut},
                    "window_pending_cut");
                unblocked.finish(
                    branch(
                        unblocked, pending, current, "window_cut",
                        [&](Cursor &cutBody, ValueRange state) {
                          auto phase = cutBody.number(Demand::DomainCut,
                                                      "window_blocked_phase");
                          auto yes = cutBody.predicate(
                              "index.equal", {state[Demand::Phase], phase},
                              "window_set_blocked");
                          Values values(state.take_front(n + 1));
                          values.push_back(yes);
                          cutBody.finish(values, true);
                        },
                        [&](Cursor &ready, ValueRange state) {
                          auto completed = ready.number(
                              Demand::Completed, "window_completed_phase");
                          auto done = ready.predicate(
                              "index.equal", {state[Demand::Phase], completed},
                              "window_completed");
                          ready.finish(
                              branch(
                                  ready, done, state, "window_terminal",
                                  [&](Cursor &terminal, ValueRange retained) {
                                    identity(terminal, retained);
                                  },
                                  [&](Cursor &active, ValueRange seed) {
                                    auto size = active.length(
                                        model.requestSequence, seed[n],
                                        "window_seed_length");
                                    auto maximum = active.number(
                                        model.capacity, "window_seed_capacity");
                                    auto room = active.predicate(
                                        "index.less", {size, maximum},
                                        "window_seed_room");
                                    active.finish(
                                        branch(
                                            active, room, seed, "window_room",
                                            [&](Cursor &loop, ValueRange args) {
                                              auto lower = loop.number(
                                                  0, "window_collect_lower");
                                              auto upper = loop.number(
                                                  model.capacity + 1,
                                                  "window_collect_upper");
                                              loop.finish(
                                                  loop.loop(
                                                      lower, upper,
                                                      args.take_front(n + 2),
                                                      args.drop_front(n + 2),
                                                      collectedTypes(), true,
                                                      "window_collect_loop",
                                                      [&](func::FuncOp region) {
                                                        iteration(region);
                                                      }),
                                                  true);
                                            },
                                            [&](Cursor &full,
                                                ValueRange retained) {
                                              identity(full, retained);
                                            }),
                                        true);
                                  }),
                              true);
                        }),
                    true);
              }));
        });
  }
  void replay() {
    Types inputs(controller.state.begin(), controller.state.end());
    append_range(inputs, Types{model.requestSequence, model.answerSequence,
                               index, index});
    append_range(inputs, controller.stores);
    body(
        model.replay, inputs, controller.state, false,
        [&](Cursor &c, ValueRange a) {
          unsigned n = controller.state.size();
          auto requests =
              c.length(model.requestSequence, a[n], "window_replay_requests");
          auto answers =
              c.length(model.answerSequence, a[n + 1], "window_replay_answers");
          c.require(c.predicate("index.equal", {requests, answers},
                                "window_equal_lengths"),
                    "window_admit_lengths");
          auto bound = c.number(model.capacity + 1, "window_replay_bound");
          c.require(c.predicate("index.less", {requests, bound},
                                "window_replay_fits"),
                    "window_admit_replay_capacity");
          auto reversed = c.predicate("index.less", {a[n + 3], a[n + 2]},
                                      "window_reversed_range");
          c.require(c.predicate("bool.not", reversed, "window_ordered_range"),
                    "window_admit_range_order");
          auto outside = c.predicate("index.less", {requests, a[n + 3]},
                                     "window_range_outside");
          c.require(c.predicate("bool.not", outside, "window_range_inside"),
                    "window_admit_range_end");
          Values captures{a[n], a[n + 1]};
          append_range(captures, a.drop_front(n + 4));
          c.finish(c.loop(
              a[n + 2], a[n + 3], a.take_front(n), captures, controller.state,
              false, "window_replay_loop", [&](func::FuncOp region) {
                Types types{index};
                append_range(types, controller.state);
                append_range(
                    types, Types{model.requestSequence, model.answerSequence});
                append_range(types, controller.stores);
                body(region, types, controller.state, true,
                     [&](Cursor &iteration, ValueRange args) {
                       Values advance(args.slice(1, n));
                       append_range(advance, args.drop_front(n + 3));
                       auto advanced =
                           iteration.call(controller.advance, advance,
                                          "window_replay_advance");
                       auto request = iteration.apply(
                           "sequence.at", exchange.request,
                           {args[n + 1], args[0]}, "window_replay_request",
                           {iteration.element(model.requestSequence)})[0];
                       auto answer = iteration.apply(
                           "sequence.at", response.answer,
                           {args[n + 2], args[0]}, "window_replay_answer",
                           {iteration.element(model.answerSequence)})[0];
                       Values resumed{request, answer};
                       append_range(resumed, advanced);
                       iteration.finish(iteration.call(response.resume, resumed,
                                                       "window_replay_resume"),
                                        true);
                     });
              }));
        });
  }
  void finish() {
    Types inputs(controller.state.begin(), controller.state.end());
    append_range(inputs, controller.stores);
    body(model.finish, inputs,
         scopedDataSignature(controller.finish).getResults(), false,
         [&](Cursor &c, ValueRange a) {
           auto advanced =
               c.call(controller.advance, a, "window_finish_advance");
           c.finish(
               c.call(controller.finish, advanced, "window_finish_payload"));
         });
  }
};
} // namespace
Error checkOracleQueryWindow(const OracleVerificationContext &context,
                             const Controller &controller, const Demand &demand,
                             const OracleQueryExchange &exchange,
                             const OracleQueryResponse &response,
                             const OracleQueryWindow &actual) {
  if (!layout(context, controller, demand, exchange, response, actual))
    return error("oracle-window-body");
  Reader reader(context, controller, demand, exchange, response, actual);
  reader.collect();
  reader.replay();
  reader.finish();
  return reader.valid ? Error::success() : error("oracle-window-body");
}
} // namespace zkc::protocol
