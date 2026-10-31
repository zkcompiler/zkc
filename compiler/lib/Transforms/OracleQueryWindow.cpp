#include "OracleQueryWindow.h"
#include "OracleVerificationContext.h"
#include "RealizationEmission.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SmallPtrSet.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using Demand = OracleQueryDemand;
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
using Control = exec::ScopedExecutionBuilder;
constexpr uint64_t operationAllowance = 4096;
struct Emitter {
  protocol_ir::ProtocolModuleOp unit;
  const OracleQueryController &controller;
  const Demand &demand;
  const OracleQueryExchange &exchange;
  const OracleQueryResponse &response;
  OracleQueryWindow result;
  OpBuilder builder;
  mathematical::RealizationEmitter bindings;
  Type index, boolean;
  unsigned next = 0;
  uint64_t generatedSlots = 0;
  Emitter(protocol_ir::ProtocolModuleOp unit,
          const OracleQueryController &controller, const Demand &demand,
          const OracleQueryExchange &exchange,
          const OracleQueryResponse &response, uint64_t capacity)
      : unit(unit), controller(controller), demand(demand), exchange(exchange),
        response(response), builder(unit.getContext()),
        bindings(unit, "_oracle_window_binding_"),
        index(IntegerType::get(unit.getContext(), 64, IntegerType::Unsigned)),
        boolean(builder.getI1Type()) {
    result.capacity = capacity;
  }
  Error plan(const OracleVerificationContext &context,
             OracleVirtualFunctionWork &work) {
    if (!result.capacity || result.capacity >= 1048576)
      return error("oracle-window-capacity");
    auto refuse = [] { return error("oracle-window-layout"); };
    if (controller.state.size() < OracleQueryController::HeaderSize ||
        demand.state.size() != Demand::HeaderSize + 1 ||
        controller.state.size() > 504 || controller.stores.size() > 504 ||
        controller.kinds.empty() || controller.kinds.size() > 504 ||
        controller.continuations.size() > 504 || !controller.capacity.nodes ||
        controller.capacity.leaves > controller.capacity.nodes ||
        controller.capacity.nodes > (1048576 - 1) / 2 ||
        controller.capacity.leaves >= 1048576 ||
        controller.answers.size() != controller.kinds.size() ||
        controller.resume.size() != controller.kinds.size() ||
        exchange.state != controller.state ||
        exchange.receiverStores != controller.stores ||
        controller.constructors.size() != controller.stores.size())
      return refuse();
    uint64_t width =
        std::max(controller.state.size() + 4, demand.state.size() + 2) +
        controller.stores.size();
    // Include scope, loop coordinates, conditional result and temporary guards.
    if (width + 8 > 512)
      return error("oracle-window-capacity");
    for (auto types :
         {ArrayRef<Type>(controller.state), ArrayRef<Type>(controller.stores),
          ArrayRef<Type>(demand.state)})
      if (!all_of(types, [&](Type type) {
            return type && type.getContext() == unit.getContext();
          }))
        return refuse();
    if (!all_of(ArrayRef<Type>(controller.state)
                    .take_front(OracleQueryController::HeaderSize),
                [&](Type type) { return type == index; }) ||
        !all_of(ArrayRef<Type>(demand.state).take_front(Demand::HeaderSize),
                [&](Type type) { return type == index; }) ||
        demand.state.back() != demand.sequence)
      return refuse();
    auto frame = dyn_cast_or_null<data::VariantType>(demand.frame);
    auto frames = dyn_cast_or_null<data::SequenceType>(demand.sequence);
    if (!frame || !frames || frames.getElementType() != frame ||
        frame.getAlternatives().size() != 1 ||
        frame.getAlternatives()[0].getLabel().getValue() != "Record" ||
        !equal(frame.getAlternatives()[0].getPayload(),
               Types(Demand::FrameSize, index)))
      return refuse();
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
    Types demandInputs(demand.state.begin(), demand.state.end()),
        controllerInputs(controller.state.begin(), controller.state.end());
    append_range(demandInputs, controller.stores);
    append_range(controllerInputs, controller.stores);
    auto initial = signature(controller.initialize);
    auto discoveryInitial = signature(demand.initialize);
    auto finished = signature(controller.finish);
    if (!has(demand.advance, demandInputs, demand.state) ||
        !has(demand.consume, demand.state, demand.state) ||
        !has(controller.advance, controllerInputs, controller.state) ||
        !initial || !discoveryInitial || !finished ||
        initial.getNumInputs() != 2 || discoveryInitial.getNumInputs() != 2 ||
        initial.getInput(1) != index || discoveryInitial.getInput(1) != index ||
        !equal(initial.getResults(), controller.state) ||
        !equal(discoveryInitial.getResults(), demand.state) ||
        !equal(finished.getInputs(), controller.state) ||
        finished.getNumResults() != 1)
      return refuse();
    if (controller.state.size() != OracleQueryController::HeaderSize +
                                       controller.kinds.size() +
                                       controller.continuations.size())
      return refuse();
    for (auto [i, kind] : enumerate(controller.kinds)) {
      auto arena = dyn_cast_or_null<data::SequenceType>(controller.answers[i]);
      if (!kind || kind.getContext() != unit.getContext() ||
          kind.getIdentity() != "table" || !arena ||
          arena.getElementType() != kind.getAnswerType() ||
          controller.state[OracleQueryController::HeaderSize + i] != arena)
        return refuse();
    }
    for (auto [i, continuation] : enumerate(controller.continuations))
      if (controller.state[OracleQueryController::HeaderSize +
                           controller.kinds.size() + i] !=
          continuation.sequence)
        return refuse();
    // Initialization may select any kind already checked in this controller.
    // The caller binds the actual common root occurrence; no kind is coerced.
    for (Type reference : {initial.getInput(0), discoveryInitial.getInput(0)}) {
      bool found = false;
      for (auto kind : controller.kinds) {
        auto expected = oracleReferenceType(kind);
        if (!expected) {
          consumeError(expected.takeError());
          return refuse();
        }
        found |= *expected == reference;
      }
      if (!found)
        return refuse();
    }
    for (const auto &arm : exchange.arms) {
      if (arm.receiverSlot >= controller.constructors.size() ||
          arm.kind >= controller.kinds.size())
        return refuse();
      const auto &item = controller.constructors[arm.receiverSlot];
      auto reference = oracleReferenceType(controller.kinds[arm.kind]);
      if (!reference) {
        consumeError(reference.takeError());
        return refuse();
      }
      if (item.source != arm.constructor || item.kind != arm.kind ||
          item.lookup != arm.receiverLookup ||
          controller.resume[arm.kind] != arm.resume ||
          *reference != arm.reference)
        return refuse();
    }
    if (auto e = checkOracleQueryResponse(context, exchange, response)) {
      consumeError(std::move(e));
      return refuse();
    }
    result.requestSequence =
        data::SequenceType::get(unit.getContext(), exchange.request);
    result.answerSequence =
        data::SequenceType::get(unit.getContext(), response.answer);
    // All factors are bounded above (capacity <2^20, width <=504), so these
    // uint64 calculations cannot overflow. Reserve CFG/outcome plumbing and
    // maximum retained request/answer payload slots before adding any IR.
    generatedSlots = operationAllowance * (width + 32);
    uint64_t slots = generatedSlots + result.capacity * 8;
    if (operationAllowance > work.operations || slots > work.slots)
      return error("oracle-window-limit");
    work.operations -= operationAllowance;
    work.slots -= slots;
    return Error::success();
  }
  Types collectedTypes() {
    Types types(demand.state.begin(), demand.state.end());
    append_range(types, Types{result.requestSequence, boolean});
    return types;
  }
  Types collectInputs() {
    auto types = collectedTypes();
    append_range(types, controller.stores);
    return types;
  }
  func::FuncOp function(StringRef label, TypeRange inputs, TypeRange outputs,
                        bool region,
                        llvm::function_ref<void(Control &, ValueRange)> emit) {
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToEnd(&unit.getBody().front());
    std::string name;
    do {
      name = "_oracle_window_" + label.str() + "_" + std::to_string(next++);
    } while (SymbolTable::lookupSymbolIn(unit, name));
    Types formals{runtime::ScopeType::get(unit.getContext())};
    append_range(formals, inputs);
    auto helper = func::FuncOp::create(
        builder, unit.getLoc(), name,
        builder.getFunctionType(
            formals,
            exec::OutcomeType::get(unit.getContext(), Types(outputs))));
    helper.setPrivate();
    helper.setNoInline(true);
    if (region)
      helper->setAttr("runtime.region", builder.getUnitAttr());
    else
      helper->setAttr("runtime.origin",
                      builder.getArrayAttr({builder.getStringAttr(name),
                                            builder.getArrayAttr({})}));
    builder.setInsertionPointToEnd(helper.addEntryBlock());
    Control control(builder, helper);
    emit(control, helper.getArguments().drop_front());
    return helper;
  }
  Values apply(Control &c, StringRef contract, TypeRange outputs,
               ValueRange inputs, StringRef site,
               ArrayRef<Attribute> statics = {},
               ArrayRef<Attribute> parameters = {}) {
    auto binding =
        bindings.binding(builder, unit.getLoc(),
                         {contract.str(), SmallVector<Attribute>(statics), ""});
    return c.invoke(
        "exec.apply", outputs, c.scoped(inputs),
        {builder.getNamedAttr("binding", binding),
         builder.getNamedAttr("parameters", builder.getArrayAttr(parameters)),
         builder.getNamedAttr("site", builder.getStringAttr(site))});
  }
  Value number(Control &c, uint64_t value, StringRef site) {
    return apply(c, "index.constant", index, {}, site, {},
                 {builder.getIntegerAttr(index, value)})[0];
  }
  Value predicate(Control &c, StringRef contract, ValueRange inputs,
                  StringRef site) {
    return apply(c, contract, boolean, inputs, site)[0];
  }
  void require(Control &c, Value predicate, StringRef site) {
    apply(c, "control.require", {}, predicate, site);
  }
  Attribute element(Type sequence) {
    return TypeAttr::get(cast<data::SequenceType>(sequence).getElementType());
  }
  Value length(Control &c, Value sequence, StringRef site) {
    return apply(c, "sequence.length", index, sequence, site,
                 {element(sequence.getType())})[0];
  }
  Values call(Control &c, func::FuncOp helper, ValueRange inputs,
              StringRef site) {
    return c.invoke(
        "func.call", scopedDataSignature(helper).getResults(), c.scoped(inputs),
        {builder.getNamedAttr("callee", FlatSymbolRefAttr::get(helper)),
         builder.getNamedAttr("runtime.site", builder.getStringAttr(site))});
  }
  // Conditional branches capture every store explicitly, even on identity
  // paths.
  Values collectBranch(Control &c, Value predicate, ValueRange inputs,
                       StringRef site,
                       llvm::function_ref<void(Control &, ValueRange)> yes,
                       llvm::function_ref<void(Control &, ValueRange)> no) {
    return c.conditional(
        predicate, inputs, collectedTypes(), site, [&](unsigned branch) {
          return function("collect_region", collectInputs(), collectedTypes(),
                          true, [&](Control &body, ValueRange a) {
                            (branch == 0 ? yes : no)(body, a);
                          });
        });
  }
  void identity(Control &c, ValueRange a) {
    c.complete(a.take_front(collectedTypes().size()));
  }
  void iteration(Control &c, ValueRange a) {
    unsigned n = demand.state.size();
    Values inputs(a.take_front(n));
    append_range(inputs, a.drop_front(n + 2));
    auto advanced = call(c, demand.advance, inputs, "window_discover");
    auto requestPhase = number(c, Demand::Request, "window_request_phase");
    auto reached =
        predicate(c, "index.equal", {advanced[Demand::Phase], requestPhase},
                  "window_is_request");
    Values captures(advanced);
    append_range(captures, a.drop_front(n));
    auto collected = collectBranch(
        c, reached, captures, "window_leaf",
        [&](Control &body, ValueRange leaf) {
          auto request = body.invoke(
              "exec.variant", exchange.request, body.scoped(leaf.take_front(3)),
              {builder.getNamedAttr("alternative",
                                    builder.getStringAttr("Record")),
               builder.getNamedAttr(
                   "site", builder.getStringAttr("window_request"))})[0];
          auto appended = apply(body, "sequence.append", result.requestSequence,
                                {leaf[n], request}, "window_append",
                                {element(result.requestSequence)})[0];
          auto consumed =
              call(body, demand.consume, leaf.take_front(n), "window_consume");
          consumed.push_back(appended);
          consumed.push_back(leaf[n + 1]);
          body.complete(consumed);
        },
        [&](Control &body, ValueRange terminal) {
          auto cut = number(body, Demand::DomainCut, "window_cut_phase");
          auto blocked =
              predicate(body, "index.equal", {terminal[Demand::Phase], cut},
                        "window_reached_cut");
          Values values(terminal.take_front(n + 1));
          values.push_back(blocked);
          body.complete(values);
        });
    auto threshold = number(c, Demand::Request, "window_active_phase");
    auto active =
        predicate(c, "index.less", {collected[Demand::Phase], threshold},
                  "window_active");
    auto size = length(c, collected[n], "window_collected_length");
    auto maximum = number(c, result.capacity, "window_packet_capacity");
    auto room = predicate(c, "index.less", {size, maximum}, "window_has_room");
    auto proceed = predicate(c, "bool.and", {active, room}, "window_continue");
    Values yielded{proceed};
    append_range(yielded, collected);
    c.complete(yielded);
  }
  void collect() {
    result.collect = function(
        "collect", collectInputs(), collectedTypes(), false,
        [&](Control &c, ValueRange a) {
          unsigned n = demand.state.size();
          auto size = length(c, a[n], "window_prefix_length");
          auto bound = number(c, result.capacity + 1, "window_prefix_bound");
          require(
              c,
              predicate(c, "index.less", {size, bound}, "window_prefix_fits"),
              "window_admit_prefix");
          auto phaseBound =
              number(c, Demand::Completed + 1, "window_phase_bound");
          require(c,
                  predicate(c, "index.less", {a[Demand::Phase], phaseBound},
                            "window_phase_valid"),
                  "window_admit_phase");
          auto request = number(c, Demand::Request, "window_entry_request");
          auto suspended =
              predicate(c, "index.equal", {a[Demand::Phase], request},
                        "window_entry_suspended");
          require(c,
                  predicate(c, "bool.not", suspended, "window_entry_consumed"),
                  "window_admit_consumed");
          auto values = collectBranch(
              c, a[n + 1], a, "window_blocked",
              [&](Control &body, ValueRange blocked) {
                identity(body, blocked);
              },
              [&](Control &body, ValueRange unblocked) {
                auto cut =
                    number(body, Demand::DomainCut, "window_pending_cut_phase");
                auto pending = predicate(body, "index.equal",
                                         {unblocked[Demand::Phase], cut},
                                         "window_pending_cut");
                body.complete(collectBranch(
                    body, pending, unblocked, "window_cut",
                    [&](Control &cutBody, ValueRange cutState) {
                      // Recompute in this closed region; no cross-region SSA.
                      auto phase = number(cutBody, Demand::DomainCut,
                                          "window_blocked_phase");
                      auto yes = predicate(cutBody, "index.equal",
                                           {cutState[Demand::Phase], phase},
                                           "window_set_blocked");
                      Values values(cutState.take_front(n + 1));
                      values.push_back(yes);
                      cutBody.complete(values);
                    },
                    [&](Control &ready, ValueRange current) {
                      auto completed = number(ready, Demand::Completed,
                                              "window_completed_phase");
                      auto done = predicate(ready, "index.equal",
                                            {current[Demand::Phase], completed},
                                            "window_completed");
                      ready.complete(collectBranch(
                          ready, done, current, "window_terminal",
                          [&](Control &terminal, ValueRange retained) {
                            identity(terminal, retained);
                          },
                          [&](Control &active, ValueRange seed) {
                            auto lengthValue =
                                length(active, seed[n], "window_seed_length");
                            auto maximum = number(active, result.capacity,
                                                  "window_seed_capacity");
                            auto room = predicate(active, "index.less",
                                                  {lengthValue, maximum},
                                                  "window_seed_room");
                            active.complete(collectBranch(
                                active, room, seed, "window_room",
                                [&](Control &loop, ValueRange args) {
                                  auto lower =
                                      number(loop, 0, "window_collect_lower");
                                  auto upper = number(loop, result.capacity + 1,
                                                      "window_collect_upper");
                                  auto values = loop.loop(
                                      lower, upper, args.take_front(n + 2),
                                      args.drop_front(n + 2), collectedTypes(),
                                      true, "window_collect_loop",
                                      [&](unsigned) {
                                        Types inputs{index};
                                        append_range(inputs, collectInputs());
                                        Types outputs{boolean};
                                        append_range(outputs, collectedTypes());
                                        return function(
                                            "collect_iteration", inputs,
                                            outputs, true,
                                            [&](Control &iterationBody,
                                                ValueRange iterationArgs) {
                                              iteration(
                                                  iterationBody,
                                                  iterationArgs.drop_front());
                                            });
                                      });
                                  loop.complete(values);
                                },
                                [&](Control &full, ValueRange retained) {
                                  identity(full, retained);
                                }));
                          }));
                    }));
              });
          c.returned(values);
        });
  }
  void replay() {
    Types inputs(controller.state.begin(), controller.state.end());
    append_range(inputs, Types{result.requestSequence, result.answerSequence,
                               index, index});
    append_range(inputs, controller.stores);
    result.replay = function(
        "replay", inputs, controller.state, false,
        [&](Control &c, ValueRange a) {
          unsigned n = controller.state.size();
          auto requests = length(c, a[n], "window_replay_requests");
          auto answers = length(c, a[n + 1], "window_replay_answers");
          require(c,
                  predicate(c, "index.equal", {requests, answers},
                            "window_equal_lengths"),
                  "window_admit_lengths");
          auto bound = number(c, result.capacity + 1, "window_replay_bound");
          require(c,
                  predicate(c, "index.less", {requests, bound},
                            "window_replay_fits"),
                  "window_admit_replay_capacity");
          auto reversed = predicate(c, "index.less", {a[n + 3], a[n + 2]},
                                    "window_reversed_range");
          require(c, predicate(c, "bool.not", reversed, "window_ordered_range"),
                  "window_admit_range_order");
          auto outside = predicate(c, "index.less", {requests, a[n + 3]},
                                   "window_range_outside");
          require(c, predicate(c, "bool.not", outside, "window_range_inside"),
                  "window_admit_range_end");
          Values captures{a[n], a[n + 1]};
          append_range(captures, a.drop_front(n + 4));
          c.returned(c.loop(
              a[n + 2], a[n + 3], a.take_front(n), captures, controller.state,
              false, "window_replay_loop", [&](unsigned) {
                Types types{index};
                append_range(types, controller.state);
                append_range(types, Types{result.requestSequence,
                                          result.answerSequence});
                append_range(types, controller.stores);
                return function(
                    "replay_iteration", types, controller.state, true,
                    [&](Control &body, ValueRange args) {
                      Values advance(args.slice(1, n));
                      append_range(advance, args.drop_front(n + 3));
                      auto advanced = call(body, controller.advance, advance,
                                           "window_replay_advance");
                      auto request =
                          apply(body, "sequence.at", exchange.request,
                                {args[n + 1], args[0]}, "window_replay_request",
                                {element(result.requestSequence)})[0];
                      auto answer =
                          apply(body, "sequence.at", response.answer,
                                {args[n + 2], args[0]}, "window_replay_answer",
                                {element(result.answerSequence)})[0];
                      Values resumed{request, answer};
                      append_range(resumed, advanced);
                      body.complete(call(body, response.resume, resumed,
                                         "window_replay_resume"));
                    });
              }));
        });
  }
  void finish() {
    Types inputs(controller.state.begin(), controller.state.end());
    append_range(inputs, controller.stores);
    result.finish = function(
        "finish", inputs, scopedDataSignature(controller.finish).getResults(),
        false, [&](Control &c, ValueRange a) {
          auto advanced =
              call(c, controller.advance, a, "window_finish_advance");
          c.returned(
              call(c, controller.finish, advanced, "window_finish_payload"));
        });
  }
};
} // namespace
Expected<OracleQueryWindow> emitOracleQueryWindow(
    ModuleOp candidate, const OracleQueryController &controller,
    const OracleQueryDemand &demand, const OracleQueryExchange &exchange,
    const OracleQueryResponse &response, uint64_t capacity,
    OracleVirtualFunctionWork &work) {
  auto context = OracleVerificationContext::read(candidate);
  if (!context) {
    consumeError(context.takeError());
    return error("oracle-window-source");
  }
  Emitter emitter(context->getUnit(), controller, demand, exchange, response,
                  capacity);
  auto savedWork = work;
  SmallPtrSet<Operation *, 32> original;
  for (auto &op : context->getUnit().getBody().front())
    original.insert(&op);
  bool published = false;
  auto rollback = llvm::scope_exit([&] {
    if (published)
      return;
    SmallVector<Operation *> additions;
    for (auto &op : emitter.unit.getBody().front())
      if (!original.contains(&op))
        additions.push_back(&op);
    for (auto *op : additions)
      op->dropAllReferences();
    for (auto *op : reverse(additions))
      op->erase();
    work = savedWork;
  });
  if (auto e = emitter.plan(*context, work))
    return std::move(e);
  emitter.collect();
  emitter.replay();
  emitter.finish();
  // Validate the conservative reservation against the actual additions before
  // publication. Subtract bounded costs instead of overflowing running sums.
  uint64_t operationsRemaining = operationAllowance;
  uint64_t slotsRemaining = emitter.generatedSlots;
  bool withinReservation = true;
  for (auto &addition : emitter.unit.getBody().front()) {
    if (original.contains(&addition))
      continue;
    addition.walk([&](Operation *op) {
      if (!withinReservation)
        return;
      auto charge = [&](uint64_t cost) {
        if (cost > slotsRemaining)
          withinReservation = false;
        else
          slotsRemaining -= cost;
      };
      if (!operationsRemaining) {
        withinReservation = false;
        return;
      }
      --operationsRemaining;
      charge(op->getNumOperands());
      charge(op->getNumResults());
      for (auto &region : op->getRegions())
        for (auto &block : region) {
          if (!operationsRemaining) {
            withinReservation = false;
            return;
          }
          --operationsRemaining;
          charge(block.getNumArguments());
        }
    });
  }
  if (!withinReservation)
    return error("oracle-window-limit");
  // Reacquire after mutation. The checker reads actual IR independently.
  auto actual = OracleVerificationContext::read(candidate);
  if (!actual) {
    consumeError(actual.takeError());
    return error("oracle-window-body");
  }
  if (auto e = checkOracleQueryWindow(*actual, controller, demand, exchange,
                                      response, emitter.result))
    return std::move(e);
  published = true;
  return std::move(emitter.result);
}
} // namespace zkc::protocol
