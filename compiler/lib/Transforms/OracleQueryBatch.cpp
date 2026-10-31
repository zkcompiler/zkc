#include "OracleQueryBatch.h"
#include "OracleVerificationContext.h"
#include "RealizationEmission.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SmallPtrSet.h"
#include <algorithm>

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using Types = SmallVector<Type>;
using Values = SmallVector<Value>;
using Control = exec::ScopedExecutionBuilder;

struct Emitter {
  protocol_ir::ProtocolModuleOp unit;
  ArrayRef<OracleQueryBatchRoot> roots;
  OracleQueryBatch result;
  Types stores, answers;
  OpBuilder builder;
  mathematical::RealizationEmitter bindings;
  Type index, boolean;
  unsigned next = 0;
  uint64_t operationAllowance = 0, generatedSlots = 0;

  Emitter(protocol_ir::ProtocolModuleOp unit,
          ArrayRef<OracleQueryBatchRoot> roots)
      : unit(unit), roots(roots), builder(unit.getContext()),
        bindings(unit, "_oracle_batch_binding_"),
        index(IntegerType::get(unit.getContext(), 64, IntegerType::Unsigned)),
        boolean(builder.getI1Type()) {}

  Error plan(const OracleVerificationContext &context,
             OracleVirtualFunctionWork &work) {
    if (roots.empty() || roots.size() > 32)
      return error("oracle-batch-capacity");
    auto signature = [&](func::FuncOp helper) -> FunctionType {
      if (!helper || helper->getParentOp() != unit || !helper.isPrivate() ||
          helper->hasAttr("runtime.region") ||
          helper->hasAttr("data.preconditions") ||
          !helper->getAttrOfType<UnitAttr>("no_inline") ||
          !context.getClosure().bodies.count(helper.getSymName().str()))
        return {};
      auto origin =
          builder.getArrayAttr({builder.getStringAttr(helper.getSymName()),
                                builder.getArrayAttr({})});
      if (helper->getAttr("runtime.origin") != origin)
        return {};
      return scopedDataSignature(helper);
    };
    auto has = [&](func::FuncOp helper, TypeRange inputs, TypeRange outputs) {
      auto type = signature(helper);
      return type && equal(type.getInputs(), inputs) &&
             equal(type.getResults(), outputs);
    };
    uint64_t capacity = 0;
    for (const auto &root : roots) {
      if (!root.controller || !root.demand || !root.window)
        return error("oracle-batch-layout");
      const auto &controller = *root.controller;
      const auto &demand = *root.demand;
      const auto &window = *root.window;
      if (!window.capacity || window.capacity >= 1048576)
        return error("oracle-batch-capacity");
      if (!capacity) {
        capacity = window.capacity;
        result.requestSequence = window.requestSequence;
        result.answerSequence = window.answerSequence;
        stores.assign(controller.stores.begin(), controller.stores.end());
      }
      if (window.capacity != capacity ||
          window.requestSequence != result.requestSequence ||
          window.answerSequence != result.answerSequence ||
          !equal(controller.stores, stores))
        return error("oracle-batch-layout");
      for (auto types :
           {ArrayRef<Type>(controller.state), ArrayRef<Type>(demand.state),
            ArrayRef<Type>(controller.stores)}) {
        if (types.size() > 512)
          return error("oracle-batch-capacity");
        if (!all_of(types, [&](Type type) {
              return type && type.getContext() == unit.getContext();
            }))
          return error("oracle-batch-layout");
      }
      if (controller.state.empty() || demand.state.empty())
        return error("oracle-batch-layout");
      for (Type type : {window.requestSequence, window.answerSequence})
        if (!isa_and_nonnull<data::SequenceType>(type) ||
            type.getContext() != unit.getContext())
          return error("oracle-batch-layout");
      append_range(result.demandState, demand.state);
      append_range(result.evaluatorState, controller.state);
      // Bound all additions before constructing function signatures or CFG.
      size_t d = result.demandState.size(), e = result.evaluatorState.size();
      if (std::max({d + stores.size() + 1,
                    e + 2 + roots.size() + stores.size() + 1,
                    d + 1 + roots.size(), e + stores.size() + 2}) > 512)
        return error("oracle-batch-capacity");
      Types collect(demand.state.begin(), demand.state.end());
      append_range(collect, Types{window.requestSequence, boolean});
      Types collected(collect);
      append_range(collect, stores);
      Types replay(controller.state.begin(), controller.state.end());
      append_range(replay, Types{window.requestSequence, window.answerSequence,
                                 index, index});
      append_range(replay, stores);
      Types finish(controller.state.begin(), controller.state.end());
      append_range(finish, stores);
      auto logicalAnswer = signature(controller.finish);
      if (!logicalAnswer || logicalAnswer.getNumResults() != 1 ||
          !equal(logicalAnswer.getInputs(), controller.state) ||
          !has(window.collect, collect, collected) ||
          !has(window.replay, replay, controller.state) ||
          !has(window.finish, finish, logicalAnswer.getResults()) ||
          window.collect == window.replay || window.collect == window.finish ||
          window.replay == window.finish)
        return error("oracle-batch-layout");
      answers.push_back(logicalAnswer.getResult(0));
    }
    // Width includes scope on calls, the conditional decision and captures,
    // replay's two sequences and every root offset, and collect's full return.
    size_t width = std::max(
        {result.demandState.size() + stores.size() + 1,
         result.evaluatorState.size() + roots.size() + stores.size() + 3,
         result.demandState.size() + roots.size() + 1,
         result.evaluatorState.size() + stores.size() + 2});
    operationAllowance = 256 * (roots.size() + 1);
    generatedSlots = operationAllowance * (width + 16);
    if (operationAllowance > work.operations || generatedSlots > work.slots)
      return error("oracle-batch-limit");
    work.operations -= operationAllowance;
    work.slots -= generatedSlots;
    return Error::success();
  }

  func::FuncOp function(StringRef label, TypeRange inputs, TypeRange outputs,
                        bool region,
                        llvm::function_ref<void(Control &, ValueRange)> emit) {
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToEnd(&unit.getBody().front());
    std::string name;
    do {
      name = "_oracle_batch_" + label.str() + "_" + std::to_string(next++);
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
  Value length(Control &c, Value sequence, StringRef site) {
    auto element =
        cast<data::SequenceType>(sequence.getType()).getElementType();
    return apply(c, "sequence.length", index, sequence, site,
                 {TypeAttr::get(element)})[0];
  }
  Values call(Control &c, func::FuncOp helper, ValueRange inputs,
              StringRef site) {
    return c.invoke(
        "func.call", scopedDataSignature(helper).getResults(), c.scoped(inputs),
        {builder.getNamedAttr("callee", FlatSymbolRefAttr::get(helper)),
         builder.getNamedAttr("runtime.site", builder.getStringAttr(site))});
  }
  static std::string site(StringRef label, unsigned root) {
    return (label + "_" + Twine(root)).str();
  }
  void collect() {
    Types inputs(result.demandState.begin(), result.demandState.end());
    append_range(inputs, stores);
    Types outputs(result.demandState.begin(), result.demandState.end());
    outputs.push_back(result.requestSequence);
    append_range(outputs, Types(roots.size(), index));
    result.collect = function(
        "collect", inputs, outputs, false, [&](Control &c, ValueRange a) {
          auto storeArgs = a.drop_front(result.demandState.size());
          auto element =
              cast<data::SequenceType>(result.requestSequence).getElementType();
          auto requests =
              apply(c, "sequence.empty", result.requestSequence, {},
                    "batch_empty_requests", {TypeAttr::get(element)})[0];
          auto zero = number(c, 0, "batch_collect_zero");
          auto blocked = apply(c, "index.less", boolean, {zero, zero},
                               "batch_unblocked")[0];
          Values updated, ends;
          unsigned offset = 0;
          for (auto [i, root] : enumerate(roots)) {
            unsigned count = root.demand->state.size();
            Values args(a.slice(offset, count));
            append_range(args, Values{requests, blocked});
            append_range(args, storeArgs);
            auto values =
                call(c, root.window->collect, args, site("batch_collect", i));
            append_range(updated, ValueRange(values).take_front(count));
            requests = values[count];
            blocked = values[count + 1];
            ends.push_back(length(c, requests, site("batch_end", i)));
            offset += count;
          }
          updated.push_back(requests);
          append_range(updated, ends);
          c.returned(updated);
        });
  }
  void checkAvailable() {
    Types inputs{result.requestSequence};
    append_range(inputs, result.evaluatorState);
    append_range(inputs, stores);
    result.checkAvailable = function(
        "check_available", inputs, {}, false, [&](Control &c, ValueRange a) {
          auto size = length(c, a[0], "batch_available_length");
          auto zero = number(c, 0, "batch_available_zero");
          auto empty = apply(c, "index.equal", boolean, {size, zero},
                             "batch_is_empty")[0];
          auto captures = a.drop_front();
          Types captureTypes(result.evaluatorState.begin(),
                             result.evaluatorState.end());
          append_range(captureTypes, stores);
          c.conditional(
              empty, captures, {}, "batch_empty_round", [&](unsigned branch) {
                return function(
                    "empty_region", captureTypes, {}, true,
                    [&](Control &body, ValueRange original) {
                      if (branch == 0) {
                        unsigned first = 0;
                        for (auto [i, root] : enumerate(roots)) {
                          unsigned count = root.controller->state.size();
                          Values args(original.slice(first, count));
                          append_range(args, original.drop_front(
                                                 result.evaluatorState.size()));
                          call(body, root.window->finish, args,
                               site("batch_empty_finish", i));
                          first += count;
                        }
                        auto zero = number(body, 0, "batch_empty_zero");
                        auto impossible =
                            apply(body, "index.less", boolean, {zero, zero},
                                  "batch_impossible_empty")[0];
                        apply(body, "control.require", {}, impossible,
                              "batch_reject_empty");
                      }
                      body.complete({});
                    });
              });
          c.returned({});
        });
  }
  void replay() {
    Types inputs(result.evaluatorState.begin(), result.evaluatorState.end());
    append_range(inputs, Types{result.requestSequence, result.answerSequence});
    append_range(inputs, Types(roots.size(), index));
    append_range(inputs, stores);
    result.replay = function(
        "replay", inputs, result.evaluatorState, false,
        [&](Control &c, ValueRange a) {
          unsigned n = result.evaluatorState.size();
          auto lengthValue = length(c, a[n], "batch_replay_length");
          auto complete = apply(c, "index.equal", boolean,
                                {a[n + 1 + roots.size()], lengthValue},
                                "batch_last_end")[0];
          apply(c, "control.require", {}, complete, "batch_admit_last_end");
          auto begin = number(c, 0, "batch_replay_zero");
          unsigned offset = 0;
          Values updated;
          for (auto [i, root] : enumerate(roots)) {
            unsigned count = root.controller->state.size();
            auto end = a[n + 2 + i];
            Values args(a.slice(offset, count));
            append_range(args, Values{a[n], a[n + 1], begin, end});
            append_range(args, a.drop_front(n + 2 + roots.size()));
            append_range(updated, call(c, root.window->replay, args,
                                       site("batch_replay", i)));
            begin = end;
            offset += count;
          }
          c.returned(updated);
        });
  }
  void finish() {
    Types inputs(result.evaluatorState.begin(), result.evaluatorState.end());
    append_range(inputs, stores);
    result.finish = function(
        "finish", inputs, answers, false, [&](Control &c, ValueRange a) {
          unsigned offset = 0;
          Values returned;
          for (auto [i, root] : enumerate(roots)) {
            unsigned count = root.controller->state.size();
            Values args(a.slice(offset, count));
            append_range(args, a.drop_front(result.evaluatorState.size()));
            append_range(returned, call(c, root.window->finish, args,
                                        site("batch_finish", i)));
            offset += count;
          }
          c.returned(returned);
        });
  }
};
} // namespace

Expected<OracleQueryBatch>
emitOracleQueryBatch(ModuleOp candidate, ArrayRef<OracleQueryBatchRoot> roots,
                     OracleVirtualFunctionWork &work) {
  auto context = OracleVerificationContext::read(candidate);
  if (!context) {
    consumeError(context.takeError());
    return error("oracle-batch-source");
  }
  Emitter emitter(context->getUnit(), roots);
  auto savedWork = work;
  SmallPtrSet<Operation *, 32> original;
  for (auto &op : emitter.unit.getBody().front())
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
  emitter.checkAvailable();
  emitter.replay();
  emitter.finish();
  uint64_t operationsRemaining = emitter.operationAllowance;
  uint64_t slotsRemaining = emitter.generatedSlots;
  bool withinReservation = true;
  for (auto &addition : emitter.unit.getBody().front()) {
    if (original.contains(&addition))
      continue;
    addition.walk([&](Operation *op) {
      if (!withinReservation)
        return;
      auto charge = [&](uint64_t slots) {
        if (slots > slotsRemaining)
          withinReservation = false;
        else
          slotsRemaining -= slots;
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
    return error("oracle-batch-limit");
  // Admission and the independent reader borrow the final candidate afresh.
  auto actual = OracleVerificationContext::read(candidate);
  if (!actual) {
    consumeError(actual.takeError());
    return error("oracle-batch-body");
  }
  if (auto e = checkOracleQueryBatch(*actual, roots, emitter.result))
    return std::move(e);
  published = true;
  return std::move(emitter.result);
}
} // namespace zkc::protocol
