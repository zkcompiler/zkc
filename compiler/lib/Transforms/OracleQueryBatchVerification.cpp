#include "NativeBindingApplication.h"
#include "OracleQueryBatch.h"
#include "OracleVerificationContext.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Refusal.h"
#include <algorithm>
#include <set>

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using Types = SmallVector<Type>;
using Values = SmallVector<Value>;

// Only composition is checked here. Source-derived controller, demand and
// window semantics are caller obligations checked once for the whole batch.
// In particular, never recursively check every window's controller closure.
struct Layout {
  Types demand, evaluator, stores, answers;
  Type requests, answerSequence;

  bool read(const OracleVerificationContext &context,
            ArrayRef<OracleQueryBatchRoot> roots,
            const OracleQueryBatch &actual) {
    if (roots.empty() || roots.size() > 32)
      return false;
    auto unit = context.getUnit();
    auto *ctx = unit.getContext();
    Type index = IntegerType::get(ctx, 64, IntegerType::Unsigned);
    Type boolean = IntegerType::get(ctx, 1);
    auto signature = [&](func::FuncOp helper) -> FunctionType {
      if (!helper || helper->getParentOp() != unit || !helper.isPrivate() ||
          helper->hasAttr("runtime.region") ||
          helper->hasAttr("data.preconditions") ||
          !helper->getAttrOfType<UnitAttr>("no_inline") ||
          !context.getClosure().bodies.count(helper.getSymName().str()))
        return {};
      auto origin =
          ArrayAttr::get(ctx, {StringAttr::get(ctx, helper.getSymName()),
                               ArrayAttr::get(ctx, {})});
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
        return false;
      const auto &controller = *root.controller;
      const auto &discovery = *root.demand;
      const auto &window = *root.window;
      if (!window.capacity || window.capacity >= 1048576)
        return false;
      if (!capacity) {
        capacity = window.capacity;
        requests = window.requestSequence;
        answerSequence = window.answerSequence;
        stores.assign(controller.stores.begin(), controller.stores.end());
      }
      if (window.capacity != capacity || window.requestSequence != requests ||
          window.answerSequence != answerSequence ||
          !equal(controller.stores, stores) || controller.state.empty() ||
          discovery.state.empty())
        return false;
      for (auto types :
           {ArrayRef<Type>(controller.state), ArrayRef<Type>(discovery.state),
            ArrayRef<Type>(controller.stores)})
        if (types.size() > 512 || !all_of(types, [&](Type type) {
              return type && type.getContext() == ctx;
            }))
          return false;
      for (Type type : {requests, answerSequence})
        if (!isa_and_nonnull<data::SequenceType>(type) ||
            type.getContext() != ctx)
          return false;
      append_range(demand, discovery.state);
      append_range(evaluator, controller.state);
      // The maximum includes borrowed scope, all replay offsets, the complete
      // collect payload, and the conditional predicate plus closed captures.
      if (std::max({demand.size() + stores.size() + 1,
                    evaluator.size() + roots.size() + stores.size() + 3,
                    demand.size() + roots.size() + 1,
                    evaluator.size() + stores.size() + 2}) > 512)
        return false;
      Types collect(discovery.state.begin(), discovery.state.end());
      append_range(collect, Types{requests, boolean});
      Types collected(collect);
      append_range(collect, stores);
      Types replay(controller.state.begin(), controller.state.end());
      append_range(replay, Types{requests, answerSequence, index, index});
      append_range(replay, stores);
      Types finish(controller.state.begin(), controller.state.end());
      append_range(finish, stores);
      auto answer = signature(controller.finish);
      if (!answer || answer.getNumResults() != 1 ||
          !equal(answer.getInputs(), controller.state) ||
          !has(window.collect, collect, collected) ||
          !has(window.replay, replay, controller.state) ||
          !has(window.finish, finish, answer.getResults()) ||
          window.collect == window.replay || window.collect == window.finish ||
          window.replay == window.finish)
        return false;
      answers.push_back(answer.getResult(0));
    }
    return equal(actual.demandState, demand) &&
           equal(actual.evaluatorState, evaluator) &&
           actual.requestSequence == requests &&
           actual.answerSequence == answerSequence && actual.collect &&
           actual.checkAvailable && actual.replay && actual.finish &&
           actual.collect != actual.checkAvailable &&
           actual.checkAvailable != actual.replay &&
           actual.checkAvailable != actual.finish &&
           actual.collect != actual.replay && actual.collect != actual.finish &&
           actual.replay != actual.finish;
  }
};

// Read the admitted actual CFG/SSA associations. Site strings locate expected
// steps but never prove them: every operation, binding, argument, return,
// selected callee and closed region is checked independently below.
struct Reader {
  const OracleVerificationContext &context;
  ArrayRef<OracleQueryBatchRoot> roots;
  const OracleQueryBatch &actual;
  const Layout &layout;
  protocol_ir::ProtocolModuleOp unit;
  Type index, boolean, scope;
  bool valid = true;
  std::set<Operation *> visited;

  Reader(const OracleVerificationContext &context,
         ArrayRef<OracleQueryBatchRoot> roots, const OracleQueryBatch &actual,
         const Layout &layout)
      : context(context), roots(roots), actual(actual), layout(layout),
        unit(context.getUnit()),
        index(IntegerType::get(unit.getContext(), 64, IntegerType::Unsigned)),
        boolean(IntegerType::get(unit.getContext(), 1)),
        scope(runtime::ScopeType::get(unit.getContext())) {}
  bool expect(bool condition) {
    valid &= condition;
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
      auto tag = step.operation->getAttrOfType<StringAttr>(
          operation == "func.call" ? "runtime.site" : "site");
      if (!reader.expect(step.operation->getName().getStringRef() ==
                             operation &&
                         tag && tag.getValue() == site))
        return nullptr;
      return &step;
    }
    Values result(const SourceExecutionStep *step, TypeRange outputs,
                  ValueRange inputs, unsigned regions = 0) {
      if (!reader.valid || !step)
        return Values(outputs.size());
      if (!reader.expect(equal(step->inputs, inputs) &&
                         step->regions.size() == regions &&
                         equal(ValueRange(step->outputs).getTypes(), outputs)))
        return Values(outputs.size());
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
      if (reader.expect(matchesNativeBinding(
              binding, {contract.str(), SmallVector<Attribute>(statics), {}})))
        reader.expect(
            invocationParametersMatch(contract, binding.getArgumentsAttr(),
                                      op.getParametersAttr(), parameters));
      return values;
    }
    Value number(uint64_t value, StringRef site) {
      return apply("index.constant", reader.index, {}, site, {},
                   {std::to_string(value)})[0];
    }
    Value length(Type sequence, Value value, StringRef site) {
      auto element = cast<data::SequenceType>(sequence).getElementType();
      return apply("sequence.length", reader.index, value, site,
                   {TypeAttr::get(element)})[0];
    }
    Values call(func::FuncOp helper, ValueRange inputs, StringRef site) {
      auto *step = take("func.call", site);
      auto values =
          result(step, scopedDataSignature(helper).getResults(), inputs);
      if (reader.valid)
        reader.expect(
            SymbolTable::lookupSymbolIn(
                reader.unit, cast<func::CallOp>(step->operation).getCallee()) ==
            helper.getOperation());
      return values;
    }
    void conditional(Value predicate, ValueRange captures, StringRef site,
                     llvm::function_ref<void(unsigned, func::FuncOp)> check) {
      auto *step = take("exec.test", site);
      Values inputs{predicate};
      append_range(inputs, captures);
      result(step, {}, inputs, 2);
      if (reader.valid)
        for (unsigned branch = 0; branch < 2; ++branch)
          check(branch, step->regions[branch]);
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
            bool region, llvm::function_ref<void(Cursor &, ValueRange)> read) {
    if (!valid)
      return;
    Types formals{scope};
    append_range(formals, inputs);
    if (!expect(function && function->getParentOp() == unit &&
                function.isPrivate() &&
                !function->hasAttr("data.preconditions") &&
                function->getAttrOfType<UnitAttr>("no_inline") &&
                function->hasAttr("runtime.region") == region &&
                visited.insert(function.getOperation()).second &&
                equal(function.getArgumentTypes(), formals) &&
                function.getNumResults() == 1))
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
    read(cursor, function.getArguments().drop_front());
    expect(cursor.offset == cursor.steps.size());
  }
  static std::string site(StringRef name, unsigned root) {
    return (name + "_" + Twine(root)).str();
  }
  void collect() {
    Types inputs(layout.demand);
    append_range(inputs, layout.stores);
    Types outputs(layout.demand);
    outputs.push_back(layout.requests);
    append_range(outputs, Types(roots.size(), index));
    body(actual.collect, inputs, outputs, false, [&](Cursor &c, ValueRange a) {
      auto storeArgs = a.drop_front(layout.demand.size());
      auto element = cast<data::SequenceType>(layout.requests).getElementType();
      auto requests =
          c.apply("sequence.empty", layout.requests, {}, "batch_empty_requests",
                  {TypeAttr::get(element)})[0];
      auto zero = c.number(0, "batch_collect_zero");
      auto blocked =
          c.apply("index.less", boolean, {zero, zero}, "batch_unblocked")[0];
      Values expected, ends;
      unsigned first = 0;
      for (auto [i, root] : enumerate(roots)) {
        unsigned count = root.demand->state.size();
        Values args(a.slice(first, count));
        append_range(args, Values{requests, blocked});
        append_range(args, storeArgs);
        auto collected =
            c.call(root.window->collect, args, site("batch_collect", i));
        append_range(expected, ValueRange(collected).take_front(count));
        requests = collected[count];
        blocked = collected[count + 1];
        ends.push_back(
            c.length(layout.requests, requests, site("batch_end", i)));
        first += count;
      }
      expected.push_back(requests);
      append_range(expected, ends);
      c.finish(expected);
    });
  }
  void checkAvailable() {
    Types inputs{layout.requests};
    append_range(inputs, layout.evaluator);
    append_range(inputs, layout.stores);
    body(
        actual.checkAvailable, inputs, {}, false, [&](Cursor &c, ValueRange a) {
          auto size = c.length(layout.requests, a[0], "batch_available_length");
          auto zero = c.number(0, "batch_available_zero");
          auto empty = c.apply("index.equal", boolean, {size, zero},
                               "batch_is_empty")[0];
          Types captures(layout.evaluator);
          append_range(captures, layout.stores);
          c.conditional(
              empty, a.drop_front(), "batch_empty_round",
              [&](unsigned branch, func::FuncOp function) {
                body(function, captures, {}, true,
                     [&](Cursor &b, ValueRange original) {
                       if (branch == 0) {
                         unsigned offset = 0;
                         for (auto [i, root] : enumerate(roots)) {
                           unsigned count = root.controller->state.size();
                           Values args(original.slice(offset, count));
                           append_range(args, original.drop_front(
                                                  layout.evaluator.size()));
                           b.call(root.window->finish, args,
                                  site("batch_empty_finish", i));
                           offset += count;
                         }
                         auto zero = b.number(0, "batch_empty_zero");
                         auto impossible =
                             b.apply("index.less", boolean, {zero, zero},
                                     "batch_impossible_empty")[0];
                         b.apply("control.require", {}, impossible,
                                 "batch_reject_empty");
                       }
                       b.finish({}, true);
                     });
              });
          c.finish({});
        });
  }
  void replay() {
    Types inputs(layout.evaluator);
    append_range(inputs, Types{layout.requests, layout.answerSequence});
    append_range(inputs, Types(roots.size(), index));
    append_range(inputs, layout.stores);
    body(actual.replay, inputs, layout.evaluator, false,
         [&](Cursor &c, ValueRange a) {
           unsigned n = layout.evaluator.size();
           auto length = c.length(layout.requests, a[n], "batch_replay_length");
           auto complete =
               c.apply("index.equal", boolean,
                       {a[n + 1 + roots.size()], length}, "batch_last_end")[0];
           c.apply("control.require", {}, complete, "batch_admit_last_end");
           auto begin = c.number(0, "batch_replay_zero");
           Values returned;
           unsigned offset = 0;
           for (auto [i, root] : enumerate(roots)) {
             unsigned count = root.controller->state.size();
             auto end = a[n + 2 + i];
             Values args(a.slice(offset, count));
             append_range(args, Values{a[n], a[n + 1], begin, end});
             append_range(args, a.drop_front(n + 2 + roots.size()));
             append_range(returned, c.call(root.window->replay, args,
                                           site("batch_replay", i)));
             begin = end;
             offset += count;
           }
           c.finish(returned);
         });
  }
  void finish() {
    Types inputs(layout.evaluator);
    append_range(inputs, layout.stores);
    body(actual.finish, inputs, layout.answers, false,
         [&](Cursor &c, ValueRange a) {
           Values returned;
           unsigned offset = 0;
           for (auto [i, root] : enumerate(roots)) {
             unsigned count = root.controller->state.size();
             Values args(a.slice(offset, count));
             append_range(args, a.drop_front(layout.evaluator.size()));
             append_range(returned, c.call(root.window->finish, args,
                                           site("batch_finish", i)));
             offset += count;
           }
           c.finish(returned);
         });
  }
};
} // namespace

Error checkOracleQueryBatch(const OracleVerificationContext &context,
                            ArrayRef<OracleQueryBatchRoot> roots,
                            const OracleQueryBatch &actual) {
  Layout layout;
  if (!layout.read(context, roots, actual))
    return error("oracle-batch-body");
  Reader reader(context, roots, actual, layout);
  reader.collect();
  reader.checkAvailable();
  reader.replay();
  reader.finish();
  return reader.valid ? Error::success() : error("oracle-batch-body");
}
} // namespace zkc::protocol
