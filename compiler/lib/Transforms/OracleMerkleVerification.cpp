#include "NativeBindingApplication.h"
#include "OracleMerkle.h"
#include "OracleVerificationContext.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Refusal.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
struct Reader {
  const OracleVerificationContext &context;
  Type index, boolean;
  bool valid = true;
  explicit Reader(const OracleVerificationContext &context)
      : context(context),
        index(IntegerType::get(context.getModule().getContext(), 64,
                               IntegerType::Unsigned)),
        boolean(IntegerType::get(context.getModule().getContext(), 1)) {}
  bool expect(bool condition) {
    valid &= condition;
    return valid;
  }
  struct Cursor {
    Reader &reader;
    ArrayRef<SourceExecutionStep> steps;
    unsigned offset = 0;
    const SourceExecutionStep *take(StringRef name, StringRef site) {
      if (!reader.valid || !reader.expect(offset < steps.size()))
        return nullptr;
      const auto &step = steps[offset++];
      auto attr = step.operation->getAttrOfType<StringAttr>(
          name == "func.call" ? "runtime.site" : "site");
      if (!reader.expect(step.operation->getName().getStringRef() == name &&
                         attr && attr.getValue() == site))
        return nullptr;
      return &step;
    }
    Values result(const SourceExecutionStep *step, TypeRange types,
                  ValueRange inputs, unsigned regions = 0) {
      if (!reader.valid || !step ||
          !reader.expect(equal(step->inputs, inputs) &&
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
    Value number(uint64_t n, StringRef site) {
      return apply("index.constant", reader.index, {}, site, {},
                   {std::to_string(n)})[0];
    }
    Value binary(StringRef contract, Value a, Value b, StringRef site) {
      return apply(contract,
                   contract == "index.less" || contract == "index.equal"
                       ? reader.boolean
                       : reader.index,
                   {a, b}, site)[0];
    }
    void require(Value predicate, StringRef site) {
      apply("control.require", {}, predicate, site);
    }
    Values call(func::FuncOp expected, TypeRange outputs, ValueRange inputs,
                StringRef site) {
      auto *step = take("func.call", site);
      auto values = result(step, outputs, inputs);
      if (reader.valid) {
        auto op = cast<func::CallOp>(step->operation);
        reader.expect(SymbolTable::lookupSymbolIn(reader.context.getUnit(),
                                                  op.getCallee()) ==
                      expected.getOperation());
      }
      return values;
    }
    Values loop(Value lower, Value upper, ValueRange seeds, TypeRange outputs,
                llvm::function_ref<void(func::FuncOp)> check) {
      auto *step = take("exec.range", "layout_bits");
      Values inputs{lower, upper};
      append_range(inputs, seeds);
      auto values = result(step, outputs, inputs, 1);
      if (reader.valid && reader.expect(step->conditional))
        check(step->regions[0]);
      return values;
    }
    Value bound(Value condition, Value height, Value limit) {
      auto *step = take("exec.test", "bit_bound");
      auto values = result(step, reader.index, {condition, height, limit}, 2);
      if (reader.valid)
        for (unsigned branch = 0; branch < 2; ++branch)
          reader.body(step->regions[branch], {reader.index, reader.index},
                      reader.index, true, [&](Cursor &body, ValueRange inputs) {
                        body.finish(inputs[branch], true);
                      });
      return values[0];
    }
    void finish(ValueRange values, bool region = false) {
      if (!reader.valid || !reader.expect(offset + 1 == steps.size()))
        return;
      const auto &step = steps[offset++];
      reader.expect((region ? isa<exec::CompleteOp>(step.operation)
                            : isa<exec::ReturnOp>(step.operation)) &&
                    step.regions.empty() && step.outputs.empty() &&
                    equal(step.inputs, values));
    }
  };
  void body(func::FuncOp function, TypeRange inputs, TypeRange outputs,
            bool region, llvm::function_ref<void(Cursor &, ValueRange)> check) {
    if (!valid)
      return;
    Types arguments{runtime::ScopeType::get(context.getModule().getContext())};
    append_range(arguments, inputs);
    if (!expect(function && function->getParentOp() == context.getUnit() &&
                function.isPrivate() &&
                function->hasAttr("runtime.region") == region &&
                equal(function.getArgumentTypes(), arguments) &&
                function.getResultTypes().size() == 1))
      return;
    auto outcome = dyn_cast<exec::OutcomeType>(function.getResultTypes()[0]);
    if (!expect(outcome && equal(outcome.getPayload(), outputs)))
      return;
    auto found = context.getClosure().bodies.find(function.getSymName().str());
    if (!expect(found != context.getClosure().bodies.end()))
      return;
    Cursor cursor{*this, found->second};
    check(cursor, function.getArguments().drop_front());
  }
  void position(func::FuncOp function, OracleLeafGrouping grouping,
                OracleLeafOrder order) {
    bool paired = grouping == OracleLeafGrouping::AntipodalPairs;
    bool reversed = order == OracleLeafOrder::BitReversed;
    body(function, {index, index}, {index, index, index}, false,
         [&](Cursor &c, ValueRange a) {
           auto zero = c.number(0, "zero");
           auto one = c.number(1, "one");
           auto width = c.number(paired ? 2 : 1, "width");
           c.require(c.binary("index.less", zero, a[0], "nonempty"),
                     "admit_rows");
           c.require(c.binary("index.less", a[1], a[0], "in_domain"),
                     "admit_query");
           if (paired) {
             auto remainder =
                 c.binary("index.mod", a[0], width, "pair_remainder");
             c.require(c.binary("index.equal", remainder, zero, "paired"),
                       "admit_pairs");
           }
           auto height = c.binary("index.div", a[0], width, "height");
           // Positive rows and, for pairs, evenness establish height > 0.
           // Read the actual total bit predicate and its guard before mapping.
           auto predecessor = c.binary("index.wrapping_sub", height, one,
                                       "height_predecessor");
           auto bits =
               c.binary("index.bit_and", height, predecessor, "height_bits");
           c.require(c.binary("index.equal", bits, zero, "power_of_two"),
                     "admit_power");
           auto leaf = c.binary("index.mod", a[1], height, "logical_leaf");
           auto slot = c.binary("index.div", a[1], height, "slot");
           if (!reversed) {
             c.finish({height, leaf, slot});
             return;
           }
           Types stateTypes{index, index, index};
           Values seeds{height, leaf, zero};
           auto limit = c.number(64, "bit_limit");
           auto small = c.binary("index.less", height, limit, "small_height");
           auto upper = c.bound(small, height, limit);
           auto state = c.loop(
               one, upper, seeds, stateTypes, [&](func::FuncOp iteration) {
                 Types inputs{index};
                 append_range(inputs, stateTypes);
                 Types outputs{boolean};
                 append_range(outputs, stateTypes);
                 body(iteration, inputs, outputs, true,
                      [&](Cursor &b, ValueRange args) {
                        auto one = b.number(1, "bit_one");
                        auto two = b.number(2, "bit_two");
                        auto span =
                            b.binary("index.div", args[1], two, "next_span");
                        auto bit =
                            b.binary("index.mod", args[2], two, "low_bit");
                        auto rest = b.binary("index.div", args[2], two,
                                             "remaining_bits");
                        auto shifted = b.binary("index.mul", args[3], two,
                                                "shift_reversed");
                        auto value =
                            b.binary("index.add", shifted, bit, "append_bit");
                        Values next{span, rest, value};
                        Values yielded{
                            b.binary("index.less", one, span, "more_bits")};
                        append_range(yielded, next);
                        b.finish(yielded, true);
                      });
               });
           c.finish({height, state[2], slot});
         });
  }
};
} // namespace
Error checkOracleMerkle(ModuleOp candidate, const OracleMerkleFunctions &actual,
                        protocol_ir::OracleKindAttr kind, StringRef scheme,
                        OracleLeafGrouping grouping, OracleLeafOrder order) {
  auto context = OracleVerificationContext::read(candidate);
  if (!context) {
    consumeError(context.takeError());
    return error("oracle-merkle-body");
  }
  return checkOracleMerkle(*context, actual, kind, scheme, grouping, order);
}
Error checkOracleMerkle(const OracleVerificationContext &context,
                        const OracleMerkleFunctions &actual,
                        protocol_ir::OracleKindAttr kind, StringRef scheme,
                        OracleLeafGrouping grouping, OracleLeafOrder order) {
  auto refuse = [] { return error("oracle-merkle-body"); };
  auto *ctx = context.getModule().getContext();
  if (!kind || kind.getContext() != ctx || kind.getIdentity() != "table" ||
      (grouping != OracleLeafGrouping::Individual &&
       grouping != OracleLeafGrouping::AntipodalPairs) ||
      (order != OracleLeafOrder::Natural &&
       order != OracleLeafOrder::BitReversed) ||
      failed(protocol_ir::OracleKindAttr::verify(
          [&]() { return emitError(context.getModule().getLoc()); },
          kind.getIdentity(), kind.getArguments())))
    return refuse();
  auto signature = resolveLogicalSignature(
      [&] { return emitError(context.getModule().getLoc()); }, ctx,
      "oracle.check", {StringAttr::get(ctx, scheme)});
  auto opening = resolveLogicalSignature(
      [&] { return emitError(context.getModule().getLoc()); }, ctx,
      "oracle.open", {StringAttr::get(ctx, scheme)});
  auto answer = dyn_cast<algebra::FieldType>(kind.getAnswerType());
  if (!answer || !signature || !opening || signature.getNumInputs() != 6 ||
      opening.getNumInputs() != 2 || opening.getNumResults() != 2 ||
      signature.getInput(4) != kind.getDataType() ||
      opening.getResult(0) != kind.getDataType() ||
      opening.getResult(1) != signature.getInput(5))
    return refuse();
  Type root = signature.getInput(0);
  Type proof = signature.getInput(5);
  Type state = opening.getInput(0);
  Reader reader(context);
  auto index = reader.index;
  unsigned width = grouping == OracleLeafGrouping::Individual ? 1 : 2;
  reader.position(actual.position, grouping, order);
  reader.body(actual.commit, {kind.getDataType(), index}, {root, state}, false,
              [&](Reader::Cursor &c, ValueRange a) {
                auto zero = c.number(0, "first_query");
                auto position = c.call(actual.position, {index, index, index},
                                       {a[1], zero}, "layout");
                auto count =
                    c.apply("vector.length", index, a[0], "actual_rows",
                            {answer.getDomain().str()})[0];
                c.require(c.binary("index.equal", count, a[1], "exact_rows"),
                          "admit_data");
                auto w = c.number(width, "width");
                Value values = a[0];
                if (grouping == OracleLeafGrouping::AntipodalPairs)
                  values = c.apply("vector.transpose", kind.getDataType(),
                                   {values, w, position[0]}, "group_rows",
                                   {answer.getDomain().str()})[0];
                if (order == OracleLeafOrder::BitReversed)
                  values =
                      c.apply("vector.bit_reverse_rows", kind.getDataType(),
                              {values, w}, "permute_leaves",
                              {answer.getDomain().str()})[0];
                c.finish(c.apply("oracle.commit", {root, state}, {values, w},
                                 "commit", {scheme.str()}));
              });
  reader.body(actual.open, {state, index, index}, {kind.getDataType(), proof},
              false, [&](Reader::Cursor &c, ValueRange a) {
                auto position = c.call(actual.position, {index, index, index},
                                       {a[1], a[2]}, "layout");
                c.finish(c.apply("oracle.open", {kind.getDataType(), proof},
                                 {a[0], position[1]}, "open", {scheme.str()}));
              });
  reader.body(
      actual.authenticate, {root, index, index, kind.getDataType(), proof},
      kind.getAnswerType(), false, [&](Reader::Cursor &c, ValueRange a) {
        auto position = c.call(actual.position, {index, index, index},
                               {a[1], a[2]}, "layout");
        auto w = c.number(width, "width");
        auto valid = c.apply("oracle.check", reader.boolean,
                             {a[0], w, position[0], position[1], a[3], a[4]},
                             "authenticate", {scheme.str()})[0];
        c.require(valid, "admit_opening");
        c.finish(c.apply("vector.get", kind.getAnswerType(),
                         {a[3], position[2]}, "answer",
                         {answer.getDomain().str()}));
      });
  return reader.valid ? Error::success() : refuse();
}
} // namespace zkc::protocol
