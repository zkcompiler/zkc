#include "ScopedExecution.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "zkc/Dialect/Data/Variant.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol::detail {
namespace {
ArrayAttr strings(Builder &builder, ArrayRef<std::string> values) {
  SmallVector<Attribute> result;
  for (const auto &value : values)
    result.push_back(builder.getStringAttr(value));
  return builder.getArrayAttr(result);
}
} // namespace
ScopedExecutionBuilder::ScopedExecutionBuilder(OpBuilder &builder,
                                               func::FuncOp function)
    : builder(builder), location(function.getLoc()), function(function),
      scope(function.getArgument(0)),
      result(cast<exec::OutcomeType>(function.getResultTypes().front())) {}
Operation *ScopedExecutionBuilder::make(StringRef name, TypeRange types,
                                        ValueRange operands,
                                        ArrayRef<NamedAttribute> attributes,
                                        ArrayRef<Block *> successors) {
  OperationState state(location, name);
  state.addTypes(types);
  state.addOperands(operands);
  state.addAttributes(attributes);
  state.addSuccessors(successors);
  return builder.create(state);
}
NamedAttribute ScopedExecutionBuilder::text(StringRef name, StringRef value) {
  return builder.getNamedAttr(name, builder.getStringAttr(value));
}
Block *ScopedExecutionBuilder::block(TypeRange types) {
  auto *block = new Block;
  function.getBody().push_back(block);
  for (auto type : types)
    block->addArgument(type, location);
  return block;
}
Block *ScopedExecutionBuilder::failed() {
  if (!failure) {
    OpBuilder::InsertionGuard guard(builder);
    failure = block(exec::StopType::get(builder.getContext()));
    builder.setInsertionPointToEnd(failure);
    auto *stopped = make("exec.failed", result, failure->getArguments());
    make("func.return", {}, stopped->getResults());
  }
  return failure;
}
void ScopedExecutionBuilder::branch(Block *target, ValueRange values) {
  cf::BranchOp::create(builder, location, target, values);
}
exec::OutcomeType ScopedExecutionBuilder::outcome(TypeRange payload) {
  return exec::OutcomeType::get(builder.getContext(),
                                SmallVector<Type>(payload));
}
runtime::TransferType ScopedExecutionBuilder::transfer(TypeRange payload) {
  return runtime::TransferType::get(builder.getContext(),
                                    SmallVector<Type>(payload));
}
ScopedExecutionBuilder::Values ScopedExecutionBuilder::dispatch(Value result,
                                                                Block *stop) {
  auto *next = block(cast<exec::OutcomeType>(result.getType()).getPayload());
  make("exec.dispatch", {}, result, {}, {next, stop ? stop : failed()});
  builder.setInsertionPointToEnd(next);
  return Values(next->getArguments());
}
ScopedExecutionBuilder::Values ScopedExecutionBuilder::invoke(
    StringRef name, TypeRange outputs, ValueRange inputs,
    ArrayRef<NamedAttribute> attributes, Block *stop) {
  auto *operation = make(name, outcome(outputs), inputs, attributes);
  return dispatch(operation->getResult(0), stop);
}
ScopedExecutionBuilder::Values
ScopedExecutionBuilder::scoped(ValueRange inputs) {
  Values result{scope};
  append_range(result, inputs);
  return result;
}

ScopedExecutionBuilder::Values ScopedExecutionBuilder::accept(Value held,
                                                              TypeRange types) {
  return invoke("runtime.accept_transfer", types, {scope, held});
}
func::FuncOp ScopedExecutionBuilder::outline(RegionBuilder body,
                                             unsigned index) {
  OpBuilder::InsertionGuard guard(builder);
  return body(index);
}
Value ScopedExecutionBuilder::region(func::FuncOp helper, ValueRange inputs,
                                     TypeRange outputs, StringRef kind,
                                     StringRef site, StringRef selection,
                                     Value coordinate, Block *stop) {
  Values entered{scope};
  if (coordinate)
    entered.push_back(coordinate);
  append_range(entered, inputs);
  SmallVector<NamedAttribute> attributes{
      text("kind", kind), text("site", site),
      builder.getNamedAttr(
          "operandSegmentSizes",
          builder.getDenseI32ArrayAttr(
              {1, coordinate ? 1 : 0, int32_t(inputs.size())}))};
  if (!selection.empty())
    attributes.push_back(text("selection", selection));
  auto child =
      invoke("runtime.enter_scope", scope.getType(), entered, attributes, stop)
          .front();
  Values actual{child};
  append_range(actual, inputs);
  auto *call =
      make("func.call", outcome(outputs), actual,
           {builder.getNamedAttr("callee",
                                 FlatSymbolRefAttr::get(builder.getContext(),
                                                        helper.getSymName()))});
  return invoke("runtime.exit_scope", transfer(outputs),
                {child, call->getResult(0)}, {}, stop)
      .front();
}
ScopedExecutionBuilder::Values
ScopedExecutionBuilder::conditional(Value condition, ValueRange captures,
                                    TypeRange types, StringRef site,
                                    RegionBuilder body) {
  auto decision = invoke("exec.test", builder.getI1Type(), {scope, condition},
                         {text("site", site)})
                      .front();
  auto *yes = block(), *no = block(), *join = block(types);
  cf::CondBranchOp::create(builder, location, decision, yes, ValueRange{}, no,
                           ValueRange{});
  for (unsigned i = 0; i < 2; ++i) {
    builder.setInsertionPointToEnd(i ? no : yes);
    auto held = region(outline(body, i), captures, types, "conditional", site,
                       i ? "else" : "then");
    branch(join, accept(held, types));
  }
  builder.setInsertionPointToEnd(join);
  return Values(join->getArguments());
}
ScopedExecutionBuilder::Values
ScopedExecutionBuilder::match(Value input, ValueRange captures, TypeRange types,
                              ArrayRef<std::string> alternatives,
                              StringRef site, RegionBuilder body) {
  auto *join = block(types);
  SmallVector<Block *> arms{failed()};
  for (const auto &alternative : alternatives) {
    auto payload = *data::variantPayloadTypes(input.getType(), alternative);
    append_range(payload, captures.getTypes());
    arms.push_back(block(payload));
  }
  Values inputs{scope, input};
  append_range(inputs, captures);
  make("exec.match", {}, inputs,
       {text("site", site),
        builder.getNamedAttr("alternatives", strings(builder, alternatives))},
       arms);
  for (auto [i, alternative] : enumerate(alternatives)) {
    builder.setInsertionPointToEnd(arms[i + 1]);
    auto held = region(outline(body, i), arms[i + 1]->getArguments(), types,
                       "match", site, alternative);
    branch(join, accept(held, types));
  }
  builder.setInsertionPointToEnd(join);
  return Values(join->getArguments());
}
ScopedExecutionBuilder::Values ScopedExecutionBuilder::loop(
    Value lower, Value upper, ValueRange seeds, ValueRange captures,
    TypeRange types, bool conditional, StringRef site, RegionBuilder body) {
  auto carry = transfer(types);
  auto counters =
      invoke("exec.range", {builder.getI64Type(), builder.getI64Type()},
             {scope, lower, upper}, {text("site", site)});
  auto initial =
      make("runtime.borrow_transfer", carry, scoped(seeds))->getResult(0);
  auto *header = block({builder.getI64Type(), carry});
  auto *iteration = block(), *finish = block(carry), *increment = block(carry);
  branch(header, {counters[0], initial});
  builder.setInsertionPointToEnd(header);
  Value coordinate = header->getArgument(0), previous = header->getArgument(1);
  auto inside = arith::CmpIOp::create(
      builder, location, arith::CmpIPredicate::ult, coordinate, counters[1]);
  cf::CondBranchOp::create(builder, location, inside, iteration, ValueRange{},
                           finish, ValueRange{previous});
  auto *cleanup = block(exec::StopType::get(builder.getContext()));
  builder.setInsertionPointToEnd(cleanup);
  make("runtime.release_transfer", {}, previous);
  branch(failed(), cleanup->getArguments());
  builder.setInsertionPointToEnd(iteration);
  auto index = invoke("runtime.iteration", lower.getType(), {scope, coordinate},
                      {text("site", site)}, cleanup)
                   .front();
  auto *peek = make("runtime.transfer_values", types, previous);
  Values inputs{index};
  append_range(inputs, peek->getResults());
  append_range(inputs, captures);
  auto helper = outline(body, 0);
  auto yielded =
      cast<exec::OutcomeType>(helper.getResultTypes().front()).getPayload();
  auto held = region(helper, inputs, yielded, "iteration", site, {}, coordinate,
                     cleanup);
  make("runtime.release_transfer", {}, previous);
  if (conditional) {
    auto decision =
        invoke("runtime.take_condition", {builder.getI1Type(), carry}, held);
    cf::CondBranchOp::create(builder, location, decision[0], increment,
                             ValueRange{decision[1]}, finish,
                             ValueRange{decision[1]});
  } else
    branch(increment, held);
  builder.setInsertionPointToEnd(increment);
  auto one = arith::ConstantIntOp::create(builder, location, 1, 64);
  auto advanced = arith::AddIOp::create(builder, location, coordinate, one);
  branch(header, {advanced, increment->getArgument(0)});
  builder.setInsertionPointToEnd(finish);
  return accept(finish->getArgument(0), types);
}

void ScopedExecutionBuilder::release(ValueRange values) {
  make("runtime.release_bindings", {}, scoped(values));
}
void ScopedExecutionBuilder::reject(StringRef reason, StringRef site) {
  auto *stop = make("exec.reject", exec::StopType::get(builder.getContext()),
                    scope, {text("site", site), text("reason", reason)});
  branch(failed(), stop->getResults());
}
void ScopedExecutionBuilder::complete(ValueRange values) {
  auto *complete = make("exec.complete", result, scoped(values));
  make("func.return", {}, complete->getResults());
}
void ScopedExecutionBuilder::returned(ValueRange values) {
  auto *returned = make("exec.returned", result, values);
  make("func.return", {}, returned->getResults());
}
} // namespace zkc::protocol::detail
