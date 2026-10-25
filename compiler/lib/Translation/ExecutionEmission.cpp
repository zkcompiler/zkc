#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Runtime/Execution.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Program/Admission.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Translation/Execution.h"
#include "llvm/ADT/StringSet.h"
#include <map>

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using Types = SmallVector<Type>;
using Values = SmallVector<Value>;
using TypeEnvironment = std::map<std::string, Type>;
using Environment = std::map<std::string, Value>;
ArrayAttr strings(Builder &builder, ArrayRef<std::string> values) {
  SmallVector<Attribute> result;
  for (const auto &value : values)
    result.push_back(builder.getStringAttr(value));
  return builder.getArrayAttr(result);
}

// Recover result types only after independent program admission. This is a
// construction aid, not another executable admission or correspondence check.
class ResultTypes {
  MLIRContext &context;
  bool physical;
  std::map<std::string, Types> bindings;
  std::map<const program::Instruction *, Types> results;
  bool valid = true;
  unsigned definitions;

  Type decode(const BoundType &bound) {
    auto type = decodeBoundType(&context, bound);
    valid &= bool(type);
    return type;
  }
  static Types select(ArrayRef<std::string> names, const TypeEnvironment &env) {
    Types types;
    for (const auto &name : names)
      types.push_back(env.at(name));
    return types;
  }
  static TypeEnvironment captures(ArrayRef<std::string> names,
                                  const TypeEnvironment &env) {
    TypeEnvironment inner;
    for (const auto &name : names)
      inner.emplace(name, env.at(name));
    return inner;
  }

public:
  ResultTypes(MLIRContext &context, bool physical, unsigned definitions)
      : context(context), physical(physical), definitions(definitions) {}
  Type type(StringRef spelling) {
    auto bound = parseBoundType(spelling, physical);
    if (!bound) {
      consumeError(bound.takeError());
      valid = false;
      return {};
    }
    return decode(*bound);
  }
  Type boolean() { return type(physical ? "bool@native.bool/0" : "bool"); }
  Types types(ArrayRef<std::string> spellings) {
    Types result;
    for (const auto &spelling : spellings)
      result.push_back(type(spelling));
    return result;
  }
  bool prepare(const program::LocalDefinitions &model) {
    for (const auto &binding : model.bindings) {
      auto signature = resolveBinding(binding.application, physical);
      if (!signature) {
        consumeError(signature.takeError());
        return false;
      }
      for (const auto &output : signature->outputs)
        bindings[binding.name].push_back(decode(output));
      bindings.try_emplace(binding.name);
    }
    for (const auto &function : model.functions) {
      TypeEnvironment env;
      for (const auto &argument : function.arguments)
        env.emplace(argument.name, type(argument.type));
      types(function.results);
      body(function.body, std::move(env));
    }
    return valid;
  }
  const Types &get(const program::Instruction &instruction) const {
    return results.at(&instruction);
  }
  Types body(const program::Body &body, TypeEnvironment env,
             unsigned depth = 0) {
    if (!valid || depth >= 64 || ++definitions > 4096) {
      valid = false;
      return {};
    }
    for (const auto &instruction : body) {
      Types outputs;
      program::Names names;
      if (auto op = instruction.get<program::Operation>()) {
        outputs = bindings.at(op->callee);
        names = op->outputs;
      } else if (auto op = instruction.get<program::BooleanConstant>()) {
        outputs = {boolean()};
        names = {op->output};
      } else if (auto op = instruction.get<program::VariantConstruct>()) {
        outputs = {type(op->type)};
        names = {op->output};
      } else if (auto op = instruction.get<program::Conditional>()) {
        auto inner = captures(op->captures, env);
        auto left = this->body(op->thenBody, inner, depth + 1);
        auto right = this->body(op->elseBody, std::move(inner), depth + 1);
        outputs = op->thenBody.back().get<program::Yield>() ? left : right;
        names = op->outputs;
      } else if (auto op = instruction.get<program::Match>()) {
        for (const auto &arm : op->arms) {
          auto payload =
              data::variantPayloadTypes(env.at(op->input), arm.alternative);
          if (!payload) {
            consumeError(payload.takeError());
            valid = false;
            return {};
          }
          auto inner = captures(op->captures, env);
          for (auto [name, type] : zip(arm.payload, *payload))
            inner.emplace(name, type);
          auto returned = this->body(arm.body, std::move(inner), depth + 1);
          if (arm.body.back().get<program::Yield>())
            outputs = std::move(returned);
        }
        names = op->outputs;
      } else if (auto op = instruction.get<program::For>()) {
        auto inner = captures(op->captures, env);
        inner.emplace(op->induction, env.at(op->lower));
        for (const auto &[name, seed] : op->carried) {
          auto type = env.at(seed);
          outputs.push_back(type);
          inner.emplace(name, type);
        }
        this->body(op->body, std::move(inner), depth + 1);
        names = op->outputs;
      } else if (auto op = instruction.get<program::Return>()) {
        return select(op->values, env);
      } else if (auto op = instruction.get<program::Yield>()) {
        return select(op->values, env);
      } else if (instruction.get<program::Stop>()) {
        return {};
      } else if (!instruction.get<program::Release>()) {
        valid = false;
        return {};
      }
      results.emplace(&instruction, outputs);
      for (auto [name, type] : zip(names, outputs))
        env.emplace(name, type);
      if (!valid)
        return {};
    }
    return {};
  }
};
class Writer;
class BodyWriter {
  Writer &writer;
  OpBuilder builder;
  Location location;
  func::FuncOp function;
  Value scope;
  exec::OutcomeType result;
  Block *failure = nullptr;
  Environment env;
  Operation *make(StringRef name, TypeRange types, ValueRange operands,
                  ArrayRef<NamedAttribute> attributes = {},
                  ArrayRef<Block *> successors = {}) {
    OperationState state(location, name);
    state.addTypes(types);
    state.addOperands(operands);
    state.addAttributes(attributes);
    state.addSuccessors(successors);
    return builder.create(state);
  }
  NamedAttribute text(StringRef name, StringRef value) {
    return builder.getNamedAttr(name, builder.getStringAttr(value));
  }
  Block *block(TypeRange types = {}) {
    auto *block = new Block;
    function.getBody().push_back(block);
    for (auto type : types)
      block->addArgument(type, location);
    return block;
  }
  Block *failed() {
    if (!failure) {
      OpBuilder::InsertionGuard guard(builder);
      failure = block(exec::StopType::get(builder.getContext()));
      builder.setInsertionPointToEnd(failure);
      auto *stopped = make("exec.failed", result, failure->getArguments());
      make("func.return", {}, stopped->getResults());
    }
    return failure;
  }
  void branch(Block *target, ValueRange values = {}) {
    cf::BranchOp::create(builder, location, target, values);
  }
  Values values(ArrayRef<std::string> names) {
    Values values;
    for (const auto &name : names)
      values.push_back(env.at(name));
    return values;
  }
  void bind(ArrayRef<std::string> names, ValueRange values) {
    for (auto [name, value] : zip(names, values))
      env.emplace(name, value);
  }
  exec::OutcomeType outcome(TypeRange payload) {
    return exec::OutcomeType::get(builder.getContext(), Types(payload));
  }
  runtime::TransferType transfer(TypeRange payload) {
    return runtime::TransferType::get(builder.getContext(), Types(payload));
  }
  Values dispatch(Value result, Block *stop = nullptr) {
    auto *next = block(cast<exec::OutcomeType>(result.getType()).getPayload());
    make("exec.dispatch", {}, result, {}, {next, stop ? stop : failed()});
    builder.setInsertionPointToEnd(next);
    return Values(next->getArguments());
  }
  Values invoke(StringRef name, TypeRange outputs, ValueRange inputs,
                ArrayRef<NamedAttribute> attributes = {},
                Block *stop = nullptr) {
    auto *operation = make(name, outcome(outputs), inputs, attributes);
    return dispatch(operation->getResult(0), stop);
  }
  Values scoped(ValueRange inputs) {
    Values result{scope};
    append_range(result, inputs);
    return result;
  }
  Value region(const program::Body &body, ArrayRef<std::string> names,
               ValueRange inputs, TypeRange outputs, StringRef kind,
               StringRef site, StringRef selection = {}, Value coordinate = {},
               Block *stop = nullptr);
  Values accept(Value held, TypeRange types) {
    return invoke("runtime.accept_transfer", types, {scope, held});
  }
  void conditional(const program::Instruction &, const program::Conditional &);
  void match(const program::Instruction &, const program::Match &);
  void loop(const program::Instruction &, const program::For &);

public:
  BodyWriter(Writer &writer, func::FuncOp function,
             ArrayRef<std::string> arguments);
  void run(const program::Body &);
};
class Writer {
  MLIRContext &context;
  OpBuilder builder;
  OwningOpRef<ModuleOp> module;
  unsigned next = 0;
  llvm::StringSet<> symbols;

public:
  ResultTypes types;
  Writer(MLIRContext &context, bool physical, unsigned bindings)
      : context(context), builder(&context),
        module(ModuleOp::create(builder.getUnknownLoc())),
        types(context, physical, bindings) {}
  func::FuncOp function(StringRef name, TypeRange inputs, TypeRange outputs) {
    builder.setInsertionPointToEnd(module->getBody());
    Types arguments{runtime::ScopeType::get(&context)};
    append_range(arguments, inputs);
    auto result = exec::OutcomeType::get(&context, Types(outputs));
    auto function =
        func::FuncOp::create(builder, builder.getUnknownLoc(), name,
                             builder.getFunctionType(arguments, {result}));
    function->setAttr("no_inline", builder.getUnitAttr());
    function.addEntryBlock();
    return function;
  }
  func::FuncOp region(const program::Body &body,
                      ArrayRef<std::string> arguments, TypeRange inputs,
                      TypeRange outputs) {
    std::string name;
    do {
      name = "execution_region_" + std::to_string(next++);
    } while (!symbols.insert(name).second);
    auto helper = function(name, inputs, outputs);
    helper.setPrivate();
    helper->setAttr("runtime.region", builder.getUnitAttr());
    BodyWriter(*this, helper, arguments).run(body);
    return helper;
  }
  Expected<OwningOpRef<ModuleOp>> run(const program::LocalDefinitions &model) {
    if (!types.prepare(model))
      return error("execution-emission",
                   "unavailable value type dialect or execution profile limit");
    for (const auto &binding : model.bindings)
      symbols.insert(binding.name);
    for (const auto &function : model.functions)
      symbols.insert(function.name);
    for (const auto &binding : model.bindings) {
      const auto &app = binding.application;
      builder.setInsertionPointToEnd(module->getBody());
      OperationState state(builder.getUnknownLoc(), "local.binding");
      state.addAttribute("sym_name", builder.getStringAttr(binding.name));
      state.addAttribute("contract", builder.getStringAttr(app.contract));
      state.addAttribute("arguments", strings(builder, app.arguments));
      state.addAttribute("implementation",
                         builder.getStringAttr(app.implementation));
      if (!app.physicalArguments.empty())
        state.addAttribute("physical_arguments",
                           strings(builder, app.physicalArguments));
      builder.create(state);
    }
    for (const auto &record : model.functions) {
      program::Names names;
      Types inputs;
      for (const auto &argument : record.arguments) {
        names.push_back(argument.name);
        inputs.push_back(types.type(argument.type));
      }
      auto root = function(record.name, inputs, types.types(record.results));
      SmallVector<Attribute> arguments;
      for (const auto &[name, value] : record.origin->arguments)
        arguments.push_back(builder.getStrArrayAttr({name, value}));
      root->setAttr("runtime.origin",
                    builder.getArrayAttr(
                        {builder.getStringAttr(record.origin->definition),
                         builder.getArrayAttr(arguments)}));
      BodyWriter(*this, root, names).run(record.body);
    }
    if (failed(verify(*module)))
      return error("execution-emission", "invalid generated CFG");
    for (auto function : module->getOps<func::FuncOp>())
      if (failed(runtime::verifyScopeOwnership(function)))
        return error("execution-emission", "invalid generated scope ownership");
    return std::move(module);
  }
};
BodyWriter::BodyWriter(Writer &writer, func::FuncOp function,
                       ArrayRef<std::string> arguments)
    : writer(writer), builder(function.getContext()),
      location(function.getLoc()), function(function),
      scope(function.getArgument(0)),
      result(cast<exec::OutcomeType>(function.getResultTypes().front())) {
  bind(arguments, function.getArguments().drop_front());
  builder.setInsertionPointToEnd(&function.front());
}
Value BodyWriter::region(const program::Body &body, ArrayRef<std::string> names,
                         ValueRange inputs, TypeRange outputs, StringRef kind,
                         StringRef site, StringRef selection, Value coordinate,
                         Block *stop) {
  auto helper = writer.region(body, names, inputs.getTypes(), outputs);
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
void BodyWriter::conditional(const program::Instruction &instruction,
                             const program::Conditional &op) {
  const auto &types = writer.types.get(instruction);
  auto condition =
      invoke("exec.test", builder.getI1Type(), {scope, env.at(op.condition)},
             {text("site", instruction.site)})
          .front();
  auto *yes = block(), *no = block(), *join = block(types);
  cf::CondBranchOp::create(builder, location, condition, yes, ValueRange{}, no,
                           ValueRange{});
  auto captured = values(op.captures);
  for (unsigned i = 0; i < 2; ++i) {
    builder.setInsertionPointToEnd(i ? no : yes);
    auto held =
        region(i ? op.elseBody : op.thenBody, op.captures, captured, types,
               "conditional", instruction.site, i ? "else" : "then");
    branch(join, accept(held, types));
  }
  builder.setInsertionPointToEnd(join);
  bind(op.outputs, join->getArguments());
}
void BodyWriter::match(const program::Instruction &instruction,
                       const program::Match &op) {
  const auto &types = writer.types.get(instruction);
  auto input = env.at(op.input);
  auto captured = values(op.captures);
  auto *join = block(types);
  SmallVector<Block *> arms{failed()};
  program::Names alternatives;
  for (const auto &arm : op.arms) {
    auto payload = *data::variantPayloadTypes(input.getType(), arm.alternative);
    append_range(payload, ValueRange(captured).getTypes());
    arms.push_back(block(payload));
    alternatives.push_back(arm.alternative);
  }
  Values inputs{scope, input};
  append_range(inputs, captured);
  make("exec.match", {}, inputs,
       {text("site", instruction.site),
        builder.getNamedAttr("alternatives", strings(builder, alternatives))},
       arms);
  for (auto [i, arm] : enumerate(op.arms)) {
    builder.setInsertionPointToEnd(arms[i + 1]);
    program::Names names = arm.payload;
    append_range(names, op.captures);
    auto held = region(arm.body, names, arms[i + 1]->getArguments(), types,
                       "match", instruction.site, arm.alternative);
    branch(join, accept(held, types));
  }
  builder.setInsertionPointToEnd(join);
  bind(op.outputs, join->getArguments());
}
void BodyWriter::loop(const program::Instruction &instruction,
                      const program::For &op) {
  const auto &types = writer.types.get(instruction);
  auto carry = transfer(types);
  auto counters =
      invoke("exec.range", {builder.getI64Type(), builder.getI64Type()},
             {scope, env.at(op.lower), env.at(op.upper)},
             {text("site", instruction.site)});
  Values seeds;
  for (const auto &[name, seed] : op.carried)
    seeds.push_back(env.at(seed));
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
  auto index =
      invoke("runtime.iteration", env.at(op.lower).getType(),
             {scope, coordinate}, {text("site", instruction.site)}, cleanup)
          .front();
  auto *peek = make("runtime.transfer_values", types, previous);
  Values inputs{index};
  append_range(inputs, peek->getResults());
  append_range(inputs, values(op.captures));
  program::Names names{op.induction};
  for (const auto &[name, seed] : op.carried)
    names.push_back(name);
  append_range(names, op.captures);
  Types yielded(types);
  if (op.conditional)
    yielded.insert(yielded.begin(), writer.types.boolean());
  auto held = region(op.body, names, inputs, yielded, "iteration",
                     instruction.site, {}, coordinate, cleanup);
  make("runtime.release_transfer", {}, previous);
  if (op.conditional) {
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
  bind(op.outputs, accept(finish->getArgument(0), types));
}
void BodyWriter::run(const program::Body &body) {
  for (const auto &instruction : body) {
    if (auto op = instruction.get<program::Operation>()) {
      bind(op->outputs,
           invoke("exec.apply", writer.types.get(instruction),
                  scoped(values(op->inputs)),
                  {text("site", instruction.site),
                   builder.getNamedAttr(
                       "binding", FlatSymbolRefAttr::get(builder.getContext(),
                                                         op->callee)),
                   builder.getNamedAttr("parameters",
                                        strings(builder, op->attributes))}));
    } else if (auto op = instruction.get<program::BooleanConstant>()) {
      bind({op->output},
           invoke("exec.boolean", writer.types.get(instruction), scope,
                  {text("site", instruction.site),
                   builder.getNamedAttr("value",
                                        builder.getBoolAttr(op->value))}));
    } else if (auto op = instruction.get<program::VariantConstruct>()) {
      bind({op->output}, invoke("exec.variant", writer.types.get(instruction),
                                scoped(values(op->payload)),
                                {text("site", instruction.site),
                                 text("alternative", op->alternative)}));
    } else if (auto op = instruction.get<program::Conditional>()) {
      conditional(instruction, *op);
    } else if (auto op = instruction.get<program::Match>()) {
      match(instruction, *op);
    } else if (auto op = instruction.get<program::For>()) {
      loop(instruction, *op);
    } else if (auto op = instruction.get<program::Release>()) {
      make("runtime.release_bindings", {}, scoped(values(op->values)));
    } else if (auto op = instruction.get<program::Stop>()) {
      auto *stop =
          make("exec.reject", exec::StopType::get(builder.getContext()), scope,
               {text("site", instruction.site), text("reason", op->reason)});
      branch(failed(), stop->getResults());
    } else {
      auto names = instruction.get<program::Return>()
                       ? instruction.get<program::Return>()->values
                       : instruction.get<program::Yield>()->values;
      auto *complete = make("exec.complete", result, scoped(values(names)));
      make("func.return", {}, complete->getResults());
    }
  }
}
} // namespace
Expected<OwningOpRef<ModuleOp>>
writeLocalExecution(MLIRContext &context,
                    const program::LocalDefinitions &definitions,
                    bool physical) {
  program::Participants model;
  model.stage = physical ? program::Participants::Stage::Physical
                         : program::Participants::Stage::Logical;
  model.bindings = definitions.bindings;
  model.functions = definitions.functions;
  if (auto e = admit(model))
    return std::move(e);
  context.loadDialect<func::FuncDialect, arith::ArithDialect,
                      cf::ControlFlowDialect, exec::ExecDialect,
                      runtime::RuntimeDialect, local::LocalDialect>();
  return Writer(context, physical, definitions.bindings.size())
      .run(definitions);
}
} // namespace zkc::protocol
