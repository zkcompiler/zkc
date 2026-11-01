#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/InvocationParameters.h"
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

// Recover result types only after independent program admission. This is a
// construction aid, not another executable admission or correspondence check.
class ResultTypes {
  MLIRContext &context;
  bool physical;
  std::map<std::string, Types> bindings;
  std::map<std::string, std::pair<std::string, ArrayAttr>> bindingParameters;
  std::map<const program::Instruction *, ArrayAttr> parameters;
  std::map<const program::Instruction *, Types> results;
  bool valid = true;

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
  ResultTypes(MLIRContext &context, bool physical)
      : context(context), physical(physical) {}
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
      auto arguments = decodeBindingArguments(&context, binding.application);
      if (!arguments) {
        consumeError(arguments.takeError());
        return false;
      }
      bindingParameters.emplace(
          binding.name,
          std::make_pair(binding.application.contract, *arguments));
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
  ArrayAttr getParameters(const program::Instruction &instruction) const {
    return parameters.at(&instruction);
  }
  Types body(const program::Body &body, TypeEnvironment env,
             unsigned depth = 0) {
    if (!valid || depth >= 64) {
      valid = false;
      return {};
    }
    // Independent Program admission already bounded all instructions and
    // callable declarations. Outlined bodies are control, not new callables.
    for (const auto &instruction : body) {
      Types outputs;
      program::Names names;
      if (auto op = instruction.get<program::Operation>()) {
        const auto &binding = bindingParameters.at(op->callee);
        auto decoded = decodeInvocationParameters(
            binding.first, binding.second, op->attributes,
            physical ? ParameterStage::Physical : ParameterStage::Logical);
        if (!decoded) {
          consumeError(decoded.takeError());
          valid = false;
          return {};
        }
        parameters.emplace(&instruction, *decoded);
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
  exec::ScopedExecutionBuilder execution;
  Environment env;
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
  NamedAttribute text(StringRef name, StringRef value) {
    return builder.getNamedAttr(name, builder.getStringAttr(value));
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
  bool physical;
  OpBuilder builder;
  OwningOpRef<ModuleOp> module;
  unsigned next = 0;
  llvm::StringSet<> symbols;

public:
  ResultTypes types;
  Writer(MLIRContext &context, bool physical)
      : context(context), physical(physical), builder(&context),
        module(ModuleOp::create(builder.getUnknownLoc())),
        types(context, physical) {}
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
      builder.setInsertionPointToEnd(module->getBody());
      auto imported =
          importBinding(builder, builder.getUnknownLoc(), binding, physical);
      if (!imported)
        return imported.takeError();
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
    if (failed(zkc::admitStage(*module)))
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
      execution(builder, function) {
  bind(arguments, function.getArguments().drop_front());
  builder.setInsertionPointToEnd(&function.front());
}
void BodyWriter::conditional(const program::Instruction &instruction,
                             const program::Conditional &op) {
  const auto &types = writer.types.get(instruction);
  auto captured = values(op.captures);
  bind(op.outputs,
       execution.conditional(env.at(op.condition), captured, types,
                             instruction.site, [&](unsigned arm) {
                               return writer.region(
                                   arm ? op.elseBody : op.thenBody, op.captures,
                                   ValueRange(captured).getTypes(), types);
                             }));
}
void BodyWriter::match(const program::Instruction &instruction,
                       const program::Match &op) {
  const auto &types = writer.types.get(instruction);
  auto input = env.at(op.input);
  auto captured = values(op.captures);
  program::Names alternatives;
  for (const auto &arm : op.arms)
    alternatives.push_back(arm.alternative);
  bind(op.outputs,
       execution.match(input, captured, types, alternatives, instruction.site,
                       [&](unsigned index) {
                         const auto &arm = op.arms[index];
                         program::Names names = arm.payload;
                         append_range(names, op.captures);
                         auto payload = *data::variantPayloadTypes(
                             input.getType(), arm.alternative);
                         append_range(payload, ValueRange(captured).getTypes());
                         return writer.region(arm.body, names, payload, types);
                       }));
}
void BodyWriter::loop(const program::Instruction &instruction,
                      const program::For &op) {
  const auto &types = writer.types.get(instruction);
  Values seeds;
  Types inputs{env.at(op.lower).getType()};
  program::Names names{op.induction};
  for (const auto &[name, seed] : op.carried) {
    seeds.push_back(env.at(seed));
    inputs.push_back(env.at(seed).getType());
    names.push_back(name);
  }
  auto captured = values(op.captures);
  append_range(inputs, ValueRange(captured).getTypes());
  append_range(names, op.captures);
  Types yielded(types);
  if (op.conditional)
    yielded.insert(yielded.begin(), writer.types.boolean());
  bind(op.outputs,
       execution.loop(env.at(op.lower), env.at(op.upper), seeds, captured,
                      types, op.conditional, instruction.site, [&](unsigned) {
                        return writer.region(op.body, names, inputs, yielded);
                      }));
}
void BodyWriter::run(const program::Body &body) {
  for (const auto &instruction : body) {
    if (auto op = instruction.get<program::Operation>()) {
      bind(op->outputs,
           execution.invoke(
               "exec.apply", writer.types.get(instruction),
               execution.scoped(values(op->inputs)),
               {text("site", instruction.site),
                builder.getNamedAttr(
                    "binding",
                    FlatSymbolRefAttr::get(builder.getContext(), op->callee)),
                builder.getNamedAttr(
                    "parameters", writer.types.getParameters(instruction))}));
    } else if (auto op = instruction.get<program::BooleanConstant>()) {
      bind({op->output},
           execution.invoke("exec.boolean", writer.types.get(instruction),
                            execution.getScope(),
                            {text("site", instruction.site),
                             builder.getNamedAttr(
                                 "value", builder.getBoolAttr(op->value))}));
    } else if (auto op = instruction.get<program::VariantConstruct>()) {
      bind({op->output},
           execution.invoke("exec.variant", writer.types.get(instruction),
                            execution.scoped(values(op->payload)),
                            {text("site", instruction.site),
                             text("alternative", op->alternative)}));
    } else if (auto op = instruction.get<program::Conditional>()) {
      conditional(instruction, *op);
    } else if (auto op = instruction.get<program::Match>()) {
      match(instruction, *op);
    } else if (auto op = instruction.get<program::For>()) {
      loop(instruction, *op);
    } else if (auto op = instruction.get<program::Release>()) {
      execution.release(values(op->values));
    } else if (auto op = instruction.get<program::Stop>()) {
      execution.reject(op->reason, instruction.site);
    } else {
      auto names = instruction.get<program::Return>()
                       ? instruction.get<program::Return>()->values
                       : instruction.get<program::Yield>()->values;
      execution.complete(values(names));
    }
  }
}
} // namespace
Expected<OwningOpRef<ModuleOp>>
writeLocalExecution(MLIRContext &context,
                    const program::LocalDefinitions &definitions,
                    bool physical) {
  if (auto e = admitExecutionDefinitions(definitions, physical))
    return std::move(e);
  context.loadDialect<func::FuncDialect, arith::ArithDialect,
                      cf::ControlFlowDialect, exec::ExecDialect,
                      runtime::RuntimeDialect>();
  return Writer(context, physical).run(definitions);
}
} // namespace zkc::protocol
