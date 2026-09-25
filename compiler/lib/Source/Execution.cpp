#include "zkc/Source/Execution.h"
#include "zkc/Compiler/Instantiation.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Protocol/Bindings.h"
#include "zkc/Protocol/Contracts.h"
#include "zkc/Protocol/Kernels.h"
#include "zkc/Source/Codec.h"
#include "zkc/Target/Json.h"

using namespace llvm;
namespace zkc::source {
namespace {
using Env = std::map<std::string, std::string>;
class Expansion {
  const source::Module &module;
  Execution result;
  std::map<std::string, const source::Function *> functions;
  std::map<std::string, const source::Protocol *> protocols;
  std::map<std::string, const source::Instance *> instances;
  std::map<std::string, protocol::BoundOperation> bindings;
  std::map<std::string, std::string> contracts;
  std::string problem;
  static constexpr size_t maxTrace = 200000;
  size_t work = 0;
  static std::string participant(const source::Instance &instance,
                                 StringRef role) {
    for (const auto &[formal, actual] : instance.roles)
      if (formal == role)
        return actual;
    llvm_unreachable("source admission established participant assignment");
  }
  void record(StringRef path, ExecutionOperation operation) {
    operation.ordinal = result.order.size();
    result.order.push_back(path.str());
    result.operations.emplace(path.str(), std::move(operation));
  }
  bool budget(size_t amount = 1) {
    if (amount > maxTrace || work > maxTrace - amount) {
      problem = "execution-expansion-limit";
      return false;
    }
    work += amount;
    return problem.empty();
  }
  std::string value(StringRef type, StringRef path, StringRef name,
                    StringRef owner) {
    if (!budget())
      return {};
    std::string id = "v" + std::to_string(result.values.size());
    result.values.emplace(
        id, ExecutionValue{type.str(), path.str(), name.str(), owner.str()});
    return id;
  }
  source::Names get(const source::Names &names, const Env &env) {
    source::Names values;
    if (!budget(names.size()))
      return values;
    for (const auto &name : names)
      values.push_back(env.at(name)); // Source admission established scope.
    return values;
  }
  void bind(const source::Names &names, const source::Names &values, Env &env) {
    if (!problem.empty())
      return;
    if (names.size() != values.size()) {
      problem = "execution-unsupported-scope";
      return;
    }
    for (size_t i = 0; i < names.size(); ++i)
      env.emplace(names[i], values[i]);
  }
  source::Names body(const source::Body &body, Env env,
                     const source::Instance &instance, StringRef role,
                     StringRef path, unsigned depth) {
    if (depth > 64) {
      problem = "execution-expansion-limit";
      return {};
    }
    for (size_t i = 0; i < body.size(); ++i) {
      if (!budget())
        return {};
      const auto &ins = body[i];
      std::string at = (path + "/" + Twine(i)).str();
      if (const auto *op = ins.get<source::Operation>()) {
        auto inputs = get(op->inputs, env);
        if (!problem.empty())
          return {};
        source::Names types, outputs;
        std::string key = op->callee;
        const auto &binding = bindings.at(key);
        key = contracts.at(key);
        for (const auto &type : binding.outputs)
          types.push_back(type.spelling());
        for (size_t n = 0; n < types.size(); ++n)
          outputs.push_back(value(types[n], at, op->outputs[n], role));
        record(at, ExecutionOperation{
                       key, inputs, outputs, role.str(), {}, op->attributes});
        if (protocol::isAcceptanceGuard(key))
          result.guards.emplace(at, ExecutionGuard{inputs.at(0), role.str()});
        bind(op->outputs, outputs, env);
      } else if (const auto *call = ins.get<source::AlgorithmCall>()) {
        auto inputs = get(call->inputs, env);
        if (!problem.empty())
          return {};
        const auto &fn = *functions.at(call->callee);
        Env local;
        for (size_t n = 0; n < inputs.size(); ++n)
          local.emplace(fn.arguments[n].name, inputs[n]);
        auto outputs = this->body(*fn.body, std::move(local), instance, role,
                                  at, depth + 1);
        result.invocations.emplace(
            at,
            ExecutionInvocation{call->callee, instance.name, inputs, outputs});
        bind(call->outputs, outputs, env);
      } else if (const auto *call = ins.get<source::LocalCall>()) {
        auto inputs = get(call->inputs, env);
        if (!problem.empty())
          return {};
        const auto &fn = *functions.at(call->callee);
        Env local;
        for (size_t n = 0; n < inputs.size(); ++n)
          local.emplace(fn.arguments[n].name, inputs[n]);
        std::string owner = role.str();
        for (const auto &[formal, actual] : instance.roles)
          if (formal == call->role)
            owner = actual;
        auto outputs = this->body(*fn.body, std::move(local), instance, owner,
                                  at, depth + 1);
        result.invocations.emplace(
            at,
            ExecutionInvocation{call->callee, instance.name, inputs, outputs});
        bind(call->outputs, outputs, env);
      } else if (const auto *call = ins.get<source::ProtocolCall>()) {
        auto inputs = get(call->inputs, env);
        if (!problem.empty())
          return {};
        std::string child;
        for (const auto &[alias, target] : instance.dependencies)
          if (alias == call->callee)
            child = target;
        auto outputs = invoke(*instances.at(child), inputs, at, depth + 1);
        bind(call->outputs, outputs, env);
      } else if (const auto *message = ins.get<source::Message>()) {
        // A received value has its own identity: no honest-prover equality is
        // assumed in a validator contract, even for the same wire schema.
        const auto &input = env.at(message->input);
        const auto sender = participant(instance, message->sender);
        const auto receiver = participant(instance, message->receiver);
        auto output =
            value(result.values.at(input).type, at, message->output, receiver);
        env.emplace(message->output, output);
        record(at, ExecutionOperation{"message",
                                      {input},
                                      {output},
                                      sender,
                                      receiver,
                                      {message->schema}});
      } else if (ins.get<source::Conditional>() || ins.get<source::For>() ||
                 ins.get<source::Match>() ||
                 ins.get<source::VariantConstruct>()) {
        problem = "execution-local-control-static-trace";
        return {};
      } else if (const auto *loop = ins.get<source::Loop>()) {
        std::string count = loop->count.value;
        if (loop->count.kind == source::LoopCount::Kind::Parameter)
          for (const auto &[name, selected] : instance.parameters)
            if (name == count) {
              const auto *constant = std::get_if<std::string>(&selected);
              if (!constant) {
                problem = "source-execution-family-input-required";
                return {};
              }
              count = *constant;
              break;
            }
        uint64_t trips = 0;
        if (StringRef(count).getAsInteger(10, trips) || !budget(trips)) {
          problem = "execution-expansion-limit";
          return {};
        }
        result.loops.emplace(at, trips);
        source::Names carried;
        for (const auto &[name, initial] : loop->carried)
          carried.push_back(env.at(initial));
        for (uint64_t iteration = 0; iteration < trips; ++iteration) {
          if (!budget(loop->carried.size() + loop->captures.size()))
            return {};
          Env inner;
          for (size_t n = 0; n < carried.size(); ++n)
            inner.emplace(loop->carried[n].first, carried[n]);
          for (const auto &name : loop->captures)
            inner.emplace(name, env.at(name));
          carried =
              this->body(loop->body, std::move(inner), instance, role,
                         at + "/i" + std::to_string(iteration), depth + 1);
          if (!problem.empty())
            return {};
        }
        bind(loop->outputs, carried, env);
      } else if (const auto *ret = ins.get<source::Return>()) {
        return get(ret->values, env);
      } else if (const auto *yield = ins.get<source::Yield>()) {
        return get(yield->values, env);
      } else {
        problem = "execution-unsupported-scope";
        return {};
      }
      if (!problem.empty())
        return {};
    }
    problem = "execution-unsupported-scope";
    return {};
  }
  source::Names invoke(const source::Instance &instance,
                       const source::Names &inputs, StringRef path,
                       unsigned depth) {
    // Even an unused count runs its selector at entry. Static provenance must
    // not silently omit that execution or infer a count without actual inputs.
    for (const auto &[name, binding] : instance.parameters)
      if (std::holds_alternative<source::FamilyIngress>(binding)) {
        problem = "source-execution-family-input-required";
        return {};
      }
    const auto &def = *protocols.at(instance.protocol);
    Env env;
    for (size_t n = 0; n < inputs.size(); ++n)
      env.emplace(def.arguments[n].name, inputs[n]);
    auto outputs = body(*def.body, std::move(env), instance, "", path, depth);
    result.invocations.emplace(
        path.str(),
        ExecutionInvocation{def.name, instance.name, inputs, outputs});
    return outputs;
  }

public:
  explicit Expansion(const source::Module &module) : module(module) {}
  Expected<Execution> run(StringRef entry) {
    for (const auto &fn : module.functions)
      functions.emplace(fn.name, &fn);
    for (const auto &def : module.protocols)
      protocols.emplace(def.name, &def);
    for (const auto &instance : module.instances)
      instances.emplace(instance.name, &instance);
    for (const auto &binding : module.bindings) {
      auto resolved = protocol::resolveBinding(binding, false);
      if (!resolved)
        return resolved.takeError();
      bindings.emplace(binding.name, std::move(*resolved));
      contracts.emplace(binding.name, binding.contract);
    }
    const source::Instance *root = nullptr;
    for (const auto &e : module.entries)
      if (e.name == entry)
        root = instances.at(e.instance);
    if (!root)
      return error("execution-entry");
    source::Names inputs;
    for (const auto &arg : protocols.at(root->protocol)->arguments)
      inputs.push_back(
          value(arg.type, "$", arg.name, participant(*root, arg.role)));
    for (const auto &[formal, actual] : root->roles) {
      (void)formal;
      result.roles.push_back(actual);
    }
    result.results = invoke(*root, inputs, "$", 0);
    if (!problem.empty())
      return error(problem);
    return std::move(result);
  }
};
} // namespace
Expected<Execution> inspectExecution(const source::Module &original,
                                     StringRef entry) {
  if (auto e = source::checkStructure(original))
    return e;
  auto prepared = original.isLibrary() ? generic::prepareLibrary(original)
                                       : Expected<source::Module>(original);
  if (!prepared)
    return prepared.takeError();
  if (auto e = protocol::admit(*prepared, true))
    return e;
  auto result = Expansion(*prepared).run(entry);
  if (!result)
    return result.takeError();
  return result;
}
} // namespace zkc::source
