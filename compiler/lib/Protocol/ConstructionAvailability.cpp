#include "ConstructionState.h"

using namespace llvm;
namespace zkc::protocol::construction {
bool Construction::account(const ValueDependencies &dep) {
  size_t cost = 1 + dep.values.size() + dep.draws.size();
  // TokenSet charges its actual bitmap copies, unions and enumeration. The
  // remaining facts have small port-index / diagnostic-string domains.
  for (const auto &blocker : dep.blockers)
    cost += 1 + blocker.size() / 16;
  for (const auto &[sampler, origins] : dep.unconvertedSamplers)
    cost += 1 + sampler.size() / 16 + origins.size();
  return budget(cost);
}

void Construction::mark(ValueInfo &v, const std::string &id,
                        const std::string &path, const std::string &name) {
  v.dep.tokens.attach(dependencyTokens);
  v.dep.tokens.insert(token(id, path, name));
  account(v.dep);
}

std::vector<ValueInfo> Construction::operands(const source::Names &v,
                                              const Env &env) {
  std::vector<ValueInfo> out;
  for (const auto &n : v)
    out.push_back(env.at(n));
  return out;
}

ValueDependencies Construction::join(const std::vector<ValueInfo> &vs) {
  ValueDependencies d;
  for (const auto &v : vs) {
    if (!account(v.dep))
      break;
    d.join(v.dep);
  }
  return d;
}

DependencySummary Construction::local(const std::string &id,
                                      const std::string &path,
                                      const source::Instruction &ins,
                                      const Env &outer) {
  const auto &call = *ins.get<source::LocalCall>();
  const auto &fn = *functions.at(call.callee);
  Env env;
  auto args = operands(call.inputs, outer);
  const auto &ports = fn.arguments;
  const std::string role = instances.at(id).roles.at(call.role);
  for (size_t i = 0; i < ports.size(); ++i)
    env[ports[i].name] = args[i];
  DependencySummary result;
  if (hasLocalControl(fn)) {
    auto dependencies = join(args);
    if (role == producer)
      result.roots.join(dependencies);
    else
      dependencies.blockers.insert("construction-local-control-replay");
    const auto &returned = fn.body->back().get<source::Return>()->values;
    for (size_t k = 0; k < fn.results.size(); ++k) {
      ValueInfo output{role, fn.results[k], dependencies};
      mark(output, id, path, returned[k]);
      result.outputs.push_back(std::move(output));
    }
    return result;
  }
  for (const auto &v : *fn.body) {
    if (!budget())
      return result;
    if (const auto *ret = v.get<source::Return>()) {
      result.outputs = operands(ret->values, env);
      return result;
    }
    if (!v.get<source::Operation>()) {
      fail("construction-local-control-static-trace");
      return result;
    }
    const auto &op = *v.get<source::Operation>();
    auto args = operands(op.inputs, env);
    ValueDependencies d = join(args);
    std::string key = op.callee;
    std::string operation = contract(key);
    const auto *sample = samplingContract(operation);
    if (sample && sample->provider == RandomnessProvider::Entropy &&
        sample->derivedCounterpart.empty()) {
      const auto &origins = args[sample->stateInput].dep.values;
      result.roots.unconvertedSamplers[operation].insert(origins.begin(),
                                                         origins.end());
    }
    ValueDependencies value = d;
    if (role == producer)
      result.roots.join(d);
    else if (randomDraw(operation)) {
      // Only the RNG operand denotes randomness authority. A query bound is
      // ordinary data that must have an available public replay at the draw.
      value = args[sample->stateInput].dep.challenge();
      for (size_t k = 0; k < args.size(); ++k)
        if (k != sample->stateInput)
          value.join(args[k].dep);
      if (!draws.count({fn.name, v.site}))
        value.blockers.insert("construction-unselected-draw");
      value.tokens.insert(token(id, path, "op/" + v.site));
      result.roots.join(
          value); // Selected draws are effects, including dead ones.
    } else if (!recipe(operation))
      value.blockers.insert("construction-unavailable-recipe:" + operation);
    const auto *selected = signature(key);
    if (!selected) {
      return result;
    }
    for (size_t k = 0; k < op.outputs.size(); ++k) {
      ValueInfo out{role, selected->outputs[k],
                    sample && k == sample->stateOutput
                        ? args[sample->stateInput].dep
                        : value};
      mark(out, id, path, op.outputs[k]);
      env[op.outputs[k]] = std::move(out);
    }
  }
  fail("construction-local-body");
  return result;
}

DependencySummary Construction::block(const std::string &id,
                                      const std::string &path,
                                      const source::Body &body, Env env) {
  DependencySummary total;
  auto &inst = instances.at(id);
  for (const auto &v : body) {
    if (!budget() || !problem.empty())
      return total;
    if (v.get<source::Return>() || v.get<source::Yield>()) {
      const auto &values = v.get<source::Return>()
                               ? v.get<source::Return>()->values
                               : v.get<source::Yield>()->values;
      total.outputs = operands(values, env);
      return total;
    }
    if (const auto *call = v.get<source::LocalCall>()) {
      auto r = local(id, path + "/" + v.site, v, env);
      if (!problem.empty())
        return total;
      total.roots.join(r.roots);
      for (size_t k = 0; k < r.outputs.size(); ++k) {
        auto out = r.outputs[k];
        mark(out, id, path, call->outputs[k]);
        env[call->outputs[k]] = std::move(out);
      }
    } else if (const auto *message = v.get<source::Message>()) {
      auto value = env.at(message->input);
      total.roots.join(value.dep);
      value.role = inst.roles.at(message->receiver);
      mark(value, id, path, message->output);
      env[message->output] = std::move(value);
    } else if (const auto *call = v.get<source::ProtocolCall>()) {
      std::string child = inst.dependencies.at(call->callee);
      analyze(child);
      if (!problem.empty())
        return total;
      auto args = operands(call->inputs, env);
      std::vector<ValueDependencies> deps;
      for (auto &arg : args)
        deps.push_back(arg.dep);
      const auto &r = instances.at(child).summary;
      total.roots.join(r.roots.substitute(deps));
      for (size_t k = 0; k < r.outputs.size(); ++k) {
        ValueInfo out = r.outputs[k];
        out.dep = out.dep.substitute(deps);
        mark(out, id, path, call->outputs[k]);
        env[call->outputs[k]] = std::move(out);
      }
    } else if (const auto *loop = v.get<source::Loop>()) {
      std::vector<ValueInfo> initial;
      for (auto &p : loop->carried)
        initial.push_back(env.at(p.second));
      auto values = initial;
      uint64_t n = count(*loop, inst);
      if (n) {
        for (;;) {
          Env inner;
          for (size_t k = 0; k < values.size(); ++k) {
            auto value = values[k];
            std::string name = loop->carried[k].first;
            mark(value, id, path + "/" + v.site, name);
            inner[name] = std::move(value);
          }
          for (auto &capture : loop->captures)
            inner[capture] = env.at(capture);
          auto r = block(id, path + "/" + v.site, loop->body, inner);
          if (!problem.empty())
            return total;
          total.roots.join(r.roots);
          if (n == 1) {
            values = std::move(r.outputs);
            break;
          }
          bool stable = true;
          // Inflationary closure. A permutation can cycle under T alone.
          // This explicitly includes the initial state and every successor.
          for (size_t k = 0; k < values.size(); ++k) {
            ValueDependencies joined = values[k].dep;
            joined.join(r.outputs[k].dep);
            stable &= joined == values[k].dep;
            values[k].dep = std::move(joined);
          }
          if (stable)
            break;
        }
      }
      for (size_t k = 0; k < values.size(); ++k) {
        mark(values[k], id, path, loop->outputs[k]);
        env[loop->outputs[k]] = values[k];
      }
    } else {
      fail("construction-incomplete-control");
      return total;
    }
  }
  fail("construction-body");
  return total;
}

void Construction::analyze(const std::string &id) {
  auto &i = instances.at(id);
  if (i.analyzed || !problem.empty())
    return;
  i.analyzed = true; // Original admission has already ruled out recursion.
  {
    std::set<std::string> actual;
    for (auto &r : i.roles)
      actual.insert(r.second);
    if (actual != std::set<std::string>{producer, validator}) {
      fail("construction-role-scope");
      return;
    }
  }
  Env env;
  const auto &ports = i.def->arguments;
  for (size_t k = 0; k < ports.size(); ++k) {
    const auto &p = ports[k];
    ValueInfo value{i.roles.at(p.role), p.type, {}};
    value.dep.values.insert(k);
    mark(value, id, "", p.name);
    env[p.name] = std::move(value);
  }
  i.summary = block(id, "", *i.def->body, env);
  for (size_t k = 0; k < i.summary.outputs.size(); ++k) {
    mark(i.summary.outputs[k], id, "", "result/" + std::to_string(k));
    if (i.summary.outputs[k].role == validator &&
        serializable(i.summary.outputs[k].type) &&
        needs(id, "", "result/" + std::to_string(k)))
      i.summary.roots.join(i.summary.outputs[k].dep);
  }
}

} // namespace zkc::protocol::construction
