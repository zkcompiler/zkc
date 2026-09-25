#include "ConstructionState.h"

using namespace llvm;
namespace zkc::protocol::construction {
Construction::Flow
Construction::resourceBlock(const std::string &id, const source::Body &body,
                            std::map<std::string, Origin> env) {
  auto values = [&](const source::Names &names) {
    Flow out;
    for (const auto &name : names)
      out.push_back(env.at(name));
    return out;
  };
  const auto &inst = instances.at(id);
  for (const auto &ins : body) {
    if (!budget())
      return {};
    if (const auto *ret = ins.get<source::Return>())
      return values(ret->values);
    if (const auto *yield = ins.get<source::Yield>())
      return values(yield->values);
    if (const auto *call = ins.get<source::LocalCall>()) {
      const auto &fn = *functions.at(call->callee);
      std::map<std::string, Origin> local;
      auto args = values(call->inputs);
      for (size_t k = 0; k < fn.arguments.size(); ++k)
        local[fn.arguments[k].name] = args[k];
      if (hasLocalControl(fn)) {
        for (const auto &output : call->outputs)
          env[output] = Origin{};
        continue;
      }
      for (const auto &op : *fn.body) {
        if (!budget())
          return {};
        if (const auto *ret = op.get<source::Return>()) {
          for (size_t k = 0; k < ret->values.size(); ++k)
            env[call->outputs[k]] = local.at(ret->values[k]);
        } else {
          if (!op.get<source::Operation>()) {
            fail("construction-local-control-static-trace");
            return {};
          }
          const auto &kernel = *op.get<source::Operation>();
          const auto *sample = samplingContract(contract(kernel.callee));
          for (size_t k = 0; k < kernel.outputs.size(); ++k)
            local[kernel.outputs[k]] =
                sample && k == sample->stateOutput
                    ? local.at(kernel.inputs[sample->stateInput])
                    : Origin{};
        }
      }
    } else if (const auto *message = ins.get<source::Message>())
      env[message->output] = env.at(message->input);
    else if (const auto *call = ins.get<source::ProtocolCall>()) {
      const auto &summary =
          resourceInstance(inst.dependencies.at(call->callee));
      if (!problem.empty())
        return {};
      auto args = values(call->inputs);
      for (size_t k = 0; k < summary.size(); ++k)
        env[call->outputs[k]] = summary[k] ? args[*summary[k]] : Origin{};
    } else if (const auto *loop = ins.get<source::Loop>()) {
      Flow initial;
      std::map<std::string, Origin> symbolic;
      for (size_t k = 0; k < loop->carried.size(); ++k) {
        const auto &p = loop->carried[k];
        initial.push_back(env.at(p.second));
        symbolic[p.first] = k;
      }
      for (const auto &capture : loop->captures)
        symbolic[capture] = Origin{};
      uint64_t n = count(*loop, inst);
      Flow selected;
      for (size_t k = 0; k < initial.size(); ++k)
        selected.push_back(k);
      if (n) {
        auto power = resourceBlock(id, loop->body, std::move(symbolic));
        if (!problem.empty())
          return {};
        while (n) {
          if (!budget(1 + selected.size() + power.size()))
            return {};
          if (n & 1)
            for (auto &origin : selected)
              origin = origin ? power[*origin] : Origin{};
          n >>= 1;
          if (n) {
            auto doubled = power;
            for (auto &origin : doubled)
              origin = origin ? power[*origin] : Origin{};
            power = std::move(doubled);
          }
        }
      }
      for (size_t k = 0; k < initial.size(); ++k)
        env[loop->outputs[k]] = selected[k] ? initial[*selected[k]] : Origin{};
    } else {
      fail("construction-incomplete-control");
      return {};
    }
  }
  fail("construction-body");
  return {};
}

const Construction::Flow &
Construction::resourceInstance(const std::string &id) {
  auto existing = resourceSummaries.find(id);
  if (existing != resourceSummaries.end())
    return existing->second;
  const auto &def = *instances.at(id).def;
  std::map<std::string, Origin> env;
  for (size_t k = 0; k < def.arguments.size(); ++k)
    env[def.arguments[k].name] = k;
  auto summary = resourceBlock(id, *def.body, std::move(env));
  return resourceSummaries.emplace(id, std::move(summary)).first->second;
}

} // namespace zkc::protocol::construction
