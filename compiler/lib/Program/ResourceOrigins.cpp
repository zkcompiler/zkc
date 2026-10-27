#include "ResourceOrigins.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Program/ResourceOrigins.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/ScopeExit.h"
#include <set>

using namespace llvm;
namespace zkc::program {
namespace {
using Environment = std::map<std::string, unsigned>;
class Analysis {
  std::map<std::string, const Function *> functions;
  std::map<std::string, const protocol::LocalRealization *> realizations;
  std::map<std::string, const protocol::OperationBinding *> bindings;
  std::map<std::string, ResourceOriginSummary> summaries;
  std::set<std::string> active;
  uint64_t &remaining;
  unsigned depthLimit;
  std::string refusalCode, refusalDetail;

  bool fail(StringRef code, StringRef detail) {
    if (refusalCode.empty()) {
      refusalCode = code.str();
      refusalDetail = detail.str();
    }
    return false;
  }
  bool charge(uint64_t amount) {
    if (amount > remaining)
      return fail("mathematical-analysis-limit",
                  "resource-origin work limit exceeded");
    remaining -= amount;
    return true;
  }
  bool depth(unsigned current, unsigned height = 1) {
    return (current && current <= depthLimit &&
            height <= depthLimit - current + 1) ||
           fail("mathematical-analysis-limit",
                "resource-origin nesting limit exceeded");
  }
  Environment captures(const Names &names, const Environment &environment) {
    Environment result;
    for (const auto &name : names)
      if (auto found = environment.find(name); found != environment.end())
        result.emplace(*found);
    return result;
  }
  bool substitute(const ResourceOriginSummary &summary, const Names &inputs,
                  const Names &outputs, Environment &environment) {
    if (!charge(inputs.size() + outputs.size()))
      return false;
    for (auto [output, input] : summary.roots) {
      if (output >= outputs.size() || input >= inputs.size())
        return fail("mathematical-formation",
                    "inconsistent resource-origin call signature");
      if (auto found = environment.find(inputs[input]);
          found != environment.end())
        environment[outputs[output]] = found->second;
    }
    return true;
  }
  bool successors(const Operation &op, Environment &environment) {
    auto binding = bindings.find(op.callee);
    if (binding == bindings.end())
      return fail("binding-reference", "resource-origin binding is absent");
    const auto *facts =
        protocol::operationContracts(binding->second->application.contract);
    if (!facts)
      return true;
    std::map<unsigned, std::optional<unsigned>> roots;
    auto pair = [&](unsigned input, unsigned output) {
      if (!charge(1))
        return false;
      if (input >= op.inputs.size() || output >= op.outputs.size())
        return fail("mathematical-formation",
                    "invalid resource successor contract");
      std::optional<unsigned> root;
      if (auto found = environment.find(op.inputs[input]);
          found != environment.end())
        root = found->second;
      auto [at, inserted] = roots.emplace(output, root);
      if (!inserted && at->second != root)
        at->second.reset();
      return true;
    };
    if ((facts->history &&
         !pair(facts->history->stateInput, facts->history->stateOutput)) ||
        (facts->sampling &&
         !pair(facts->sampling->stateInput, facts->sampling->stateOutput)) ||
        (facts->observation && !pair(facts->observation->stateInput,
                                     facts->observation->stateOutput)))
      return false;
    for (auto [output, root] : roots)
      if (root)
        environment[op.outputs[output]] = *root;
    return true;
  }
  void join(ResourceOriginSummary &result, const ResourceOriginSummary &arm) {
    result.depth = std::max(result.depth, arm.depth + 1);
    if (!arm.continues)
      return;
    if (!result.continues)
      result.roots = arm.roots;
    else
      for (auto it = result.roots.begin(); it != result.roots.end();) {
        auto other = arm.roots.find(it->first);
        if (other == arm.roots.end() || other->second != it->second)
          it = result.roots.erase(it);
        else
          ++it;
      }
    result.continues = true;
  }
  bool body(const Body &instructions, Environment environment, unsigned level,
            ResourceOriginSummary &result) {
    if (!depth(level))
      return false;
    for (const auto &instruction : instructions) {
      if (!charge(1))
        return false;
      if (instruction.get<Stop>()) {
        result.continues = false;
        return true;
      }
      const Names *returned = nullptr;
      if (const auto *value = instruction.get<Return>())
        returned = &value->values;
      if (const auto *value = instruction.get<Yield>())
        returned = &value->values;
      if (returned) {
        if (!charge(returned->size()))
          return false;
        for (auto [i, value] : enumerate(*returned))
          if (auto found = environment.find(value); found != environment.end())
            result.roots[i] = found->second;
        return true;
      }
      if (const auto *op = instruction.get<Operation>()) {
        if (!charge(op->inputs.size() + op->outputs.size()) ||
            !successors(*op, environment))
          return false;
      } else if (const auto *call = instruction.get<LocalApply>()) {
        const auto *summary = get(call->callee, level + 1);
        if (!summary)
          return false;
        result.depth = std::max(result.depth, summary->depth + 1);
        if (!summary->continues) {
          result.continues = false;
          return true;
        }
        if (!substitute(*summary, call->inputs, call->outputs, environment))
          return false;
      } else if (const auto *branch = instruction.get<Conditional>()) {
        if (!charge(branch->captures.size() + branch->outputs.size()))
          return false;
        auto inner = captures(branch->captures, environment);
        ResourceOriginSummary merged;
        merged.continues = false;
        for (const auto *arm : {&branch->thenBody, &branch->elseBody}) {
          ResourceOriginSummary summary;
          if (!body(*arm, inner, level + 1, summary))
            return false;
          join(merged, summary);
        }
        result.depth = std::max(result.depth, merged.depth);
        if (!merged.continues) {
          result.continues = false;
          return true;
        }
        for (auto [index, root] : merged.roots)
          environment[branch->outputs[index]] = root;
      } else if (const auto *match = instruction.get<Match>()) {
        if (!charge(match->captures.size() + match->outputs.size()))
          return false;
        auto inner = captures(match->captures, environment);
        ResourceOriginSummary merged;
        merged.continues = false;
        for (const auto &arm : match->arms) {
          if (!charge(arm.payload.size() + 1))
            return false;
          // Payload roots are unknown even for a nearby variant constructor.
          ResourceOriginSummary summary;
          if (!body(arm.body, inner, level + 1, summary))
            return false;
          join(merged, summary);
        }
        result.depth = std::max(result.depth, merged.depth);
        if (!merged.continues) {
          result.continues = false;
          return true;
        }
        for (auto [index, root] : merged.roots)
          environment[match->outputs[index]] = root;
      } else if (const auto *loop = instruction.get<For>()) {
        if (!charge(2 * loop->carried.size() + loop->captures.size() +
                    loop->outputs.size()))
          return false;
        Environment inner;
        for (auto [index, state] : enumerate(loop->carried))
          inner[state.first] = index;
        ResourceOriginSummary transition;
        if (!body(loop->body, std::move(inner), level + 1, transition))
          return false;
        result.depth = std::max(result.depth, transition.depth + 1);
        for (auto [index, state] : enumerate(loop->carried)) {
          auto root =
              transition.roots.find(index + unsigned(loop->conditional));
          if (transition.continues &&
              (root == transition.roots.end() || root->second != index))
            continue;
          if (auto initial = environment.find(state.second);
              initial != environment.end())
            environment[loop->outputs[index]] = initial->second;
        }
        // A zero-trip loop continues with its initial state even when every
        // reached iteration stops. Neither bounds nor predicates are guessed.
      } else if (const auto *release = instruction.get<Release>()) {
        if (!charge(release->values.size()))
          return false;
        for (const auto &value : release->values)
          environment.erase(value);
      } else if (const auto *variant = instruction.get<VariantConstruct>()) {
        if (!charge(variant->payload.size()))
          return false;
      } else if (!instruction.get<BooleanConstant>())
        return fail("mathematical-formation",
                    "unsupported local resource-origin instruction");
    }
    return fail("mathematical-formation",
                "resource-origin body has no terminator");
  }

public:
  Analysis(const LocalDefinitions &definitions,
           ArrayRef<protocol::LocalRealization> selected, uint64_t &remaining,
           unsigned depthLimit)
      : remaining(remaining), depthLimit(depthLimit) {
    if (!charge(definitions.functions.size() + definitions.bindings.size() +
                selected.size()))
      return;
    for (const auto &function : definitions.functions)
      functions.emplace(function.name, &function);
    for (const auto &binding : definitions.bindings)
      bindings.emplace(binding.name, &binding);
    for (const auto &realization : selected)
      realizations.emplace(realization.name, &realization);
  }
  const ResourceOriginSummary *get(const std::string &name,
                                   unsigned level = 1) {
    if (!refusalCode.empty() || !depth(level) || !charge(1))
      return nullptr;
    if (auto found = summaries.find(name); found != summaries.end()) {
      if (!depth(level, found->second.depth))
        return nullptr;
      return &found->second;
    }
    if (!active.insert(name).second) {
      fail("mathematical-formation", "resource-origin calls must be acyclic");
      return nullptr;
    }
    auto cleanup = scope_exit([&] { active.erase(name); });
    ResourceOriginSummary summary;
    if (auto found = realizations.find(name); found != realizations.end()) {
      const auto &realization = *found->second;
      if (!charge(realization.inputs.size() + realization.outputs.size()))
        return nullptr;
      if (realization.kind == protocol::LocalRealization::Kind::FiniteFold &&
          any_of(realization.outputs,
                 [](StringRef type) { return protocol::affine(type); })) {
        // The native finite reader checks the whole callback ABI. Also check
        // the state ports here before interpreting formal indices as state
        // roots: this internal API must not infer roots from mismatched ports.
        auto callback = functions.find(realization.callbacks.front());
        if (callback == functions.end() ||
            callback->second->results != realization.outputs ||
            callback->second->arguments.size() < realization.outputs.size()) {
          fail("mathematical-formation", "invalid finite state callback ABI");
          return nullptr;
        }
        for (auto [index, type] : enumerate(realization.outputs))
          if (callback->second->arguments[index].type != type) {
            fail("mathematical-formation", "invalid finite state callback ABI");
            return nullptr;
          }
        const auto *step = get(realization.callbacks.front(), level + 1);
        if (!step)
          return nullptr;
        summary.depth = step->depth + 1;
        for (auto [index, type] : enumerate(realization.outputs)) {
          if (!protocol::affine(type))
            continue;
          auto root = step->roots.find(index);
          if (step->continues &&
              (root == step->roots.end() || root->second != index)) {
            fail(
                "mathematical-formation",
                "finite state transition must preserve each exact affine root");
            return nullptr;
          }
          summary.roots[index] = realization.domainArguments + index;
        }
      }
    } else if (auto found = functions.find(name); found != functions.end()) {
      const auto &function = *found->second;
      if (!charge(function.arguments.size() + function.results.size()))
        return nullptr;
      Environment environment;
      for (auto [index, argument] : enumerate(function.arguments))
        if (protocol::affine(argument.type))
          environment[argument.name] = index;
      if (!body(function.body, std::move(environment), level, summary))
        return nullptr;
      for (auto it = summary.roots.begin(); it != summary.roots.end();)
        if (it->first >= function.results.size() ||
            !protocol::affine(function.results[it->first]))
          it = summary.roots.erase(it);
        else
          ++it;
    } else {
      fail("mathematical-formation", "resource-origin callee is absent");
      return nullptr;
    }
    if (!depth(level, summary.depth))
      return nullptr;
    return &summaries.emplace(name, std::move(summary)).first->second;
  }
  Error takeFailure() {
    if (!refusalCode.empty())
      return error(refusalCode, refusalDetail);
    return error("mathematical-formation", "resource-origin analysis refused");
  }
  Expected<ResourceOriginSummary> query(StringRef function, unsigned level) {
    const auto *result = get(function.str(), level);
    if (!result || !charge(result->roots.size()))
      return takeFailure();
    return *result;
  }
};
} // namespace

struct ResourceOriginAnalysis::Impl {
  LocalDefinitions definitions;
  std::vector<protocol::LocalRealization> realizations;
  Analysis analysis;
  Impl(LocalDefinitions definitions,
       std::vector<protocol::LocalRealization> realizations,
       uint64_t &remaining, unsigned depthLimit)
      : definitions(std::move(definitions)),
        realizations(std::move(realizations)),
        analysis(this->definitions, this->realizations, remaining, depthLimit) {
  }
};
ResourceOriginAnalysis::ResourceOriginAnalysis(std::unique_ptr<Impl> impl)
    : impl(std::move(impl)) {}
ResourceOriginAnalysis::~ResourceOriginAnalysis() = default;
Expected<std::unique_ptr<ResourceOriginAnalysis>>
ResourceOriginAnalysis::create(
    LocalDefinitions definitions,
    std::vector<protocol::LocalRealization> realizations, uint64_t &remaining,
    unsigned depthLimit) {
  if (auto error =
          protocol::admitNativeLocalDefinitions(definitions, realizations))
    return std::move(error);
  return std::unique_ptr<ResourceOriginAnalysis>(new ResourceOriginAnalysis(
      std::make_unique<Impl>(std::move(definitions), std::move(realizations),
                             remaining, depthLimit)));
}
Expected<ResourceOriginSummary> ResourceOriginAnalysis::get(StringRef function,
                                                            unsigned depth) {
  return impl->analysis.query(function, depth);
}

Error detail::verifyFiniteResourceOrigins(
    const LocalDefinitions &definitions,
    ArrayRef<protocol::LocalRealization> realizations) {
  if (none_of(realizations, [](const auto &value) {
        return value.kind == protocol::LocalRealization::Kind::FiniteFold &&
               any_of(value.outputs,
                      [](StringRef type) { return protocol::affine(type); });
      }))
    return Error::success();
  uint64_t remaining = 100000;
  Analysis analysis(definitions, realizations, remaining, 64);
  for (const auto &realization : realizations)
    if (realization.kind == protocol::LocalRealization::Kind::FiniteFold &&
        !analysis.get(realization.name))
      return analysis.takeFailure();
  return Error::success();
}
Expected<ResourceOriginSummary>
analyzeResourceOrigins(const LocalDefinitions &definitions,
                       ArrayRef<protocol::LocalRealization> realizations,
                       StringRef function, uint64_t &remaining,
                       unsigned depthLimit) {
  auto analysis = ResourceOriginAnalysis::create(
      definitions, {realizations.begin(), realizations.end()}, remaining,
      depthLimit);
  if (!analysis)
    return analysis.takeError();
  return (*analysis)->get(function);
}
} // namespace zkc::program
