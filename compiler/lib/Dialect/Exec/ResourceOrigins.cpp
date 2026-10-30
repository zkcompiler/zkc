#include "zkc/Dialect/Exec/ResourceOrigins.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"
using namespace mlir;
using namespace llvm;
namespace zkc::exec {
struct ResourceOriginAnalysis::Impl {
  using Environment = llvm::DenseMap<Value, unsigned>;
  Operation *owner;
  llvm::DenseMap<Operation *, std::vector<protocol::SourceExecutionStep>>
      bodies;
  llvm::DenseMap<Operation *, ResourceOriginSummary> summaries;
  llvm::DenseSet<Operation *> active;
  SymbolTableCollection symbols;
  mathematical::NativeTypePolicies types;
  uint64_t &remaining;
  unsigned depthLimit;
  std::string code, detail;

  Impl(Operation *owner, uint64_t &remaining, unsigned depthLimit)
      : owner(owner), types(owner), remaining(remaining),
        depthLimit(depthLimit) {}
  bool fail(StringRef reason, StringRef message) {
    if (code.empty()) {
      code = reason.str();
      detail = message.str();
    }
    return false;
  }
  bool malformed(StringRef message) {
    return fail("mathematical-formation", message);
  }
  bool charge(uint64_t amount) {
    if (amount > remaining)
      return fail("mathematical-analysis-limit",
                  "resource-origin work limit exceeded");
    remaining -= amount;
    return true;
  }
  bool depth(unsigned level, unsigned height = 1) {
    return (level && level <= depthLimit && height <= depthLimit - level + 1) ||
           fail("mathematical-analysis-limit",
                "resource-origin nesting limit exceeded");
  }
  bool affine(Type type) {
    auto policy = types.get(type);
    if (!policy)
      malformed("resource-origin type has no native policy");
    return policy && policy->affine;
  }
  bool index(protocol::SourceExecutionClosure closure) {
    if (!owner || owner->getNumRegions() != 1 ||
        !owner->getRegion(0).hasOneBlock())
      return malformed("resource-origin owner has no definition table");
    if (!charge(closure.bodies.size()))
      return false;
    for (auto &[name, body] : closure.bodies) {
      auto function = symbols.lookupSymbolIn<func::FuncOp>(
          owner, StringAttr::get(owner->getContext(), name));
      if (!function || function.isExternal() ||
          !protocol::isScopedExecutionFunction(function))
        return malformed("resource-origin association has no actual function");
      bodies.try_emplace(function, std::move(body));
    }
    return true;
  }
  Error failure() {
    return error(code.empty() ? "mathematical-formation" : code,
                 detail.empty() ? "resource-origin analysis refused" : detail);
  }
  bool substitute(const ResourceOriginSummary &summary, ValueRange inputs,
                  ValueRange outputs, Environment &environment) {
    if (!charge(inputs.size() + outputs.size()))
      return false;
    for (auto [output, input] : summary.roots) {
      if (output >= outputs.size() || input >= inputs.size())
        return malformed("inconsistent resource-origin call signature");
      if (auto found = environment.find(inputs[input]);
          found != environment.end())
        environment[outputs[output]] = found->second;
    }
    return true;
  }
  bool successors(const protocol::SourceExecutionStep &step, ApplyOp call,
                  Environment &environment) {
    auto binding = symbols.lookupNearestSymbolFrom<runtime::BindingOp>(
        call, call.getBindingAttr());
    if (!binding || binding->getParentOp() != owner)
      return malformed("resource-origin binding is outside its closure");
    const auto *facts = protocol::operationContracts(binding.getContract());
    if (!facts)
      return malformed("resource-origin binding has no catalog declaration");
    std::map<unsigned, std::optional<unsigned>> roots;
    auto pair = [&](unsigned input, unsigned output) {
      if (!charge(1))
        return false;
      if (input >= step.inputs.size() || output >= step.outputs.size())
        return malformed("invalid resource successor contract");
      std::optional<unsigned> root;
      if (auto found = environment.find(step.inputs[input]);
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
      if (root && affine(step.outputs[output].getType()))
        environment[step.outputs[output]] = *root;
    return code.empty();
  }
  static void join(ResourceOriginSummary &result,
                   const ResourceOriginSummary &arm) {
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
  bool alternatives(const protocol::SourceExecutionStep &step,
                    Environment &environment, unsigned level,
                    ResourceOriginSummary &result) {
    ResourceOriginSummary merged;
    merged.continues = false;
    auto captures = ValueRange(step.inputs).drop_front();
    bool match = isa<MatchOp>(step.operation);
    for (auto region : step.regions) {
      const auto *summary = get(region, level + 1);
      if (!summary)
        return false;
      unsigned formals = region.getNumArguments() - 1;
      if (formals < captures.size() || (!match && formals != captures.size()))
        return malformed("inconsistent closed-region capture signature");
      unsigned payload = formals - captures.size();
      ResourceOriginSummary mapped;
      mapped.continues = summary->continues;
      mapped.depth = summary->depth;
      if (!charge(captures.size() + summary->roots.size()))
        return false;
      for (auto [output, input] : summary->roots) {
        if (input >= formals || output >= step.outputs.size())
          return malformed("inconsistent closed-region result signature");
        // A variant's selected payload has no inferred resource root. Only
        // explicitly captured values transport roots into a match arm.
        if (input >= payload)
          if (auto found = environment.find(captures[input - payload]);
              found != environment.end())
            mapped.roots[output] = found->second;
      }
      join(merged, mapped);
    }
    result.depth = std::max(result.depth, merged.depth);
    if (!merged.continues) {
      result.continues = false;
      return true;
    }
    for (auto [output, root] : merged.roots)
      environment[step.outputs[output]] = root;
    return true;
  }
  bool loop(const protocol::SourceExecutionStep &step, Environment &environment,
            unsigned level, ResourceOriginSummary &result) {
    if (step.regions.size() != 1 ||
        step.inputs.size() < 2 + step.outputs.size())
      return malformed("inconsistent resource-origin loop ports");
    const auto *transition = get(step.regions.front(), level + 1);
    if (!transition)
      return false;
    result.depth = std::max(result.depth, transition->depth + 1);
    for (auto [i, output] : enumerate(step.outputs)) {
      auto root = transition->roots.find(i + unsigned(step.conditional));
      if (transition->continues &&
          (root == transition->roots.end() || root->second != 1 + i))
        continue;
      if (auto initial = environment.find(step.inputs[2 + i]);
          initial != environment.end())
        environment[output] = initial->second;
    }
    // A zero-trip loop retains its initial state even if every reached body
    // stops. Bounds and predicates are not guessed by this analysis.
    return true;
  }
  bool fold(const protocol::SourceExecutionStep &step, unsigned level,
            ResourceOriginSummary &summary) {
    finite::Computation computation;
    if (failed(
            finite::describe(step.operation, computation, owner, &symbols)) ||
        computation.collect || !computation.scoped)
      return malformed("invalid native state computation");
    if (!charge(step.inputs.size() + step.outputs.size()))
      return false;
    if (none_of(step.outputs,
                [&](Value value) { return affine(value.getType()); }))
      return code.empty();
    auto callback =
        finite::readCallbackABI(computation, finite::CallbackRole::Step);
    if (failed(callback) ||
        callback->formals.state.size() != step.outputs.size())
      return malformed("invalid native finite state ABI");
    auto function = dyn_cast<func::FuncOp>(callback->symbol);
    if (!function)
      return malformed(
          "finite affine state requires an actual scoped callback");
    const auto *transition = get(function, level + 1);
    if (!transition)
      return false;
    summary.depth = transition->depth + 1;
    for (auto [i, output] : enumerate(step.outputs)) {
      if (output.getType() != callback->formals.state[i].getType())
        return malformed("finite affine state ports differ");
      if (!affine(output.getType()))
        continue;
      auto root = transition->roots.find(i);
      if (transition->continues &&
          (root == transition->roots.end() || root->second != i))
        return malformed(
            "finite state transition must preserve each exact affine root");
      summary.roots[i] = computation.arguments + i;
    }
    return code.empty() && depth(level, summary.depth);
  }
  bool body(ArrayRef<protocol::SourceExecutionStep> steps,
            Environment environment, unsigned level,
            ResourceOriginSummary &result) {
    for (const auto &step : steps) {
      if (!charge(1 + step.inputs.size() + step.outputs.size()))
        return false;
      auto *op = step.operation;
      if (isa<RejectOp>(op)) {
        result.continues = false;
        return true;
      }
      if (isa<ReturnOp, CompleteOp>(op)) {
        for (auto [i, value] : enumerate(step.inputs))
          if (auto found = environment.find(value); found != environment.end())
            result.roots[i] = found->second;
        return true;
      }
      if (auto call = dyn_cast<ApplyOp>(op)) {
        if (!successors(step, call, environment))
          return false;
      } else if (auto call = dyn_cast<func::CallOp>(op)) {
        const auto *summary = get(
            symbols.lookupSymbolIn<func::FuncOp>(owner, call.getCalleeAttr()),
            level + 1);
        if (!summary)
          return false;
        result.depth = std::max(result.depth, summary->depth + 1);
        if (!summary->continues) {
          result.continues = false;
          return true;
        }
        if (!substitute(*summary, step.inputs, step.outputs, environment))
          return false;
      } else if (isa<TestOp, MatchOp>(op)) {
        if (!alternatives(step, environment, level, result))
          return false;
        if (!result.continues)
          return true;
      } else if (isa<RangeOp>(op)) {
        if (!loop(step, environment, level, result))
          return false;
      } else if (isa<FoldOp>(op)) {
        ResourceOriginSummary summary;
        if (!fold(step, level + 1, summary) ||
            !substitute(summary, step.inputs, step.outputs, environment))
          return false;
        result.depth = std::max(result.depth, summary.depth + 1);
      } else if (isa<runtime::ReleaseBindingsOp>(op)) {
        for (auto value : step.inputs)
          environment.erase(value);
      } else if (!isa<BooleanOp, VariantOp, ComputeOp, CollectOp>(op))
        return malformed("unsupported native resource-origin instruction");
    }
    return malformed("native resource-origin body has no terminator");
  }
  const ResourceOriginSummary *get(func::FuncOp function, unsigned level) {
    if (!code.empty() || !depth(level) || !charge(1))
      return nullptr;
    if (!function || function->getParentOp() != owner ||
        !bodies.contains(function)) {
      malformed("resource-origin function is outside its admitted closure");
      return nullptr;
    }
    if (auto found = summaries.find(function); found != summaries.end())
      return depth(level, found->second.depth) ? &found->second : nullptr;
    if (!active.insert(function).second) {
      malformed("resource-origin calls must be acyclic");
      return nullptr;
    }
    auto cleanup = scope_exit([&] { active.erase(function); });
    auto signature = protocol::scopedDataSignature(function);
    // Closed region functions use the same ports but are not ordinary helpers.
    if (!signature) {
      auto outcome = dyn_cast<OutcomeType>(function.getResultTypes().front());
      if (!outcome || !function.getNumArguments()) {
        malformed("invalid native resource-origin signature");
        return nullptr;
      }
      signature = FunctionType::get(function.getContext(),
                                    function.getArgumentTypes().drop_front(),
                                    outcome.getPayload());
    }
    if (!charge(signature.getNumInputs() + signature.getNumResults()))
      return nullptr;
    Environment environment;
    for (auto [i, argument] : enumerate(function.getArguments().drop_front()))
      if (affine(argument.getType()))
        environment[argument] = i;
    ResourceOriginSummary summary;
    if (!code.empty() ||
        !body(bodies.at(function), std::move(environment), level, summary))
      return nullptr;
    for (auto it = summary.roots.begin(); it != summary.roots.end();)
      if (it->first >= signature.getNumResults() ||
          !affine(signature.getResult(it->first)))
        it = summary.roots.erase(it);
      else
        ++it;
    if (!code.empty() || !depth(level, summary.depth))
      return nullptr;
    return &summaries.try_emplace(function, std::move(summary)).first->second;
  }
};
ResourceOriginAnalysis::ResourceOriginAnalysis(std::unique_ptr<Impl> impl)
    : impl(std::move(impl)) {}
ResourceOriginAnalysis::~ResourceOriginAnalysis() = default;
Expected<std::unique_ptr<ResourceOriginAnalysis>>
ResourceOriginAnalysis::create(Operation *owner,
                               protocol::SourceExecutionClosure closure,
                               uint64_t &remaining, unsigned depthLimit) {
  auto impl = std::make_unique<Impl>(owner, remaining, depthLimit);
  if (!impl->index(std::move(closure)))
    return impl->failure();
  return std::unique_ptr<ResourceOriginAnalysis>(
      new ResourceOriginAnalysis(std::move(impl)));
}
Expected<ResourceOriginSummary>
ResourceOriginAnalysis::get(func::FuncOp function, unsigned depth) {
  const auto *summary = impl->get(function, depth);
  if (!summary || !impl->charge(summary->roots.size()))
    return impl->failure();
  return *summary;
}
Error ResourceOriginAnalysis::verifyFiniteState() {
  if (!impl->code.empty())
    return impl->failure();
  for (const auto &[function, body] : impl->bodies)
    for (const auto &step : body) {
      if (!impl->charge(1))
        return impl->failure();
      if (isa<FoldOp>(step.operation)) {
        ResourceOriginSummary summary;
        if (!impl->fold(step, 1, summary))
          return impl->failure();
      }
    }
  return Error::success();
}
} // namespace zkc::exec
