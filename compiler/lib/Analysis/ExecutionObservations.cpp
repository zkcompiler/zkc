#include "zkc/Analysis/ExecutionObservations.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Analysis/TotalClosure.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"

using namespace mlir;
using namespace llvm;
namespace zkc {
namespace {
using Summary = ExecutionObservationSummary;
using Dependencies = SmallVector<BitVector>;
using Environment = llvm::DenseMap<Value, BitVector>;
using Step = protocol::SourceExecutionStep;
constexpr unsigned maxPorts = 1024, maxDepth = 64;
} // namespace

struct ExecutionObservationAnalysis::Impl {
  Operation *owner;
  SymbolTableCollection symbols;
  mathematical::NativeTypePolicies types;
  std::map<Operation *, protocol::SourceExecutionClosure> closures;
  llvm::DenseMap<Operation *, std::unique_ptr<mathematical::TotalClosure>>
      mathematics;
  std::map<Operation *, Summary> summaries;
  llvm::DenseSet<Operation *> active;
  llvm::DenseSet<Type> immutableTypes;
  std::string failureCode, failureDetail;

  explicit Impl(Operation *owner) : owner(owner), types(owner) {}
  bool fail(StringRef code, StringRef detail) {
    if (failureCode.empty()) {
      failureCode = code.str();
      failureDetail = detail.str();
    }
    return false;
  }
  bool unsupported(const Twine &detail) {
    return fail("execution-observation-unsupported", detail.str());
  }
  bool charge(facts::Work &work, uint64_t amount = 1) {
    return work.charge(amount) ||
           fail("execution-observation-capacity", "observation work exhausted");
  }
  bool depth(facts::Work &work, unsigned level, unsigned height = 1) {
    if (level && level <= maxDepth && height <= maxDepth - level + 1)
      return true;
    work.exhaust();
    return fail("execution-observation-capacity",
                "observation call depth exceeded");
  }
  Error failure() { return error(failureCode, failureDetail); }
  bool unite(BitVector &target, const BitVector &source, facts::Work &work) {
    if (target.size() != source.size())
      return unsupported("inconsistent dependency width");
    if (!charge(work, 1 + (target.size() + 63) / 64))
      return false;
    target |= source;
    return true;
  }
  bool dataType(Type type, facts::Work &work, unsigned nesting = 0) {
    if (!charge(work) || !depth(work, nesting + 1))
      return false;
    if (immutableTypes.contains(type))
      return true;
    auto policy = types.get(type);
    if (!policy || policy->affine)
      return unsupported("observation requires immutable logical data");
    if (auto variant = dyn_cast<data::VariantType>(type)) {
      for (auto arm : variant.getAlternatives())
        for (Type child : arm.getPayload())
          if (!dataType(child, work, nesting + 1))
            return false;
    } else {
      auto interface = dyn_cast<CatalogTypeInterface>(type);
      auto application =
          interface ? interface.getCatalogApplication() : std::nullopt;
      if (!application)
        return unsupported("observation type has no logical data contract");
      auto kind = application->constructor;
      const auto *permissions = protocol::typePermissions(kind);
      // Mathematical eligibility is not immutability: commitments, proofs
      // and finite polynomial carriers are public data too. Conversely Copy
      // alone would admit private setup keys and opaque opening handles.
      bool snapshot = kind == "sequence" || kind == "fixed_vector" ||
                      kind == "shake128_state";
      if (!permissions || !permissions->copy ||
          (permissions->custody != protocol::Custody::PublicValue && !snapshot))
        return unsupported("observation type carries private authority");
      for (Attribute argument : application->arguments)
        if (auto child = dyn_cast<TypeAttr>(argument))
          if (!dataType(child.getValue(), work, nesting + 1))
            return false;
    }
    immutableTypes.insert(type);
    return true;
  }
  bool data(TypeRange values, facts::Work &work) {
    for (auto type : values)
      if (!dataType(type, work))
        return false;
    return true;
  }
  bool values(ValueRange inputs, const Environment &env, Dependencies &result,
              facts::Work &work) {
    for (auto value : inputs) {
      auto found = env.find(value);
      if (found == env.end())
        return unsupported("missing actual data association");
      if (!charge(work, 1 + (found->second.size() + 63) / 64))
        return false;
      result.push_back(found->second);
    }
    return true;
  }
  bool substitute(const BitVector &formal, ArrayRef<BitVector> actual,
                  BitVector &result, facts::Work &work) {
    if (formal.size() != actual.size())
      return unsupported("inconsistent helper data signature");
    for (int port : formal.set_bits())
      if (!unite(result, actual[port], work))
        return false;
    return true;
  }
  bool store(ValueRange outputs, ArrayRef<BitVector> deps, Environment &env,
             const BitVector &control, facts::Work &work) {
    if (outputs.size() != deps.size())
      return unsupported("inconsistent helper results");
    for (auto [value, dependency] : zip(outputs, deps)) {
      BitVector result = dependency;
      if (!unite(result, control, work))
        return false;
      env[value] = std::move(result);
    }
    return true;
  }
  bool call(const Summary &callee, ArrayRef<BitVector> inputs,
            Dependencies &results, BitVector &control, Summary &summary,
            facts::Work &work) {
    summary.depth = std::max(summary.depth, callee.depth + 1);
    if (callee.mayStop) {
      BitVector stops(control);
      if (!substitute(callee.stops, inputs, stops, work) ||
          !unite(summary.stops, stops, work) || !unite(control, stops, work))
        return false;
      summary.mayStop = true;
    }
    for (const auto &formal : callee.results) {
      BitVector result(control);
      if (!substitute(formal, inputs, result, work))
        return false;
      results.push_back(std::move(result));
    }
    return true;
  }
  const Summary *reference(func::FuncOp function, Summary &summary,
                           facts::Work &work, unsigned level) {
    const auto *result = get(function, work, level + 1);
    if (!result)
      return nullptr;
    if (!charge(work, summary.callees.size() + 1))
      return nullptr;
    if (!is_contained(summary.callees, function))
      summary.callees.push_back(function);
    summary.depth = std::max(summary.depth, result->depth + 1);
    return result;
  }
  bool alternatives(const Step &step, ArrayRef<BitVector> inputs,
                    Environment &env, BitVector &control, Summary &summary,
                    facts::Work &work, unsigned level, bool &continues) {
    if (inputs.empty() || step.regions.empty())
      return unsupported("missing branch association");
    BitVector branchControl(control);
    if (!unite(branchControl, inputs.front(), work))
      return false;
    Dependencies merged(step.outputs.size(), BitVector(control.size()));
    continues = false;
    for (auto region : step.regions) {
      const auto *arm = reference(region, summary, work, level);
      if (!arm)
        return false;
      unsigned captures = inputs.size() - 1;
      if (arm->stops.size() < captures ||
          (!isa<exec::MatchOp>(step.operation) &&
           arm->stops.size() != captures))
        return unsupported("branch data ABI differs");
      // Every selected variant payload depends on the scrutinee. Captures
      // retain their distinct formal ports even when actual SSA values alias.
      Dependencies actual(arm->stops.size() - captures, inputs.front());
      append_range(actual, inputs.drop_front());
      Dependencies results;
      BitVector armControl(branchControl);
      if (!call(*arm, actual, results, armControl, summary, work))
        return false;
      if (arm->mayReturn) {
        if (results.size() != merged.size())
          return unsupported("branch result ABI differs");
        for (auto [target, source] : zip(merged, results))
          if (!unite(target, source, work))
            return false;
        continues = true;
      }
      if (arm->mayStop && !unite(control, armControl, work))
        return false;
    }
    return !continues || store(step.outputs, merged, env, control, work);
  }
  bool loop(const Step &step, ArrayRef<BitVector> inputs, Environment &env,
            BitVector &control, Summary &summary, facts::Work &work,
            unsigned level) {
    unsigned states = step.outputs.size();
    if (step.regions.size() != 1 || inputs.size() < 2 + states)
      return unsupported("loop data ABI differs");
    const auto *body = reference(step.regions.front(), summary, work, level);
    if (!body || body->stops.size() + 1 != inputs.size() ||
        body->results.size() != states + unsigned(step.conditional))
      return body ? unsupported("loop callback ABI differs") : false;
    BitVector loopControl(control);
    if (!unite(loopControl, inputs[0], work) ||
        !unite(loopControl, inputs[1], work))
      return false;
    // Initial state is a real zero-trip alternative. The iterator and reached
    // body depend on both bounds. A conditional backedge also observes its
    // flag.
    Dependencies state(inputs.begin() + 2, inputs.begin() + 2 + states);
    bool changed;
    do {
      if (!charge(work))
        return false;
      Dependencies actual{loopControl};
      append_range(actual, state);
      append_range(actual, inputs.drop_front(2 + states));
      Dependencies results;
      BitVector reached(loopControl);
      if (!call(*body, actual, results, reached, summary, work))
        return false;
      auto previousControl = loopControl;
      if (!unite(loopControl, reached, work))
        return false;
      if (body->mayReturn && step.conditional &&
          !unite(loopControl, results.front(), work))
        return false;
      changed = previousControl != loopControl;
      if (body->mayReturn)
        for (unsigned i = 0; i < states; ++i) {
          auto previous = state[i];
          if (!unite(state[i], results[i + unsigned(step.conditional)], work))
            return false;
          changed |= previous != state[i];
        }
    } while (changed);
    // Invalid range bounds can stop before entering the body. This is logical
    // partiality, not a claim about the resource budget of a successful range.
    summary.mayStop = true;
    if (!unite(summary.stops, loopControl, work) ||
        !unite(control, loopControl, work))
      return false;
    return store(step.outputs, state, env, control, work);
  }
  bool finite(const Step &step, ArrayRef<BitVector> inputs, Environment &env,
              BitVector &control, Summary &summary, facts::Work &work,
              unsigned level) {
    finite::Computation computation;
    auto *unit = step.operation->getParentOfType<func::FuncOp>()->getParentOp();
    if (failed(finite::describe(step.operation, computation, unit, &symbols)) ||
        !computation.scoped ||
        failed(finite::partitionEntry(computation, step.inputs)))
      return unsupported("finite observation ABI differs");
    BitVector combined(control);
    for (const auto &dependency : inputs)
      if (!unite(combined, dependency, work))
        return false;
    auto inspect = [&](finite::CallbackRole role) {
      auto abi = finite::readCallbackABI(computation, role);
      if (failed(abi))
        return unsupported("finite callback ABI differs");
      auto function = dyn_cast<func::FuncOp>(abi->symbol);
      const auto *callback = reference(function, summary, work, level);
      if (!callback)
        return false;
      // Conservatively close item, state, domain and capture feedback together.
      // This finite top transfer avoids enumeration and inspects every actual
      // callback (including a predicate whose result controls cardinality).
      if (callback->mayStop) {
        summary.mayStop = true;
        if (!unite(summary.stops, combined, work) ||
            !unite(control, combined, work))
          return false;
      }
      return true;
    };
    if (!inspect(computation.collect ? finite::CallbackRole::Body
                                     : finite::CallbackRole::Step) ||
        (computation.predicate && !inspect(finite::CallbackRole::Predicate)))
      return false;
    return store(step.outputs, Dependencies(step.outputs.size(), combined), env,
                 control, work);
  }
  bool body(ArrayRef<Step> steps, Environment env, Summary &summary,
            facts::Work &work, unsigned level) {
    BitVector control(summary.stops.size());
    for (const auto &step : steps) {
      if (!charge(work, 1 + step.inputs.size() + step.outputs.size()))
        return false;
      Dependencies inputs;
      if (!values(step.inputs, env, inputs, work))
        return false;
      auto *op = step.operation;
      if (isa<exec::RejectOp>(op)) {
        summary.mayStop = true;
        return unite(summary.stops, control, work);
      }
      if (isa<exec::ReturnOp, exec::CompleteOp>(op)) {
        if (inputs.size() != summary.results.size())
          return unsupported("returned data ABI differs");
        for (auto [target, source] : zip(summary.results, inputs))
          if (!unite(target, source, work) || !unite(target, control, work))
            return false;
        summary.mayReturn = true;
        return true;
      }
      if (isa<exec::TestOp, exec::MatchOp>(op)) {
        bool continues;
        if (!alternatives(step, inputs, env, control, summary, work, level,
                          continues))
          return false;
        if (!continues)
          return true;
        continue;
      }
      if (isa<exec::RangeOp>(op)) {
        if (!loop(step, inputs, env, control, summary, work, level))
          return false;
        continue;
      }
      if (isa<exec::FoldOp, exec::CollectOp>(op)) {
        if (!finite(step, inputs, env, control, summary, work, level))
          return false;
        continue;
      }
      func::FuncOp helper;
      if (auto invocation = dyn_cast<func::CallOp>(op))
        helper = symbols.lookupNearestSymbolFrom<func::FuncOp>(
            invocation, invocation.getCalleeAttr());
      else if (auto computation = dyn_cast<exec::ComputeOp>(op))
        helper = computation.resolveCallee(symbols);
      if (helper) {
        const auto *callee = reference(helper, summary, work, level);
        Dependencies results;
        if (!callee || !call(*callee, inputs, results, control, summary, work))
          return false;
        if (!callee->mayReturn)
          return true;
        if (!store(step.outputs, results, env, control, work))
          return false;
        continue;
      }
      BitVector combined(control);
      for (const auto &dependency : inputs)
        if (!unite(combined, dependency, work))
          return false;
      if (auto application = dyn_cast<exec::ApplyOp>(op)) {
        auto binding = symbols.lookupNearestSymbolFrom<runtime::BindingOp>(
            application, application.getBindingAttr());
        auto *contract =
            binding ? protocol::operationContracts(binding.getContract())
                    : nullptr;
        if (!contract || !contract->deterministicData ||
            protocol::hasUnclassifiedProviderEffect(binding.getContract()) ||
            !data(ValueRange(step.inputs).getTypes(), work) ||
            !data(ValueRange(step.outputs).getTypes(), work))
          return unsupported(
              Twine("primitive lacks a deterministic data interpretation: ") +
              (binding ? binding.getContract() : StringRef("missing binding")));
        summary.primitives.push_back(op);
        // No totality facet is inferred. An eager ignored call can still stop.
        summary.mayStop = true;
        if (!unite(summary.stops, combined, work) ||
            !unite(control, combined, work))
          return false;
      } else if (isa<runtime::ReleaseBindingsOp>(op)) {
        for (Value value : step.inputs)
          env.erase(value);
        continue;
      } else if (!isa<exec::BooleanOp, exec::VariantOp>(op))
        return unsupported("unclassified execution observation");
      if (!store(step.outputs, Dependencies(step.outputs.size(), combined), env,
                 control, work))
        return false;
    }
    return unsupported("execution body has no admitted exit");
  }
  const Summary *get(func::FuncOp function, facts::Work &work, unsigned level) {
    if (!failureCode.empty() || !charge(work) || !depth(work, level))
      return nullptr;
    if (!isa_and_nonnull<ModuleOp>(owner) || !function ||
        !owner->isProperAncestor(function) || function.isExternal()) {
      fail("execution-observation-owner", "function is outside the module");
      return nullptr;
    }
    if (auto found = summaries.find(function); found != summaries.end()) {
      auto &summary = found->second;
      if (!depth(work, level, summary.depth) ||
          !charge(work, (summary.results.size() + 1) *
                            (1 + (summary.stops.size() + 63) / 64)))
        return nullptr;
      return &summary;
    }
    if (!active.insert(function).second) {
      unsupported("observation helper closure is cyclic");
      return nullptr;
    }
    auto leave = scope_exit([&] { active.erase(function); });
    bool scoped = protocol::isScopedExecutionFunction(function);
    FunctionType signature = function.getFunctionType();
    if (scoped) {
      if (!function.getNumArguments() || function.getNumResults() != 1) {
        unsupported("scoped observation signature differs");
        return nullptr;
      }
      auto outcome = dyn_cast<exec::OutcomeType>(function.getResultTypes()[0]);
      if (!outcome) {
        unsupported("scoped observation has no outcome");
        return nullptr;
      }
      signature = FunctionType::get(function.getContext(),
                                    function.getArgumentTypes().drop_front(),
                                    outcome.getPayload());
    }
    if (signature.getNumInputs() > maxPorts ||
        signature.getNumResults() > maxPorts) {
      work.exhaust();
      fail("execution-observation-capacity", "observation port count exceeded");
      return nullptr;
    }
    if (!data(signature.getInputs(), work) ||
        !data(signature.getResults(), work))
      return nullptr;
    Summary summary;
    summary.stops.resize(signature.getNumInputs());
    summary.results.assign(signature.getNumResults(),
                           BitVector(signature.getNumInputs()));
    auto *unit = function->getParentOp();
    if (!scoped) {
      auto &closure = mathematics[unit];
      if (!closure) {
        auto module = dyn_cast<ModuleOp>(unit);
        auto entry =
            module ? mathematical::getComputationEntry(module) : func::FuncOp();
        closure =
            std::make_unique<mathematical::TotalClosure>(unit, symbols, entry);
      }
      const mathematical::TotalSummary *total = nullptr;
      if (failed(closure->get(function, total))) {
        unsupported("mathematical observation closure refused");
        return nullptr;
      }
      if (!charge(work, total->expandedOperations))
        return nullptr;
      summary.results = total->results;
      summary.depth = total->depth;
      summary.mayReturn = true;
    } else {
      auto found = closures.find(unit);
      if (found == closures.end()) {
        auto walk = unit->walk([&](Operation *) {
          return charge(work) ? WalkResult::advance() : WalkResult::interrupt();
        });
        if (walk.wasInterrupted())
          return nullptr;
        auto closure = protocol::readSourceExecutionClosure(unit);
        if (!closure) {
          auto reason = toString(closure.takeError());
          unsupported(reason);
          return nullptr;
        }
        found = closures.try_emplace(unit, std::move(*closure)).first;
      }
      auto source = found->second.bodies.find(function.getSymName().str());
      if (source == found->second.bodies.end()) {
        unsupported("missing admitted function association");
        return nullptr;
      }
      Environment env;
      for (auto [i, argument] :
           enumerate(function.getArguments().drop_front())) {
        if (!charge(work, 1 + (signature.getNumInputs() + 63) / 64))
          return nullptr;
        BitVector formal(signature.getNumInputs());
        formal.set(i);
        env[argument] = std::move(formal);
      }
      if (!body(source->second, std::move(env), summary, work, level))
        return nullptr;
    }
    if (!depth(work, level, summary.depth))
      return nullptr;
    return &summaries.try_emplace(function, std::move(summary)).first->second;
  }
};

ExecutionObservationAnalysis::ExecutionObservationAnalysis(Operation *module)
    : impl_(std::make_unique<Impl>(module)) {}
ExecutionObservationAnalysis::ExecutionObservationAnalysis(Operation *module,
                                                           AnalysisManager &)
    : ExecutionObservationAnalysis(module) {}
ExecutionObservationAnalysis::~ExecutionObservationAnalysis() = default;
Operation *ExecutionObservationAnalysis::getOwner() const {
  return impl_->owner;
}
void ExecutionObservationAnalysis::clear() {
  impl_ = std::make_unique<Impl>(impl_->owner);
}
bool ExecutionObservationAnalysis::isInvalidated(
    const AnalysisManager::PreservedAnalyses &preserved) {
  return !preserved.isPreserved<ExecutionObservationAnalysis>();
}
Expected<const ExecutionObservationSummary *>
ExecutionObservationAnalysis::get(func::FuncOp function, facts::Work &work) {
  auto *result = impl_->get(function, work, 1);
  if (!result)
    return impl_->failure();
  return result;
}
} // namespace zkc
