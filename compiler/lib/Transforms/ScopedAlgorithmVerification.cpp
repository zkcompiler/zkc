#include "Computation/Support.h"
#include "FiniteVerification.h"
#include "ScopedCandidate.h"
#include "ScopedCollectionSum.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Algorithms.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using Values = SmallVector<Value>;
using Environment = llvm::DenseMap<Value, Value>;
using Steps = std::vector<SourceExecutionStep>;
class ScopedCorrespondence {
  const SourceExecutionClosure &source, &candidate;
  SymbolTable symbols;
  uint64_t defaultRemaining = 1000000, defaultBytes = 16 * 1024 * 1024;
  uint64_t &remaining, &remainingBytes;
  mathematical::RealizationWork *finiteWork;
  MathematicalSelectionPolicy finitePolicy;
  const llvm::DenseSet<Operation *> *fixedBindings;
  mathematical::VerificationDecision *finiteOutcome;
  const mathematical::ScopedCandidate *view;
  Operation *sourceRoot;
  llvm::DenseMap<Operation *, unsigned> positions;
  llvm::DenseSet<Operation *> finiteBindings;
  bool valid = true;
  std::string root;
  std::vector<AlgorithmOrigin> origins;
  StringRef definition(func::FuncOp function) {
    return cast<StringAttr>(
               function->getAttrOfType<ArrayAttr>("runtime.origin")[0])
        .getValue();
  }
  LogicalResult refuse(Operation *op, StringRef detail) {
    valid = false;
    return diagnostics::emit(op->emitOpError(), "algorithm-correspondence",
                             detail);
  }
  bool charge(Operation *op, uint64_t amount) {
    if (amount > remaining) {
      (void)refuse(op, "scoped substitution work limit");
      return false;
    }
    remaining -= amount;
    return true;
  }
  bool bind(ValueRange original, ValueRange actual, Environment &env) {
    if (original.size() != actual.size() ||
        original.getTypes() != actual.getTypes())
      return false;
    for (auto [before, after] : zip(original, actual))
      env[before] = after;
    return true;
  }
  Values mapped(ValueRange values, const Environment &env) {
    Values result;
    for (Value value : values)
      result.push_back(env.lookup(value));
    return result;
  }
  Expected<std::string> occurrence(const Assignments &path, StringRef site) {
    if (!finiteWork || !path.empty())
      return algorithmSite(path, site, remainingBytes);
    if (site.size() > remainingBytes)
      return createStringError(inconvertibleErrorCode(),
                               "algorithm-origin-limit");
    remainingBytes -= site.size();
    return site.str();
  }
  bool finite(Operation *op, const Steps &actual, unsigned &cursor,
              Environment &env, const SourceExecutionStep &step,
              const Assignments &path, unsigned depth,
              const SourceExecutionStep *sum, bool &fused) {
    fused = false;
    if (!view || cursor >= actual.size())
      return false;
    auto rootSite =
        occurrence(path, op->getAttrOfType<StringAttr>("site").getValue());
    if (!rootSite) {
      consumeError(rootSite.takeError());
      return false;
    }
    auto callback =
        [&](func::FuncOp function, ValueRange inputs, StringRef callSite,
            Operation *&at) -> FailureOr<finite::ScopedCallbackResult> {
      if (!at)
        return failure();
      auto body = cast<func::FuncOp>(at->getParentOp());
      const auto &steps = candidate.bodies.at(body.getSymName().str());
      auto found = positions.find(at);
      if (found == positions.end())
        return failure();
      unsigned position = found->second;
      Environment arguments;
      if (!bind(function.getArguments().drop_front(), inputs, arguments))
        return failure();
      Assignments nested(path);
      nested.emplace_back(callSite.str(), function.getSymName().str());
      Values returned;
      bool stopped = false;
      if (!block(function, steps, position, std::move(arguments), nested,
                 definition(function), depth + 1, true, returned, stopped))
        return failure();
      at = position < steps.size() ? steps[position].operation : nullptr;
      return finite::ScopedCallbackResult{std::move(returned), stopped};
    };
    finite::VerificationLimits limits;
    limits.sharedReader = &finiteWork->requiredFiniteChecking;
    limits.sharedComparison = &finiteWork->optionalFiniteChecking;
    limits.sharedSiteBytes = &remainingBytes;
    limits.candidate = view;
    limits.sourceClosure = &source;
    limits.fixedBindings = fixedBindings;
    limits.callback = callback;
    limits.finiteSite = *rootSite;
    std::string sumSite;
    if (sum) {
      auto encoded = occurrence(
          path, sum->operation->getAttrOfType<StringAttr>("site").getValue());
      if (!encoded) {
        consumeError(encoded.takeError());
        return false;
      }
      sumSite = std::move(*encoded);
      limits.collectionSumSite = sumSite;
      limits.collectionSumLocation = sum->operation->getLoc();
    }
    auto pure = [](Operation *, ValueRange, Operation *&) -> FailureOr<Values> {
      return failure();
    };
    auto *begin = actual[cursor].operation;
    auto *at = begin;
    finite::VerificationResult outcome{finite::VerificationStatus::Mismatch,
                                       {}};
    auto result =
        finite::verifyExpression(op, mapped(step.inputs, env), at, pure,
                                 sourceRoot, limits, outcome, finitePolicy);
    if (failed(result)) {
      if (finiteOutcome) {
        using Observation = mathematical::VerificationObservation;
        finiteOutcome->outcome =
            outcome.status == finite::VerificationStatus::OptionalCapacity
                ? Observation::OptionalCapacity
            : outcome.status == finite::VerificationStatus::RequiredCapacity
                ? Observation::RequiredCapacity
                : Observation::Mismatch;
        finiteOutcome->detail = outcome.detail.str();
        finiteOutcome->capacity = outcome.capacity;
        finiteOutcome->subject = outcome.subject;
      }
      return false;
    }
    fused = sum && result->size() == 1 &&
            (*result)[0].getType() == sum->outputs[0].getType();
    if (!bind(fused ? sum->outputs : step.outputs, *result, env))
      return false;
    mathematical::CandidatePorts ports(view);
    for (auto *node = begin; node != at; node = ports.next(node)) {
      if (!node || ports
                       .walk(node,
                             [&](Operation *nested) {
                               if (!charge(nested, 1))
                                 return WalkResult::interrupt();
                               if (auto reference =
                                       nested->getAttrOfType<FlatSymbolRefAttr>(
                                           "binding")) {
                                 auto *binding =
                                     SymbolTable::lookupNearestSymbolFrom(
                                         nested, reference);
                                 if (!binding)
                                   return WalkResult::interrupt();
                                 finiteBindings.insert(binding);
                               }
                               return WalkResult::advance();
                             })
                       .wasInterrupted())
        return false;
    }
    if (at) {
      auto found = positions.find(at);
      if (found == positions.end() || found->second < cursor ||
          found->second >= actual.size() ||
          actual[found->second].operation != at)
        return false;
      cursor = found->second;
    } else
      cursor = actual.size();
    return true;
  }
  bool attrs(Operation *original, Operation *actual, const Assignments &path,
             StringRef definition) {
    NamedAttrList expected(original->getAttrs());
    NamedAttrList observed(actual->getAttrs());
    if (isa<exec::MatchOp>(original) && isa<exec::MatchOp>(actual)) {
      // Capture substitution may shrink each native successor segment. Both
      // closures have checked that storage, and control() independently derives
      // the ordered logical captures and every arm's argument association.
      expected.erase("successor_operand_segments");
      observed.erase("successor_operand_segments");
    }
    if (auto site = original->getAttrOfType<StringAttr>("site")) {
      auto encoded = occurrence(path, site.getValue());
      if (!encoded) {
        consumeError(encoded.takeError());
        return false;
      }
      expected.set("site", StringAttr::get(actual->getContext(), *encoded));
      origins.push_back({root, *encoded, definition.str(), site.str(), path});
    }
    return original->getLoc() == actual->getLoc() &&
           original->getName() == actual->getName() &&
           expected.getDictionary(actual->getContext()) ==
               observed.getDictionary(actual->getContext());
  }
  bool control(const SourceExecutionStep &before,
               const SourceExecutionStep &after, const Environment &env,
               const Assignments &path, StringRef definition, unsigned depth,
               bool &terminal) {
    const bool loop = isa<exec::RangeOp>(before.operation);
    unsigned prefix = loop ? 2 + before.outputs.size() : 1;
    auto inputs = mapped(before.inputs, env);
    if (inputs.size() < prefix || after.inputs.size() < prefix ||
        !equal(ArrayRef(inputs).take_front(prefix),
               ArrayRef(after.inputs).take_front(prefix)) ||
        before.regions.size() != after.regions.size() ||
        before.conditional != after.conditional)
      return false;
    // Derive the distinct actual captures from substitution. The candidate's
    // ports and each original formal position must agree with that sequence.
    Values expected;
    SmallVector<unsigned> positions;
    llvm::DenseMap<Value, unsigned> seen;
    for (Value value : ArrayRef(inputs).drop_front(prefix)) {
      auto [found, inserted] = seen.try_emplace(value, expected.size());
      if (inserted)
        expected.push_back(value);
      positions.push_back(found->second);
    }
    if (!equal(expected, ArrayRef(after.inputs).drop_front(prefix)))
      return false;
    bool allStopped = true, changedType = false;
    auto empty = exec::OutcomeType::get(before.operation->getContext(), {});
    for (auto pair : zip(before.regions, after.regions)) {
      func::FuncOp left = std::get<0>(pair), right = std::get<1>(pair);
      unsigned formals = left.getNumArguments() - 1 - positions.size();
      if (right.getNumArguments() != 1 + formals + expected.size())
        return false;
      if (left.getResultTypes() != right.getResultTypes()) {
        if (loop || !equal(right.getResultTypes(), TypeRange{empty}))
          return false;
        changedType = true;
      }
      Environment inner;
      if (!bind(left.getArguments().slice(1, formals),
                right.getArguments().slice(1, formals), inner))
        return false;
      for (auto [index, position] : enumerate(positions)) {
        auto input = left.getArgument(1 + formals + index);
        auto actual = right.getArgument(1 + formals + position);
        if (input.getType() != actual.getType())
          return false;
        inner[input] = actual;
      }
      // Preconditions index actual function arguments, including the scope
      // port. Recover their candidate coordinates from the checked SSA map.
      NamedAttrList attributes(left->getAttrs());
      attributes.set("sym_name", right->getAttr("sym_name"));
      attributes.set("function_type", right->getAttr("function_type"));
      if (auto conditions =
              left->getAttrOfType<ArrayAttr>("data.preconditions")) {
        if (!charge(left, conditions.size()))
          return false;
        auto argument = [&](unsigned index) {
          return cast<BlockArgument>(inner.lookup(left.getArgument(index)))
              .getArgNumber();
        };
        SmallVector<Attribute> transported;
        for (Attribute condition : conditions) {
          if (auto bound = dyn_cast<data::IndexBoundAttr>(condition))
            transported.push_back(data::IndexBoundAttr::get(
                right.getContext(), argument(bound.getIndexArg()),
                argument(bound.getContainerArg()), bound.getAxis()));
          else {
            auto equal = cast<data::EqualExtentAttr>(condition);
            transported.push_back(data::EqualExtentAttr::get(
                right.getContext(), argument(equal.getLeftArg()),
                equal.getLeftAxis(), argument(equal.getRightArg()),
                equal.getRightAxis()));
          }
        }
        attributes.set("data.preconditions",
                       ArrayAttr::get(right.getContext(), transported));
      }
      if (attributes.getDictionary(right.getContext()) !=
          right->getAttrDictionary())
        return false;
      const auto &body = candidate.bodies.at(right.getSymName().str());
      unsigned cursor = 0;
      Values returned;
      bool stopped = false;
      if (!block(left, body, cursor, std::move(inner), path, definition,
                 depth + 1, false, returned, stopped) ||
          cursor != body.size())
        return false;
      allStopped &= stopped;
    }
    terminal = !loop && allStopped;
    if (changedType && !terminal)
      return false;
    if (terminal)
      for (auto function : after.regions)
        if (!equal(function.getResultTypes(), TypeRange{empty}))
          return false;
    return true;
  }
  // Walk the original under virtual substitution and consume actual candidate
  // steps. A source helper return binds values in the caller; it consumes no
  // candidate instruction and must not become a charged completion.
  bool block(func::FuncOp function, const Steps &actual, unsigned &cursor,
             Environment env, const Assignments &path, StringRef origin,
             unsigned depth, bool inlineReturn, Values &returned,
             bool &stopped) {
    if (depth > 64)
      return false;
    const auto &steps = source.bodies.at(function.getSymName().str());
    for (unsigned index = 0; index < steps.size(); ++index) {
      const auto &step = steps[index];
      auto *op = step.operation;
      if (!charge(op, 1 + step.inputs.size() + step.outputs.size()))
        return false;
      if (finiteWork && isa<exec::FoldOp, exec::CollectOp>(op)) {
        auto *sum = index + 1 < steps.size() ? &steps[index + 1] : nullptr;
        if (!finitePolicy.vectorReductionFusion ||
            !finite::collectionSumConsumer(step, sum, fixedBindings))
          sum = nullptr;
        bool fused = false;
        if (!finite(op, actual, cursor, env, step, path, depth, sum, fused))
          return false;
        if (fused) {
          ++index;
          if (!charge(sum->operation,
                      1 + sum->inputs.size() + sum->outputs.size()))
            return false;
        }
        continue;
      }
      if (auto call = dyn_cast<func::CallOp>(op)) {
        auto callee = symbols.lookup<func::FuncOp>(call.getCallee());
        Environment arguments;
        if (!bind(callee.getArguments().drop_front(), mapped(step.inputs, env),
                  arguments))
          return false;
        Assignments nested(path);
        nested.emplace_back(
            call->getAttrOfType<StringAttr>("runtime.site").getValue().str(),
            call.getCallee().str());
        Values result;
        if (!block(callee, actual, cursor, std::move(arguments), nested,
                   definition(callee), depth + 1, true, result, stopped))
          return false;
        if (stopped)
          return true;
        if (!bind(step.outputs, result, env))
          return false;
        continue;
      }
      if (inlineReturn && isa<exec::ReturnOp>(op)) {
        returned = mapped(step.inputs, env);
        return true;
      }
      if (cursor == actual.size())
        return false;
      const auto &observed = actual[cursor++];
      if (!attrs(op, observed.operation, path, origin))
        return false;
      if (!step.regions.empty()) {
        bool terminal = false;
        if (!control(step, observed, env, path, origin, depth, terminal))
          return false;
        if (terminal) {
          if (!observed.outputs.empty() || cursor == actual.size())
            return false;
          const auto &end = actual[cursor++];
          auto reject = dyn_cast<exec::RejectOp>(end.operation);
          if (!reject || reject.getReason() != "abort" ||
              !reject.getSite().starts_with("unreachable_") ||
              !end.inputs.empty() || !end.outputs.empty() ||
              !end.regions.empty())
            return false;
          stopped = true;
          return true;
        }
      } else if (!observed.regions.empty() ||
                 mapped(step.inputs, env) != observed.inputs) {
        return false;
      }
      if (!bind(step.outputs, observed.outputs, env))
        return false;
      if (isa<exec::ReturnOp, exec::CompleteOp>(op)) {
        returned = mapped(step.inputs, env);
        return true;
      }
      if (isa<exec::RejectOp>(op)) {
        stopped = true;
        return true;
      }
    }
    return false;
  }

public:
  std::vector<AlgorithmOrigin> takeOrigins() { return std::move(origins); }
  ScopedCorrespondence(
      const SourceExecutionClosure &source,
      const SourceExecutionClosure &candidate, Operation *original,
      mathematical::RealizationWork *work = nullptr,
      const mathematical::ScopedCandidate *view = nullptr,
      MathematicalSelectionPolicy policy = {},
      mathematical::VerificationDecision *outcome = nullptr,
      const llvm::DenseSet<Operation *> *fixedBindings = nullptr)
      : source(source), candidate(candidate), symbols(original),
        remaining(work ? work->numericalContextChecking : defaultRemaining),
        remainingBytes(work ? work->numericalCheckSiteBytes : defaultBytes),
        finiteWork(work), finitePolicy(policy), fixedBindings(fixedBindings),
        finiteOutcome(outcome), view(view), sourceRoot(original) {
    for (const auto &[name, steps] : candidate.bodies)
      for (auto [index, step] : enumerate(steps))
        positions[step.operation] = index;
  }
  LogicalResult run(protocol_ir::ProtocolModuleOp before,
                    protocol_ir::ProtocolModuleOp after) {
    if (before->getAttrDictionary() != after->getAttrDictionary())
      return refuse(after, "changed execution owner");
    SymbolTable target(after);
    llvm::StringSet<> roots;
    SmallVector<Operation *> originalDeclarations, actualDeclarations;
    for (Operation &op : before.getBody().front()) {
      auto function = dyn_cast<func::FuncOp>(op);
      if (!function || !isScopedExecutionFunction(function)) {
        originalDeclarations.push_back(&op);
        continue;
      }
      if (function->hasAttr("runtime.region"))
        continue;
      roots.insert(function.getSymName());
      root = function.getSymName().str();
      auto actual = target.lookup<func::FuncOp>(function.getSymName());
      if (!actual ||
          actual->getAttrDictionary() != function->getAttrDictionary())
        return refuse(after, "changed scoped function inventory or interface");
      Environment env;
      if (!bind(function.getArguments().drop_front(),
                actual.getArguments().drop_front(), env))
        return refuse(actual, "changed scoped function arguments");
      unsigned cursor = 0;
      Values returned;
      bool stopped = false;
      const auto &body = candidate.bodies.at(actual.getSymName().str());
      if (!block(function, body, cursor, std::move(env), {},
                 definition(function), 0, false, returned, stopped) ||
          cursor != body.size())
        return refuse(actual, "scoped helper substitution differs");
    }
    for (Operation &op : after.getBody().front()) {
      auto function = dyn_cast<func::FuncOp>(op);
      if (!function || !isScopedExecutionFunction(function)) {
        if (finiteWork && isa<runtime::BindingOp>(op) &&
            !symbols.lookup(SymbolTable::getSymbolName(&op))) {
          if (!finiteBindings.contains(&op))
            return refuse(&op, "unaccounted finite binding");
          continue;
        }
        actualDeclarations.push_back(&op);
        continue;
      }
      if (!function->hasAttr("runtime.region") &&
          !roots.contains(function.getSymName()))
        return refuse(function, "added scoped root");
    }
    if (originalDeclarations.size() != actualDeclarations.size())
      return refuse(after, "changed non-execution declaration inventory");
    for (auto [original, actual] :
         zip(originalDeclarations, actualDeclarations))
      if (!OperationEquivalence::isEquivalentTo(
              original, actual, OperationEquivalence::IgnoreLocations))
        return refuse(actual, "changed non-execution declaration");
    return success(valid);
  }
};
} // namespace
LogicalResult
verifyScopedHelperExpansionPreserved(ModuleOp source, ModuleOp candidate,
                                     std::vector<AlgorithmOrigin> *origins) {
  if (failed(zkc::admitStage(source)) || failed(zkc::admitStage(candidate)) ||
      !hasSingleElement(*source.getBody()) ||
      !hasSingleElement(*candidate.getBody()) ||
      source->getAttrDictionary() != candidate->getAttrDictionary())
    return failure();
  auto before =
      dyn_cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  auto after =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!before || !after)
    return failure();
  auto original = readSourceExecutionClosure(before);
  if (!original)
    return diagnostics::emit(before.emitOpError(), original.takeError());
  auto actual = readSourceExecutionClosure(after);
  if (!actual)
    return diagnostics::emit(after.emitOpError(), actual.takeError());
  ScopedCorrespondence checker(*original, *actual, before);
  if (failed(checker.run(before, after)))
    return failure();
  if (origins)
    *origins = checker.takeOrigins();
  return success();
}
LogicalResult verifyScopedFinitePreparation(
    ModuleOp source, ModuleOp candidate, mathematical::RealizationWork &work,
    MathematicalSelectionPolicy policy,
    mathematical::VerificationDecision *outcome,
    const llvm::DenseSet<Operation *> *fixedBindings) {
  if (outcome)
    *outcome = {mathematical::VerificationObservation::Mismatch,
                "scoped finite preparation differs"};
  if (failed(zkc::admitStage(source)) || failed(zkc::admitStage(candidate)) ||
      !hasSingleElement(*source.getBody()) ||
      !hasSingleElement(*candidate.getBody()) ||
      source->getAttrDictionary() != candidate->getAttrDictionary() ||
      !computation::chargeCopy(source, work.numericalContextChecking) ||
      !computation::chargeCopy(candidate, work.numericalContextChecking))
    return failure();
  auto before =
      dyn_cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  auto after =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!before || !after)
    return failure();
  auto original = readSourceExecutionClosure(before);
  auto actual = readSourceExecutionClosure(after);
  auto view = mathematical::ScopedCandidate::read(
      after, mathematical::ScopedCandidate::Requests::Retained);
  if (!original || !actual || !view) {
    if (!original)
      consumeError(original.takeError());
    if (!actual)
      consumeError(actual.takeError());
    if (!view)
      consumeError(view.takeError());
    return failure();
  }
  bool unresolved = false;
  after.walk([&](Operation *op) {
    unresolved |= isa<exec::FoldOp, exec::CollectOp>(op);
  });
  if (unresolved)
    return failure();
  auto checked =
      ScopedCorrespondence(*original, *actual, before, &work, view->get(),
                           policy, outcome, fixedBindings)
          .run(before, after);
  if (succeeded(checked) && outcome)
    *outcome = {mathematical::VerificationObservation::Verified, {}};
  return checked;
}

} // namespace zkc::protocol
