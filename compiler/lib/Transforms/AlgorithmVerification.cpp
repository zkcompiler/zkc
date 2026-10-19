#include "AlgorithmSupport.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/detail/Builders.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/DenseMap.h"
#include <functional>

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
// Interpret source calls by substitution while reading the actual expanded
// candidate. No IR is emitted and the expansion implementation is not invoked.
class AlgorithmCorrespondence {
  using Values = llvm::DenseMap<Value, Value>;
  SymbolTable symbols;
  AlgorithmExpansionPhase phase;
  const detail::AlgorithmExpansionRecord &input;
  detail::AlgorithmExpansionRecord expected;
  std::string functionName, declarationName, definitionName;
  std::map<std::string, bool> selected;

  // The reader derives retention need from outgoing calls. It does not use
  // the producer's reverse graph or trust a producer selection record.
  LogicalResult select(protocol_ir::ProtocolModuleOp source) {
    std::map<std::string, SmallVector<std::string>> dependencies;
    std::map<std::string, bool> direct;
    for (auto function : source.getBody().front().getOps<local::FuncOp>()) {
      auto name = function.getSymName().str();
      direct[name] = false;
      auto result = function.walk([&](Operation *op) {
        if (op == function.getOperation())
          return WalkResult::advance();
        if (failed(charge(op)))
          return WalkResult::interrupt();
        if (!expected.inspectionWork) {
          diagnostics::emit(op->emitOpError(), "algorithm-expansion-limit");
          return WalkResult::interrupt();
        }
        --expected.inspectionWork;
        if (auto call = dyn_cast<local::ApplyOp>(op)) {
          auto *callee = symbols.lookup(call.getCallee());
          if (isa_and_nonnull<local::FuncOp>(callee)) {
            dependencies[name].push_back(call.getCallee().str());
            direct[name] |= phase == AlgorithmExpansionPhase::Finish;
          } else if (isa_and_nonnull<algebra::MapRealizeOp>(callee) ||
                     (phase == AlgorithmExpansionPhase::RetainMaps &&
                      isa_and_nonnull<local::FiniteFoldOp,
                                      local::FiniteCollectOp>(callee))) {
            direct[name] = true;
          } else {
            (void)refuse(op, "unsupported local callee");
            return WalkResult::interrupt();
          }
        }
        return WalkResult::advance();
      });
      if (result.wasInterrupted())
        return failure();
    }
    std::function<bool(const std::string &)> needsRetention =
        [&](const std::string &name) {
          auto found = selected.find(name);
          if (found != selected.end())
            return found->second;
          bool needed = direct.at(name);
          for (const auto &callee : dependencies[name])
            needed |= needsRetention(callee);
          selected.emplace(name, needed);
          return needed;
        };
    if (phase == AlgorithmExpansionPhase::RetainMaps) {
      for (const auto &entry : direct)
        needsRetention(entry.first);
      // Callback references are separate analysis roots, not ordinary call
      // edges. Resolve them independently of the producer's selected set.
      // block() reads their complete transitive helper substitution; a helper
      // need not be selected as a standalone declaration to be read there.
      auto callback = [&](FlatSymbolRefAttr reference) {
        if (!reference)
          return;
        auto found = dependencies.find(reference.getValue().str());
        if (found != dependencies.end() && !found->second.empty())
          selected[found->first] = true;
      };
      for (auto fold : source.getBody().front().getOps<local::FiniteFoldOp>()) {
        callback(fold.getStepAttr());
        callback(fold.getPredicateAttr());
      }
      for (auto collect :
           source.getBody().front().getOps<local::FiniteCollectOp>()) {
        callback(collect.getBodyAttr());
        callback(collect.getPredicateAttr());
      }
    } else {
      selected = std::move(direct);
    }
    return success();
  }

  LogicalResult refuse(Operation *op, StringRef reason) {
    return diagnostics::emit(op->emitOpError(), "algorithm-correspondence",
                             reason);
  }
  LogicalResult charge(Operation *op) {
    if (!expected.checkWork)
      return diagnostics::emit(op->emitOpError(),
                               "algorithm-correspondence-limit");
    --expected.checkWork;
    return success();
  }
  StringRef definition(local::FuncOp function) {
    if (auto origin = function->getAttrOfType<ArrayAttr>("logical_origin"))
      return cast<StringAttr>(origin[0]).getValue();
    return function.getSymName();
  }
  LogicalResult bind(ValueRange a, ValueRange b, Values &values) {
    if (a.size() != b.size())
      return failure();
    for (auto [x, y] : zip(a, b)) {
      if (x.getType() != y.getType())
        return failure();
      values[x] = y;
    }
    return success();
  }
  // Exact structural/SSA reading of an unchanged declaration. No substitution,
  // capture canonicalization, site renaming or terminal normalization is legal.
  LogicalResult unchanged(Block &source, Block &target, unsigned depth = 0) {
    if (depth > 64)
      return refuse(target.getParentOp(), "preserved region depth");
    Values values;
    if (source.getOperations().size() != target.getOperations().size() ||
        failed(bind(source.getArguments(), target.getArguments(), values)))
      return refuse(target.getParentOp(), "preserved block shape");
    for (auto [op, actual] : zip(source, target)) {
      if (failed(charge(&op)))
        return failure();
      if (op.getName() != actual.getName() ||
          op.getAttrDictionary() != actual.getAttrDictionary() ||
          op.getNumRegions() != actual.getNumRegions() ||
          op.getNumOperands() != actual.getNumOperands())
        return refuse(&actual, "preserved operation");
      for (auto [operand, candidate] :
           zip(op.getOperands(), actual.getOperands()))
        if (values.lookup(operand) != candidate)
          return refuse(&actual, "preserved operand");
      if (failed(bind(op.getResults(), actual.getResults(), values)))
        return refuse(&actual, "preserved results");
      if (op.hasAttr("site")) {
        auto site = attr(&op, "site").str();
        auto saved = detail::occurrence(input, declarationName, site);
        auto record =
            saved ? *saved
                  : detail::AlgorithmOccurrence{
                        definitionName, declarationName, site, {}, depth};
        if (record.path.size() > 64 || record.depth > 64 ||
            (isa<local::ApplyOp>(op) &&
             (record.path.size() >= 64 || record.depth >= 64)))
          return refuse(&actual, "preserved occurrence depth");
        if ((saved || phase == AlgorithmExpansionPhase::Finish) &&
            !expected.occurrences
                 .emplace(detail::OccurrenceKey{functionName, site}, record)
                 .second)
          return refuse(&actual, "duplicate preserved occurrence");
      }
      for (auto [a, b] : zip(op.getRegions(), actual.getRegions())) {
        if (a.getBlocks().size() != b.getBlocks().size())
          return refuse(&actual, "preserved region shape");
        for (auto [x, y] : zip(a, b))
          if (failed(unchanged(x, y, depth + 1)))
            return failure();
      }
    }
    return success();
  }
  // The selected capture indices refer to the original capture list. Aliases
  // introduced by calls identify repeated immutable bindings, not loop state.
  LogicalResult block(Block &source, Block &target, Block::iterator &cursor,
                      Values &values, const protocol::Assignments &path,
                      bool encode, SmallVectorImpl<Value> &returned,
                      bool &stopped, unsigned depth,
                      ArrayRef<unsigned> yieldIndices = {},
                      bool filterYield = false,
                      const protocol::Assignments &invocation = {},
                      unsigned invocationDepth = 0) {
    if (depth > 64)
      return diagnostics::emit(source.getParentOp()->emitOpError(),
                               "algorithm-correspondence-limit");
    for (auto &op : source) {
      if (failed(charge(&op)))
        return failure();
      auto call = dyn_cast<local::ApplyOp>(op);
      auto *callee = call ? symbols.lookup(call.getCallee()) : nullptr;
      bool retainedPreparationRequest =
          isa_and_nonnull<algebra::MapRealizeOp>(callee) ||
          (phase == AlgorithmExpansionPhase::RetainMaps &&
           isa_and_nonnull<local::FiniteFoldOp, local::FiniteCollectOp>(
               callee));
      bool expand = call && !retainedPreparationRequest;
      bool substitution = !invocation.empty() || expand;
      if (substitution && !expected.work)
        return diagnostics::emit(op.emitOpError(), "algorithm-expansion-limit");
      if (substitution)
        --expected.work;
      auto saved =
          detail::occurrence(input, declarationName, attr(&op, "site"));
      auto currentPath = saved ? invocation : path;
      if (saved)
        currentPath.insert(currentPath.end(), saved->path.begin(),
                           saved->path.end());
      auto originalSite = saved ? saved->originalSite : attr(&op, "site").str();
      unsigned currentDepth = saved ? invocationDepth + saved->depth : depth;
      if (currentPath.size() > 64 || currentDepth > 64)
        return refuse(&op, "expanded occurrence depth");
      if (auto ret = dyn_cast<local::ReturnOp>(op)) {
        for (auto value : ret.getOperands()) {
          auto mapped = values.lookup(value);
          if (!mapped)
            return refuse(&op, "unbound return");
          returned.push_back(mapped);
        }
        return success();
      }
      if (expand) {
        auto callee = symbols.lookup<local::FuncOp>(call.getCallee());
        if (!callee || !callee.getBody().hasOneBlock())
          return refuse(&op, "missing local body");
        Values inner;
        for (auto [argument, operand] :
             zip(callee.getArguments(), call.getOperands())) {
          auto mapped = values.lookup(operand);
          if (!mapped)
            return refuse(&op, "unbound actual argument");
          inner[argument] = mapped;
        }
        auto nested = currentPath;
        nested.emplace_back(originalSite, definition(callee).str());
        auto oldDeclaration = declarationName, oldDefinition = definitionName;
        declarationName = callee.getSymName().str();
        definitionName = definition(callee).str();
        SmallVector<Value> results;
        if (failed(block(callee.getBody().front(), target, cursor, inner,
                         nested, true, results, stopped, currentDepth + 1, {},
                         false, nested, currentDepth + 1)))
          return failure();
        declarationName = std::move(oldDeclaration);
        definitionName = std::move(oldDefinition);
        if (stopped)
          return success();
        if (failed(bind(call.getResults(), results, values)))
          return refuse(&op, "call result substitution");
        continue;
      }
      if (cursor == target.end())
        return refuse(&op, "missing expanded operation");
      Operation &actual = *cursor++;
      bool removedResults = isa<local::LocalIfOp, local::LocalMatchOp>(op) &&
                            actual.getNumResults() == 0;
      if (op.getName() != actual.getName() ||
          op.getNumRegions() != actual.getNumRegions() ||
          (!removedResults && op.getResultTypes() != actual.getResultTypes()))
        return refuse(&actual, "operation identity");
      NamedAttrList attributes(op.getAttrs());
      if (isa<local::ApplyOp>(op) &&
          (currentDepth >= 64 || currentPath.size() >= 64))
        return refuse(&op, "retained map call depth");
      if (encode && (!saved || !invocation.empty()) && op.hasAttr("site")) {
        auto site =
            algorithmSite(currentPath, originalSite, expected.checkOriginBytes);
        if (!site)
          return diagnostics::emit(actual.emitOpError(), site.takeError());
        // Producer and checker have independent cumulative encoding budgets.
        auto measured =
            algorithmSite(currentPath, originalSite, expected.originBytes);
        if (!measured)
          return diagnostics::emit(actual.emitOpError(), measured.takeError());
        attributes.set("site", StringAttr::get(op.getContext(), *site));
      }
      if (attributes.getDictionary(op.getContext()) !=
          actual.getAttrDictionary())
        return refuse(&actual, "operation attributes");
      if (op.hasAttr("site")) {
        auto record = saved ? *saved
                            : detail::AlgorithmOccurrence{
                                  definitionName, declarationName, originalSite,
                                  currentPath, currentDepth};
        record.path = currentPath;
        record.depth = currentDepth;
        if (!expected.occurrences
                 .emplace(detail::OccurrenceKey{functionName,
                                                attr(&actual, "site").str()},
                          std::move(record))
                 .second)
          return refuse(&actual, "duplicate occurrence record");
      }
      SmallVector<Value> operands;
      for (Value operand : op.getOperands()) {
        Value mapped = values.lookup(operand);
        if (!mapped)
          return refuse(&op, "unbound operand");
        operands.push_back(mapped);
      }
      bool control =
          isa<local::LocalIfOp, local::LocalMatchOp, local::LocalForOp>(op);
      unsigned prefix = isa<local::LocalForOp>(op) ? 2 + op.getNumResults() : 1;
      SmallVector<unsigned> retained;
      SmallVector<unsigned> captureMap;
      if (control) {
        SmallVector<Value> unique;
        llvm::DenseMap<Value, unsigned> coordinates;
        for (unsigned i = prefix; i < operands.size(); ++i) {
          if (failed(charge(&op)))
            return failure();
          auto [found, inserted] =
              coordinates.try_emplace(operands[i], unique.size());
          if (inserted) {
            captureMap.push_back(unique.size());
            retained.push_back(i - prefix);
            unique.push_back(operands[i]);
          } else {
            auto type = encodeBoundType(operands[i].getType(), false);
            if (!type)
              return diagnostics::emit(op.emitOpError(), type.takeError());
            if (!duplicable(type->spelling()))
              return refuse(&op, "nonduplicable capture alias");
            captureMap.push_back(found->second);
          }
        }
        operands.resize(prefix);
        append_range(operands, unique);
      } else if (filterYield &&
                 isa<local::LocalYieldOp, local::LocalConditionOp>(op)) {
        SmallVector<Value> selected;
        unsigned condition = isa<local::LocalConditionOp>(op) ? 1 : 0;
        if (condition)
          selected.push_back(operands.front());
        for (unsigned index : yieldIndices) {
          if (index + condition >= operands.size())
            return refuse(&op, "yield coordinate");
          selected.push_back(operands[index + condition]);
        }
        operands = std::move(selected);
      }
      if (!llvm::equal(operands, actual.getOperands()))
        return refuse(&actual, "operand correspondence");
      bool allStopped = !op.getRegions().empty();
      for (auto [a, b] : zip(op.getRegions(), actual.getRegions())) {
        if (!a.hasOneBlock() || !b.hasOneBlock())
          return refuse(&actual, "region shape");
        auto &before = a.front();
        auto &after = b.front();
        Values inner;
        if (control) {
          unsigned captures = captureMap.size();
          if (before.getNumArguments() < captures)
            return refuse(&op, "capture arguments");
          unsigned start = before.getNumArguments() - captures;
          if (after.getNumArguments() != start + retained.size())
            return refuse(&actual, "capture arguments");
          for (unsigned i = 0; i < before.getNumArguments(); ++i) {
            unsigned j = i < start ? i : start + captureMap[i - start];
            if (before.getArgument(i).getType() !=
                after.getArgument(j).getType())
              return refuse(&actual, "region argument type");
            inner[before.getArgument(i)] = after.getArgument(j);
          }
        } else if (failed(bind(before.getArguments(), after.getArguments(),
                               inner)))
          return refuse(&actual, "region arguments");
        SmallVector<unsigned> yields;
        if (isa<local::LocalForOp>(op)) {
          for (unsigned i = 0; i < op.getNumResults(); ++i)
            yields.push_back(i);
          for (unsigned i : retained)
            yields.push_back(op.getNumResults() + i);
        }
        auto position = after.begin();
        SmallVector<Value> ignored;
        bool terminated = false;
        if (failed(block(before, after, position, inner, currentPath, encode,
                         ignored, terminated, currentDepth + 1, yields,
                         isa<local::LocalForOp>(op), invocation,
                         invocationDepth)) ||
            position != after.end())
          return refuse(&actual, "region body correspondence");
        allStopped &= terminated;
      }
      if (isa<local::LocalIfOp, local::LocalMatchOp>(op) && allStopped) {
        if (actual.getNumResults() || cursor == target.end())
          return refuse(&actual, "terminal control results");
        auto unreachable = dyn_cast<local::StopOp>(*cursor++);
        if (!unreachable || unreachable.getReason() != "abort" ||
            !unreachable.getSite().starts_with("unreachable_"))
          return refuse(&actual, "missing unreachable terminator");
        stopped = true;
        return success();
      }
      if (failed(bind(op.getResults(), actual.getResults(), values)))
        return refuse(&actual, "result correspondence");
      if (isa<local::StopOp>(op)) {
        stopped = true;
        return success();
      }
    }
    return success();
  }

public:
  AlgorithmCorrespondence(protocol_ir::ProtocolModuleOp source,
                          AlgorithmExpansionPhase phase,
                          const detail::AlgorithmExpansionRecord &input)
      : symbols(source), phase(phase), input(input), expected(input) {
    expected.occurrences.clear();
    expected.retained = phase == AlgorithmExpansionPhase::RetainMaps;
    expected.finished = phase == AlgorithmExpansionPhase::Finish;
  }
  const detail::AlgorithmExpansionRecord &result() const { return expected; }
  LogicalResult initialize(protocol_ir::ProtocolModuleOp source) {
    return select(source);
  }
  LogicalResult function(local::FuncOp before, local::FuncOp after) {
    if (before->getAttrDictionary() != after->getAttrDictionary() ||
        before.isExternal() != after.isExternal())
      return refuse(after, "function declaration");
    if (before.isExternal())
      return success();
    if (!before.getBody().hasOneBlock() || !after.getBody().hasOneBlock())
      return refuse(after, "function body");
    functionName = before.getSymName().str();
    declarationName = functionName;
    definitionName = definition(before).str();
    if (!selected.at(functionName))
      return unchanged(before.getBody().front(), after.getBody().front());
    Values values;
    if (failed(bind(before.getArguments(), after.getArguments(), values)))
      return refuse(after, "function arguments");
    bool encode = false;
    before.walk([&](local::ApplyOp) { encode = true; });
    auto &target = after.getBody().front();
    auto position = target.begin();
    SmallVector<Value> returned;
    bool stopped = false;
    if (failed(block(before.getBody().front(), target, position, values, {},
                     encode, returned, stopped, 0)))
      return failure();
    if (!stopped) {
      if (position == target.end())
        return refuse(after, "missing return");
      auto ret = dyn_cast<local::ReturnOp>(*position++);
      if (!ret || !ret->getAttrs().empty() ||
          !llvm::equal(returned, ret.getOperands()))
        return refuse(after, "function return");
    }
    return position == target.end() ? success()
                                    : refuse(after, "extra operation");
  }
};
} // namespace
LogicalResult detail::checkAlgorithmExpansion(
    ModuleOp before, ModuleOp after, AlgorithmExpansionPhase phase,
    const AlgorithmExpansionRecord &input, AlgorithmExpansionRecord &output,
    bool compareRecords) {
  if (failed(verify(before)) || failed(verify(after)))
    return failure();
  auto refuse = [&] {
    return diagnostics::emit(after.emitError(), "algorithm-correspondence");
  };
  if (input.finished ||
      (phase == AlgorithmExpansionPhase::RetainMaps && input.retained))
    return refuse();
  if (before->getAttrDictionary() != after->getAttrDictionary() ||
      !hasSingleElement(*before.getBody()) ||
      !hasSingleElement(*after.getBody()))
    return refuse();
  auto a = dyn_cast<protocol_ir::ProtocolModuleOp>(before.getBody()->front());
  auto b = dyn_cast<protocol_ir::ProtocolModuleOp>(after.getBody()->front());
  if (!a || !b || a->getAttrDictionary() != b->getAttrDictionary() ||
      a.getBody().front().getOperations().size() !=
          b.getBody().front().getOperations().size())
    return refuse();
  if (a.getProfile() != protocol_ir::Profile::Protocol)
    return refuse();
  uint64_t remaining = 1000000;
  if (auto error = mathematical::checkMapFormulas(before, remaining)) {
    consumeError(std::move(error));
    return refuse();
  }
  if (phase == AlgorithmExpansionPhase::Finish) {
    for (Operation &op : a.getBody().front())
      if (isa<PreparationCallableOpInterface>(op) &&
          !isa<algebra::MapRealizeOp>(op))
        return refuse();
  }
  AlgorithmCorrespondence check(a, phase, input);
  if (failed(check.initialize(a)))
    return failure();
  for (auto [x, y] : zip(a.getBody().front(), b.getBody().front())) {
    if (auto function = dyn_cast<local::FuncOp>(x)) {
      auto candidate = dyn_cast<local::FuncOp>(y);
      if (!candidate || failed(check.function(function, candidate)))
        return failure();
    } else if (!OperationEquivalence::isEquivalentTo(
                   &x, &y, OperationEquivalence::IgnoreLocations))
      return refuse();
  }
  const auto &expected = check.result();
  if (compareRecords && !expected.sameExpansion(output))
    return refuse();
  output.checkWork = expected.checkWork;
  output.checkOriginBytes = expected.checkOriginBytes;
  return success();
}

LogicalResult verifyAlgorithmExpansionPreserved(ModuleOp before,
                                                ModuleOp after) {
  detail::AlgorithmExpansionRecord input, output;
  return detail::checkAlgorithmExpansion(
      before, after, AlgorithmExpansionPhase::Finish, input, output, false);
}

LogicalResult verifyStagedAlgorithmExpansionPreserved(
    ModuleOp before, ModuleOp after, AlgorithmExpansionPhase phase,
    const AlgorithmExpansionState &beforeState,
    const AlgorithmExpansionState &afterState) {
  auto output = detail::AlgorithmStateAccess::get(afterState);
  return detail::checkAlgorithmExpansion(
      before, after, phase, detail::AlgorithmStateAccess::get(beforeState),
      output, true);
}
} // namespace zkc::protocol
