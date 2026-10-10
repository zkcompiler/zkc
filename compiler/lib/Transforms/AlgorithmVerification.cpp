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
#include "llvm/ADT/DenseMap.h"

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
  // The selected capture indices refer to the original capture list. Aliases
  // introduced by calls identify repeated immutable bindings, not loop state.
  LogicalResult block(Block &source, Block &target, Block::iterator &cursor,
                      Values &values, const protocol::Assignments &path,
                      bool encode, SmallVectorImpl<Value> &returned,
                      bool &stopped, unsigned depth,
                      ArrayRef<unsigned> yieldIndices = {},
                      bool filterYield = false) {
    if (depth > 64)
      return diagnostics::emit(source.getParentOp()->emitOpError(),
                               "algorithm-correspondence-limit");
    for (auto &op : source) {
      if (failed(charge(&op)))
        return failure();
      if (!expected.work)
        return diagnostics::emit(op.emitOpError(), "algorithm-expansion-limit");
      --expected.work;
      auto saved =
          detail::occurrence(input, declarationName, attr(&op, "site"));
      auto currentPath = saved ? saved->path : path;
      auto originalSite = saved ? saved->originalSite : attr(&op, "site").str();
      unsigned currentDepth = saved ? saved->depth : depth;
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
      if (auto call = dyn_cast<local::ApplyOp>(op);
          call && !(phase == AlgorithmExpansionPhase::RetainMaps &&
                    symbols.lookup<algebra::MapRealizeOp>(call.getCallee()))) {
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
                         nested, true, results, stopped, currentDepth + 1)))
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
      if (op.getName() != actual.getName() ||
          op.getNumRegions() != actual.getNumRegions() ||
          op.getResultTypes() != actual.getResultTypes())
        return refuse(&actual, "operation identity");
      NamedAttrList attributes(op.getAttrs());
      if (isa<local::ApplyOp>(op) &&
          (currentDepth >= 64 || currentPath.size() >= 64))
        return refuse(&op, "retained map call depth");
      if (encode && !saved && op.hasAttr("site")) {
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
                         isa<local::LocalForOp>(op))) ||
            position != after.end())
          return refuse(&actual, "region body correspondence");
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
  AlgorithmCorrespondence check(a, phase, input);
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
  if (compareRecords && (expected.occurrences != output.occurrences ||
                         expected.work != output.work ||
                         expected.originBytes != output.originBytes ||
                         expected.retained != output.retained ||
                         expected.finished != output.finished))
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
