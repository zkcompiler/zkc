#include "AlgorithmSupport.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Dialect/detail/Builders.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Transforms/Protocol.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
Expected<std::string> algorithmSite(const protocol::Assignments &path,
                                    StringRef site, uint64_t &remainingBytes) {
  uint64_t size = 2;
  auto measure = [&](StringRef value) {
    uint64_t prefix = 2 + std::to_string(value.size()).size();
    if (size > remainingBytes || prefix > remainingBytes - size ||
        value.size() > remainingBytes - size - prefix)
      return false;
    size += prefix + value.size();
    return true;
  };
  for (const auto &[call, callee] : path)
    if (!measure(call) || !measure(callee))
      return error("algorithm-origin-limit");
  if (!measure(site))
    return error("algorithm-origin-limit");
  remainingBytes -= size;
  std::string result = "lc";
  result.reserve(size);
  auto append = [&](StringRef value) {
    result += "_" + std::to_string(value.size()) + "_" + value.str();
  };
  for (const auto &[call, callee] : path) {
    append(call);
    append(callee);
  }
  append(site);
  if (result.size() > 128)
    return "lc_h_" + toHex(SHA256::hash(arrayRefFromStringRef(result)), true);
  return result;
}
namespace {
// Inlining an identity helper can make two admitted, distinct capture bindings
// alias one SSA value. Retain its first occurrence and rewrite the region's
// arguments together. Recurse after rewriting: aliases can reach inner regions.
LogicalResult canonicalizeCaptures(Operation *op) {
  if (isa<zkc::local::LocalIfOp, zkc::local::LocalMatchOp,
          zkc::local::LocalForOp>(op)) {
    unsigned prefix =
        isa<zkc::local::LocalForOp>(op) ? 2 + op->getNumResults() : 1;
    unsigned captures = op->getNumOperands() - prefix;
    for (unsigned i = captures; i-- > 0;) {
      Value value = op->getOperand(prefix + i);
      unsigned first = 0;
      while (first < i && op->getOperand(prefix + first) != value)
        ++first;
      if (first == i)
        continue;
      auto type = encodeBoundType(value.getType(), false);
      if (!type)
        return diagnostics::emit(op->emitOpError(), type.takeError());
      if (!duplicable(type->spelling()))
        return diagnostics::emit(op->emitOpError(),
                                 "interactive-resource-reuse");
      for (Region &region : op->getRegions()) {
        Block &block = region.front();
        unsigned start = block.getNumArguments() - captures;
        block.getArgument(start + i).replaceAllUsesWith(
            block.getArgument(start + first));
        if (isa<zkc::local::LocalForOp>(op) &&
            isa<zkc::local::LocalYieldOp, zkc::local::LocalConditionOp>(
                block.back()))
          block.back().eraseOperand(
              op->getNumResults() + i +
              (isa<zkc::local::LocalConditionOp>(block.back()) ? 1 : 0));
        block.eraseArgument(start + i);
      }
      op->eraseOperand(prefix + i);
      --captures;
    }
  }
  for (Region &region : op->getRegions())
    for (Block &block : region)
      for (Operation &nested : block)
        if (failed(canonicalizeCaptures(&nested)))
          return failure();
  return success();
}

class Expander {
  OpBuilder builder;
  std::map<std::string, zkc::local::FuncOp> functions;
  AlgorithmExpansionPhase phase;
  const detail::AlgorithmExpansionRecord &input;
  detail::AlgorithmExpansionRecord output;
  std::map<std::string, algebra::MapRealizeOp> maps;
  std::vector<AlgorithmOrigin> origins;

  std::string definition(zkc::local::FuncOp function) {
    if (auto origin = function->getAttrOfType<ArrayAttr>("logical_origin"))
      return cast<StringAttr>(origin[0]).getValue().str();
    return function.getSymName().str();
  }

  LogicalResult body(zkc::local::FuncOp function, Block &block,
                     IRMapping &mapping, StringRef root,
                     protocol::Assignments path, bool encode,
                     SmallVector<Value> &returned, unsigned depth = 0) {
    if (path.size() > 64 || depth > 64)
      return diagnostics::emit(function.emitOpError(),
                               "interactive-call-depth");
    for (auto &op : block) {
      // Bound traversal as well as output: empty helpers can also form an
      // exponentially large DAG. Admission separately bounds depth/cycles.
      if (!output.work)
        return diagnostics::emit(op.emitOpError(), "algorithm-expansion-limit");
      --output.work;
      auto saved =
          detail::occurrence(input, function.getSymName(), attr(&op, "site"));
      auto currentPath = saved ? saved->path : path;
      auto originalSite = saved ? saved->originalSite : attr(&op, "site").str();
      unsigned currentDepth = saved ? saved->depth : depth;
      if (currentPath.size() > 64 || currentDepth > 64)
        return diagnostics::emit(op.emitOpError(), "interactive-call-depth");
      if (auto ret = dyn_cast<zkc::local::ReturnOp>(op)) {
        for (auto value : ret.getOperands())
          returned.push_back(mapping.lookup(value));
      } else if (auto call = dyn_cast<zkc::local::ApplyOp>(op);
                 call && !(phase == AlgorithmExpansionPhase::RetainMaps &&
                           maps.count(call.getCallee().str()))) {
        auto found = functions.find(call.getCallee().str());
        if (found == functions.end() || found->second.isExternal() ||
            !llvm::hasSingleElement(found->second.getBody()))
          return diagnostics::emit(call.emitOpError(), "algorithm-call-symbol");
        auto callee = found->second;
        IRMapping inner;
        for (auto [arg, value] : zip(callee.getArguments(), call.getOperands()))
          inner.map(arg, mapping.lookup(value));
        auto nested = currentPath;
        nested.emplace_back(originalSite, definition(callee));
        SmallVector<Value> results;
        if (failed(body(callee, callee.getBody().front(), inner, root,
                        std::move(nested), true, results, currentDepth + 1)))
          return failure();
        if (!builder.getInsertionBlock()->empty() &&
            isa<zkc::local::StopOp>(builder.getInsertionBlock()->back()))
          return success();
        for (auto [old, value] : zip(call.getResults(), results))
          mapping.map(old, value);
      } else if (isa<zkc::local::LocalYieldOp, zkc::local::LocalConditionOp>(
                     op)) {
        builder.clone(op, mapping);
      } else {
        std::string site = attr(&op, "site").str();
        std::string original = originalSite;
        if (isa<local::ApplyOp>(op) &&
            (currentPath.size() >= 64 || currentDepth >= 64))
          return diagnostics::emit(op.emitOpError(), "interactive-call-depth");
        if (encode && !saved) {
          auto encoded =
              algorithmSite(currentPath, original, output.originBytes);
          if (!encoded)
            return diagnostics::emit(op.emitOpError(), encoded.takeError());
          site = std::move(*encoded);
        }
        auto *copy = builder.cloneWithoutRegions(op, mapping);
        for (auto [before, after] : zip(op.getRegions(), copy->getRegions())) {
          auto *nestedBlock = new Block();
          after.push_back(nestedBlock);
          IRMapping inner;
          for (auto arg : before.front().getArguments())
            inner.map(arg,
                      nestedBlock->addArgument(arg.getType(), arg.getLoc()));
          OpBuilder::InsertionGuard guard(builder);
          builder.setInsertionPointToEnd(nestedBlock);
          SmallVector<Value> ignored;
          if (failed(body(function, before.front(), inner, root, currentPath,
                          encode, ignored, currentDepth + 1)))
            return failure();
        }
        if (op.hasAttr("site"))
          copy->setAttr("site", builder.getStringAttr(site));
        // Specialization can make every continuing arm stop. Until expansion
        // can rebuild the surrounding result-less region and continuation,
        // refuse at the actual control operation rather than emit undefined
        // results that fail later during source export.
        if (isa<zkc::local::LocalIfOp, zkc::local::LocalMatchOp>(copy) &&
            copy->getNumResults() &&
            llvm::all_of(copy->getRegions(), [](Region &region) {
              return isa<zkc::local::StopOp>(region.front().back());
            }))
          return diagnostics::emit(copy->emitOpError(),
                                   "algorithm-terminal-results");
        // Cloning retains the leaf diagnostic location. The checked site path
        // carries the nested occurrence separately from diagnostic metadata.
        auto record =
            saved ? *saved
                  : detail::AlgorithmOccurrence{
                        definition(function), function.getSymName().str(),
                        original, currentPath, currentDepth};
        if (op.hasAttr("site"))
          output.occurrences.emplace(detail::OccurrenceKey{root.str(), site},
                                     record);
        origins.push_back(
            {root.str(), site, record.definition, original, currentPath});
        if (record.definition != record.declaration)
          origins.push_back(
              {root.str(), site, record.declaration, original, currentPath});
        if (isa<zkc::local::StopOp>(copy))
          return success();
      }
    }
    return success();
  }

public:
  Expander(ModuleOp original, AlgorithmExpansionPhase phase,
           const detail::AlgorithmExpansionRecord &input)
      : builder(original.getContext()), phase(phase), input(input),
        output(input) {
    output.occurrences.clear();
    auto root =
        cast<zkc::protocol_ir::ProtocolModuleOp>(&original.getBody()->front());
    for (auto fn : root.getBody().front().getOps<zkc::local::FuncOp>())
      functions.emplace(fn.getSymName().str(), fn);
    for (auto map : root.getBody().front().getOps<algebra::MapRealizeOp>())
      maps.emplace(map.getSymName().str(), map);
  }
  LogicalResult run(ModuleOp candidate) {
    auto root =
        cast<zkc::protocol_ir::ProtocolModuleOp>(&candidate.getBody()->front());
    for (auto fn : root.getBody().front().getOps<zkc::local::FuncOp>()) {
      if (fn.isExternal())
        continue;
      auto original = functions.at(fn.getSymName().str());
      bool calls = false;
      original.walk([&](zkc::local::ApplyOp) { calls = true; });
      auto &block = fn.getBody().front();
      block.dropAllReferences();
      block.getOperations().clear();
      builder.setInsertionPointToEnd(&block);
      IRMapping mapping;
      for (auto [old, value] : zip(original.getArguments(), fn.getArguments()))
        mapping.map(old, value);
      SmallVector<Value> returned;
      if (failed(body(original, original.getBody().front(), mapping,
                      fn.getSymName(), {}, calls, returned)))
        return failure();
      if (block.empty() || !isa<zkc::local::StopOp>(block.back()))
        zkc::local::ReturnOp::create(
            builder, original.getBody().front().back().getLoc(), returned);
      if (failed(canonicalizeCaptures(fn)))
        return failure();
    }
    return success();
  }
  detail::AlgorithmExpansionRecord takeRecord() {
    output.retained = phase == AlgorithmExpansionPhase::RetainMaps;
    output.finished = phase == AlgorithmExpansionPhase::Finish;
    return std::move(output);
  }
  std::vector<AlgorithmOrigin> takeOrigins() { return std::move(origins); }
};
struct AlgorithmExpansionPass
    : PassWrapper<AlgorithmExpansionPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(AlgorithmExpansionPass)
  StringRef getArgument() const final { return "zkc-expand-algorithms"; }
  StringRef getDescription() const final {
    return "Expand acyclic local SSA calls under canonical local accounting";
  }
  void runOnOperation() final {
    if (failed(expandAlgorithms(getOperation())))
      signalPassFailure();
  }
};
} // namespace
LogicalResult expandAlgorithms(ModuleOp module,
                               std::vector<AlgorithmOrigin> *origins) {
  AlgorithmExpansionState state;
  return expandAlgorithms(module, AlgorithmExpansionPhase::Finish, state,
                          origins);
}

LogicalResult expandAlgorithms(ModuleOp module, AlgorithmExpansionPhase phase,
                               AlgorithmExpansionState &state,
                               std::vector<AlgorithmOrigin> *origins) {
  const auto &input = detail::AlgorithmStateAccess::get(state);
  if (input.finished ||
      (phase == AlgorithmExpansionPhase::RetainMaps && input.retained))
    return diagnostics::emit(module.emitError(), "algorithm-expansion-stage");
  if (llvm::hasSingleElement(*module.getBody())) {
    auto unit =
        dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
    if (unit && unit.getProfile() == protocol_ir::Profile::Protocol) {
      if (failed(verify(module)))
        return failure();
      if (phase == AlgorithmExpansionPhase::RetainMaps) {
        // Admission explicitly names maps and checks all expanded scalar work.
        // A preparation interface by itself never authorizes atomic retention.
        uint64_t remaining = 1000000;
        if (auto error = mathematical::checkMapFormulas(module, remaining))
          return diagnostics::emit(module.emitError(), std::move(error));
      } else {
        for (Operation &op : unit.getBody().front())
          if (isa<PreparationCallableOpInterface>(op))
            return diagnostics::emit(
                op.emitOpError(), "algorithm-call-symbol",
                "Finish requires realized preparation declarations");
      }
      bool calls = false;
      unit.walk([&](local::ApplyOp) { calls = true; });
      if (!calls && !origins && !input.retained &&
          phase == AlgorithmExpansionPhase::Finish)
        return success();
      OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(module->clone()));
      Expander expansion(module, phase, input);
      if (failed(expansion.run(*candidate)) || failed(verify(*candidate)))
        return failure();
      auto output = expansion.takeRecord();
      if (failed(detail::checkAlgorithmExpansion(module, *candidate, phase,
                                                 input, output, true)))
        return failure();
      module.getBodyRegion().takeBody(candidate->getBodyRegion());
      detail::AlgorithmStateAccess::set(state, std::move(output));
      if (origins)
        *origins = expansion.takeOrigins();
      return success();
    }
  }
  return diagnostics::emit(module.emitError(), "algorithm-expansion-stage");
}

std::unique_ptr<Pass> createExpandAlgorithmsPass() {
  return std::make_unique<AlgorithmExpansionPass>();
}
} // namespace zkc::protocol
