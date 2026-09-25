#include "zkc/Protocol/Algorithms.h"
#include "Support.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Protocol/Bindings.h"
#include "zkc/Protocol/TypeProperties.h"
#include "zkc/Transforms/Passes.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
Expected<std::string> algorithmSite(const source::Assignments &path,
                                    StringRef site) {
  std::string result = "lc";
  auto append = [&](StringRef value) {
    result += "_" + std::to_string(value.size()) + "_" + value.str();
  };
  for (const auto &[call, callee] : path) {
    append(call);
    append(callee);
  }
  append(site);
  if (result.size() > 128)
    return error("algorithm-origin-limit");
  return result;
}
namespace {
// Inlining an identity helper can make two admitted, distinct capture bindings
// alias one SSA value. Retain its first occurrence and rewrite the region's
// arguments together. Recurse after rewriting: aliases can reach inner regions.
LogicalResult canonicalizeCaptures(Operation *op) {
  if (isa<LocalIfOp, LocalMatchOp, LocalForOp>(op)) {
    unsigned prefix = isa<LocalForOp>(op) ? 2 + op->getNumResults() : 1;
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
        return op->emitOpError(toString(type.takeError()));
      if (!duplicable(type->spelling()))
        return op->emitOpError("interactive-resource-reuse");
      for (Region &region : op->getRegions()) {
        Block &block = region.front();
        unsigned start = block.getNumArguments() - captures;
        block.getArgument(start + i).replaceAllUsesWith(
            block.getArgument(start + first));
        if (isa<LocalForOp>(op) && isa<LocalYieldOp>(block.back()))
          block.back().eraseOperand(op->getNumResults() + i);
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
  std::map<std::string, func::FuncOp> functions;
  size_t work = 0;
  std::vector<AlgorithmOrigin> origins;

  std::string definition(func::FuncOp function) {
    if (auto origin = function->getAttrOfType<ArrayAttr>("logical_origin"))
      return cast<StringAttr>(origin[0]).getValue().str();
    return function.getSymName().str();
  }

  LogicalResult body(func::FuncOp function, Block &block, IRMapping &mapping,
                     StringRef root, source::Assignments path, bool encode,
                     SmallVector<Value> &returned) {
    for (auto &op : block) {
      // Bound traversal as well as output: empty helpers can also form an
      // exponentially large DAG. Admission separately bounds depth/cycles.
      if (++work > 32768)
        return op.emitOpError("algorithm-expansion-limit");
      if (auto ret = dyn_cast<func::ReturnOp>(op)) {
        for (auto value : ret.getOperands())
          returned.push_back(mapping.lookup(value));
      } else if (auto call = dyn_cast<func::CallOp>(op)) {
        auto callee = functions.at(call.getCallee().str());
        IRMapping inner;
        for (auto [arg, value] : zip(callee.getArguments(), call.getOperands()))
          inner.map(arg, mapping.lookup(value));
        auto nested = path;
        nested.emplace_back(attr(&op, "site").str(), definition(callee));
        SmallVector<Value> results;
        if (failed(body(callee, callee.getBody().front(), inner, root,
                        std::move(nested), true, results)))
          return failure();
        if (!builder.getInsertionBlock()->empty() &&
            isa<HaltOp>(builder.getInsertionBlock()->back()))
          return success();
        for (auto [old, value] : zip(call.getResults(), results))
          mapping.map(old, value);
      } else if (isa<LocalYieldOp>(op)) {
        builder.clone(op, mapping);
      } else {
        std::string site = attr(&op, "site").str();
        std::string original = site;
        if (encode) {
          auto encoded = algorithmSite(path, site);
          if (!encoded)
            return op.emitOpError(toString(encoded.takeError()));
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
          if (failed(body(function, before.front(), inner, root, path, encode,
                          ignored)))
            return failure();
        }
        copy->setAttr("site", builder.getStringAttr(site));
        // Specialization can make every continuing arm stop. Until expansion
        // can rebuild the surrounding result-less region and continuation,
        // refuse at the actual control operation rather than emit undefined
        // results that fail later during source export.
        if (isa<LocalIfOp, LocalMatchOp>(copy) && copy->getNumResults() &&
            llvm::all_of(copy->getRegions(), [](Region &region) {
              return isa<HaltOp>(region.front().back());
            }))
          return copy->emitOpError("algorithm-terminal-results");
        // Cloning retains the leaf diagnostic location. The checked site path
        // carries the nested occurrence separately from diagnostic metadata.
        origins.push_back(
            {root.str(), site, definition(function), original, path});
        if (definition(function) != function.getSymName())
          origins.push_back(
              {root.str(), site, function.getSymName().str(), original, path});
        if (isa<HaltOp>(copy))
          return success();
      }
    }
    return success();
  }

public:
  explicit Expander(ModuleOp original) : builder(original.getContext()) {
    auto root = cast<ProtocolModuleOp>(&original.getBody()->front());
    for (auto fn : root.getBody().front().getOps<func::FuncOp>())
      functions.emplace(fn.getSymName().str(), fn);
  }
  LogicalResult run(ModuleOp candidate) {
    auto root = cast<ProtocolModuleOp>(&candidate.getBody()->front());
    for (auto fn : root.getBody().front().getOps<func::FuncOp>()) {
      if (fn.isExternal())
        continue;
      auto original = functions.at(fn.getSymName().str());
      bool calls = false;
      original.walk([&](func::CallOp) { calls = true; });
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
      if (block.empty() || !isa<HaltOp>(block.back()))
        func::ReturnOp::create(
            builder, original.getBody().front().back().getLoc(), returned);
      if (failed(canonicalizeCaptures(fn)))
        return failure();
    }
    return success();
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
  auto source = exportSource(module);
  if (!source)
    return module.emitError(toString(source.takeError()));
  auto *common = std::get_if<source::Module>(&*source);
  if (!common)
    return module.emitError("algorithm-expansion-stage");
  if (auto e = admit(*common, true))
    return module.emitError(toString(std::move(e)));
  bool calls = false;
  for (const auto &fn : common->functions)
    if (fn.body)
      source::walk(*fn.body, [&](const source::Instruction &ins) {
        calls |= ins.get<source::AlgorithmCall>() != nullptr;
      });
  if (!calls && !origins)
    return success();
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(module->clone()));
  Expander expansion(module);
  if (failed(expansion.run(*candidate)) || failed(verify(*candidate)))
    return failure();
  // Do not expose partial rewrites on failure.
  module.getBodyRegion().takeBody(candidate->getBodyRegion());
  if (origins)
    *origins = expansion.takeOrigins();
  return success();
}
Expected<ExpandedAlgorithms> expandAlgorithms(const source::Module &source,
                                              MLIRContext &context) {
  auto module = importModule(source, context);
  if (!module)
    return module.takeError();
  std::vector<AlgorithmOrigin> origins;
  if (failed(expandAlgorithms(**module, &origins)))
    return error("algorithm-expansion-failed");
  auto result = exportSource(**module);
  if (!result)
    return result.takeError();
  auto expanded = source;
  expanded.functions = std::get<source::Module>(std::move(*result)).functions;
  return ExpandedAlgorithms{std::move(expanded), std::move(origins)};
}
std::unique_ptr<Pass> createExpandAlgorithmsPass() {
  return std::make_unique<AlgorithmExpansionPass>();
}
} // namespace zkc::protocol
