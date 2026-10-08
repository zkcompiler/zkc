#include "zkc/Transforms/Algorithms.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Dialect/detail/Builders.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Transforms/Protocol.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
Expected<std::string> algorithmSite(const protocol::Assignments &path,
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
  size_t work = 0;
  std::vector<AlgorithmOrigin> origins;

  std::string definition(zkc::local::FuncOp function) {
    if (auto origin = function->getAttrOfType<ArrayAttr>("logical_origin"))
      return cast<StringAttr>(origin[0]).getValue().str();
    return function.getSymName().str();
  }

  LogicalResult body(zkc::local::FuncOp function, Block &block,
                     IRMapping &mapping, StringRef root,
                     protocol::Assignments path, bool encode,
                     SmallVector<Value> &returned) {
    if (path.size() > 64)
      return diagnostics::emit(function.emitOpError(),
                               "interactive-call-depth");
    for (auto &op : block) {
      // Bound traversal as well as output: empty helpers can also form an
      // exponentially large DAG. Admission separately bounds depth/cycles.
      if (++work > 32768)
        return diagnostics::emit(op.emitOpError(), "algorithm-expansion-limit");
      if (auto ret = dyn_cast<zkc::local::ReturnOp>(op)) {
        for (auto value : ret.getOperands())
          returned.push_back(mapping.lookup(value));
      } else if (auto call = dyn_cast<zkc::local::ApplyOp>(op)) {
        auto found = functions.find(call.getCallee().str());
        if (found == functions.end() || found->second.isExternal() ||
            !llvm::hasSingleElement(found->second.getBody()))
          return diagnostics::emit(call.emitOpError(), "algorithm-call-symbol");
        auto callee = found->second;
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
            isa<zkc::local::StopOp>(builder.getInsertionBlock()->back()))
          return success();
        for (auto [old, value] : zip(call.getResults(), results))
          mapping.map(old, value);
      } else if (isa<zkc::local::LocalYieldOp, zkc::local::LocalConditionOp>(
                     op)) {
        builder.clone(op, mapping);
      } else {
        std::string site = attr(&op, "site").str();
        std::string original = site;
        if (encode) {
          auto encoded = algorithmSite(path, site);
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
          if (failed(body(function, before.front(), inner, root, path, encode,
                          ignored)))
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
        origins.push_back(
            {root.str(), site, definition(function), original, path});
        if (definition(function) != function.getSymName())
          origins.push_back(
              {root.str(), site, function.getSymName().str(), original, path});
        if (isa<zkc::local::StopOp>(copy))
          return success();
      }
    }
    return success();
  }

public:
  explicit Expander(ModuleOp original) : builder(original.getContext()) {
    auto root =
        cast<zkc::protocol_ir::ProtocolModuleOp>(&original.getBody()->front());
    for (auto fn : root.getBody().front().getOps<zkc::local::FuncOp>())
      functions.emplace(fn.getSymName().str(), fn);
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
  if (llvm::hasSingleElement(*module.getBody())) {
    auto unit =
        dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
    if (unit && unit.getProfile() == protocol_ir::Profile::Protocol) {
      if (failed(verify(module)))
        return failure();
      bool calls = false;
      unit.walk([&](local::ApplyOp) { calls = true; });
      if (!calls && !origins)
        return success();
      OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(module->clone()));
      Expander expansion(module);
      if (failed(expansion.run(*candidate)) || failed(verify(*candidate)) ||
          failed(verifyAlgorithmExpansionPreserved(module, *candidate)))
        return failure();
      module.getBodyRegion().takeBody(candidate->getBodyRegion());
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
