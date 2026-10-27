#include "AlgorithmSupport.h"
#include "CheckedCandidate.h"
#include "RealizationTrace.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/detail/Builders.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Protocol.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"
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
// Inlining an identity helper can make two admitted, distinct capture bindings
// alias one SSA value. Retain its first occurrence and rewrite the region's
// arguments together. Recurse after rewriting: aliases can reach inner regions.
LogicalResult detail::canonicalizeCaptures(Operation *op) {
  if (isa<zkc::local::LocalIfOp, zkc::local::LocalMatchOp,
          zkc::local::LocalForOp>(op)) {
    unsigned prefix =
        isa<zkc::local::LocalForOp>(op) ? 2 + op->getNumResults() : 1;
    unsigned captures = op->getNumOperands() - prefix;
    llvm::DenseMap<Value, unsigned> firstOccurrences;
    SmallVector<std::pair<unsigned, unsigned>> aliases;
    for (unsigned i = 0; i < captures; ++i) {
      Value value = op->getOperand(prefix + i);
      auto [first, inserted] = firstOccurrences.try_emplace(value, i);
      if (inserted)
        continue;
      auto type = encodeBoundType(value.getType(), false);
      if (!type)
        return diagnostics::emit(op->emitOpError(), type.takeError());
      if (!duplicable(type->spelling()))
        return diagnostics::emit(op->emitOpError(),
                                 "interactive-resource-reuse");
      aliases.emplace_back(i, first->second);
    }
    if (!aliases.empty()) {
      // Batch port removal avoids rescanning or shifting the capture list for
      // each alias. Distinct SSA values retain their first-occurrence order.
      llvm::BitVector operands(op->getNumOperands());
      for (auto [alias, first] : aliases)
        operands.set(prefix + alias);
      for (Region &region : op->getRegions()) {
        Block &block = region.front();
        unsigned start = block.getNumArguments() - captures;
        llvm::BitVector arguments(block.getNumArguments());
        for (auto [alias, first] : aliases) {
          block.getArgument(start + alias)
              .replaceAllUsesWith(block.getArgument(start + first));
          arguments.set(start + alias);
        }
        if (isa<zkc::local::LocalForOp>(op) &&
            isa<zkc::local::LocalYieldOp, zkc::local::LocalConditionOp>(
                block.back())) {
          llvm::BitVector forwarded(block.back().getNumOperands());
          unsigned offset =
              op->getNumResults() +
              (isa<zkc::local::LocalConditionOp>(block.back()) ? 1 : 0);
          for (auto [alias, first] : aliases)
            forwarded.set(offset + alias);
          block.back().eraseOperands(forwarded);
        }
        block.eraseArguments(arguments);
      }
      op->eraseOperands(operands);
    }
  }
  for (Region &region : op->getRegions())
    for (Block &block : region)
      for (Operation &nested : block)
        if (failed(canonicalizeCaptures(&nested)))
          return failure();
  return success();
}

namespace {
class Expander {
  OpBuilder builder;
  std::map<std::string, zkc::local::FuncOp> functions;
  AlgorithmExpansionPhase phase;
  const detail::AlgorithmExpansionRecord &input;
  detail::AlgorithmExpansionRecord output;
  std::map<std::string, Operation *> maps;
  llvm::StringSet<> selected;
  std::vector<AlgorithmOrigin> origins;
  mathematical::RealizationScope &scope;

  LogicalResult select() {
    std::map<std::string, SmallVector<std::string>> callers;
    llvm::StringSet<> calling;
    SmallVector<std::string> pending;
    auto selectFunction = [&](StringRef name) {
      if (selected.insert(name).second)
        pending.push_back(name.str());
    };
    for (const auto &entry : functions) {
      const auto &name = entry.first;
      auto function = entry.second;
      auto result = function.walk([&](Operation *op) {
        if (op == function.getOperation())
          return WalkResult::advance();
        if (!output.inspectionWork) {
          scope.failure(mathematical::RequiredFailure{
              "algorithm source inspection",
              CapacityCause{WorkOwner::AlgorithmExpansion, 1,
                            output.inspectionWork}});
          diagnostics::emit(op->emitOpError(), "algorithm-expansion-limit");
          return WalkResult::interrupt();
        }
        --output.inspectionWork;
        if (auto call = dyn_cast<local::ApplyOp>(op)) {
          calling.insert(name);
          auto callee = call.getCallee().str();
          if (maps.count(callee) &&
              (phase == AlgorithmExpansionPhase::RetainMaps ||
               isa<algebra::MapRealizeOp>(maps.at(callee)))) {
            selectFunction(name);
          } else if (functions.count(callee)) {
            callers[callee].push_back(name);
            if (phase == AlgorithmExpansionPhase::Finish)
              selectFunction(name);
          } else {
            diagnostics::emit(op->emitOpError(), "algorithm-call-symbol");
            return WalkResult::interrupt();
          }
        }
        return WalkResult::advance();
      });
      if (result.wasInterrupted())
        return failure();
    }
    // Every declaration is a root in its own right, including unused ones.
    // Only retention needs the reverse closure; Finish selects actual callers.
    if (phase == AlgorithmExpansionPhase::RetainMaps) {
      while (!pending.empty()) {
        auto name = pending.pop_back_val();
        for (const auto &caller : callers[name])
          selectFunction(caller);
      }
      // Finite analysis reads callbacks through declaration attributes, not
      // local.apply edges. Expose their full ordinary helper chains as well.
      // Add these roots after the reverse closure: unrelated users of a
      // callback do not need preparation. Call-free callbacks remain exact.
      for (const auto &entry : maps)
        if (isa<local::FiniteFoldOp, local::FiniteCollectOp>(entry.second))
          for (StringRef role : {"step", "body", "predicate"})
            if (auto callback =
                    entry.second->getAttrOfType<FlatSymbolRefAttr>(role))
              if (calling.contains(callback.getValue()))
                selected.insert(callback.getValue());
    }
    return success();
  }

  LogicalResult preserve(zkc::local::FuncOp function, Block &block,
                         unsigned depth = 0) {
    if (depth > 64)
      return diagnostics::emit(function.emitOpError(),
                               "interactive-call-depth");
    for (Operation &op : block) {
      for (Region &region : op.getRegions())
        for (Block &nested : region)
          if (failed(preserve(function, nested, depth + 1)))
            return failure();
      if (op.hasAttr("site")) {
        auto site = attr(&op, "site").str();
        auto saved = detail::occurrence(input, function.getSymName(), site);
        auto record =
            saved ? *saved
                  : detail::AlgorithmOccurrence{definition(function),
                                                function.getSymName().str(),
                                                site,
                                                {},
                                                depth};
        if (record.path.size() > 64 || record.depth > 64 ||
            (isa<local::ApplyOp>(op) &&
             (record.path.size() >= 64 || record.depth >= 64)))
          return diagnostics::emit(op.emitOpError(), "interactive-call-depth");
        // A raw preserved site is not an earlier expansion. Recording it in
        // RetainMaps would suppress its first canonical encoding in Finish.
        if (saved || phase == AlgorithmExpansionPhase::Finish)
          output.occurrences.emplace(
              detail::OccurrenceKey{function.getSymName().str(), site}, record);
        origins.push_back({function.getSymName().str(), site, record.definition,
                           record.originalSite, record.path});
        if (record.definition != record.declaration)
          origins.push_back({function.getSymName().str(), site,
                             record.declaration, record.originalSite,
                             record.path});
      }
    }
    return success();
  }

  std::string definition(zkc::local::FuncOp function) {
    if (auto origin = function->getAttrOfType<ArrayAttr>("logical_origin"))
      return cast<StringAttr>(origin[0]).getValue().str();
    return function.getSymName().str();
  }

  LogicalResult body(zkc::local::FuncOp function, Block &block,
                     IRMapping &mapping, StringRef root,
                     protocol::Assignments path, bool encode,
                     SmallVector<Value> &returned, unsigned depth = 0,
                     const protocol::Assignments &invocation = {},
                     unsigned invocationDepth = 0) {
    if (path.size() > 64 || depth > 64)
      return diagnostics::emit(function.emitOpError(),
                               "interactive-call-depth");
    for (auto &op : block) {
      auto call = dyn_cast<local::ApplyOp>(op);
      auto declaration = call ? maps.find(call.getCallee().str()) : maps.end();
      bool retained = declaration != maps.end() &&
                      (phase == AlgorithmExpansionPhase::RetainMaps ||
                       isa<algebra::MapRealizeOp>(declaration->second));
      bool expand = call && !retained;
      // The existing root body was charged to source inspection. Substitution
      // charges its call and every callee visit, even a return-only helper.
      // A callee's own declaration never pays for copies in another root.
      bool substitution = !invocation.empty() || expand;
      if (substitution && !output.work) {
        scope.failure(mathematical::RequiredFailure{
            "algorithm expansion work",
            CapacityCause{WorkOwner::AlgorithmExpansion, 1, output.work}});
        return diagnostics::emit(op.emitOpError(), "algorithm-expansion-limit");
      }
      if (substitution)
        --output.work;
      auto saved =
          detail::occurrence(input, function.getSymName(), attr(&op, "site"));
      // Recorded paths are relative to this function's earlier expansion.
      // A later caller adds its own prefix, including inside recorded regions.
      auto currentPath = saved ? invocation : path;
      if (saved)
        llvm::append_range(currentPath, saved->path);
      auto originalSite = saved ? saved->originalSite : attr(&op, "site").str();
      unsigned currentDepth = saved ? invocationDepth + saved->depth : depth;
      if (currentPath.size() > 64 || currentDepth > 64)
        return diagnostics::emit(op.emitOpError(), "interactive-call-depth");
      if (auto ret = dyn_cast<zkc::local::ReturnOp>(op)) {
        for (auto value : ret.getOperands())
          returned.push_back(mapping.lookup(value));
      } else if (expand) {
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
        if (failed(body(callee, callee.getBody().front(), inner, root, nested,
                        true, results, currentDepth + 1, nested,
                        currentDepth + 1)))
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
        if (encode && (!saved || !invocation.empty())) {
          auto encoded =
              algorithmSite(currentPath, original, output.originBytes);
          if (!encoded) {
            scope.failure(mathematical::RequiredFailure{
                "algorithm origin encoding",
                CapacityCause{
                    WorkOwner::AlgorithmOriginBytes, {}, output.originBytes}});
            return diagnostics::emit(op.emitOpError(), encoded.takeError());
          }
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
                          encode, ignored, currentDepth + 1, invocation,
                          invocationDepth)))
            return failure();
        }
        if (op.hasAttr("site"))
          copy->setAttr("site", builder.getStringAttr(site));
        bool terminal = isa<local::LocalIfOp, local::LocalMatchOp>(copy) &&
                        llvm::all_of(copy->getRegions(), [](Region &region) {
                          return isa<local::StopOp>(region.front().back());
                        });
        if (terminal && copy->getNumResults()) {
          // No arm returns these results. Rebuild without results and discard
          // the unreachable continuation instead of leaving undefined values.
          OperationState state(copy->getLoc(), copy->getName());
          state.addOperands(copy->getOperands());
          state.addAttributes(copy->getAttrs());
          for (Region &region : copy->getRegions())
            state.addRegion()->takeBody(region);
          auto *replacement = builder.create(state);
          copy->erase();
          copy = replacement;
        }
        // Cloning retains the leaf diagnostic location. The checked site path
        // carries the nested occurrence separately from diagnostic metadata.
        auto record =
            saved ? *saved
                  : detail::AlgorithmOccurrence{
                        definition(function), function.getSymName().str(),
                        original, currentPath, currentDepth};
        record.path = currentPath;
        record.depth = currentDepth;
        if (op.hasAttr("site"))
          output.occurrences.emplace(detail::OccurrenceKey{root.str(), site},
                                     record);
        origins.push_back(
            {root.str(), site, record.definition, original, currentPath});
        if (record.definition != record.declaration)
          origins.push_back(
              {root.str(), site, record.declaration, original, currentPath});
        if (terminal) {
          // A syntactic terminator is required, but cannot be reached. Its
          // name is fresh in the generated function; it has no source event.
          llvm::StringSet<> sites;
          copy->getParentOfType<local::FuncOp>().walk([&](Operation *at) {
            if (auto s = at->getAttrOfType<StringAttr>("site"))
              sites.insert(s.getValue());
          });
          unsigned number = 0;
          std::string unreachable;
          do {
            unreachable = "unreachable_" + std::to_string(number++);
          } while (sites.contains(unreachable));
          local::StopOp::create(builder, copy->getLoc(), unreachable, "abort");
          return success();
        }
        if (isa<zkc::local::StopOp>(copy))
          return success();
      }
    }
    return success();
  }

public:
  Expander(ModuleOp original, AlgorithmExpansionPhase phase,
           const detail::AlgorithmExpansionRecord &input,
           mathematical::RealizationScope &scope)
      : builder(original.getContext()), phase(phase), input(input),
        output(input), scope(scope) {
    output.occurrences.clear();
    auto root =
        cast<zkc::protocol_ir::ProtocolModuleOp>(&original.getBody()->front());
    for (auto fn : root.getBody().front().getOps<zkc::local::FuncOp>())
      functions.emplace(fn.getSymName().str(), fn);
    for (auto &op : root.getBody().front())
      if (isa<algebra::MapRealizeOp, local::FiniteFoldOp,
              local::FiniteCollectOp>(op))
        maps.emplace(SymbolTable::getSymbolName(&op).str(), &op);
  }
  LogicalResult run(ModuleOp candidate) {
    if (failed(select()))
      return failure();
    auto root =
        cast<zkc::protocol_ir::ProtocolModuleOp>(&candidate.getBody()->front());
    for (auto fn : root.getBody().front().getOps<zkc::local::FuncOp>()) {
      if (fn.isExternal())
        continue;
      auto original = functions.at(fn.getSymName().str());
      if (!selected.contains(fn.getSymName())) {
        if (failed(preserve(original, original.getBody().front())))
          return failure();
        continue;
      }
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
      if (failed(detail::canonicalizeCaptures(fn)))
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
} // namespace
static LogicalResult
expandAlgorithmsImpl(ModuleOp module, AlgorithmExpansionPhase phase,
                     AlgorithmExpansionState &state,
                     std::vector<AlgorithmOrigin> *origins,
                     mathematical::RealizationTrace *trace) {
  mathematical::RealizationScope scope(
      trace,
      phase == AlgorithmExpansionPhase::RetainMaps ? "retain-algorithms"
                                                   : "finish-algorithms",
      module);
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
      // Both phases retain only explicitly admitted map formulas. A callable
      // preparation interface alone never authorizes retention in Finish.
      uint64_t remaining = 1000000;
      if (auto error = mathematical::checkMapFormulas(module, remaining))
        return diagnostics::emit(module.emitError(), std::move(error));
      if (phase == AlgorithmExpansionPhase::Finish) {
        for (Operation &op : unit.getBody().front())
          if (isa<PreparationCallableOpInterface>(op) &&
              !isa<algebra::MapRealizeOp>(op))
            return diagnostics::emit(
                op.emitOpError(), "algorithm-call-symbol",
                "Finish requires realized non-map preparation declarations");
      }
      scope.propose();
      mathematical::CheckedCandidate candidate(module);
      Expander expansion(module, phase, input, scope);
      if (failed(expansion.run(*candidate)) || failed(verify(*candidate)))
        return failure();
      auto output = expansion.takeRecord();
      scope.failure(mathematical::VerificationDecision{
          mathematical::VerificationObservation::Unclassified,
          "algorithm expansion correspondence",
          {},
          {}});
      if (failed(candidate.publish([&](ModuleOp before, ModuleOp after) {
            return detail::checkAlgorithmExpansion(before, after, phase, input,
                                                   output, true);
          })))
        return failure();
      detail::AlgorithmStateAccess::set(state, std::move(output));
      if (origins)
        *origins = expansion.takeOrigins();
      scope.publish();
      return success();
    }
  }
  return diagnostics::emit(module.emitError(), "algorithm-expansion-stage");
}

LogicalResult expandAlgorithms(ModuleOp module,
                               std::vector<AlgorithmOrigin> *origins,
                               mathematical::RealizationTrace *trace) {
  AlgorithmExpansionState state;
  return expandAlgorithmsImpl(module, AlgorithmExpansionPhase::Finish, state,
                              origins, trace);
}
LogicalResult expandAlgorithms(ModuleOp module, AlgorithmExpansionPhase phase,
                               AlgorithmExpansionState &state,
                               std::vector<AlgorithmOrigin> *origins,
                               mathematical::RealizationTrace *trace) {
  return expandAlgorithmsImpl(module, phase, state, origins, trace);
}

} // namespace zkc::protocol
