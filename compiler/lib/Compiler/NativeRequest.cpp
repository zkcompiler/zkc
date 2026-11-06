#include "NativeRequest.h"
#include "NativeProofVerification.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Analysis/TotalClosure.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/SelectedControl.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::detail {
namespace {
namespace pir = protocol_ir;
bool dataType(Type type) {
  auto logical = protocol::encodeBoundType(type, false);
  if (!logical) {
    consumeError(logical.takeError());
    return false;
  }
  return protocol::duplicable(*logical) && protocol::discardable(*logical) &&
         !protocol::nativeSetupType(*logical) && logical->kind != "service" &&
         logical->kind != "capability";
}
// Charge before traversing or allocating clone/reader state. Counts include
// region/block containers and SSA bindings, not only operation visits.
bool requestCharge(uint64_t &remaining, uint64_t work) {
  if (work > remaining) {
    remaining = 0;
    return false;
  }
  remaining -= work;
  return true;
}
bool requestTree(Operation *op, uint64_t &remaining, unsigned depth = 0) {
  if (depth > 64 ||
      !requestCharge(remaining, 1 + uint64_t(op->getNumOperands()) +
                                    op->getNumResults() + op->getNumRegions() +
                                    op->getAttrs().size()))
    return false;
  for (Region &region : op->getRegions())
    for (Block &block : region) {
      if (!requestCharge(remaining, 1 + uint64_t(block.getNumArguments())))
        return false;
      unsigned nestedDepth = depth + !isa<ModuleOp, pir::ProtocolModuleOp,
                                          pir::ParticipantOp, func::FuncOp>(op);
      for (Operation &child : block)
        if (!requestTree(&child, remaining, nestedDepth))
          return false;
    }
  return true;
}
// Closed selected arms admit only their payload/capture arguments and earlier
// results. Validate that MLIR clone can resolve every use; its internal default
// mapping behavior must never retain an ambient source value.
bool closedRequestRegions(Operation *op, uint64_t &remaining,
                          unsigned depth = 0) {
  if (depth > 64 || !requestCharge(remaining, 1 + op->getNumRegions()))
    return false;
  if (op->getNumRegions() && !isa<data::BranchOp>(op))
    return false;
  for (Region &region : op->getRegions()) {
    if (!hasSingleElement(region))
      return false;
    Block &block = region.front();
    if (!requestCharge(remaining, 1 + block.getNumArguments()))
      return false;
    llvm::DenseSet<Value> available;
    for (Value arg : block.getArguments())
      available.insert(arg);
    for (Operation &child : block) {
      if (!requestCharge(remaining, child.getNumOperands() +
                                        uint64_t(child.getNumResults())))
        return false;
      for (Value input : child.getOperands())
        if (!available.contains(input))
          return false;
      if (!closedRequestRegions(&child, remaining, depth + 1))
        return false;
      for (Value output : child.getResults())
        available.insert(output);
    }
  }
  return true;
}
class Planner {
  pir::ProtocolModuleOp module;
  const NativeProofPolicy &policy;
  ArrayRef<NativeTranscriptEvent> events;
  SymbolTable symbols;
  protocol::SourceExecutionClosure execution;
  NativeRequestPlan plan;
  StringMap<Operation *> producerSites, validatorSites;
  StringMap<StringRef> draws;
  llvm::DenseSet<Operation *> deterministic, active, totalSelections;
  llvm::DenseMap<Operation *, NativeRequestLoop *> validatorLoops;
  llvm::DenseMap<Operation *, NativeRequestBranch *> validatorBranches;
  StringMap<const NativeTranscriptEvent *> eventSites;
  ArrayRef<NativeRequestCountPair> structuralCounts;
  unsigned remaining = 1000000;
  std::string problem;
  bool checkingSelector = false, carriedSelector = false;
  SymbolTableCollection mathSymbols;
  mathematical::TotalClosure totalMath;
  bool charge(uint64_t work = 1) {
    if (work > remaining) {
      remaining = 0;
      return fail("bounded request analysis exhausted");
    }
    remaining -= work;
    return true;
  }
  bool fail(StringRef why) {
    if (problem.empty())
      problem = why.str();
    return false;
  }
  bool boundedDepth(unsigned depth) {
    if (depth <= 64)
      return true;
    remaining = 0;
    return fail("bounded request nesting exhausted");
  }
  bool types(TypeRange types) {
    return all_of(types, [&](Type type) { return charge() && dataType(type); });
  }
  bool finiteOperation(Operation *op, unsigned depth) {
    finite::Computation model;
    if (!charge() || !boundedDepth(depth) ||
        failed(finite::describe(op, model)) || !model.domain || !model.helper ||
        !domain(model.domain, depth + 1))
      return fail("unclassified finite deterministic execution");
    auto callback = [&](Operation *target) {
      auto function = dyn_cast_or_null<func::FuncOp>(target);
      return function && (protocol::isScopedExecutionFunction(function)
                              ? closure(function, depth + 1)
                              : mathematics(function, depth + 1));
    };
    return callback(model.helper) &&
           (!model.predicate || callback(model.predicate));
  }
  bool domain(data::DomainOp function, unsigned depth) {
    if (!charge() || !boundedDepth(depth) ||
        !hasSingleElement(function.getBody()) ||
        !types(function.getFunctionType().getInputs()))
      return fail("unsupported deterministic finite domain");
    for (Operation &op : function.getBody().front()) {
      if (!charge())
        return false;
      // These constructors have installed ordered finite-domain meanings.
      // Retain every constructor's own admission and stopped behavior.
      if (isa<data::DomainElementsOp, data::DomainIndicesOp,
              data::DomainRangeOp, data::DomainZipOp, data::DomainProductOp,
              data::DomainMatrixRowOp, data::DomainMatrixColumnOp,
              data::DomainMatrixCoordinatesOp, data::DomainYieldOp>(op))
        continue;
      if (!mathematical::isTotal(&op) || !operation(&op, depth + 1))
        return fail("unclassified finite domain expression");
    }
    return true;
  }
  bool mathematics(func::FuncOp function, unsigned depth) {
    if (!function || !charge() || !boundedDepth(depth) ||
        function.isExternal() || !hasSingleElement(function.getBody()) ||
        !types(function.getArgumentTypes()) ||
        !types(function.getResultTypes()))
      return fail("unsupported deterministic mathematical helper");
    if (deterministic.contains(function))
      return true;
    if (!active.insert(function).second)
      return fail("recursive deterministic mathematical helper");
    for (auto &op : function.getBody().front()) {
      if (!charge())
        return false;
      if (isa<func::ReturnOp>(op))
        continue;
      if (auto call = dyn_cast<func::CallOp>(op)) {
        if (!mathematics(symbols.lookup<func::FuncOp>(call.getCallee()),
                         depth + 1))
          return false;
      } else if (!operation(&op, depth + 1))
        return false;
    }
    active.erase(function);
    deterministic.insert(function);
    return true;
  }
  bool closure(func::FuncOp function, unsigned depth = 0) {
    if (!function || !charge() || !boundedDepth(depth))
      return fail("missing or excessive deterministic Local closure");
    if (deterministic.contains(function))
      return true;
    if (function.isExternal() || !active.insert(function).second)
      return fail("external or recursive Local closure");
    auto found = execution.bodies.find(function.getSymName().str());
    if (found == execution.bodies.end())
      return fail("Local body has no admitted scoped execution");
    // Read every operation and every arm, including stopped arms. The original
    // complete function is invoked under the replica caller's scope.
    for (const auto &step : found->second) {
      if (!charge(1 + step.inputs.size() + step.outputs.size()) ||
          !types(ValueRange(step.inputs).getTypes()) ||
          !types(ValueRange(step.outputs).getTypes()))
        return fail("Local closure has non-data logical ports");
      auto *op = step.operation;
      if (auto apply = dyn_cast<exec::ApplyOp>(op)) {
        auto binding = symbols.lookup<runtime::BindingOp>(apply.getBinding());
        auto *contract =
            binding ? protocol::operationContracts(binding.getContract())
                    : nullptr;
        if (!binding || !binding.getImplementation().empty() || !contract ||
            !contract->deterministicData)
          return fail("uninstalled deterministic-data implementation");
      } else if (auto call = dyn_cast<func::CallOp>(op)) {
        if (!closure(symbols.lookup<func::FuncOp>(call.getCallee()), depth + 1))
          return false;
      } else if (auto compute = dyn_cast<exec::ComputeOp>(op)) {
        SymbolTableCollection tables;
        if (!mathematics(compute.resolveCallee(tables), depth + 1))
          return false;
      } else if (isa<exec::FoldOp, exec::CollectOp>(op)) {
        if (!finiteOperation(op, depth + 1))
          return false;
      } else if (!isa<exec::BooleanOp, exec::VariantOp, exec::TestOp,
                      exec::MatchOp, exec::RangeOp, exec::ReturnOp,
                      exec::CompleteOp, exec::RejectOp,
                      runtime::ReleaseBindingsOp>(op)) {
        return fail("unclassified deterministic Local execution step");
      }
      for (auto region : step.regions)
        if (!closure(region, depth + 1))
          return false;
    }
    active.erase(function);
    deterministic.insert(function);
    return true;
  }
  bool operation(Operation *op, unsigned depth = 0) {
    if (!boundedDepth(depth))
      return false;
    if (isa<data::BranchOp>(op)) {
      // The caller supplies formed ordinary IR. Account for all nested clone
      // and environment work before querying the owning total-Math closure,
      // whose helper analysis also has its own cumulative work allowance.
      uint64_t allowance = remaining;
      if (!requestTree(op, allowance, depth)) {
        remaining = 0;
        return fail("bounded selected Math replica exhausted");
      }
      bool closed = closedRequestRegions(op, allowance, depth);
      remaining = allowance;
      if (!closed)
        return fail("selected Math replica has an unresolved lexical input");
      if (!charge(1))
        return false;
      if (totalSelections.contains(op))
        return true;
      if (failed(totalMath.verifySelected(op)))
        return fail("request selection is not admitted total mathematics");
      totalSelections.insert(op);
      return true;
    }
    if (!charge(1 + op->getNumOperands() + op->getNumResults()) ||
        op->getNumRegions() || !types(op->getOperandTypes()) ||
        !types(op->getResultTypes()))
      return fail("request dependency is not immutable deterministic data");
    if (auto call = dyn_cast<pir::LocalCallOp>(op))
      return closure(symbols.lookup<func::FuncOp>(call.getCallee()), depth + 1);
    if (finite::isComputation(op))
      return finiteOperation(op, depth + 1);
    return mathematical::isTotal(op) ||
           fail("request dependency has no exact mathematical interpretation");
  }
  // Evaluate a capture at the saved entry frontier, never at the parent's
  // eventual end-of-block environment. Moving the environment back is exact.
  bool entrySame(Value v, Value p, NativeRequestFrame &child,
                 NativeRequestFrame &parent, unsigned depth) {
    if (!charge(child.entryRelations.size()))
      return false;
    auto prior = std::move(parent.relations);
    parent.relations = child.entryRelations;
    bool result = same(v, p, parent, depth + 1);
    parent.relations = std::move(prior);
    return result;
  }
  std::optional<NativeRequestValue>
  entryNeed(Value value, NativeRequestFrame &child, NativeRequestFrame &parent,
            Operation *anchor, Operation *frontier, unsigned depth) {
    if (!charge(child.entryRelations.size() + parent.relations.size()))
      return {};
    auto prior = std::move(parent.relations);
    parent.relations = child.entryRelations;
    auto result = need(value, parent, anchor, frontier, depth + 1);
    child.entryRelations = parent.relations;
    for (const auto &item : parent.relations)
      prior.try_emplace(item.first, item.second);
    parent.relations = std::move(prior);
    return result;
  }
  bool same(Value v, Value p, NativeRequestFrame &frame, unsigned depth = 0) {
    if (!charge() || !boundedDepth(depth) || v.getType() != p.getType())
      return false;
    auto known = frame.relations.find(v);
    if (known != frame.relations.end() && known->second.ordinary &&
        known->second.source == p)
      return true;
    auto va = dyn_cast<BlockArgument>(v), pa = dyn_cast<BlockArgument>(p);
    if (checkingSelector && frame.loop &&
        ((va && va.getOwner() == frame.validator && va.getArgNumber() &&
          va.getArgNumber() <= frame.loop->validator.getCarried()) ||
         (pa && pa.getOwner() == frame.producer && pa.getArgNumber() &&
          pa.getArgNumber() <= frame.loop->producer.getCarried()))) {
      carriedSelector = true;
      return false;
    }
    if (va && pa && frame.loop && va.getOwner() == frame.validator &&
        pa.getOwner() == frame.producer &&
        va.getArgNumber() > frame.loop->validator.getCarried() &&
        pa.getArgNumber() > frame.loop->producer.getCarried()) {
      // Captures preserve the exact incoming value. Follow each role's actual
      // input slot to the entry frontier; no relation between carried records
      // or equal-looking block arguments is assumed.
      return entrySame(frame.loop->validator.getInputs()[va.getArgNumber()],
                       frame.loop->producer.getInputs()[pa.getArgNumber()],
                       frame, *frame.loop->parent, depth);
    }
    if (va && pa && frame.branch && va.getOwner() == frame.validator &&
        pa.getOwner() == frame.producer) {
      Value vc = selectedCapture(va), pc = selectedCapture(pa);
      if (vc || pc)
        return vc && pc &&
               entrySame(vc, pc, frame, *frame.branch->parent, depth);
      // Whole-selector correspondence was established before building either
      // arm. Only this alternative's exact payload position is related.
      return va.getArgNumber() == pa.getArgNumber();
    }
    auto vb = v.getDefiningOp<pir::ParticipantBranchOp>();
    auto pb = p.getDefiningOp<pir::ParticipantBranchOp>();
    if (vb || pb) {
      auto *branch = vb ? validatorBranches.lookup(vb) : nullptr;
      if (!branch || branch->producer != pb || !branch->arms.front()->finished)
        return false;
      auto key = std::make_pair(v, p);
      auto cached = branch->joins.find(key);
      if (cached != branch->joins.end())
        return cached->second;
      if (!charge(1 + branch->arms.size()))
        return false;
      unsigned vi = cast<OpResult>(v).getResultNumber();
      unsigned pi = cast<OpResult>(p).getResultNumber();
      bool equal = true;
      for (const auto &arm : branch->arms)
        if (!same(arm->validator->back().getOperand(vi),
                  arm->producer->back().getOperand(pi), *arm, depth + 1)) {
          equal = false;
          break;
        }
      branch->joins.try_emplace(key, equal);
      return equal;
    }
    auto *a = v.getDefiningOp(), *b = p.getDefiningOp();
    if (a && b && isa<data::BranchOp>(a) && isa<data::BranchOp>(b)) {
      if (cast<OpResult>(v).getResultNumber() !=
              cast<OpResult>(p).getResultNumber() ||
          a->getNumOperands() != b->getNumOperands())
        return false;
      // A closed Math selection is compared in its entirety. No tag-only
      // equivalence, arm pruning, or speculative evaluation is introduced.
      if (!operation(a, depth + 1) || !operation(b, depth + 1))
        return false;
      llvm::DenseMap<Value, Value> bound;
      for (auto [x, y] : zip(a->getOperands(), b->getOperands())) {
        if (!same(x, y, frame, depth + 1))
          return false;
        bound[x] = y;
      }
      return OperationEquivalence::isEquivalentTo(
                 a, b,
                 [&](Value x, Value y) {
                   return success(charge() && bound.lookup(x) == y);
                 },
                 [&](Value x, Value y) {
                   if (charge())
                     bound[x] = y;
                 },
                 OperationEquivalence::IgnoreLocations) &&
             remaining;
    }
    if (!a || !b || a->getName() != b->getName() ||
        cast<OpResult>(v).getResultNumber() !=
            cast<OpResult>(p).getResultNumber() ||
        a->getNumOperands() != b->getNumOperands() || !operation(a) ||
        !operation(b))
      return false;
    NamedAttrList aa(a->getAttrs()), bb(b->getAttrs());
    if (isa<pir::LocalCallOp>(a)) {
      aa.erase("site");
      aa.erase("role");
      bb.erase("site");
      bb.erase("role");
    }
    if (aa != bb)
      return false;
    for (auto [x, y] : zip(a->getOperands(), b->getOperands()))
      if (!same(x, y, frame, depth + 1))
        return false;
    return true;
  }
  std::optional<NativeRequestValue> need(Value value, NativeRequestFrame &frame,
                                         Operation *anchor, Operation *frontier,
                                         unsigned depth = 0) {
    if (!charge() || !boundedDepth(depth) || !dataType(value.getType())) {
      fail("request value has unsupported custody or analysis depth");
      return {};
    }
    auto *definition = value.getDefiningOp();
    auto installed = frame.definitions.find(definition);
    if (installed != frame.definitions.end()) {
      if (!frontier || definition->getBlock() != frame.validator ||
          !definition->isBeforeInBlock(frontier)) {
        fail("replica definition is beyond the event frontier");
        return {};
      }
      Operation *prior = installed->second;
      if (anchor == prior || prior->isBeforeInBlock(anchor)) {
        // A saved loop-entry environment can predate this plan entry. Recover
        // only the actual already-scheduled replica, never later send seeds.
        frame.relations[value] = {value, false};
        return NativeRequestValue{value, false};
      }
      // A late-discovered carry/count may need a value earlier than its first
      // request. Move its one complete source invocation and recursively move
      // dependencies to the earlier admitted frontier; do not duplicate it.
      auto &steps = frame.before[prior];
      if (!charge(steps.size()))
        return {};
      auto step = find_if(
          steps, [&](const auto &step) { return step.source == definition; });
      if (step == steps.end()) {
        fail("replica source slot has no scheduled definition");
        return {};
      }
      steps.erase(step);
      frame.definitions.erase(installed);
      for (Value output : definition->getResults())
        frame.relations.erase(output);
    }
    auto known = frame.relations.find(value);
    if (known != frame.relations.end())
      return known->second;
    if (auto arg = dyn_cast<BlockArgument>(value)) {
      if (frame.branch && arg.getOwner() == frame.validator) {
        auto &branch = *frame.branch;
        auto parent = selectedCapture(arg);
        if (!parent) {
          // Payload types and positions were checked at branch entry.
          Value payload = frame.producer->getArgument(arg.getArgNumber());
          frame.relations[value] = {payload, true};
          return frame.relations.lookup(value);
        }
        unsigned index = 0;
        auto payload = selectedPayloadTypes(branch.validator, frame.arm);
        if (!payload) {
          consumeError(payload.takeError());
          return {};
        }
        index = 1 + arg.getArgNumber() - payload->size();
        if (!charge(branch.captures.size()))
          return {};
        auto found = llvm::find(branch.captures, index);
        if (found == branch.captures.end()) {
          auto input = entryNeed(parent, frame, *branch.parent, branch.producer,
                                 branch.validator, depth);
          if (!input || !charge())
            return {};
          branch.captures.push_back(index);
          branch.captured.push_back(*input);
        }
        frame.relations[value] = {value, false};
        return frame.relations.lookup(value);
      }
      auto *loop = frame.loop;
      if (!loop || arg.getOwner() != frame.validator || !arg.getArgNumber()) {
        fail("verifier-only input is unavailable to the producer");
        return {};
      }
      unsigned index = arg.getArgNumber() - 1;
      if (index < loop->validator.getCarried()) {
        if (!carry(*loop, index, depth + 1))
          return {};
      } else {
        // Captures are reproduced independently, including receiver stores.
        auto input =
            entryNeed(loop->validator.getInputs()[1 + index], frame,
                      *loop->parent, loop->producer, loop->validator, depth);
        if (!input)
          return {};
        loop->captures.push_back(index - loop->validator.getCarried());
        loop->captured.push_back(*input);
        frame.relations[value] = {value, false};
      }
      return frame.relations.lookup(value);
    }
    auto *op = value.getDefiningOp();
    if (!op || op->getBlock() != frame.validator || !frontier ||
        !op->isBeforeInBlock(frontier)) {
      fail("request dependency is beyond the corresponding event frontier");
      return {};
    }
    if (auto loop = dyn_cast<pir::ProtocolLoopOp>(op)) {
      auto *paired = validatorLoops.lookup(loop);
      unsigned index = cast<OpResult>(value).getResultNumber();
      if (!paired || !carry(*paired, index, depth + 1))
        return {};
      // The saved entry frontier may predate discovery of this carry. Its
      // invariant and actual result slot are already installed in the earlier
      // paired loop; recover that exact result after checking source dominance
      // above, rather than looking it up in the older frontier environment.
      NativeRequestValue related{value, false};
      frame.relations[value] = related;
      return related;
    }
    if (auto branch = dyn_cast<pir::ParticipantBranchOp>(op)) {
      auto *paired = validatorBranches.lookup(branch);
      unsigned index = cast<OpResult>(value).getResultNumber();
      if (!paired || !branchOutput(*paired, index, depth + 1))
        return {};
      frame.relations[value] = {value, false};
      return frame.relations.lookup(value);
    }
    if (!operation(op, depth))
      return {};
    NativeRequestStep step{op, {}};
    for (Value input : op->getOperands()) {
      auto related = need(input, frame, anchor, frontier, depth + 1);
      if (!related)
        return {};
      step.inputs.push_back(*related);
    }
    // Resolving an input can install another carry and read its back edge.
    // That recursion may already have scheduled this complete invocation.
    // Reuse or relocate its actual definition through the same frontier checks
    // instead of appending a second copy of the source operation.
    if (frame.definitions.count(op))
      return need(value, frame, anchor, frontier, depth + 1);
    if (!charge(2 + op->getNumResults()))
      return {};
    frame.before[anchor].push_back(std::move(step));
    frame.definitions[op] = anchor;
    for (Value output : op->getResults())
      frame.relations[output] = {output, false};
    return frame.relations.lookup(value);
  }
  bool carry(NativeRequestLoop &loop, unsigned index, unsigned depth) {
    auto &frame = *loop.body;
    auto arg = frame.validator->getArgument(1 + index);
    if (frame.relations.count(arg))
      return true;
    if (index >= pir::ProtocolLoopOp(loop.validator).getCarried() ||
        !boundedDepth(depth))
      return fail("invalid replica carry position");
    auto initial =
        entryNeed(loop.validator.getInputs()[1 + index], frame, *loop.parent,
                  loop.producer, loop.validator, depth);
    if (!initial)
      return false;
    // Install the invariant variable before reading its back edge. This is an
    // induction hypothesis with an independently checked initializer/yield,
    // not equality to a private holder record.
    unsigned slot = loop.carried.size();
    loop.carried.push_back(index);
    loop.initial.push_back(*initial);
    loop.yielded.push_back({});
    frame.relations[arg] = {arg, false};
    loop.parent
        ->relations[pir::ProtocolLoopOp(loop.validator).getResult(index)] = {
        pir::ProtocolLoopOp(loop.validator).getResult(index), false};
    if (!frame.finished)
      return true;
    return yield(loop, slot, depth);
  }
  bool yield(NativeRequestLoop &loop, unsigned slot, unsigned depth) {
    auto &frame = *loop.body;
    unsigned index = loop.carried[slot];
    auto yield = cast<pir::ProtocolYieldOp>(frame.validator->back());
    auto related = need(yield.getOperand(index), frame, &frame.producer->back(),
                        yield, depth + 1);
    if (!related)
      return false;
    loop.yielded[slot] = *related;
    return true;
  }
  bool branchOutput(NativeRequestBranch &branch, unsigned index,
                    unsigned depth) {
    if (!charge(branch.outputs.size()))
      return false;
    if (is_contained(branch.outputs, index))
      return true;
    if (!charge(1 + branch.arms.size()) || !boundedDepth(depth))
      return fail("replica branch output exceeds analysis depth");
    SmallVector<NativeRequestValue> values;
    for (auto &arm : branch.arms) {
      auto *yield = &arm->validator->back();
      auto input = need(yield->getOperand(index), *arm, &arm->producer->back(),
                        yield, depth + 1);
      if (!input)
        return false;
      values.push_back(*input);
    }
    branch.outputs.push_back(index);
    for (auto [arm, value] : enumerate(values))
      branch.yielded[arm].push_back(value);
    return true;
  }
  bool build(NativeRequestFrame &frame, unsigned depth = 0) {
    if (!boundedDepth(depth))
      return fail("request loop depth limit");
    for (auto &op : *frame.producer) {
      if (!charge())
        return false;
      auto site = op.getAttrOfType<StringAttr>("site");
      auto *other = site ? validatorSites.lookup(site.getValue()) : nullptr;
      if (auto branch = dyn_cast<pir::ParticipantBranchOp>(op)) {
        auto vbranch = dyn_cast_or_null<pir::ParticipantBranchOp>(other);
        if (!vbranch)
          continue; // A role-local branch has no cross-role premise.
        if (vbranch->getBlock() != frame.validator ||
            branch.getAlternatives() != vbranch.getAlternatives() ||
            branch->getNumRegions() != vbranch->getNumRegions() ||
            !branch->getNumRegions() ||
            branch->getNumRegions() > selectedRegionArmLimit)
          return fail("paired branch alternative shape differs");
        checkingSelector = true;
        bool agreed =
            same(vbranch.getInputs()[0], branch.getInputs()[0], frame);
        checkingSelector = false;
        if (!agreed) {
          problem = "branch selector needs checked correspondence";
          return false;
        }
        auto paired = std::make_unique<NativeRequestBranch>();
        paired->producer = branch;
        paired->validator = vbranch;
        paired->parent = &frame;
        paired->yielded.resize(branch->getNumRegions());
        for (unsigned i = 0; i < branch->getNumRegions(); ++i) {
          if (!charge(1 + frame.relations.size()))
            return false;
          auto pp = selectedPayloadTypes(branch, i);
          auto vp = selectedPayloadTypes(vbranch, i);
          if (!pp || !vp) {
            if (!pp)
              consumeError(pp.takeError());
            if (!vp)
              consumeError(vp.takeError());
            return fail("unsupported branch payload shape");
          }
          if (*pp != *vp || !hasSingleElement(branch->getRegion(i)) ||
              !hasSingleElement(vbranch->getRegion(i)))
            return fail("paired branch payload shape differs");
          auto child = std::make_unique<NativeRequestFrame>();
          child->producer = &branch->getRegion(i).front();
          child->validator = &vbranch->getRegion(i).front();
          child->branch = paired.get();
          child->arm = i;
          child->entryRelations = frame.relations;
          for (unsigned j = 0; j < pp->size(); ++j)
            child->relations[child->validator->getArgument(j)] = {
                child->producer->getArgument(j), true};
          plan.frames[child->producer] = child.get();
          paired->arms.push_back(std::move(child));
        }
        auto *installed = paired.get();
        validatorBranches[vbranch] = installed;
        frame.branches[branch] = std::move(paired);
        for (auto &arm : installed->arms)
          if (!build(*arm, depth + 1))
            return false;
      } else if (auto loop = dyn_cast<pir::ProtocolLoopOp>(op)) {
        auto vloop = dyn_cast_or_null<pir::ProtocolLoopOp>(other);
        if (!vloop)
          continue;
        if (vloop->getBlock() != frame.validator)
          return fail("paired loop belongs to another lexical frame");
        auto paired = std::make_unique<NativeRequestLoop>();
        paired->producer = loop;
        paired->validator = vloop;
        paired->parent = &frame;
        paired->body = std::make_unique<NativeRequestFrame>();
        auto &child = *paired->body;
        child.producer = &loop.getBody().front();
        child.validator = &vloop.getBody().front();
        child.loop = paired.get();
        if (!charge(frame.relations.size()))
          return false;
        child.entryRelations = frame.relations;
        child.relations[child.validator->getArgument(0)] = {
            child.producer->getArgument(0), true};
        validatorLoops[vloop] = paired.get();
        plan.frames[child.producer] = &child;
        frame.loops[loop] = std::move(paired);
        if (!build(child, depth + 1))
          return false;
      } else if (auto send = dyn_cast<pir::EmitOp>(op)) {
        auto receive = dyn_cast_or_null<pir::AwaitOp>(other);
        if (!receive || receive->getBlock() != frame.validator ||
            receive.getPeer() != policy.producer ||
            send.getPeer() != policy.validator ||
            receive.getOutput().getType() != send.getInput().getType())
          return fail("ordinary send/receive association differs");
        frame.relations[receive.getOutput()] = {send.getInput(), true};
      } else if (auto receive = dyn_cast<pir::AwaitOp>(op)) {
        auto send = dyn_cast_or_null<pir::EmitOp>(other);
        if (!send || send->getBlock() != frame.validator ||
            receive.getPeer() != policy.validator ||
            send.getPeer() != policy.producer ||
            receive.getOutput().getType() != send.getInput().getType())
          return fail("ordinary request lacks its actual verifier send");
        auto draw = draws.find(receive.getSite());
        if (draw != draws.end()) {
          auto query = dyn_cast_or_null<pir::ParticipantQueryOp>(
              validatorSites.lookup(draw->second));
          if (!query || query.getNumResults() != 1 ||
              send.getInput() != query.getResult(0))
            return fail("selected delivery does not match its query");
          frame.relations[query.getResult(0)] = {receive.getOutput(), true};
          continue;
        }
        auto *fact = eventSites.lookup(receive.getSite());
        if (!fact || !fact->reconstructed || fact->query)
          return fail("request occurrence is not admitted as reconstructed");
        auto value = need(send.getInput(), frame, &op, send);
        if (!value)
          return false;
        frame.requests[&op] = *value;
      }
    }
    frame.finished = true;
    if (frame.loop)
      for (unsigned i = 0; i < frame.loop->carried.size(); ++i)
        if (!frame.loop->yielded[i].source && !yield(*frame.loop, i, depth + 1))
          return false;
    return true;
  }
  bool counts(NativeRequestFrame &frame) {
    // Count-driven replica discovery follows actual source order across both
    // kinds of control, rather than processing two independent hash rosters.
    for (Operation &op : *frame.producer) {
      if (!charge())
        return false;
      auto selected = frame.branches.find(&op);
      if (selected != frame.branches.end()) {
        for (const auto &arm : selected->second->arms)
          if (!counts(*arm))
            return false;
        continue;
      }
      auto found = frame.loops.find(&op);
      if (found == frame.loops.end())
        continue;
      const auto &child = found->second;
      if (!charge(1 + structuralCounts.size()))
        return false;
      auto p = child->producer, v = child->validator;
      bool structural = is_contained(
          structuralCounts,
          NativeRequestCountPair{p.getInputs()[0], v.getInputs()[0]});
      // The original joint driver checks every participating count before
      // entry, even when this loop has no communication or replica state.
      if (p.getMaximumAttr() != v.getMaximumAttr() ||
          (!structural && !entrySame(v.getInputs()[0], p.getInputs()[0],
                                     *child->body, frame, 0)))
        return fail("loop count needs checked structural recurrence");
      if (structural) {
        auto count = entryNeed(v.getInputs()[0], *child->body, frame, p, v, 0);
        if (!count)
          return false;
        child->count = *count;
      }
      if (!counts(*child->body))
        return false;
    }
    return true;
  }

public:
  Planner(pir::ProtocolModuleOp module, const NativeProofPolicy &policy,
          ArrayRef<NativeTranscriptEvent> events,
          protocol::SourceExecutionClosure execution,
          ArrayRef<NativeRequestCountPair> structuralCounts, unsigned allowance)
      : module(module), policy(policy), events(events), symbols(module),
        execution(std::move(execution)), structuralCounts(structuralCounts),
        remaining(allowance), totalMath(module, mathSymbols) {}
  Expected<NativeRequestPlan> run() {
    // Every paired source loop requires count correspondence, even without
    // events. Profile restrictions apply only to new request synthesis.
    if (!charge(events.size() + policy.draws.size() +
                policy.publicInputs.size()))
      return error("native-request-limit");
    bool reconstruct =
        any_of(events, [](const auto &event) { return event.reconstructed; });
    if (reconstruct && (!policy.construction.empty() ||
                        protocol::nativeChallengeField(policy.suite).empty()))
      return error("native-request-construction",
                   "custom request plans are unsupported");
    for (auto p : module.getBody().front().getOps<pir::ParticipantOp>()) {
      if (p.getRole() == policy.producer)
        plan.producer = p;
      if (p.getRole() == policy.validator)
        plan.validator = p;
    }
    if (!plan.producer || !plan.validator)
      return error("native-request-participants");
    auto index = [&](pir::ParticipantOp p, StringMap<Operation *> &sites) {
      bool ok = true;
      p.walk([&](Operation *op) {
        if (!charge(1 + op->getNumOperands() + op->getNumResults())) {
          ok = false;
          return WalkResult::interrupt();
        }
        if (auto site = op->getAttrOfType<StringAttr>("site"))
          ok &= sites.try_emplace(site.getValue(), op).second;
        return WalkResult::advance();
      });
      return ok;
    };
    if (!index(plan.producer, producerSites) ||
        !index(plan.validator, validatorSites))
      return error(remaining ? "native-request-sites" : "native-request-limit");
    for (const auto &event : events) {
      if (!charge())
        return error("native-request-limit");
      if (!eventSites.try_emplace(event.site, &event).second)
        return error("native-request-sites");
    }
    for (const auto &draw : policy.draws) {
      if (!charge())
        return error("native-request-limit");
      draws[draw.second] = draw.first;
    }
    plan.root = std::make_unique<NativeRequestFrame>();
    auto &root = *plan.root;
    root.producer = &plan.producer.getBody().front();
    root.validator = &plan.validator.getBody().front();
    plan.frames[root.producer] = &root;
    auto projections = module.getBody().front().getOps<pir::ProjectionOp>();
    if (!hasSingleElement(projections) ||
        (*projections.begin()).getInterfaces().size() != 1)
      return error("native-request-interface");
    auto interface =
        cast<DictionaryAttr>((*projections.begin()).getInterfaces()[0]);
    llvm::DenseMap<unsigned, Value> pInputs, vInputs;
    for (Attribute item : interface.getAs<ArrayAttr>("participants")) {
      if (!charge())
        return error("native-request-limit");
      auto row = cast<DictionaryAttr>(item);
      auto ref = row.getAs<FlatSymbolRefAttr>("participant");
      pir::ParticipantOp p = ref == FlatSymbolRefAttr::get(plan.producer)
                                 ? plan.producer
                             : ref == FlatSymbolRefAttr::get(plan.validator)
                                 ? plan.validator
                                 : pir::ParticipantOp();
      if (!p)
        continue;
      auto &ports = p == plan.producer ? pInputs : vInputs;
      for (auto [i, port] : enumerate(row.getAs<ArrayAttr>("inputs"))) {
        if (!charge())
          return error("native-request-limit");
        ports[cast<IntegerAttr>(port).getInt()] =
            p.getBody().front().getArgument(i);
      }
    }
    for (unsigned port : policy.publicInputs) {
      if (!charge())
        return error("native-request-limit");
      Value p = pInputs.lookup(port), v = vInputs.lookup(port);
      if (p && v && p.getType() == v.getType() && dataType(v.getType()))
        root.relations[v] = {p, true};
    }
    if (!build(root) || !counts(root))
      return error(!remaining        ? "native-request-limit"
                   : carriedSelector ? "native-request-selector-profile"
                                     : "native-request-reconstruction",
                   problem);
    // A role-local enclosing control is ordinary native execution. It must
    // not hide a paired control obligation or an admitted reverse request.
    for (const auto &item : validatorSites) {
      if (!charge())
        return error("native-request-limit");
      auto *other = producerSites.lookup(item.getKey());
      if ((isa<pir::ParticipantBranchOp>(item.second) &&
           isa_and_nonnull<pir::ParticipantBranchOp>(other) &&
           !validatorBranches.count(item.second)) ||
          (isa<pir::ProtocolLoopOp>(item.second) &&
           isa_and_nonnull<pir::ProtocolLoopOp>(other) &&
           !validatorLoops.count(item.second)))
        return error("native-request-control-profile",
                     "paired control is hidden by an unpaired enclosing frame");
    }
    for (const auto &event : events) {
      if (!charge())
        return error("native-request-limit");
      if (!event.reconstructed)
        continue;
      auto *source = producerSites.lookup(event.site);
      auto *frame = source ? plan.frames.lookup(source->getBlock()) : nullptr;
      if (!frame || !frame->requests.count(source))
        return error("native-request-control-profile",
                     "request is hidden by an unpaired enclosing frame");
    }
    return std::move(plan);
  }
};
} // namespace
Expected<NativeRequestPlan>
planNativeRequests(pir::ProtocolModuleOp projected,
                   const NativeProofPolicy &policy,
                   ArrayRef<NativeTranscriptEvent> events,
                   const mathematical::RealizedProtocol *realization) {
  // Bound discovery before symbol-table/closure setup and all later copies.
  // Each recursive descent checks its depth before visiting another region.
  uint64_t setup = 1000000;
  if (!requestTree(projected, setup))
    return error("native-request-limit", "bounded request discovery exhausted");
  if (events.size() > setup || policy.draws.size() > setup ||
      policy.publicInputs.size() > setup)
    return error("native-request-limit");
  SmallVector<NativeRequestCountPair> counts;
  if (realization &&
      any_of(events, [](const auto &event) { return event.reconstructed; })) {
    auto actual = readNativeRequestCounts(*realization, projected, policy);
    if (!actual)
      return actual.takeError();
    counts = std::move(*actual);
  }
  auto execution = protocol::readSourceExecutionClosure(projected);
  if (!execution)
    return execution.takeError();
  return Planner(projected, policy, events, std::move(*execution), counts,
                 setup)
      .run();
}

namespace {
// Compare actual operations without cloning, normalizing or consulting emitted
// metadata. Only root Local calls have construction-owned site/role fields.
// Nested Math symbols and all other attributes must agree exactly; the
// enclosing native checker independently retains the definitions those symbols
// name.
bool readRequestOperation(Operation *source, Operation *actual,
                          NativeRequestValues &bound, uint64_t &remaining,
                          unsigned depth = 0) {
  if (!actual || depth > 64 ||
      !requestCharge(remaining, 1 + uint64_t(source->getNumOperands()) +
                                    source->getNumResults() +
                                    source->getNumRegions() +
                                    source->getAttrs().size() +
                                    actual->getAttrs().size()) ||
      source->getName() != actual->getName() ||
      source->getNumOperands() != actual->getNumOperands() ||
      source->getResultTypes() != actual->getResultTypes() ||
      source->getNumRegions() != actual->getNumRegions() ||
      source->getNumSuccessors() || actual->getNumSuccessors())
    return false;
  NamedAttrList expected(source->getAttrs()), observed(actual->getAttrs());
  if (!depth && isa<pir::LocalCallOp>(source)) {
    auto call = cast<pir::LocalCallOp>(actual);
    auto participant = call->getParentOfType<pir::ParticipantOp>();
    if (!participant || call.getRole() != participant.getRole() ||
        !call.getSiteAttr() || call.getSite().empty())
      return false;
    expected.erase("site");
    expected.erase("role");
    observed.erase("site");
    observed.erase("role");
  }
  if (expected != observed)
    return false;
  for (auto [from, to] : zip(source->getOperands(), actual->getOperands())) {
    Value value = bound.lookup(from);
    if (!value || value != to || from.getType() != to.getType())
      return false;
  }
  if (source->getNumRegions() && !isa<data::BranchOp>(source))
    return false;
  for (auto [left, right] : zip(source->getRegions(), actual->getRegions())) {
    if (!hasSingleElement(left) || !hasSingleElement(right))
      return false;
    auto &a = left.front();
    auto &b = right.front();
    if (!requestCharge(remaining, 1 + uint64_t(a.getNumArguments())) ||
        a.getArgumentTypes() != b.getArgumentTypes())
      return false;
    // No parent map is copied: a Math arm is closed. Exact formal positions
    // bind the selected payload, followed by the explicit ordered captures.
    NativeRequestValues arm;
    for (auto [from, to] : zip(a.getArguments(), b.getArguments()))
      arm.try_emplace(from, to);
    auto cursor = b.begin();
    for (Operation &child : a) {
      if (cursor == b.end() ||
          !readRequestOperation(&child, &*cursor, arm, remaining, depth + 1))
        return false;
      ++cursor;
    }
    if (cursor != b.end())
      return false;
  }
  for (auto [from, to] : zip(source->getResults(), actual->getResults()))
    if (!bound.try_emplace(from, to).second)
      return false;
  return true;
}
// Read actual shape before indexing any appended slot. Extra slots belong to
// the transcript/codec consumer and are checked there, never by copied IDs.
bool branchShape(const NativeRequestBranch &branch,
                 pir::ParticipantBranchOp actual, unsigned extraCaptures,
                 unsigned extraOutputs, std::optional<unsigned> onlyArm = {}) {
  auto p = branch.producer;
  if (!actual || actual.getAlternatives() != p.getAlternatives() ||
      actual.getSite() != p.getSite() ||
      actual->getNumRegions() != branch.arms.size() ||
      actual.getNumOperands() !=
          p.getNumOperands() + branch.captured.size() + extraCaptures ||
      actual.getNumResults() !=
          p.getNumResults() + branch.outputs.size() + extraOutputs ||
      branch.captures.size() != branch.captured.size() ||
      branch.yielded.size() != branch.arms.size())
    return false;
  for (auto [i, type] : enumerate(p.getResultTypes()))
    if (actual.getResult(i).getType() != type)
      return false;
  for (auto [i, index] : enumerate(branch.outputs))
    if (index >= pir::ParticipantBranchOp(branch.validator).getNumResults() ||
        actual.getResult(p.getNumResults() + i).getType() !=
            pir::ParticipantBranchOp(branch.validator)
                .getResult(index)
                .getType())
      return false;
  uint64_t remaining = 1000000;
  for (auto [i, arm] : enumerate(branch.arms)) {
    if (onlyArm && *onlyArm != i)
      continue;
    if (!hasSingleElement(actual->getRegion(i)) ||
        branch.yielded[i].size() != branch.outputs.size())
      return false;
    auto &body = actual->getRegion(i).front();
    uint64_t work = 1 + body.getNumArguments() + actual.getNumOperands();
    if (work > remaining)
      return false;
    remaining -= work;
    if (body.getNumArguments() != arm->producer->getNumArguments() +
                                      branch.captured.size() + extraCaptures)
      return false;
    for (auto [j, arg] : enumerate(arm->producer->getArguments()))
      if (body.getArgument(j).getType() != arg.getType())
        return false;
    unsigned payload =
        arm->producer->getNumArguments() - (p.getNumOperands() - 1);
    for (unsigned j = 1; j < actual.getNumOperands(); ++j)
      if (body.getArgument(payload + j - 1).getType() !=
          actual.getOperand(j).getType())
        return false;
  }
  return true;
}
} // namespace
bool readNativeRequestSteps(const NativeRequestFrame &frame, Operation *anchor,
                            Operation *&cursor,
                            const NativeRequestValues &ordinary,
                            NativeRequestValues &replica, uint64_t &allowance) {
  if (!requestCharge(allowance, 1))
    return false;
  auto found = frame.before.find(anchor);
  if (found == frame.before.end())
    return true;
  for (const auto &step : found->second) {
    if (!step.source || !cursor ||
        !requestCharge(allowance,
                       1 + step.inputs.size() + step.source->getNumResults()) ||
        step.inputs.size() != step.source->getNumOperands())
      return false;
    NativeRequestValues bound;
    for (auto [input, source] : zip(step.inputs, step.source->getOperands())) {
      Value value = resolveNativeRequestValue(input, ordinary, replica);
      if (!value || source.getType() != value.getType())
        return false;
      auto [entry, inserted] = bound.try_emplace(source, value);
      if (!inserted && entry->second != value)
        return false;
    }
    if (!readRequestOperation(step.source, cursor, bound, allowance))
      return false;
    // Arm-local definitions never escape. Bind only the complete invocation's
    // exact result slots after every actual arm and yield has been checked.
    for (auto [from, to] : zip(step.source->getResults(), cursor->getResults()))
      if (!replica.try_emplace(from, to).second)
        return false;
    cursor = cursor->getNextNode();
  }
  return true;
}
bool readNativeRequestBranchInputs(const NativeRequestBranch &branch,
                                   pir::ParticipantBranchOp actual,
                                   unsigned extraCaptures,
                                   unsigned extraOutputs,
                                   const NativeRequestValues &ordinary,
                                   const NativeRequestValues &replica) {
  if (!branchShape(branch, actual, extraCaptures, extraOutputs))
    return false;
  auto p = branch.producer;
  for (auto [i, source] : enumerate(p.getInputs())) {
    Value expected = ordinary.lookup(source);
    if (!expected || actual.getOperand(i) != expected)
      return false;
  }
  for (auto [i, input] : enumerate(branch.captured)) {
    Value expected = resolveNativeRequestValue(input, ordinary, replica);
    if (!expected || actual.getOperand(p.getNumOperands() + i) != expected)
      return false;
  }
  return true;
}
bool bindNativeRequestBranchArm(const NativeRequestBranch &branch,
                                pir::ParticipantBranchOp actual, unsigned arm,
                                unsigned extraCaptures, unsigned extraOutputs,
                                NativeRequestValues &ordinary,
                                NativeRequestValues &replica) {
  if (arm >= branch.arms.size() ||
      !branchShape(branch, actual, extraCaptures, extraOutputs, arm))
    return false;
  auto &frame = *branch.arms[arm];
  auto &body = actual->getRegion(arm).front();
  for (auto [source, target] :
       zip(frame.producer->getArguments(), body.getArguments()))
    if (!ordinary.try_emplace(source, target).second)
      return false;
  unsigned payload =
      frame.validator->getNumArguments() -
      (pir::ParticipantBranchOp(branch.validator).getNumOperands() - 1);
  for (auto [i, index] : enumerate(branch.captures)) {
    if (!index ||
        index >= pir::ParticipantBranchOp(branch.validator).getNumOperands())
      return false;
    Value source = frame.validator->getArgument(payload + index - 1);
    Value target = body.getArgument(frame.producer->getNumArguments() + i);
    if (source.getType() != target.getType() ||
        !replica.try_emplace(source, target).second)
      return false;
  }
  return true;
}
bool readNativeRequestBranchYield(const NativeRequestBranch &branch,
                                  unsigned arm, ValueRange actual,
                                  unsigned extraOutputs,
                                  const NativeRequestValues &ordinary,
                                  const NativeRequestValues &replica) {
  if (arm >= branch.arms.size())
    return false;
  auto &frame = *branch.arms[arm];
  auto expected =
      cast<pir::ProtocolYieldOp>(frame.producer->back()).getOperands();
  if (actual.size() != expected.size() + branch.outputs.size() + extraOutputs ||
      branch.yielded[arm].size() != branch.outputs.size())
    return false;
  for (auto [i, source] : enumerate(expected)) {
    Value value = ordinary.lookup(source);
    if (!value || actual[i] != value)
      return false;
  }
  for (auto [i, input] : enumerate(branch.yielded[arm])) {
    Value value = resolveNativeRequestValue(input, ordinary, replica);
    if (!value || actual[expected.size() + i] != value)
      return false;
  }
  return true;
}
bool bindNativeRequestBranchOutputs(const NativeRequestBranch &branch,
                                    pir::ParticipantBranchOp actual,
                                    unsigned extraOutputs,
                                    NativeRequestValues &ordinary,
                                    NativeRequestValues &replica) {
  auto p = branch.producer;
  if (!actual || actual.getNumResults() !=
                     p.getNumResults() + branch.outputs.size() + extraOutputs)
    return false;
  for (auto [source, target] : zip(p.getResults(), actual.getResults()))
    if (source.getType() != target.getType() ||
        !ordinary.try_emplace(source, target).second)
      return false;
  for (auto [i, index] : enumerate(branch.outputs)) {
    Value source = pir::ParticipantBranchOp(branch.validator).getResult(index);
    Value target = actual.getResult(p.getNumResults() + i);
    if (source.getType() != target.getType() ||
        !replica.try_emplace(source, target).second)
      return false;
  }
  return true;
}

Expected<NativeRequestEmission>
emitNativeRequests(const NativeRequestPlan &plan,
                   pir::ProtocolModuleOp candidate,
                   llvm::function_ref<std::string()> fresh) {
  NativeRequestEmission result;
  if (!plan.root)
    return result;
  uint64_t remaining = 1000000;
  if (!requestTree(candidate, remaining))
    return error("native-request-limit");
  SymbolTable symbols(candidate);
  auto producer = symbols.lookup<pir::ParticipantOp>(
      pir::ParticipantOp(plan.producer).getSymName());
  if (!producer || producer.getFunctionType() !=
                       pir::ParticipantOp(plan.producer).getFunctionType())
    return error("native-request-subject");
  OpBuilder builder(candidate.getContext());
  NativeRequestValues ordinary, replicas;
  if (!requestCharge(remaining,
                     1 + producer.getBody().front().getNumArguments()))
    return error("native-request-limit");
  // Construct a fresh isolated body. Original operations retain order and
  // operands through the ordinary map. The caller discards a failed candidate.
  Region replacement;
  auto *body = new Block;
  replacement.push_back(body);
  for (auto arg : producer.getBody().front().getArguments())
    body->addArgument(arg.getType(), arg.getLoc());
  for (auto [a, b] :
       zip(plan.root->producer->getArguments(), body->getArguments()))
    ordinary[a] = b;
  bool valid = true;
  auto charge = [&](uint64_t work) {
    if (work > remaining) {
      remaining = 0;
      valid = false;
      return false;
    }
    remaining -= work;
    return true;
  };
  auto value = [&](NativeRequestValue input) {
    if (!charge(1))
      return Value();
    Value result = resolveNativeRequestValue(input, ordinary, replicas);
    valid &= bool(result);
    return result;
  };
  auto emit = [&](auto &&self, const NativeRequestFrame &frame, Block &target,
                  unsigned depth) -> void {
    if (depth > 64) {
      remaining = 0;
      valid = false;
      return;
    }
    if (!charge(1))
      return;
    for (auto &source : *frame.producer) {
      if (!valid ||
          !charge(1 + source.getNumOperands() + source.getNumResults()))
        return;
      builder.setInsertionPointToEnd(&target);
      auto steps = frame.before.find(&source);
      if (steps != frame.before.end())
        for (const auto &step : steps->second) {
          if (!charge(1 + step.inputs.size() + step.source->getNumResults()))
            return;
          if (!requestTree(step.source, remaining) ||
              !closedRequestRegions(step.source, remaining)) {
            valid = false;
            return;
          }
          if (step.inputs.size() != step.source->getNumOperands()) {
            valid = false;
            return;
          }
          SmallVector<Value> inputs;
          for (auto input : step.inputs)
            inputs.push_back(value(input));
          if (!valid)
            return;
          IRMapping mapping;
          for (auto [a, b] : zip(step.source->getOperands(), inputs)) {
            Value prior = mapping.lookupOrNull(a);
            if (a.getType() != b.getType() || (prior && prior != b)) {
              valid = false;
              return;
            }
            mapping.map(a, b);
          }
          auto *copy = builder.clone(*step.source, mapping);
          if (auto call = dyn_cast<pir::LocalCallOp>(copy)) {
            call.setSite(fresh());
            call.setRole(producer.getRole());
            auto *at = &source;
            while (at && !at->getAttrOfType<StringAttr>("site")) {
              if (!charge(1))
                return;
              at = at->getPrevNode();
            }
            auto anchor =
                at ? at->getAttrOfType<StringAttr>("site") : StringAttr();
            if (!anchor)
              anchor = step.source->getAttrOfType<StringAttr>("site");
            if (!anchor) {
              valid = false;
              return;
            }
            result.actions.push_back({anchor.str(), call});
          }
          for (auto [a, b] : zip(step.source->getResults(), copy->getResults()))
            replicas[a] = b;
        }
      if (auto receive = dyn_cast<pir::AwaitOp>(source);
          frame.requests.count(&source)) {
        Value payload = value(frame.requests.lookup(&source));
        if (!valid)
          return;
        // Emitter consumes this actual receive slot into a payload observation.
        auto copy = pir::AwaitOp::create(
            builder, source.getLoc(), receive.getOutput().getType(),
            receive.getSite(), receive.getSchema(), receive.getPeer());
        result.requests[copy] = payload;
        ordinary[receive.getOutput()] = copy.getOutput();
        continue;
      }
      auto selected = frame.branches.find(&source);
      if (selected != frame.branches.end()) {
        const auto &branch = *selected->second;
        auto p = branch.producer;
        if (!charge(1 + branch.captured.size() + branch.outputs.size() +
                    branch.arms.size()))
          return;
        SmallVector<Value> inputs;
        for (Value input : p.getInputs())
          inputs.push_back(ordinary.lookup(input));
        for (auto input : branch.captured)
          inputs.push_back(value(input));
        if (!valid || is_contained(inputs, Value())) {
          valid = false;
          return;
        }
        SmallVector<Type> outputs(p.getResultTypes());
        for (unsigned index : branch.outputs)
          outputs.push_back(pir::ParticipantBranchOp(branch.validator)
                                .getResult(index)
                                .getType());
        OperationState state(p.getLoc(), p->getName());
        state.addOperands(inputs);
        state.addTypes(outputs);
        state.addAttributes(p->getAttrs());
        for (unsigned i = 0; i < branch.arms.size(); ++i)
          state.addRegion();
        auto copy = cast<pir::ParticipantBranchOp>(builder.create(state));
        // Construct every arm's formal shape before the independent binding
        // helper inspects it. The branch's state slots are outside this layer.
        for (auto [i, arm] : enumerate(branch.arms)) {
          if (!charge(1 + arm->producer->getNumArguments() +
                      branch.captured.size()))
            return;
          auto *child = new Block;
          copy->getRegion(i).push_back(child);
          for (auto arg : arm->producer->getArguments())
            child->addArgument(arg.getType(), arg.getLoc());
          for (auto input : branch.captured)
            child->addArgument(input.source.getType(), p.getLoc());
        }
        if (!readNativeRequestBranchInputs(branch, copy, 0, 0, ordinary,
                                           replicas)) {
          valid = false;
          return;
        }
        if (!charge(ordinary.size() + replicas.size()))
          return;
        auto parentOrdinary = ordinary, parentReplicas = replicas;
        for (auto [i, arm] : enumerate(branch.arms)) {
          if (!charge(parentOrdinary.size() + parentReplicas.size() +
                      arm->producer->getNumArguments() +
                      branch.captured.size()))
            return;
          ordinary = parentOrdinary;
          replicas = parentReplicas;
          if (!bindNativeRequestBranchArm(branch, copy, i, 0, 0, ordinary,
                                          replicas)) {
            valid = false;
            return;
          }
          self(self, *arm, copy->getRegion(i).front(), depth + 1);
          if (!valid)
            return;
        }
        ordinary = std::move(parentOrdinary);
        replicas = std::move(parentReplicas);
        if (!bindNativeRequestBranchOutputs(branch, copy, 0, ordinary,
                                            replicas)) {
          valid = false;
          return;
        }
        continue;
      }
      auto paired = frame.loops.find(&source);
      if (paired != frame.loops.end()) {
        const auto &loop = *paired->second;
        auto p = loop.producer;
        if (!charge(1 + loop.initial.size() + loop.captured.size() +
                    loop.carried.size() +
                    p.getBody().front().getNumArguments() +
                    loop.carried.size() + loop.captures.size()))
          return;
        unsigned split = 1 + p.getCarried();
        SmallVector<Value> inputs;
        for (Value input : p.getInputs().take_front(split))
          inputs.push_back(ordinary.lookup(input));
        if (loop.count)
          inputs[0] = value(*loop.count);
        for (auto input : loop.initial)
          inputs.push_back(value(input));
        for (Value input : p.getInputs().drop_front(split))
          inputs.push_back(ordinary.lookup(input));
        for (auto input : loop.captured)
          inputs.push_back(value(input));
        SmallVector<Type> outputs(p.getResultTypes());
        for (unsigned index : loop.carried)
          outputs.push_back(
              pir::ProtocolLoopOp(loop.validator).getResult(index).getType());
        if (!valid || is_contained(inputs, Value())) {
          valid = false;
          return;
        }
        auto copy = pir::ProtocolLoopOp::create(
            builder, p.getLoc(), outputs, inputs, p.getSiteAttr(),
            builder.getI64IntegerAttr(p.getCarried() + loop.carried.size()),
            p.getCountAttr(), p.getParameterAttr(), p.getMaximumAttr());
        auto *child = new Block;
        copy.getBody().push_back(child);
        auto &old = p.getBody().front();
        for (auto arg : old.getArguments().take_front(split))
          child->addArgument(arg.getType(), arg.getLoc());
        for (unsigned index : loop.carried)
          child->addArgument(
              loop.body->validator->getArgument(1 + index).getType(),
              p.getLoc());
        for (auto arg : old.getArguments().drop_front(split))
          child->addArgument(arg.getType(), arg.getLoc());
        for (unsigned index : loop.captures)
          child->addArgument(
              loop.body->validator
                  ->getArgument(
                      1 + pir::ProtocolLoopOp(loop.validator).getCarried() +
                      index)
                  .getType(),
              p.getLoc());
        if (!charge(ordinary.size() + replicas.size()))
          return;
        auto parentOrdinary = ordinary, parentReplicas = replicas;
        for (unsigned i = 0; i < old.getNumArguments(); ++i)
          ordinary[old.getArgument(i)] =
              child->getArgument(i < split ? i : i + loop.carried.size());
        if (!bindNativeRequestLoop(loop, copy, 0, replicas)) {
          valid = false;
          return;
        }
        self(self, *loop.body, *child, depth + 1);
        ordinary = std::move(parentOrdinary);
        replicas = std::move(parentReplicas);
        for (auto [i, index] : enumerate(loop.carried))
          replicas[pir::ProtocolLoopOp(loop.validator).getResult(index)] =
              copy.getResult(p.getNumResults() + i);
        for (auto [a, b] : zip(p.getResults(), copy.getResults()))
          ordinary[a] = b;
        continue;
      }
      if (!requestTree(&source, remaining)) {
        valid = false;
        return;
      }
      IRMapping mapping;
      for (Value input : source.getOperands()) {
        Value actual = ordinary.lookup(input);
        if (!actual) {
          valid = false;
          return;
        }
        mapping.map(input, actual);
      }
      // MLIR clone maps internal definitions itself. Every external use must
      // already be in the explicit ordinary environment, including nested uses.
      source.walk([&](Operation *nested) {
        if (!charge(1 + nested->getNumOperands()))
          return WalkResult::interrupt();
        for (Value input : nested->getOperands()) {
          Operation *owner = input.getParentBlock()->getParentOp();
          if (owner == &source || source.isAncestor(owner))
            continue;
          Value actual = ordinary.lookup(input);
          if (!actual) {
            valid = false;
            return WalkResult::interrupt();
          }
          mapping.map(input, actual);
        }
        return WalkResult::advance();
      });
      if (!valid)
        return;
      auto *copy = builder.clone(source, mapping);
      if (isa<pir::ProtocolYieldOp>(copy) && frame.loop) {
        SmallVector<Value> yielded;
        for (auto input : frame.loop->yielded)
          yielded.push_back(value(input));
        if (!valid)
          return;
        copy->insertOperands(copy->getNumOperands(), yielded);
      }
      if (isa<pir::ProtocolYieldOp>(copy) && frame.branch) {
        SmallVector<Value> yielded;
        for (auto input : frame.branch->yielded[frame.arm])
          yielded.push_back(value(input));
        if (!valid)
          return;
        copy->insertOperands(copy->getNumOperands(), yielded);
      }
      for (auto [a, b] : zip(source.getResults(), copy->getResults()))
        ordinary[a] = b;
    }
  };
  emit(emit, *plan.root, *body, 0);
  if (!valid)
    return error(
        remaining ? "native-request-emission" : "native-request-limit",
        "unresolved actual source slot or exhausted emission allowance");
  producer.getBody().takeBody(replacement);
  return result;
}
} // namespace zkc::detail
