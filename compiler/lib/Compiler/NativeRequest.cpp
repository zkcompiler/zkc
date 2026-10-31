#include "NativeRequest.h"
#include "NativeProofVerification.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
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
class Planner {
  pir::ProtocolModuleOp module;
  const NativeProofPolicy &policy;
  ArrayRef<NativeTranscriptEvent> events;
  SymbolTable symbols;
  protocol::SourceExecutionClosure execution;
  NativeRequestPlan plan;
  StringMap<Operation *> producerSites, validatorSites;
  StringMap<StringRef> draws;
  llvm::DenseSet<Operation *> deterministic, active;
  llvm::DenseMap<Operation *, NativeRequestLoop *> validatorLoops;
  ArrayRef<NativeRequestCountPair> structuralCounts;
  unsigned remaining = 1000000;
  std::string problem;
  bool charge(unsigned work = 1) {
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
  bool types(TypeRange types) {
    return all_of(types, [&](Type type) { return charge() && dataType(type); });
  }
  bool finiteOperation(Operation *op, unsigned depth) {
    finite::Computation model;
    if (!charge() || depth > 64 || failed(finite::describe(op, model)) ||
        !model.domain || !model.helper || !domain(model.domain, depth + 1))
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
    if (!charge() || depth > 64 || !hasSingleElement(function.getBody()) ||
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
    if (!function || !charge() || depth > 64 || function.isExternal() ||
        !hasSingleElement(function.getBody()) ||
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
    if (!function || !charge() || depth > 64)
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
  bool same(Value v, Value p, NativeRequestFrame &frame, unsigned depth = 0) {
    if (!charge() || depth > 64 || v.getType() != p.getType())
      return false;
    auto known = frame.relations.find(v);
    if (known != frame.relations.end() && known->second.ordinary &&
        known->second.source == p)
      return true;
    auto va = dyn_cast<BlockArgument>(v), pa = dyn_cast<BlockArgument>(p);
    if (va && pa && frame.loop && va.getOwner() == frame.validator &&
        pa.getOwner() == frame.producer &&
        va.getArgNumber() > frame.loop->validator.getCarried() &&
        pa.getArgNumber() > frame.loop->producer.getCarried()) {
      // Captures preserve the exact incoming value. Follow each role's actual
      // input slot to the entry frontier; no relation between carried records
      // or equal-looking block arguments is assumed.
      auto &parent = *frame.loop->parent;
      auto prior = parent.relations;
      parent.relations = frame.entryRelations;
      bool equal = same(frame.loop->validator.getInputs()[va.getArgNumber()],
                        frame.loop->producer.getInputs()[pa.getArgNumber()],
                        parent, depth + 1);
      parent.relations = std::move(prior);
      return equal;
    }
    auto *a = v.getDefiningOp(), *b = p.getDefiningOp();
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
    if (!charge() || depth > 64 || !dataType(value.getType())) {
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
        auto prior = loop->parent->relations;
        loop->parent->relations = frame.entryRelations;
        auto input = need(loop->validator.getInputs()[1 + index], *loop->parent,
                          loop->producer, loop->validator, depth + 1);
        // Retain dependencies created at the loop-entry frontier, without
        // importing any later ordinary-send seed into that frontier.
        frame.entryRelations = loop->parent->relations;
        for (const auto &item : loop->parent->relations)
          prior.try_emplace(item.first, item.second);
        loop->parent->relations = std::move(prior);
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
    if (!operation(op))
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
    if (index >= pir::ProtocolLoopOp(loop.validator).getCarried() || depth > 64)
      return fail("invalid replica carry position");
    auto prior = loop.parent->relations;
    loop.parent->relations = frame.entryRelations;
    auto initial = need(loop.validator.getInputs()[1 + index], *loop.parent,
                        loop.producer, loop.validator, depth + 1);
    frame.entryRelations = loop.parent->relations;
    for (const auto &item : loop.parent->relations)
      prior.try_emplace(item.first, item.second);
    loop.parent->relations = std::move(prior);
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
  bool build(NativeRequestFrame &frame, unsigned depth = 0) {
    if (depth > 64)
      return fail("request loop depth limit");
    for (auto &op : *frame.producer) {
      if (!charge())
        return false;
      auto site = op.getAttrOfType<StringAttr>("site");
      auto *other = site ? validatorSites.lookup(site.getValue()) : nullptr;
      if (auto loop = dyn_cast<pir::ProtocolLoopOp>(op)) {
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
        auto fact = find_if(events, [&](const auto &event) {
          return event.site == receive.getSite();
        });
        if (fact == events.end() || !fact->reconstructed || fact->query)
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
    for (const auto &[op, child] : frame.loops) {
      auto p = child->producer, v = child->validator;
      bool structural = is_contained(
          structuralCounts,
          NativeRequestCountPair{p.getInputs()[0], v.getInputs()[0]});
      // The original joint driver checks every participating count before
      // entry, even when this loop has no communication or replica state.
      if (p.getMaximumAttr() != v.getMaximumAttr() ||
          (!structural && !same(v.getInputs()[0], p.getInputs()[0], frame)))
        return fail("loop count needs checked structural recurrence");
      if (structural) {
        auto prior = frame.relations;
        frame.relations = child->body->entryRelations;
        auto count = need(v.getInputs()[0], frame, p, v);
        child->body->entryRelations = frame.relations;
        for (const auto &item : frame.relations)
          prior.try_emplace(item.first, item.second);
        frame.relations = std::move(prior);
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
          ArrayRef<NativeRequestCountPair> structuralCounts)
      : module(module), policy(policy), events(events), symbols(module),
        execution(std::move(execution)), structuralCounts(structuralCounts) {}
  Expected<NativeRequestPlan> run() {
    // Every paired source loop requires count correspondence, even without
    // events. Profile restrictions apply only to new request synthesis.
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
        if (auto site = op->getAttrOfType<StringAttr>("site"))
          ok &= charge() && sites.try_emplace(site.getValue(), op).second;
      });
      return ok;
    };
    if (!index(plan.producer, producerSites) ||
        !index(plan.validator, validatorSites))
      return error("native-request-sites");
    for (const auto &draw : policy.draws)
      draws[draw.second] = draw.first;
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
      for (auto [i, port] : enumerate(row.getAs<ArrayAttr>("inputs")))
        ports[cast<IntegerAttr>(port).getInt()] =
            p.getBody().front().getArgument(i);
    }
    for (unsigned port : policy.publicInputs) {
      Value p = pInputs.lookup(port), v = vInputs.lookup(port);
      if (p && v && p.getType() == v.getType() && dataType(v.getType()))
        root.relations[v] = {p, true};
    }
    if (!build(root) || !counts(root))
      return error(remaining ? "native-request-reconstruction"
                             : "native-request-limit",
                   problem);
    return std::move(plan);
  }
};
} // namespace
Expected<NativeRequestPlan>
planNativeRequests(pir::ProtocolModuleOp projected,
                   const NativeProofPolicy &policy,
                   ArrayRef<NativeTranscriptEvent> events,
                   const mathematical::RealizedProtocol *realization) {
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
  return Planner(projected, policy, events, std::move(*execution), counts)
      .run();
}

Expected<NativeRequestEmission>
emitNativeRequests(const NativeRequestPlan &plan,
                   pir::ProtocolModuleOp candidate,
                   llvm::function_ref<std::string()> fresh) {
  NativeRequestEmission result;
  if (!plan.root)
    return result;
  SymbolTable symbols(candidate);
  auto producer = symbols.lookup<pir::ParticipantOp>(
      pir::ParticipantOp(plan.producer).getSymName());
  if (!producer || producer.getFunctionType() !=
                       pir::ParticipantOp(plan.producer).getFunctionType())
    return error("native-request-subject");
  OpBuilder builder(candidate.getContext());
  NativeRequestValues ordinary, replicas;
  for (auto [a, b] : zip(plan.root->producer->getArguments(),
                         producer.getBody().front().getArguments()))
    ordinary[a] = b;
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
  auto value = [&](NativeRequestValue input) {
    Value result = resolveNativeRequestValue(input, ordinary, replicas);
    valid &= bool(result);
    return result;
  };
  auto emit = [&](auto &&self, const NativeRequestFrame &frame,
                  Block &target) -> void {
    for (auto &source : *frame.producer) {
      builder.setInsertionPointToEnd(&target);
      auto steps = frame.before.find(&source);
      if (steps != frame.before.end())
        for (const auto &step : steps->second) {
          SmallVector<Value> inputs;
          for (auto input : step.inputs)
            inputs.push_back(value(input));
          if (!valid)
            return;
          IRMapping mapping;
          for (auto [a, b] : zip(step.source->getOperands(), inputs))
            mapping.map(a, b);
          auto *copy = builder.clone(*step.source, mapping);
          if (auto call = dyn_cast<pir::LocalCallOp>(copy)) {
            call.setSite(fresh());
            call.setRole(producer.getRole());
            auto *at = &source;
            while (at && !at->getAttrOfType<StringAttr>("site"))
              at = at->getPrevNode();
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
      auto paired = frame.loops.find(&source);
      if (paired != frame.loops.end()) {
        const auto &loop = *paired->second;
        auto p = loop.producer;
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
        for (unsigned i = 0; i < old.getNumArguments(); ++i)
          ordinary[old.getArgument(i)] =
              child->getArgument(i < split ? i : i + loop.carried.size());
        if (!bindNativeRequestLoop(loop, copy, 0, replicas)) {
          valid = false;
          return;
        }
        self(self, *loop.body, *child);
        for (auto [a, b] : zip(p.getResults(), copy.getResults()))
          ordinary[a] = b;
        continue;
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
      auto *copy = builder.clone(source, mapping);
      if (isa<pir::ProtocolYieldOp>(copy) && frame.loop) {
        SmallVector<Value> yielded;
        for (auto input : frame.loop->yielded)
          yielded.push_back(value(input));
        if (!valid)
          return;
        copy->insertOperands(copy->getNumOperands(), yielded);
      }
      for (auto [a, b] : zip(source.getResults(), copy->getResults()))
        ordinary[a] = b;
    }
  };
  emit(emit, *plan.root, *body);
  if (!valid)
    return error("native-request-emission", "unresolved actual source slot");
  producer.getBody().takeBody(replacement);
  return result;
}
} // namespace zkc::detail
