#include "NativeProofVerification.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"
using namespace llvm;
using namespace mlir;
namespace zkc::detail {
namespace {
namespace pir = protocol_ir;
using Env = llvm::DenseMap<Value, Value>;
class TranscriptCorrespondence {
  const NativeProofPolicy &policy;
  ArrayRef<NativeTranscriptEvent> events;
  SymbolTable symbols;
  Type stateType;
  StringMap<const NativeTranscriptEvent *> bySite;
  StringMap<std::string> deliveries;
  StringMap<const NativeTranscriptEvent *> checkedHelpers;
  llvm::StringSet<> bindings, originalSymbols;
  llvm::DenseSet<Operation *> observedLoops;
  size_t remaining = 1000000;
  std::string checkpoint;
  bool charge(size_t work = 1) {
    if (work > remaining) {
      remaining = 0;
      return false;
    }
    remaining -= work;
    return true;
  }
  static StringRef text(Operation *op, StringRef key) {
    auto value = op->getAttrOfType<StringAttr>(key);
    return value ? value.getValue() : StringRef();
  }
  static bool attributes(Operation *a, Operation *b,
                         ArrayRef<StringRef> omitted = {}) {
    NamedAttrList left(a->getAttrs()), right(b->getAttrs());
    for (auto key : omitted) {
      left.erase(key);
      right.erase(key);
    }
    return left == right;
  }
  bool operands(ValueRange a, ValueRange b, const Env &env) {
    if (a.size() != b.size())
      return false;
    for (auto [x, y] : zip(a, b))
      if (!charge() || env.lookup(x) != y)
        return false;
    return true;
  }
  bool bind(ValueRange a, ValueRange b, Env &env) {
    if (a.size() != b.size())
      return false;
    for (auto [x, y] : zip(a, b)) {
      if (!charge() || x.getType() != y.getType())
        return false;
      env[x] = y;
    }
    return true;
  }
  bool exact(Operation &a, Operation &b, Env &env, unsigned depth) {
    if (!charge() || depth > 64 || a.getName() != b.getName() ||
        !attributes(&a, &b) ||
        !operands(a.getOperands(), b.getOperands(), env) ||
        a.getNumRegions() != b.getNumRegions())
      return false;
    for (auto [x, y] : zip(a.getRegions(), b.getRegions())) {
      if (!x.hasOneBlock() || !y.hasOneBlock())
        return false;
      Env inner;
      if (!a.hasTrait<OpTrait::IsIsolatedFromAbove>()) {
        if (!charge(env.size()))
          return false;
        inner = env;
      }
      if (!bind(x.front().getArguments(), y.front().getArguments(), inner) ||
          x.front().getOperations().size() != y.front().getOperations().size())
        return false;
      for (auto [u, v] : zip(x.front(), y.front()))
        if (!exact(u, v, inner, depth + 1))
          return false;
    }
    return bind(a.getResults(), b.getResults(), env);
  }
  bool kernel(Operation *op, StringRef contract,
              ArrayRef<std::string> arguments, ValueRange inputs,
              ArrayRef<std::string> parameters) {
    if (!op || !charge() || op->getAttrs().size() != 3 ||
        !op->getAttrOfType<StringAttr>("site") ||
        op->getName().getStringRef() !=
            protocol::boundOperationName(contract) ||
        op->getOperands() != inputs || op->getNumRegions())
      return false;
    auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto binding =
        reference
            ? symbols.lookup<local::OperationBindingOp>(reference.getValue())
            : local::OperationBindingOp();
    auto strings = [](ArrayAttr a, ArrayRef<std::string> b) {
      if (!a || a.size() != b.size())
        return false;
      for (auto [x, y] : zip(a, b)) {
        auto string = dyn_cast<StringAttr>(x);
        if (!string || string.getValue() != y)
          return false;
      }
      return true;
    };
    if (!binding || binding.getContract() != contract ||
        !binding.getImplementation().empty() ||
        !strings(binding.getArguments(), arguments) ||
        !strings(op->getAttrOfType<ArrayAttr>("parameters"), parameters))
      return false;
    bindings.insert(binding.getSymName());
    return true;
  }
  bool helper(local::FuncOp function, const NativeTranscriptEvent &event) {
    auto prior = checkedHelpers.find(function.getSymName());
    if (prior != checkedHelpers.end())
      return prior->second == &event;
    if (originalSymbols.count(function.getSymName()) ||
        function->getAttrs().size() != 3)
      return false;
    auto origin = function->getAttrOfType<ArrayAttr>("logical_origin");
    if (!origin || origin.size() != 2 || !isa<StringAttr>(origin[0]) ||
        cast<StringAttr>(origin[0]).getValue() != function.getSymName() ||
        !isa<ArrayAttr>(origin[1]) || !cast<ArrayAttr>(origin[1]).empty())
      return false;
    SmallVector<Type> inputs{stateType}, outputs;
    if (event.query)
      outputs.push_back(event.payload);
    else
      inputs.push_back(event.payload);
    unsigned data = inputs.size();
    inputs.append(event.depth, IntegerType::get(function.getContext(), 64,
                                                IntegerType::Unsigned));
    outputs.push_back(stateType);
    if (function.getFunctionType() !=
            FunctionType::get(function.getContext(), inputs, outputs) ||
        !function.getBody().hasOneBlock())
      return false;
    auto &block = function.getBody().front();
    Operation *cursor = &block.front();
    SmallVector<Value> operands(block.getArguments().take_front(data));
    {
      if (!kernel(cursor, "indices.empty", {}, {}, {}))
        return false;
      Value indices = cursor->getResult(0);
      cursor = cursor->getNextNode();
      for (Value coordinate : block.getArguments().drop_front(data)) {
        if (!kernel(cursor, "indices.append", {}, {indices, coordinate}, {}))
          return false;
        indices = cursor->getResult(0);
        cursor = cursor->getNextNode();
      }
      operands.push_back(indices);
    }
    auto logical = protocol::encodeBoundType(event.payload, false);
    if (!logical) {
      consumeError(logical.takeError());
      return false;
    }
    std::string contract = event.query
                               ? "transcript.native.indexed.challenge"
                               : "transcript.native.indexed.observe.data";
    SmallVector<std::string> arguments{policy.suite};
    if (!event.query)
      arguments.push_back(logical->spelling());
    if (!kernel(cursor, contract, arguments, operands, {event.origin}))
      return false;
    auto ret = dyn_cast_if_present<local::ReturnOp>(cursor->getNextNode());
    if (!ret || ret->getNextNode() || ret.getInputs() != cursor->getResults())
      return false;
    checkedHelpers.try_emplace(function.getSymName(), &event);
    return true;
  }
  bool call(Operation *&cursor, const NativeTranscriptEvent &event,
            Value &state, Value payload, ArrayRef<Value> coordinates,
            Value *challenge,
            SmallVectorImpl<const NativeTranscriptEvent *> &reached) {
    auto invocation = dyn_cast_if_present<local::CallOp>(cursor);
    if (!invocation || !charge())
      return false;
    auto function = symbols.lookup<local::FuncOp>(invocation.getCallee());
    if (!function || !helper(function, event))
      return false;
    SmallVector<Value> inputs{state};
    if (payload)
      inputs.push_back(payload);
    append_range(inputs, coordinates);
    if (invocation.getInputs() != ValueRange(inputs) ||
        coordinates.size() != event.depth || event.query != bool(challenge))
      return false;
    if (challenge)
      *challenge = invocation.getResult(0);
    state = invocation.getResults().back();
    reached.push_back(&event);
    cursor = cursor->getNextNode();
    return true;
  }
  bool indexObservedLoops(pir::ParticipantOp participant) {
    observedLoops.clear();
    llvm::DenseSet<Operation *> observed;
    // Discover required state threading from the actual source operations,
    // independently of the supplied event facts. Propagate once in postorder
    // so nested message-only loops cannot hide an omitted event.
    return !participant
                .walk<WalkOrder::PostOrder>([&](Operation *op) {
                  if (!charge())
                    return WalkResult::interrupt();
                  bool required =
                      observed.contains(op) ||
                      isa<pir::EmitOp, pir::AwaitOp, pir::FinishIfOp>(op) ||
                      (isa<pir::ParticipantQueryOp>(op) &&
                       participant.getRole() == policy.validator);
                  if (required) {
                    if (isa<pir::ProtocolLoopOp>(op))
                      observedLoops.insert(op);
                    observed.insert(op->getParentOp());
                  }
                  return WalkResult::advance();
                })
                .wasInterrupted();
  }
  bool body(Block &a, Block &b, Env env, Value state,
            ArrayRef<Value> coordinates, StringRef role,
            SmallVectorImpl<const NativeTranscriptEvent *> &reached,
            unsigned depth) {
    if (depth > 64)
      return false;
    Operation *cursor = &b.front();
    llvm::DenseMap<const NativeTranscriptEvent *, Value> challenges;
    for (auto &op : a) {
      checkpoint =
          op.getName().getStringRef().str() + " at " + text(&op, "site").str();
      if (!charge() || !cursor)
        return false;
      auto event = bySite.find(text(&op, "site"));
      if (event == bySite.end() &&
          (isa<pir::EmitOp, pir::AwaitOp>(op) ||
           (isa<pir::ParticipantQueryOp>(op) && role == policy.validator)))
        return false;
      if (auto loop = dyn_cast<pir::ProtocolLoopOp>(op);
          loop && observedLoops.contains(loop)) {
        auto actual = dyn_cast<pir::ProtocolLoopOp>(cursor);
        unsigned split = 1 + loop.getCarried();
        if (!actual || !loop.getMaximum() ||
            !attributes(&op, cursor, {"carried"}) ||
            actual.getCarried() != loop.getCarried() + 1 ||
            actual.getNumOperands() !=
                loop.getNumOperands() + 1 + coordinates.size() ||
            actual.getNumResults() != loop.getNumResults() + 1 ||
            actual.getInputs()[split] != state ||
            actual.getResults().back().getType() != stateType ||
            !operands(loop.getInputs().take_front(split),
                      actual.getInputs().take_front(split), env) ||
            !operands(loop.getInputs().drop_front(split),
                      actual.getInputs().slice(split + 1,
                                               loop.getNumOperands() - split),
                      env) ||
            actual.getInputs().take_back(coordinates.size()) !=
                ValueRange(coordinates))
          return false;
        auto &x = loop.getBody().front();
        auto &y = actual.getBody().front();
        Env inner;
        if (y.getNumArguments() !=
                x.getNumArguments() + 1 + coordinates.size() ||
            y.getArgument(split).getType() != stateType ||
            !bind(x.getArguments().take_front(split),
                  y.getArguments().take_front(split), inner) ||
            !bind(
                x.getArguments().drop_front(split),
                y.getArguments().slice(split + 1, x.getNumArguments() - split),
                inner))
          return false;
        SmallVector<Value> indices(
            y.getArguments().take_back(coordinates.size()));
        indices.push_back(y.getArgument(0));
        if (!body(x, y, std::move(inner), y.getArgument(split), indices, role,
                  reached, depth + 1) ||
            !bind(loop.getResults(), actual.getResults().drop_back(), env))
          return false;
        state = actual.getResults().back();
        cursor = cursor->getNextNode();
      } else if (isa<pir::FinishOp, pir::ProtocolYieldOp, pir::FinishIfOp>(
                     op)) {
        bool continuing = isa<pir::FinishIfOp>(op);
        if (op.getName() != cursor->getName() || !attributes(&op, cursor) ||
            cursor->getNumOperands() != op.getNumOperands() + 1 ||
            cursor->getNumResults() !=
                op.getNumResults() + unsigned(continuing) ||
            cursor->getOperands().back() != state ||
            !operands(op.getOperands(), cursor->getOperands().drop_back(),
                      env) ||
            !bind(op.getResults(),
                  cursor->getResults().take_front(op.getNumResults()), env))
          return false;
        if (continuing) {
          state = cursor->getResults().back();
          if (state.getType() != stateType)
            return false;
        }
        cursor = cursor->getNextNode();
      } else if (event != bySite.end()) {
        const auto &fact = *event->second;
        auto delivery = deliveries.find(fact.site);
        if (isa<pir::ParticipantQueryOp>(op)) {
          Value challenge;
          if (role != policy.validator || !fact.query ||
              !call(cursor, fact, state, {}, coordinates, &challenge,
                    reached) ||
              op.getNumResults() != 1 ||
              challenge.getType() != op.getResult(0).getType())
            return false;
          env[op.getResult(0)] = challenge;
          challenges[&fact] = challenge;
        } else if (auto receive = dyn_cast<pir::AwaitOp>(op)) {
          Value payload;
          if (fact.query)
            return false;
          if (delivery != deliveries.end()) {
            auto query = bySite.find(delivery->second);
            if (role != policy.producer || query == bySite.end() ||
                !query->second->query ||
                !call(cursor, *query->second, state, {}, coordinates, &payload,
                      reached) ||
                payload.getType() != receive.getOutput().getType())
              return false;
            env[receive.getOutput()] = payload;
          } else {
            if (role != policy.validator || !exact(op, *cursor, env, depth))
              return false;
            payload = env.lookup(receive.getOutput());
            cursor = cursor->getNextNode();
          }
          if (!call(cursor, fact, state, payload, coordinates, nullptr,
                    reached))
            return false;
        } else if (auto send = dyn_cast<pir::EmitOp>(op)) {
          if (fact.query ||
              role != (delivery != deliveries.end() ? policy.validator
                                                    : policy.producer))
            return false;
          if (delivery == deliveries.end()) {
            if (!exact(op, *cursor, env, depth))
              return false;
            cursor = cursor->getNextNode();
          }
          Value payload = env.lookup(send.getInput());
          if (delivery != deliveries.end()) {
            auto query = bySite.find(delivery->second);
            if (query == bySite.end() ||
                challenges.lookup(query->second) != payload)
              return false;
          }
          if (!payload || !call(cursor, fact, state, payload, coordinates,
                                nullptr, reached))
            return false;
        } else
          return false;
      } else {
        if (!exact(op, *cursor, env, depth))
          return false;
        cursor = cursor->getNextNode();
      }
    }
    return !cursor;
  }
  bool participant(pir::ParticipantOp a, pir::ParticipantOp b) {
    if (!indexObservedLoops(a) ||
        !attributes(a, b, {"function_type", "service_ports"}))
      return false;
    auto x = a.getFunctionType(), y = b.getFunctionType();
    if (y.getNumInputs() != x.getNumInputs() + 1 ||
        y.getNumResults() != x.getNumResults() + 1 ||
        y.getInputs().drop_back() != x.getInputs() ||
        y.getResults().drop_back() != x.getResults() ||
        y.getInputs().back() != stateType || y.getResults().back() != stateType)
      return false;
    if (a.getRole() == policy.validator) {
      if (b->hasAttr("service_ports"))
        return false;
    } else if (a->getAttr("service_ports") != b->getAttr("service_ports"))
      return false;
    auto &before = a.getBody().front();
    auto &after = b.getBody().front();
    Env env;
    if (!bind(before.getArguments(), after.getArguments().drop_back(), env))
      return false;
    SmallVector<const NativeTranscriptEvent *> reached;
    if (!body(before, after, std::move(env), after.getArguments().back(), {},
              a.getRole(), reached, 0) ||
        reached.size() != events.size())
      return false;
    for (auto [actual, expected] : zip(reached, events))
      if (actual != &expected)
        return false;
    return true;
  }
  bool projection(pir::ProjectionOp a, pir::ProjectionOp b) {
    if (a.getInterfaces().size() != 1 || b.getInterfaces().size() != 1 ||
        !attributes(a, b, {"interfaces"}))
      return false;
    auto before = cast<DictionaryAttr>(a.getInterfaces()[0]);
    NamedAttrList after(cast<DictionaryAttr>(b.getInterfaces()[0]));
    auto construction =
        dyn_cast_if_present<DictionaryAttr>(after.erase("construction"));
    if (!construction || construction.size() != 4 ||
        after.getDictionary(a.getContext()) != before ||
        !construction.getAs<StringAttr>("format") ||
        construction.getAs<StringAttr>("format").getValue() !=
            "zkc.native-construction/5" ||
        !construction.getAs<TypeAttr>("transcript") ||
        construction.getAs<TypeAttr>("transcript").getValue() != stateType)
      return false;
    auto removed = construction.getAs<ArrayAttr>("removed_services");
    return removed && removed.size() == 1 && policy.service &&
           isa<IntegerAttr>(removed[0]) &&
           cast<IntegerAttr>(removed[0]).getInt() == *policy.service &&
           bool(construction.getAs<ArrayAttr>("actions"));
  }

public:
  TranscriptCorrespondence(pir::ProtocolModuleOp candidate,
                           const NativeProofPolicy &policy,
                           ArrayRef<NativeTranscriptEvent> events)
      : policy(policy), events(events), symbols(candidate),
        stateType(local::CapabilityType::get(candidate.getContext(),
                                             "transcript:" + policy.suite)) {}
  bool check(pir::ProtocolModuleOp before, pir::ProtocolModuleOp after) {
    if (!attributes(before, after))
      return false;
    llvm::StringSet<> origins, queries;
    for (const auto &event : events) {
      if (!bySite.try_emplace(event.site, &event).second ||
          !origins.insert(event.origin).second)
        return false;
      if (event.query)
        queries.insert(event.site);
    }
    for (const auto &draw : policy.draws) {
      auto delivery = bySite.find(draw.second);
      if (!deliveries.try_emplace(draw.second, draw.first).second ||
          !queries.erase(draw.first) || delivery == bySite.end() ||
          delivery->second->query)
        return false;
    }
    if (!queries.empty())
      return false;
    for (auto &op : before.getBody().front())
      if (auto name = op.getAttrOfType<StringAttr>("sym_name"))
        originalSymbols.insert(name.getValue());
    unsigned projections = 0;
    for (auto &op : before.getBody().front()) {
      if (!charge())
        return false;
      if (auto record = dyn_cast<pir::ProjectionOp>(op)) {
        auto records = after.getBody().front().getOps<pir::ProjectionOp>();
        if (!hasSingleElement(records) || !projection(record, *records.begin()))
          return false;
        ++projections;
        continue;
      }
      auto name = op.getAttrOfType<StringAttr>("sym_name");
      auto *actual = name ? symbols.lookup(name.getValue()) : nullptr;
      if (!actual)
        return false;
      if (auto p = dyn_cast<pir::ParticipantOp>(op)) {
        auto q = dyn_cast<pir::ParticipantOp>(actual);
        if (!q || !participant(p, q))
          return false;
      } else if (!OperationEquivalence::isEquivalentTo(
                     &op, actual, OperationEquivalence::IgnoreLocations))
        return false;
    }
    for (auto &op : after.getBody().front()) {
      if (!charge())
        return false;
      if (isa<pir::ProjectionOp>(op))
        continue;
      auto name = text(&op, "sym_name");
      if (originalSymbols.count(name))
        continue;
      if (isa<local::FuncOp>(op) && checkedHelpers.count(name))
        continue;
      if (isa<local::OperationBindingOp>(op) && bindings.count(name))
        continue;
      return false;
    }
    return projections == 1 && checkedHelpers.size() == events.size();
  }
  bool exhausted() const { return !remaining; }
  StringRef detail() const { return checkpoint; }
};
} // namespace
Error verifyNativeEntrySelection(ModuleOp prepared, ModuleOp selected,
                                 StringRef entry) {
  if (!prepared || !selected || failed(verify(prepared)) ||
      failed(verify(selected)) || !hasSingleElement(*prepared.getBody()) ||
      !hasSingleElement(*selected.getBody()))
    return error("native-entry-correspondence");
  auto a = dyn_cast<pir::ProtocolModuleOp>(prepared.getBody()->front());
  auto b = dyn_cast<pir::ProtocolModuleOp>(selected.getBody()->front());
  if (!a || !b || a->getAttrDictionary() != b->getAttrDictionary())
    return error("native-entry-correspondence");
  auto cursor = b.getBody().front().begin();
  unsigned entries = 0;
  for (auto &op : a.getBody().front()) {
    if (auto protocol = dyn_cast<pir::MathematicalOp>(op)) {
      if (protocol.getSymName() != entry)
        continue;
      ++entries;
    }
    if (cursor == b.getBody().front().end() ||
        !OperationEquivalence::isEquivalentTo(
            &op, &*cursor++, OperationEquivalence::IgnoreLocations))
      return error("native-entry-correspondence");
  }
  if (entries != 1 || cursor != b.getBody().front().end())
    return error("native-entry-correspondence");
  return Error::success();
}
Error verifyNativeTranscript(ModuleOp projected, ModuleOp constructed,
                             const NativeProofPolicy &policy,
                             ArrayRef<NativeTranscriptEvent> events) {
  if (!projected || !constructed ||
      projected.getContext() != constructed.getContext() ||
      failed(verify(projected)) || failed(verify(constructed)) ||
      !hasSingleElement(*projected.getBody()) ||
      !hasSingleElement(*constructed.getBody()))
    return error("native-transcript-subject");
  if (policy.suite.empty()) {
    if (!OperationEquivalence::isEquivalentTo(
            projected, constructed, OperationEquivalence::IgnoreLocations))
      return error("native-transcript-correspondence");
    return Error::success();
  }
  auto before = dyn_cast<pir::ProtocolModuleOp>(projected.getBody()->front());
  auto after = dyn_cast<pir::ProtocolModuleOp>(constructed.getBody()->front());
  if (!before || !after || before.getProfile() != pir::Profile::Participant ||
      after.getProfile() != pir::Profile::Participant)
    return error("native-transcript-subject");
  TranscriptCorrespondence checker(after, policy, events);
  if (!checker.check(before, after))
    return error(checker.exhausted() ? "native-transcript-limit"
                                     : "native-transcript-correspondence",
                 checker.detail());
  return Error::success();
}
} // namespace zkc::detail
