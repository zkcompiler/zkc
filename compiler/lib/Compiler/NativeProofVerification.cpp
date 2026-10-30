#include "NativeProofVerification.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/MathExtras.h"
#include <map>
using namespace llvm;
using namespace mlir;
namespace zkc::detail {
namespace {
namespace pir = protocol_ir;
using Env = llvm::DenseMap<Value, Value>;
class TranscriptCorrespondence {
  const NativeProofPolicy &policy;
  const protocol::ConstructionPlan *plan;
  StringMap<const protocol::ConstructionRule *> rules;
  std::map<std::string, protocol::ConstructionRule> startRules;
  llvm::StringSet<> rootHelpers, recordedHelpers;
  bool hostRoot;
  ArrayRef<NativeTranscriptEvent> events;
  SymbolTable symbols;
  const protocol::SourceExecutionClosure &execution;
  SmallVector<Type> stateTypes;
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
  bool kernel(const protocol::SourceExecutionStep *step, StringRef contract,
              ArrayRef<Attribute> arguments, ValueRange inputs,
              ArrayRef<std::string> parameters, StringRef site) {
    if (!step || !charge(1 + inputs.size()) || !step->regions.empty())
      return false;
    auto *op = step->operation;
    if (!isa<exec::ApplyOp>(op) || op->getAttrs().size() != 3 ||
        text(op, "site") != site || ValueRange(step->inputs) != inputs)
      return false;
    auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto binding =
        reference ? symbols.lookup<runtime::BindingOp>(reference.getValue())
                  : runtime::BindingOp();
    if (!binding || binding.getContract() != contract ||
        !binding.getImplementation().empty() ||
        !llvm::equal(binding.getArguments(), arguments) ||
        !protocol::invocationParametersMatch(
            contract, binding.getArgumentsAttr(),
            op->getAttrOfType<ArrayAttr>("parameters"), parameters))
      return false;
    bindings.insert(binding.getSymName());
    return true;
  }
  bool helper(func::FuncOp function, const NativeTranscriptEvent &event) {
    auto prior = checkedHelpers.find(function.getSymName());
    if (prior != checkedHelpers.end())
      return prior->second == &event;
    if (originalSymbols.count(function.getSymName()) ||
        function->getAttrs().size() != 5 || !function.isPrivate() ||
        !function->getAttrOfType<UnitAttr>("no_inline"))
      return false;
    auto origin = function->getAttrOfType<ArrayAttr>("runtime.origin");
    if (!origin || origin.size() != 2 || !isa<StringAttr>(origin[0]) ||
        cast<StringAttr>(origin[0]).getValue() != function.getSymName() ||
        !isa<ArrayAttr>(origin[1]) || !cast<ArrayAttr>(origin[1]).empty())
      return false;
    auto *rule = rules.lookup(event.site);
    if ((!rule && plan && !plan->nativeBase) ||
        (!rule && event.bound && !isPowerOf2_64(*event.bound)))
      return false;
    SmallVector<Type> inputs(stateTypes), outputs;
    if (event.query)
      outputs.push_back(event.payload);
    else if (event.startInputs)
      append_range(inputs, *event.startInputs);
    else if (rule)
      append_range(inputs, rule->payload);
    else
      inputs.push_back(event.payload);
    unsigned data = inputs.size();
    inputs.append(event.depth, IntegerType::get(function.getContext(), 64,
                                                IntegerType::Unsigned));
    append_range(outputs, stateTypes);
    auto signature = protocol::scopedDataSignature(function);
    auto found = execution.bodies.find(function.getSymName().str());
    if (!signature || signature.getInputs() != ArrayRef<Type>(inputs) ||
        signature.getResults() != ArrayRef<Type>(outputs) ||
        found == execution.bodies.end())
      return false;
    const auto &body = found->second;
    size_t cursor = 0;
    auto take = [&]() -> const protocol::SourceExecutionStep * {
      return cursor < body.size() ? &body[cursor++] : nullptr;
    };
    auto arguments = function.getArguments().drop_front();
    SmallVector<Value> operands(arguments.take_front(data));
    if (event.bound) {
      auto *step = take();
      if (!event.query ||
          !kernel(step, "index.constant", {}, {},
                  {std::to_string(*event.bound)}, "bound") ||
          step->outputs.size() != 1 ||
          step->outputs[0].getType() != event.payload)
        return false;
      operands.push_back(step->outputs[0]);
    }
    SmallVector<Value> results;
    if (rule) {
      auto *step = take();
      auto call =
          step ? dyn_cast<func::CallOp>(step->operation) : func::CallOp();
      auto source = symbols.lookup<func::FuncOp>(rule->handler.getValue());
      auto handler = protocol::scopedDataSignature(source);
      if (!handler || !call || call->getAttrs().size() != 2 ||
          call.getCalleeAttr() != rule->handler ||
          text(call, "runtime.site") != "handler" ||
          ValueRange(step->inputs) != ValueRange(operands) ||
          step->outputs.size() != handler.getNumResults() ||
          step->outputs.size() != stateTypes.size() + unsigned(event.query))
        return false;
      if (event.query)
        results.push_back(step->outputs.back());
      append_range(results,
                   ArrayRef(step->outputs).take_front(stateTypes.size()));
      if (event.bound) {
        auto *range = take();
        if (!kernel(range, "index.less", {}, {results.front(), operands.back()},
                    {}, "range") ||
            range->outputs.size() != 1)
          return false;
        auto *require = take();
        if (!kernel(require, "control.require", {}, range->outputs, {},
                    "require_range") ||
            !require->outputs.empty())
          return false;
      }
    } else {
      if (event.startInputs)
        return false;
      auto *empty = take();
      if (!kernel(empty, "indices.empty", {}, {}, {}, "coordinates") ||
          empty->outputs.size() != 1)
        return false;
      Value indices = empty->outputs[0];
      for (auto [i, coordinate] : enumerate(arguments.drop_front(data))) {
        auto *append = take();
        if (!kernel(append, "indices.append", {}, {indices, coordinate}, {},
                    "coordinate_" + std::to_string(i)) ||
            append->outputs.size() != 1)
          return false;
        indices = append->outputs[0];
      }
      operands.push_back(indices);
      std::string contract =
          !event.query  ? "transcript.native.indexed.observe.data"
          : event.bound ? "transcript.native.indexed.index"
                        : "transcript.native.indexed.challenge";
      SmallVector<Attribute> parameters{
          StringAttr::get(function.getContext(), policy.suite)};
      if (!event.query)
        parameters.push_back(TypeAttr::get(event.payload));
      auto *step = take();
      if (!kernel(step, contract, parameters, operands, {event.origin},
                  "transition"))
        return false;
      results = step->outputs;
    }
    auto *returned = take();
    if (!returned || !isa<exec::ReturnOp>(returned->operation) ||
        returned->inputs != results || cursor != body.size())
      return false;
    checkedHelpers.try_emplace(function.getSymName(), &event);
    return true;
  }
  bool call(Operation *&cursor, const NativeTranscriptEvent &event,
            SmallVectorImpl<Value> &state, ValueRange payload,
            ArrayRef<Value> coordinates, Value *challenge,
            SmallVectorImpl<const NativeTranscriptEvent *> &reached) {
    auto invocation = dyn_cast_if_present<pir::LocalCallOp>(cursor);
    if (!invocation || !charge())
      return false;
    auto function = symbols.lookup<func::FuncOp>(invocation.getCallee());
    if (!function || !helper(function, event))
      return false;
    SmallVector<Value> inputs(state.begin(), state.end());
    append_range(inputs, payload);
    append_range(inputs, coordinates);
    if (invocation.getInputs() != ValueRange(inputs) ||
        coordinates.size() != event.depth || event.query != bool(challenge))
      return false;
    if (challenge)
      *challenge = invocation.getResult(0);
    state.clear();
    append_range(state, invocation.getResults().take_back(stateTypes.size()));
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
                      isa<pir::EmitOp, pir::AwaitOp, pir::FinishIfOp,
                          pir::ConstructionStartOp>(op) ||
                      (isa<pir::ParticipantQueryOp>(op) &&
                       bySite.contains(text(op, "site")));
                  if (required) {
                    if (isa<pir::ProtocolLoopOp>(op))
                      observedLoops.insert(op);
                    observed.insert(op->getParentOp());
                  }
                  return WalkResult::advance();
                })
                .wasInterrupted();
  }
  bool body(Block &a, Block &b, Env env, SmallVector<Value> state,
            ArrayRef<Value> coordinates, StringRef role,
            SmallVectorImpl<const NativeTranscriptEvent *> &reached,
            unsigned depth, Operation *first = nullptr) {
    if (depth > 64)
      return false;
    Operation *cursor = first ? first : &b.front();
    SmallVector<Value> payloadGroup;
    auto observe = [&](const NativeTranscriptEvent &event, Value payload) {
      payloadGroup.push_back(payload);
      auto *rule = rules.lookup(event.site);
      if (rule && rule->sites.back() != event.site) {
        reached.push_back(&event);
        return true;
      }
      bool valid = call(cursor, event, state, payloadGroup, coordinates,
                        nullptr, reached);
      payloadGroup.clear();
      return valid;
    };
    llvm::DenseMap<const NativeTranscriptEvent *, Value> challenges;
    for (auto &op : a) {
      checkpoint =
          op.getName().getStringRef().str() + " at " + text(&op, "site").str();
      if (!charge() || !cursor)
        return false;
      auto event = bySite.find(text(&op, "site"));
      if (event == bySite.end() && isa<pir::EmitOp, pir::AwaitOp>(op))
        return false;
      if (auto loop = dyn_cast<pir::ProtocolLoopOp>(op);
          loop && observedLoops.contains(loop)) {
        auto actual = dyn_cast<pir::ProtocolLoopOp>(cursor);
        unsigned split = 1 + loop.getCarried();
        if (!actual || !loop.getMaximum() ||
            !attributes(&op, cursor, {"carried"}) ||
            actual.getCarried() != loop.getCarried() + stateTypes.size() ||
            actual.getNumOperands() != loop.getNumOperands() +
                                           stateTypes.size() +
                                           coordinates.size() ||
            actual.getNumResults() !=
                loop.getNumResults() + stateTypes.size() ||
            actual.getInputs().slice(split, stateTypes.size()) !=
                ValueRange(state) ||
            !llvm::equal(
                actual.getResults().take_back(stateTypes.size()).getTypes(),
                stateTypes) ||
            !operands(loop.getInputs().take_front(split),
                      actual.getInputs().take_front(split), env) ||
            !operands(loop.getInputs().drop_front(split),
                      actual.getInputs().slice(split + stateTypes.size(),
                                               loop.getNumOperands() - split),
                      env) ||
            actual.getInputs().take_back(coordinates.size()) !=
                ValueRange(coordinates))
          return false;
        auto &x = loop.getBody().front();
        auto &y = actual.getBody().front();
        Env inner;
        if (y.getNumArguments() !=
                x.getNumArguments() + stateTypes.size() + coordinates.size() ||
            !llvm::equal(ValueRange(y.getArguments())
                             .slice(split, stateTypes.size())
                             .getTypes(),
                         stateTypes) ||
            !bind(x.getArguments().take_front(split),
                  y.getArguments().take_front(split), inner) ||
            !bind(x.getArguments().drop_front(split),
                  y.getArguments().slice(split + stateTypes.size(),
                                         x.getNumArguments() - split),
                  inner))
          return false;
        SmallVector<Value> indices(
            y.getArguments().take_back(coordinates.size()));
        indices.push_back(y.getArgument(0));
        if (!body(x, y, std::move(inner),
                  SmallVector<Value>(
                      y.getArguments().slice(split, stateTypes.size())),
                  indices, role, reached, depth + 1) ||
            !bind(loop.getResults(),
                  actual.getResults().drop_back(stateTypes.size()), env))
          return false;
        state.clear();
        append_range(state, actual.getResults().take_back(stateTypes.size()));
        cursor = cursor->getNextNode();
      } else if (isa<pir::FinishOp, pir::ProtocolYieldOp, pir::FinishIfOp>(
                     op)) {
        bool continuing =
            isa<pir::FinishIfOp>(op) &&
            (!plan || plan->root == protocol::ConstructionPlan::Root::Host);
        if (op.getName() != cursor->getName() || !attributes(&op, cursor) ||
            cursor->getNumOperands() !=
                op.getNumOperands() + stateTypes.size() ||
            cursor->getNumResults() !=
                op.getNumResults() + (continuing ? stateTypes.size() : 0) ||
            cursor->getOperands().take_back(stateTypes.size()) !=
                ValueRange(state) ||
            !operands(op.getOperands(),
                      cursor->getOperands().drop_back(stateTypes.size()),
                      env) ||
            !bind(op.getResults(),
                  cursor->getResults().take_front(op.getNumResults()), env))
          return false;
        if (continuing) {
          state.clear();
          append_range(state,
                       cursor->getResults().take_back(stateTypes.size()));
          if (!llvm::equal(
                  cursor->getResults().take_back(stateTypes.size()).getTypes(),
                  stateTypes))
            return false;
        }
        cursor = cursor->getNextNode();
      } else if (event != bySite.end()) {
        const auto &fact = *event->second;
        auto delivery = deliveries.find(fact.site);
        if (auto start = dyn_cast<pir::ConstructionStartOp>(op)) {
          SmallVector<Value> inputs;
          for (Value input : start.getInputs()) {
            auto value = env.lookup(input);
            if (!value)
              return false;
            inputs.push_back(value);
          }
          if (!fact.startInputs || !payloadGroup.empty() ||
              !call(cursor, fact, state, inputs, coordinates, nullptr, reached))
            return false;
        } else if (isa<pir::ParticipantQueryOp>(op)) {
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
          if (!observe(fact, payload))
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
          if (!payload || !observe(fact, payload))
            return false;
        } else
          return false;
      } else {
        if (!exact(op, *cursor, env, depth))
          return false;
        cursor = cursor->getNextNode();
      }
    }
    return !cursor && payloadGroup.empty();
  }
  bool participant(pir::ParticipantOp a, pir::ParticipantOp b) {
    if (!indexObservedLoops(a) ||
        !attributes(a, b, {"function_type", "service_ports"}))
      return false;
    auto x = a.getFunctionType(), y = b.getFunctionType();
    unsigned extraInputs = hostRoot ? stateTypes.size() : 0;
    if (y.getNumInputs() != x.getNumInputs() + extraInputs ||
        y.getNumResults() != x.getNumResults() + stateTypes.size() ||
        y.getInputs().drop_back(extraInputs) != x.getInputs() ||
        y.getResults().drop_back(stateTypes.size()) != x.getResults() ||
        (hostRoot &&
         y.getInputs().take_back(extraInputs) != ArrayRef<Type>(stateTypes)) ||
        y.getResults().take_back(stateTypes.size()) !=
            ArrayRef<Type>(stateTypes))
      return false;
    auto retained = a->getAttrOfType<ArrayAttr>("service_ports");
    if (a.getRole() == policy.validator) {
      auto records =
          a->getParentOp()->getRegion(0).front().getOps<pir::ProjectionOp>();
      if (!hasSingleElement(records))
        return false;
      auto source = cast<DictionaryAttr>((*records.begin()).getInterfaces()[0]);
      auto owners = source.getAs<ArrayAttr>("input_roles");
      if (!owners || policy.services.empty() ||
          policy.services.back() >= owners.size())
        return false;
      SmallVector<unsigned> selected;
      unsigned ingress = 0;
      for (auto [i, roles] : enumerate(owners)) {
        if (!is_contained(cast<ArrayAttr>(roles), a.getRoleAttr()))
          continue;
        if (is_contained(policy.services, i))
          selected.push_back(ingress);
        ++ingress;
      }
      SmallVector<Attribute> kept;
      if (retained)
        for (auto port : retained)
          if (auto row = cast<ArrayAttr>(port);
              !is_contained(selected, cast<IntegerAttr>(row[2]).getInt())) {
            auto ingress = cast<IntegerAttr>(row[2]).getInt();
            kept.push_back(ArrayAttr::get(
                a.getContext(),
                {row[0], row[1],
                 IntegerAttr::get(
                     IntegerType::get(a.getContext(), 64),
                     ingress - llvm::count_if(selected, [&](unsigned port) {
                       return port < ingress;
                     }))}));
          }
      retained =
          kept.empty() ? ArrayAttr() : ArrayAttr::get(a.getContext(), kept);
    }
    if (retained != b->getAttrOfType<ArrayAttr>("service_ports"))
      return false;
    auto &before = a.getBody().front();
    auto &after = b.getBody().front();
    Env env;
    if (!bind(before.getArguments(),
              after.getArguments().drop_back(extraInputs), env))
      return false;
    SmallVector<const NativeTranscriptEvent *> reached;
    SmallVector<Value> state(after.getArguments().take_back(extraInputs));
    Operation *cursor = &after.front();
    auto rootCall = [&](FlatSymbolRefAttr reference, ValueRange operands) {
      auto call = dyn_cast_if_present<pir::LocalCallOp>(cursor);
      if (!call || call.getCalleeAttr() != reference ||
          call.getInputs() != operands ||
          !llvm::equal(call.getResultTypes(), stateTypes))
        return false;
      rootHelpers.insert(reference.getValue());
      state.assign(call.getResults().begin(), call.getResults().end());
      cursor = cursor->getNextNode();
      return true;
    };
    if (plan) {
      if (!hostRoot && !rootCall(plan->initializer, {}))
        return false;
      for (const auto &rule : plan->rules) {
        if (rule.kind != protocol::ConstructionRule::Kind::Start)
          continue;
        SmallVector<Value> operands(state);
        auto records =
            a->getParentOp()->getRegion(0).front().getOps<pir::ProjectionOp>();
        if (!hasSingleElement(records))
          return false;
        auto interface =
            cast<DictionaryAttr>((*records.begin()).getInterfaces()[0]);
        for (auto item : interface.getAs<ArrayAttr>("participants")) {
          auto port = cast<DictionaryAttr>(item);
          if (port.getAs<FlatSymbolRefAttr>("participant") !=
              FlatSymbolRefAttr::get(a))
            continue;
          auto inputs = port.getAs<ArrayAttr>("inputs");
          for (unsigned original : rule.inputs) {
            auto found = llvm::find_if(inputs, [&](Attribute value) {
              return cast<IntegerAttr>(value).getInt() == original;
            });
            if (found == inputs.end())
              return false;
            operands.push_back(after.getArgument(found - inputs.begin()));
          }
        }
        if (!rootCall(rule.handler, operands))
          return false;
      }
    }
    if (!cursor ||
        !body(before, after, std::move(env), std::move(state), {}, a.getRole(),
              reached, 0, cursor) ||
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
    auto states =
        construction ? construction.getAs<ArrayAttr>("state") : ArrayAttr();
    auto helpers =
        construction ? construction.getAs<ArrayAttr>("helpers") : ArrayAttr();
    if (!construction || construction.size() != 7 ||
        after.getDictionary(a.getContext()) != before ||
        construction.getAs<StringAttr>("format") !=
            StringAttr::get(a.getContext(), "zkc.native-construction/0") ||
        construction.getAs<StringAttr>("plan") !=
            StringAttr::get(a.getContext(), policy.construction) ||
        construction.getAs<StringAttr>("root") !=
            StringAttr::get(a.getContext(), hostRoot ? "host" : "local") ||
        !states || states.size() != stateTypes.size() || !helpers)
      return false;
    for (auto [type, value] : zip(stateTypes, states))
      if (value != TypeAttr::get(type))
        return false;
    for (auto value : helpers) {
      auto ref = dyn_cast<FlatSymbolRefAttr>(value);
      if (!ref || !recordedHelpers.insert(ref.getValue()).second)
        return false;
    }
    auto removed = construction.getAs<ArrayAttr>("removed_services");
    if (!removed || removed.size() != policy.services.size())
      return false;
    for (auto [attr, service] : zip(removed, policy.services)) {
      auto port = dyn_cast<IntegerAttr>(attr);
      if (!port || port.getInt() != service)
        return false;
    }
    return bool(construction.getAs<ArrayAttr>("actions"));
  }

public:
  TranscriptCorrespondence(
      pir::ProtocolModuleOp candidate, const NativeProofPolicy &policy,
      ArrayRef<NativeTranscriptEvent> events,
      const protocol::ConstructionPlan *plan,
      ArrayRef<protocol::ConstructionInvocation> invocations,
      const protocol::SourceExecutionClosure &execution)
      : policy(policy), plan(plan),
        hostRoot(!plan || plan->root == protocol::ConstructionPlan::Root::Host),
        events(events), symbols(candidate), execution(execution) {
    if (plan) {
      stateTypes = plan->state;
      for (const auto &rule : plan->rules)
        if (!protocol::isCodecRule(rule.kind))
          for (const auto &site : rule.sites)
            rules[site] = &rule;
    } else {
      stateTypes.push_back(runtime::CapabilityType::get(
          candidate.getContext(), zkc::runtime::CapabilityKind::Transcript,
          policy.suite));
    }
    for (const auto &invocation : invocations) {
      auto inserted = startRules.emplace(
          invocation.site,
          protocol::ConstructionRule{protocol::ConstructionRuleKind::Start,
                                     invocation.handler,
                                     {invocation.site},
                                     invocation.inputs,
                                     {},
                                     {}});
      rules[invocation.site] = &inserted.first->second;
    }
  }
  bool check(pir::ProtocolModuleOp before, pir::ProtocolModuleOp after) {
    if (!attributes(before, after) ||
        (plan &&
         (!plan->symbol || plan->symbol.getValue() != policy.construction ||
          plan->suite != policy.suite ||
          !llvm::equal(plan->services, policy.services))))
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
      if (isa<func::FuncOp>(op) && checkedHelpers.count(name))
        continue;
      if (isa<runtime::BindingOp>(op) && bindings.count(name))
        continue;
      return false;
    }
    unsigned expectedHelpers = count_if(events, [&](const auto &event) {
      auto *rule = rules.lookup(event.site);
      return !rule || rule->sites.back() == event.site;
    });
    if (recordedHelpers.size() != checkedHelpers.size() + rootHelpers.size())
      return false;
    for (const auto &item : checkedHelpers)
      if (!recordedHelpers.count(item.first()))
        return false;
    for (const auto &item : rootHelpers)
      if (!recordedHelpers.count(item.first()))
        return false;
    return projections == 1 && checkedHelpers.size() == expectedHelpers;
  }
  bool exhausted() const { return !remaining; }
  StringRef detail() const { return checkpoint; }
};
} // namespace
Error verifyNativeEntrySelection(ModuleOp prepared, ModuleOp selected,
                                 StringRef entry) {
  if (!prepared || !selected || failed(zkc::admitStage(prepared)) ||
      failed(zkc::admitStage(selected)) ||
      !hasSingleElement(*prepared.getBody()) ||
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
Error verifyNativeTranscript(
    ModuleOp projected, ModuleOp constructed, const NativeProofPolicy &policy,
    ArrayRef<NativeTranscriptEvent> events,
    const protocol::ConstructionPlan *plan,
    ArrayRef<protocol::ConstructionInvocation> invocations) {
  if (!projected || !constructed ||
      projected.getContext() != constructed.getContext() ||
      failed(zkc::admitStage(projected)) ||
      failed(zkc::admitStage(constructed)) ||
      !hasSingleElement(*projected.getBody()) ||
      !hasSingleElement(*constructed.getBody()))
    return error("native-transcript-subject");
  if (policy.suite.empty() && !plan) {
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
  auto execution = protocol::readSourceExecutionClosure(after);
  if (!execution)
    return execution.takeError();
  TranscriptCorrespondence checker(after, policy, events, plan, invocations,
                                   *execution);
  if (!checker.check(before, after))
    return error(checker.exhausted() ? "native-transcript-limit"
                                     : "native-transcript-correspondence",
                 checker.detail());
  return Error::success();
}
} // namespace zkc::detail
