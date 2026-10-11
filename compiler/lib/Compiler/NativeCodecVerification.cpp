#include "NativeCodec.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"
#include <utility>
using namespace mlir;
using namespace llvm;
namespace zkc::detail {
namespace {
namespace pir = protocol_ir;
using Env = llvm::DenseMap<Value, Value>;
using Rule = protocol::ConstructionRule;
struct CodecMessage {
  const Rule *encode = nullptr, *receive = nullptr, *decode = nullptr,
             *wire = nullptr;
  FlatSymbolRefAttr slice;
  SmallVector<FlatSymbolRefAttr> observations;
};
class CodecCorrespondence {
  const NativeProofPolicy &policy;
  const protocol::ConstructionPlan &plan;
  const protocol::ConstructionCodec &codec;
  SymbolTable symbols;
  Type bytes;
  StringMap<CodecMessage> messages;
  StringMap<CodecMessage *> leaves, observerMessages;
  llvm::StringSet<> allowedFunctions, allowedBindings, usedHelpers;
  FlatSymbolRefAttr conditionalWrite, conditionalFinish;
  uint64_t remaining = 1000000;
  std::string checkpoint;
  bool charge(size_t n = 1) {
    if (n > remaining) {
      remaining = 0;
      return false;
    }
    remaining -= n;
    return true;
  }
  static bool attributes(Operation *a, Operation *b,
                         ArrayRef<StringRef> omitted = {}) {
    NamedAttrList x(a->getAttrs()), y(b->getAttrs());
    for (auto key : omitted) {
      x.erase(key);
      y.erase(key);
    }
    return x == y;
  }
  bool bind(ValueRange x, ValueRange y, Env &env) {
    if (x.size() != y.size())
      return false;
    for (auto [a, b] : zip(x, y)) {
      if (!charge() || a.getType() != b.getType())
        return false;
      env[a] = b;
    }
    return true;
  }
  bool operands(ValueRange x, ValueRange y, const Env &env) {
    if (x.size() != y.size())
      return false;
    for (auto [a, b] : zip(x, y))
      if (!charge() || env.lookup(a) != b)
        return false;
    return true;
  }
  bool exact(Operation &a, Operation &b, Env &env, unsigned depth) {
    if (!charge() || depth > 64 || a.getName() != b.getName() ||
        !attributes(&a, &b) ||
        !operands(a.getOperands(), b.getOperands(), env) ||
        a.getNumRegions() != b.getNumRegions())
      return false;
    for (auto [x, y] : zip(a.getRegions(), b.getRegions())) {
      if (!x.hasOneBlock() || !y.hasOneBlock() ||
          x.front().getOperations().size() != y.front().getOperations().size())
        return false;
      // Both subjects are verified: SSA values are globally distinct and
      // cannot escape their regions. Non-isolated regions can share mappings.
      Env isolated;
      Env &inner = a.hasTrait<OpTrait::IsIsolatedFromAbove>() ? isolated : env;
      if (!bind(x.front().getArguments(), y.front().getArguments(), inner))
        return false;
      for (auto [u, v] : zip(x.front(), y.front()))
        if (!exact(u, v, inner, depth + 1))
          return false;
    }
    return bind(a.getResults(), b.getResults(), env);
  }
  bool exactWithState(
      Operation &source, Operation &candidate, Env &env,
      const llvm::DenseMap<Operation *, SmallVector<Value>> &overrides,
      unsigned depth) {
    auto found = overrides.find(&source);
    if (found == overrides.end())
      return exact(source, candidate, env, depth);
    if (!charge(found->second.size()))
      return false;
    SmallVector<std::pair<Value, Value>> saved;
    for (auto [oldState, newState] :
         zip(source.getOperands().take_front(plan.state.size()),
             found->second)) {
      saved.emplace_back(oldState, env.lookup(oldState));
      env[oldState] = newState;
    }
    bool matches = exact(source, candidate, env, depth);
    for (auto [value, previous] : reverse(saved))
      env[value] = previous;
    return matches;
  }

  bool kernel(Operation *op, StringRef contract, ValueRange inputs,
              unsigned results) {
    if (!op || !charge() ||
        op->getName().getStringRef() !=
            protocol::boundOperationName(contract) ||
        op->getAttrs().size() != 3 || !op->getAttrOfType<StringAttr>("site") ||
        op->getOperands() != inputs || op->getNumResults() != results ||
        op->getNumRegions())
      return false;
    auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto binding =
        reference
            ? symbols.lookup<local::OperationBindingOp>(reference.getValue())
            : local::OperationBindingOp();
    auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
    if (!binding || binding.getContract() != contract ||
        !binding.getArguments().empty() ||
        !binding.getImplementation().empty() || !parameters ||
        !parameters.empty())
      return false;
    allowedBindings.insert(binding.getSymName());
    return true;
  }
  local::FuncOp generated(FlatSymbolRefAttr reference) {
    auto f = symbols.lookup<local::FuncOp>(reference.getValue());
    auto origin =
        f ? f->getAttrOfType<ArrayAttr>("logical_origin") : ArrayAttr();
    if (!f || !f.getBody().hasOneBlock() || f->getAttrs().size() != 3 ||
        !origin || origin.size() != 2 ||
        origin[0] != StringAttr::get(f.getContext(), f.getSymName()) ||
        !isa<ArrayAttr>(origin[1]) || !cast<ArrayAttr>(origin[1]).empty())
      return {};
    allowedFunctions.insert(f.getSymName());
    return f;
  }
  bool slice(FlatSymbolRefAttr reference, unsigned count) {
    auto f = generated(reference);
    auto index =
        IntegerType::get(bytes.getContext(), 64, IntegerType::Unsigned);
    SmallVector<Type> inputs{bytes}, outputs(count, bytes);
    inputs.append(2 * count, index);
    if (!f || f.getArgumentTypes() != ArrayRef<Type>(inputs) ||
        f.getResultTypes() != ArrayRef<Type>(outputs))
      return false;
    auto &body = f.getBody().front();
    Operation *cursor = &body.front();
    auto args = body.getArguments();
    SmallVector<Value> chunks;
    for (unsigned i = 0; i < count; ++i) {
      if (!kernel(cursor, "bytes.slice",
                  {args[0], args[1 + 2 * i], args[2 + 2 * i]}, 1))
        return false;
      chunks.push_back(cursor->getResult(0));
      cursor = cursor->getNextNode();
    }
    auto returned = dyn_cast_or_null<local::ReturnOp>(cursor);
    return returned && returned->getAttrs().empty() &&
           returned.getInputs() == ValueRange(chunks) && !cursor->getNextNode();
  }
  bool conditional(FlatSymbolRefAttr reference, FlatSymbolRefAttr method,
                   bool writing) {
    auto f = generated(reference);
    auto source = symbols.lookup<local::FuncOp>(method.getValue());
    if (!f || !source || !source.getBody().hasOneBlock())
      return false;
    SmallVector<Type> inputs{IntegerType::get(bytes.getContext(), 1)};
    append_range(inputs, source.getArgumentTypes());
    if (f.getArgumentTypes() != ArrayRef<Type>(inputs) ||
        f.getResultTypes() != source.getResultTypes())
      return false;
    auto &body = f.getBody().front();
    auto branch = dyn_cast<local::LocalIfOp>(body.front());
    if (!branch || branch->getAttrs().size() != 1 || !branch.getSiteAttr() ||
        branch.getInputs() != ValueRange(body.getArguments()) ||
        branch.getResultTypes() != source.getResultTypes())
      return false;
    auto &taken = branch.getThenRegion().front();
    Env env;
    if (!bind(source.getBody().front().getArguments(), taken.getArguments(),
              env))
      return false;
    auto cursor = taken.begin();
    for (auto &op : source.getBody().front()) {
      if (cursor == taken.end())
        return false;
      if (auto ret = dyn_cast<local::ReturnOp>(op)) {
        auto yield = dyn_cast<local::LocalYieldOp>(*cursor);
        if (!yield || !yield->getAttrs().empty() ||
            !operands(ret.getInputs(), yield.getInputs(), env))
          return false;
      } else if (!exact(op, *cursor, env, 0))
        return false;
      ++cursor;
    }
    if (cursor != taken.end())
      return false;
    auto &untaken = branch.getElseRegion().front();
    if (untaken.getArgumentTypes() != source.getArgumentTypes())
      return false;
    Operation *otherwise = &untaken.front();
    SmallVector<Value> empty;
    if (writing) {
      if (!kernel(otherwise, "bytes.empty", {}, 1))
        return false;
      empty.push_back(otherwise->getResult(0));
      otherwise = otherwise->getNextNode();
    }
    auto yield = dyn_cast_or_null<local::LocalYieldOp>(otherwise);
    auto returned = dyn_cast_or_null<local::ReturnOp>(branch->getNextNode());
    return yield && yield->getAttrs().empty() &&
           yield.getInputs() == ValueRange(empty) &&
           !otherwise->getNextNode() && returned &&
           returned->getAttrs().empty() &&
           returned.getInputs() == branch.getResults() &&
           !returned->getNextNode();
  }
  local::CallOp invoke(Operation *&cursor, FlatSymbolRefAttr reference,
                       ValueRange inputs) {
    auto call = dyn_cast_or_null<local::CallOp>(cursor);
    if (!call || !charge() || call->getAttrs().size() != 2 ||
        !call.getSiteAttr() || call.getCalleeAttr() != reference ||
        call.getInputs() != inputs)
      return {};
    usedHelpers.insert(reference.getValue());
    cursor = cursor->getNextNode();
    return call;
  }
  bool body(Block &source, Operation *cursor, Env env,
            SmallVector<Value> record, Value proof, bool writing,
            unsigned depth, Operation *sourceStart = nullptr) {
    if (depth > 64)
      return false;
    struct Occurrences {
      SmallVector<Operation *> transport;
      SmallVector<local::CallOp> observations;
    };
    llvm::DenseMap<const CodecMessage *, Occurrences> occurrences;
    for (auto &op : source) {
      if (!charge())
        return false;
      if (isa<pir::EmitOp, pir::AwaitOp>(op)) {
        auto site = op.getAttrOfType<StringAttr>("site");
        if (auto *message = site ? leaves.lookup(site.getValue()) : nullptr)
          occurrences[message].transport.push_back(&op);
      } else if (auto call = dyn_cast<local::CallOp>(op)) {
        if (auto *message = observerMessages.lookup(call.getCallee()))
          occurrences[message].observations.push_back(call);
      }
    }
    llvm::DenseSet<Operation *> completed, postponed;
    llvm::DenseMap<Operation *, SmallVector<Value>> overridden;
    for (auto &op :
         make_range(sourceStart ? sourceStart->getIterator() : source.begin(),
                    source.end())) {
      checkpoint = op.getName().getStringRef().str();
      if (!charge() || !cursor)
        return false;
      if (completed.contains(&op))
        continue;
      if (auto loop = dyn_cast<pir::ProtocolLoopOp>(op)) {
        auto actual = dyn_cast<pir::ProtocolLoopOp>(cursor);
        unsigned split = 1 + loop.getCarried(), extra = record.size(),
                 capture = unsigned(bool(proof));
        if (!actual || !attributes(loop, actual, {"carried"}) ||
            actual.getCarried() != loop.getCarried() + extra ||
            actual.getNumOperands() !=
                loop.getNumOperands() + extra + capture ||
            actual.getNumResults() != loop.getNumResults() + extra ||
            !operands(loop.getInputs().take_front(split),
                      actual.getInputs().take_front(split), env) ||
            actual.getInputs().slice(split, extra) != ValueRange(record) ||
            !operands(loop.getInputs().drop_front(split),
                      actual.getInputs().slice(split + extra,
                                               loop.getNumOperands() - split),
                      env) ||
            (proof && actual.getInputs().back() != proof))
          return false;
        auto &a = loop.getBody().front();
        auto &b = actual.getBody().front();
        Env inner;
        if (b.getNumArguments() != a.getNumArguments() + extra + capture ||
            !bind(a.getArguments().take_front(split),
                  b.getArguments().take_front(split), inner) ||
            !bind(a.getArguments().drop_front(split),
                  b.getArguments().slice(split + extra,
                                         a.getNumArguments() - split),
                  inner) ||
            !body(a, &b.front(), std::move(inner),
                  SmallVector<Value>(b.getArguments().slice(split, extra)),
                  proof ? b.getArguments().back() : Value(), writing,
                  depth + 1) ||
            !bind(loop.getResults(),
                  actual.getResults().take_front(loop.getNumResults()), env))
          return false;
        record.assign(actual.getResults().take_back(extra).begin(),
                      actual.getResults().take_back(extra).end());
        cursor = cursor->getNextNode();
      } else if (auto yield = dyn_cast<pir::ProtocolYieldOp>(op)) {
        auto actual = dyn_cast<pir::ProtocolYieldOp>(cursor);
        if (!actual || !attributes(yield, actual) ||
            actual.getNumOperands() != yield.getNumOperands() + record.size() ||
            !operands(yield.getInputs(),
                      actual.getInputs().take_front(yield.getNumOperands()),
                      env) ||
            actual.getInputs().take_back(record.size()) != ValueRange(record))
          return false;
        cursor = cursor->getNextNode();
      } else if (isa<pir::FinishOp, pir::FinishIfOp>(op)) {
        auto conditional = dyn_cast<pir::FinishIfOp>(op);
        SmallVector<Value> inputs;
        if (conditional)
          inputs.push_back(env.lookup(conditional.getCondition()));
        append_range(inputs, record);
        if (!writing)
          inputs.push_back(proof);
        auto call = invoke(
            cursor,
            conditional ? (writing ? conditionalWrite : conditionalFinish)
                        : (writing ? codec.write : codec.finish),
            inputs);
        if (!call || !cursor || cursor->getName() != op.getName() ||
            !attributes(&op, cursor) ||
            cursor->getNumOperands() !=
                op.getNumOperands() + unsigned(writing) ||
            cursor->getNumResults() != op.getNumResults() ||
            !operands(op.getOperands(),
                      cursor->getOperands().take_front(op.getNumOperands()),
                      env) ||
            (writing && cursor->getOperands().back() != call.getResult(0)) ||
            !bind(op.getResults(),
                  cursor->getResults().take_front(op.getNumResults()), env))
          return false;
        cursor = cursor->getNextNode();
      } else if (isa<pir::EmitOp, pir::AwaitOp>(op)) {
        auto site = op.getAttrOfType<StringAttr>("site");
        auto *message = site ? leaves.lookup(site.getValue()) : nullptr;
        if (!message)
          return false;
        bool boundary =
            site.getValue() == (writing ? message->encode->sites.back()
                                        : message->encode->sites.front());
        if (!boundary)
          continue;
        auto &group = occurrences[message];
        const auto &transport = group.transport;
        auto &observations = group.observations;
        if (!llvm::equal(
                transport, message->encode->sites,
                [](Operation *op, const std::string &site) {
                  return op->getAttrOfType<StringAttr>("site").getValue() ==
                         site;
                }) ||
            transport.size() != message->encode->sites.size() ||
            observations.size() != message->observations.size())
          return false;
        SmallVector<Value> inputs(record), chunks;
        if (writing) {
          for (auto *send : transport) {
            auto value = env.lookup(cast<pir::EmitOp>(send).getInput());
            if (!value)
              return false;
            inputs.push_back(value);
          }
          auto encoded = invoke(cursor, message->encode->handler, inputs);
          if (!encoded)
            return false;
          record.assign(
              encoded.getResults().take_front(codec.record.size()).begin(),
              encoded.getResults().take_front(codec.record.size()).end());
          append_range(chunks,
                       encoded.getResults().drop_front(codec.record.size()));
        } else {
          inputs.push_back(proof);
          auto received = invoke(cursor, message->receive->handler, inputs);
          if (!received)
            return false;
          record.assign(
              received.getResults().take_front(codec.record.size()).begin(),
              received.getResults().take_front(codec.record.size()).end());
          inputs.assign(1, proof);
          append_range(inputs,
                       received.getResults().drop_front(codec.record.size()));
          auto sliced = invoke(cursor, message->slice, inputs);
          if (!sliced)
            return false;
          append_range(chunks, sliced.getResults());
        }
        SmallVector<Value> observedState;
        if (message->wire) {
          inputs.clear();
          for (Value state :
               observations.front().getInputs().take_front(plan.state.size())) {
            auto value = env.lookup(state);
            if (!value)
              return false;
            inputs.push_back(value);
          }
          append_range(inputs, chunks);
          auto observed = invoke(cursor, message->wire->handler, inputs);
          if (!observed)
            return false;
          append_range(observedState, observed.getResults());
          overridden[observations.front()] = observedState;
        }
        // Only total calculations and this message's observations may be
        // crossed while gathering one logical payload.
        for (auto *between = transport.front(); between != transport.back();
             between = between->getNextNode()) {
          if (!between || !charge())
            return false;
          if (is_contained(transport, between) ||
              is_contained(observations, dyn_cast<local::CallOp>(between)))
            continue;
          if (!mathematical::isTotal(between))
            return false;
        }
        if (!writing) {
          auto decoded = invoke(cursor, message->decode->handler, chunks);
          if (!decoded || decoded.getNumResults() != transport.size())
            return false;
          for (auto [i, receive] : enumerate(transport))
            env[receive->getResult(0)] = decoded.getResult(i);
        }
        for (auto call : observations) {
          if (!cursor ||
              !exactWithState(*call, *cursor, env, overridden, depth))
            return false;
          completed.insert(call);
          cursor = cursor->getNextNode();
        }
      } else {
        if (writing) {
          auto call = dyn_cast<local::CallOp>(op);
          bool pending = call && observerMessages.count(call.getCallee());
          if (pending) {
            postponed.insert(&op);
            continue;
          }
        }
        if (!exactWithState(op, *cursor, env, overridden, depth))
          return false;
        cursor = cursor->getNextNode();
      }
    }
    return !cursor && all_of(postponed, [&](Operation *op) {
      return completed.contains(op);
    });
  }

public:
  CodecCorrespondence(pir::ProtocolModuleOp candidate,
                      const NativeProofPolicy &policy,
                      const protocol::ConstructionPlan &plan)
      : policy(policy), plan(plan), codec(*plan.codec), symbols(candidate) {
    bytes = data::BytesType::get(candidate.getContext());
  }
  bool check(pir::ProtocolModuleOp source, pir::ProtocolModuleOp candidate,
             ArrayRef<NativeTranscriptEvent> events,
             const json::Array &transcript, const json::Array &selected) {
    if (selected.size() != 9 || !attributes(source, candidate))
      return false;
    json::Array recordTypes, layoutInputs;
    for (Type type : codec.record) {
      auto encoded = protocol::encodeBoundType(type, false);
      if (!encoded) {
        consumeError(encoded.takeError());
        return false;
      }
      recordTypes.push_back(encoded->spelling());
    }
    for (unsigned input : codec.inputs)
      layoutInputs.push_back(std::to_string(input));
    if (selected[0] != json::Value(codec.provider) ||
        selected[1] != json::Value(std::move(recordTypes)) ||
        selected[2] != json::Value(codec.initialize.getValue()) ||
        selected[3] != json::Value(codec.write.getValue()) ||
        selected[4] != json::Value(codec.finish.getValue()) ||
        selected[5] != json::Value(std::move(layoutInputs)))
      return false;
    bool needsConditional = false;
    source.walk([&](pir::FinishIfOp) { needsConditional = true; });
    if (!selected[7].getAsString() || !selected[8].getAsString())
      return false;
    if (needsConditional) {
      conditionalWrite = FlatSymbolRefAttr::get(source.getContext(),
                                                *selected[7].getAsString());
      conditionalFinish = FlatSymbolRefAttr::get(source.getContext(),
                                                 *selected[8].getAsString());
      if (!conditional(conditionalWrite, codec.write, true) ||
          !conditional(conditionalFinish, codec.finish, false))
        return false;
    } else if (!selected[7].getAsString()->empty() ||
               !selected[8].getAsString()->empty())
      return false;
    StringMap<FlatSymbolRefAttr> observations;
    for (const auto &item : *transcript[6].getAsArray()) {
      const auto &row = *item.getAsArray();
      for (const auto &origin : *row[2].getAsArray())
        observations[*origin.getAsString()] =
            FlatSymbolRefAttr::get(source.getContext(), *row[0].getAsString());
    }
    for (const auto &rule : plan.rules) {
      if (!protocol::isCodecRule(rule.kind))
        continue;
      auto &message = messages[rule.sites.front()];
      switch (rule.kind) {
      case Rule::Kind::Encode:
        message.encode = &rule;
        break;
      case Rule::Kind::Receive:
        message.receive = &rule;
        break;
      case Rule::Kind::Decode:
        message.decode = &rule;
        break;
      case Rule::Kind::Wire:
        message.wire = &rule;
        break;
      default:
        llvm_unreachable("checked codec rule");
      }
    }
    auto associations = selected[6].getAsArray();
    if (!associations || associations->size() != messages.size())
      return false;
    StringMap<const NativeTranscriptEvent *> bySite;
    for (const auto &event : events) {
      if (!charge())
        return false;
      bySite[event.site] = &event;
    }
    unsigned association = 0;
    for (const auto &first : events) {
      auto found = messages.find(first.site);
      if (found == messages.end())
        continue;
      auto &message = found->second;
      auto row = (*associations)[association++].getAsArray();
      if (!row || row->size() != 6 || !(*row)[4].getAsString())
        return false;
      message.slice =
          FlatSymbolRefAttr::get(source.getContext(), *(*row)[4].getAsString());
      if (!slice(message.slice, message.encode->chunks.size()))
        return false;
      json::Array origins;
      for (const auto &site : message.encode->sites) {
        leaves[site] = &message;
        auto *event = bySite.lookup(site);
        if (!event || !charge())
          return false;
        origins.push_back(event->origin);
        auto ref = observations.lookup(event->origin);
        if (!ref)
          return false;
        auto inserted = observerMessages.try_emplace(ref.getValue(), &message);
        if (!inserted.second && inserted.first->second != &message)
          return false;
        if (!is_contained(message.observations, ref))
          message.observations.push_back(ref);
      }
      json::Value expected(json::Array{
          message.encode->handler.getValue(),
          message.receive->handler.getValue(),
          message.decode->handler.getValue(),
          message.wire ? message.wire->handler.getValue() : StringRef(),
          message.slice.getValue(), std::move(origins)});
      if ((*associations)[association - 1] != expected)
        return false;
    }
    if (association != associations->size())
      return false;
    auto projection =
        *source.getBody().front().getOps<pir::ProjectionOp>().begin();
    auto original = cast<DictionaryAttr>(projection.getInterfaces()[0]);
    llvm::StringSet<> originals;
    for (auto &op : source.getBody().front()) {
      if (!charge())
        return false;
      if (isa<pir::ProjectionOp>(op))
        continue;
      auto name = op.getAttrOfType<StringAttr>("sym_name");
      if (!name)
        return false;
      originals.insert(name.getValue());
      auto *actual = symbols.lookup(name.getValue());
      if (!actual)
        return false;
      auto p = dyn_cast<pir::ParticipantOp>(op);
      if (!p) {
        if (!OperationEquivalence::isEquivalentTo(
                &op, actual, OperationEquivalence::IgnoreLocations))
          return false;
        continue;
      }
      auto q = dyn_cast<pir::ParticipantOp>(actual);
      bool writing = p.getRole() == policy.producer;
      auto x = p.getFunctionType(),
           y = q ? q.getFunctionType() : FunctionType();
      if (!q || !attributes(p, q, {"function_type"}) ||
          y.getNumInputs() != x.getNumInputs() + unsigned(!writing) ||
          y.getNumResults() != x.getNumResults() + unsigned(writing) ||
          y.getInputs().take_front(x.getNumInputs()) != x.getInputs() ||
          y.getResults().take_front(x.getNumResults()) != x.getResults() ||
          (writing ? y.getResults().back() != bytes
                   : y.getInputs().back() != bytes))
        return false;
      auto &a = p.getBody().front();
      auto &b = q.getBody().front();
      Env env;
      if (!bind(a.getArguments(),
                b.getArguments().take_front(a.getNumArguments()), env))
        return false;
      Operation *cursor = &b.front();
      unsigned roots =
          unsigned(plan.root == protocol::ConstructionPlan::Root::Local) +
          count_if(plan.rules, [](const Rule &rule) {
            return rule.kind == Rule::Kind::Start;
          });
      auto start = a.begin();
      for (unsigned i = 0; i < roots; ++i) {
        if (start == a.end() || !cursor || !exact(*start, *cursor, env, 0))
          return false;
        ++start;
        cursor = cursor->getNextNode();
      }
      SmallVector<Value> layout;
      for (auto item : original.getAs<ArrayAttr>("participants")) {
        auto ports = cast<DictionaryAttr>(item);
        if (ports.getAs<FlatSymbolRefAttr>("participant") !=
            FlatSymbolRefAttr::get(p))
          continue;
        auto inputs = ports.getAs<ArrayAttr>("inputs");
        for (unsigned input : codec.inputs) {
          auto found = find_if(inputs, [&](Attribute a) {
            return cast<IntegerAttr>(a).getInt() == input;
          });
          if (found == inputs.end())
            return false;
          layout.push_back(b.getArgument(found - inputs.begin()));
        }
      }
      auto initialized = invoke(cursor, codec.initialize, layout);
      if (!initialized || !cursor)
        return false;
      if (start == a.end() ||
          !body(a, cursor, std::move(env),
                SmallVector<Value>(initialized.getResults()),
                writing ? Value() : b.getArguments().back(), writing, 0,
                &*start))
        return false;
    }
    for (auto &op : candidate.getBody().front()) {
      if (isa<pir::ProjectionOp>(op))
        continue;
      auto name = op.getAttrOfType<StringAttr>("sym_name");
      if (!name || (!originals.contains(name.getValue()) &&
                    !(isa<local::FuncOp>(op) &&
                      allowedFunctions.contains(name.getValue())) &&
                    !(isa<local::OperationBindingOp>(op) &&
                      allowedBindings.contains(name.getValue()))))
        return false;
    }
    auto records = candidate.getBody().front().getOps<pir::ProjectionOp>();
    if (!hasSingleElement(records))
      return false;
    auto record = *records.begin();
    if (record.getCalculations() != projection.getCalculations())
      return false;
    auto interface = cast<DictionaryAttr>(record.getInterfaces()[0]);
    NamedAttrList a(original), b(interface);
    a.erase("construction");
    b.erase("construction");
    if (a != b)
      return false;
    auto constructed = interface.getAs<DictionaryAttr>("construction");
    auto previous = original.getAs<DictionaryAttr>("construction");
    for (auto key : {"format", "state", "root", "plan", "removed_services"})
      if (constructed.get(key) != previous.get(key))
        return false;
    auto codecRecord = constructed.getAs<DictionaryAttr>("codec");
    if (!codecRecord ||
        codecRecord.getAs<StringAttr>("producer").getValue() !=
            policy.producer ||
        codecRecord.getAs<StringAttr>("validator").getValue() !=
            policy.validator)
      return false;
    llvm::StringSet<> listed;
    for (auto helper : codecRecord.getAs<ArrayAttr>("helpers"))
      listed.insert(cast<FlatSymbolRefAttr>(helper).getValue());
    return listed.size() == usedHelpers.size() &&
           all_of(listed, [&](const auto &item) {
             return usedHelpers.contains(item.getKey());
           });
  }
  bool exhausted() const { return !remaining; }
  StringRef detail() const { return checkpoint; }
};
} // namespace
Error verifyNativeCodec(ModuleOp transcript, ModuleOp encoded,
                        const NativeProofPolicy &policy,
                        const protocol::ConstructionPlan &plan,
                        ArrayRef<NativeTranscriptEvent> events,
                        const json::Array &transcriptPlan,
                        const json::Array &codecPlan) {
  if (!transcript || !encoded || failed(verify(transcript)) ||
      failed(verify(encoded)))
    return error("native-codec-subject");
  auto source = cast<pir::ProtocolModuleOp>(transcript.getBody()->front());
  auto candidate = cast<pir::ProtocolModuleOp>(encoded.getBody()->front());
  CodecCorrespondence checker(candidate, policy, plan);
  if (!checker.check(source, candidate, events, transcriptPlan, codecPlan))
    return error(checker.exhausted() ? "native-codec-limit"
                                     : "native-codec-correspondence",
                 checker.detail());
  return Error::success();
}
} // namespace zkc::detail
