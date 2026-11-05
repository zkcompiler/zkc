#include "NativeCodec.h"
#include "NativeCodecCapacity.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"
#include <map>
using namespace mlir;
using namespace llvm;
namespace zkc::detail {
namespace {
namespace pir = protocol_ir;
using Rule = protocol::ConstructionRule;
struct Message {
  const Rule *encode = nullptr, *receive = nullptr, *decode = nullptr,
             *wire = nullptr;
  FlatSymbolRefAttr slice;
  SmallVector<FlatSymbolRefAttr> observations;
  SmallVector<std::string> origins;
};
class CodecEmitter {
  pir::ProtocolModuleOp module;
  const NativeProofPolicy &policy;
  const protocol::ConstructionPlan &plan;
  const protocol::ConstructionCodec &codec;
  OpBuilder builder;
  SymbolTable symbols;
  Type bytes, index;
  unsigned ordinal = 0;
  llvm::StringSet<> occupied;
  StringMap<Message> messages;
  StringMap<Message *> leaves;
  SmallVector<Attribute> helpers, prefix;
  std::map<std::string, SmallVector<Attribute>> before, after;
  std::map<unsigned, FlatSymbolRefAttr> slices;
  FlatSymbolRefAttr conditionalWrite, conditionalFinish;
  CodecCapacity &capacity;

  bool charge(uint64_t count = 1) { return capacity.charge(count); }

  std::string fresh() {
    std::string name;
    do {
      name = "_codec_" + std::to_string(ordinal++);
    } while (symbols.lookup(name) || !occupied.insert(name).second);
    return name;
  }
  FlatSymbolRefAttr binding(StringRef contract) {
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToStart(&module.getBody().front());
    auto op =
        runtime::BindingOp::create(builder, module.getLoc(), fresh(), contract,
                                   builder.getArrayAttr({}), "");
    symbols.insert(op);
    return FlatSymbolRefAttr::get(op);
  }
  SmallVector<Value> kernel(exec::ScopedExecutionBuilder &control,
                            StringRef contract, ValueRange inputs,
                            TypeRange outputs, StringRef site) {
    return control.invoke(
        "exec.apply", outputs, control.scoped(inputs),
        {builder.getNamedAttr("binding", binding(contract)),
         builder.getNamedAttr("site", builder.getStringAttr(site)),
         builder.getNamedAttr("parameters", builder.getArrayAttr({}))});
  }
  func::FuncOp function(TypeRange inputs, TypeRange outputs,
                        bool region = false) {
    builder.setInsertionPointToEnd(&module.getBody().front());
    SmallVector<Type> scoped{runtime::ScopeType::get(module.getContext())};
    append_range(scoped, inputs);
    auto f = func::FuncOp::create(
        builder, module.getLoc(), fresh(),
        builder.getFunctionType(
            scoped, {exec::OutcomeType::get(module.getContext(),
                                            SmallVector<Type>(outputs))}));
    f.setPrivate();
    f.setNoInline(true);
    if (region)
      f->setAttr("runtime.region", builder.getUnitAttr());
    else
      f->setAttr("runtime.origin",
                 builder.getArrayAttr({builder.getStringAttr(f.getSymName()),
                                       builder.getArrayAttr({})}));
    symbols.insert(f);
    builder.setInsertionPointToEnd(f.addEntryBlock());
    return f;
  }
  FlatSymbolRefAttr slicer(unsigned count) {
    auto found = slices.find(count);
    if (found != slices.end())
      return found->second;
    if (!charge(16 * uint64_t(count) + 32))
      return {};
    SmallVector<Type> inputs{bytes}, outputs(count, bytes);
    inputs.append(2 * count, index);
    auto f = function(inputs, outputs);
    exec::ScopedExecutionBuilder control(builder, f);
    auto args = f.getArguments().drop_front();
    SmallVector<Value> values;
    for (unsigned i = 0; i < count; ++i)
      values.push_back(kernel(control, "bytes.slice",
                              {args[0], args[1 + 2 * i], args[2 + 2 * i]},
                              {bytes}, "slice_" + std::to_string(i))[0]);
    control.returned(values);
    auto result = FlatSymbolRefAttr::get(f);
    slices.emplace(count, result);
    return result;
  }
  Expected<FlatSymbolRefAttr> conditional(FlatSymbolRefAttr method,
                                          bool writing) {
    auto source = symbols.lookup<func::FuncOp>(method.getValue());
    auto signature = protocol::scopedDataSignature(source);
    if (!signature)
      return error("native-proof-codec-function");
    SmallVector<Type> inputs{builder.getI1Type()};
    append_range(inputs, signature.getInputs());
    auto f = function(inputs, signature.getResults());
    exec::ScopedExecutionBuilder control(builder, f);
    auto args = f.getArguments().drop_front();
    auto values = control.conditional(
        args.front(), args.drop_front(), signature.getResults(), "finish",
        [&](unsigned arm) {
          auto body =
              function(signature.getInputs(), signature.getResults(), true);
          exec::ScopedExecutionBuilder nested(builder, body);
          SmallVector<Value> returned;
          if (!arm)
            returned = nested.invoke(
                "func.call", signature.getResults(),
                nested.scoped(body.getArguments().drop_front()),
                {builder.getNamedAttr("callee", method),
                 builder.getNamedAttr("runtime.site",
                                      builder.getStringAttr("handler"))});
          else if (writing)
            returned = kernel(nested, "bytes.empty", {}, {bytes}, "empty");
          nested.complete(returned);
          return body;
        });
    control.returned(values);
    return FlatSymbolRefAttr::get(f);
  }
  pir::LocalCallOp invoke(pir::ParticipantOp participant,
                          FlatSymbolRefAttr reference, ValueRange inputs,
                          StringRef anchor, bool following = false) {
    auto f = symbols.lookup<func::FuncOp>(reference.getValue());
    if (!capacity.text(reference.getValue()) || !capacity.text(anchor) ||
        !charge(1 + inputs.size() +
                protocol::scopedDataSignature(f).getNumResults() +
                helpers.size()))
      return {};
    auto location =
        builder.getInsertionPoint() == builder.getInsertionBlock()->end()
            ? participant.getLoc()
            : builder.getInsertionPoint()->getLoc();
    auto call = pir::LocalCallOp::create(
        builder, location, protocol::scopedDataSignature(f).getResults(),
        inputs, reference, builder.getStringAttr(fresh()),
        participant.getRoleAttr());
    if (!is_contained(helpers, reference))
      helpers.push_back(reference);
    auto target = builder.getDictionaryAttr(
        {builder.getNamedAttr("participant",
                              FlatSymbolRefAttr::get(participant)),
         builder.getNamedAttr("operation",
                              builder.getStringAttr("protocol.local_call"))});
    auto action = builder.getDictionaryAttr(
        {builder.getNamedAttr("site", call.getSiteAttr()),
         builder.getNamedAttr("kind",
                              builder.getStringAttr("protocol.local_call")),
         builder.getNamedAttr("callee", reference),
         builder.getNamedAttr("targets", builder.getArrayAttr({target}))});
    (following ? after : before)[anchor.str()].push_back(action);
    return call;
  }
  Error indexMessages(ArrayRef<NativeTranscriptEvent> events,
                      const json::Array &transcript) {
    StringMap<FlatSymbolRefAttr> observers;
    StringMap<std::string> sites;
    StringMap<const NativeTranscriptEvent *> bySite;
    for (const auto &event : events) {
      sites[event.origin] = event.site;
      bySite[event.site] = &event;
    }
    for (const auto &item : *transcript[6].getAsArray()) {
      const auto &adapter = *item.getAsArray();
      if (!charge(1 + adapter[2].getAsArray()->size()))
        return error("native-proof-codec-limit");
      for (const auto &origin : *adapter[2].getAsArray()) {
        auto name = *adapter[0].getAsString();
        auto found = sites.find(*origin.getAsString());
        if (!capacity.text(name) ||
            (found != sites.end() && !capacity.text(found->second)))
          return error("native-proof-codec-limit");
        observers[found == sites.end() ? StringRef()
                                       : StringRef(found->second)] =
            FlatSymbolRefAttr::get(module.getContext(), name);
      }
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
    for (auto &item : messages) {
      auto &message = item.second;
      message.slice = slicer(message.decode->chunks.size());
      if (!message.slice)
        return error("native-proof-codec-limit");
      for (const auto &site : message.encode->sites) {
        leaves[site] = &message;
        auto observation = observers.lookup(site);
        if (!observation)
          return error("native-proof-codec-observation");
        if (!charge(1 + message.observations.size()))
          return error("native-proof-codec-limit");
        if (!is_contained(message.observations, observation))
          message.observations.push_back(observation);
        auto *event = bySite.lookup(site);
        if (!event)
          return error("native-proof-codec-origin");
        if (!capacity.text(event->origin))
          return error("native-proof-codec-limit");
        message.origins.push_back(event->origin);
      }
    }
    return Error::success();
  }
  Error message(pir::ParticipantOp participant, Message &selected,
                ArrayRef<Operation *> transport, SmallVectorImpl<Value> &record,
                Value proof,
                const StringMap<SmallVector<pir::LocalCallOp>> &calls) {
    if (!charge(4 * record.size() + 4 * selected.decode->chunks.size() +
                3 * transport.size() + selected.observations.size()))
      return error("native-proof-codec-limit");
    if (transport.size() != selected.encode->sites.size() ||
        !llvm::equal(
            transport, selected.encode->sites,
            [](Operation *op, const std::string &site) {
              return op->getAttrOfType<StringAttr>("site").getValue() == site;
            }))
      return error("native-proof-codec-group");
    bool writing = participant.getRole() == policy.producer;
    SmallVector<pir::LocalCallOp> observations;
    for (auto reference : selected.observations) {
      auto found = calls.find(reference.getValue());
      if (found == calls.end() || found->second.size() != 1)
        return error("native-proof-codec-observation");
      observations.push_back(found->second.front());
    }
    // Read through the final observer, not just the final leaf: moving a
    // single-leaf observer across a branch or a stopping call is also illegal.
    // Ordered cursors avoid a quadratic membership search for large groups.
    unsigned nextTransport = 0, nextObservation = 0;
    for (auto *between = transport.front();
         nextTransport != transport.size() ||
         nextObservation != observations.size();
         between = between->getNextNode()) {
      if (!charge())
        return error("native-proof-codec-limit");
      if (!between)
        return error("native-proof-codec-group");
      if (nextTransport < transport.size() &&
          between == transport[nextTransport])
        ++nextTransport;
      else if (nextObservation < observations.size() &&
               between == observations[nextObservation].getOperation())
        ++nextObservation;
      else if (!mathematical::isTotal(between))
        return error("native-proof-codec-group");
    }
    auto first = observations.front();
    StringRef anchor = first.getSite();
    if (writing) {
      builder.setInsertionPointAfter(transport.back());
      // All payload leaves now dominate encoding. Original admission permitted
      // only total computations between leaves, so move their observations as
      // one ordered group after encoding and original-byte observation.
      for (auto call : reverse(observations))
        call->moveAfter(transport.back());
      builder.setInsertionPoint(first);
    } else
      builder.setInsertionPoint(transport.front());
    SmallVector<Value> inputs(record.begin(), record.end()), chunks;
    if (writing) {
      for (auto *op : transport)
        inputs.push_back(cast<pir::EmitOp>(op).getInput());
      auto call = invoke(participant, selected.encode->handler, inputs, anchor);
      if (!call)
        return error("native-proof-codec-limit");
      record.assign(call.getResults().take_front(codec.record.size()).begin(),
                    call.getResults().take_front(codec.record.size()).end());
      append_range(chunks, call.getResults().drop_front(codec.record.size()));
    } else {
      inputs.push_back(proof);
      auto call =
          invoke(participant, selected.receive->handler, inputs, anchor);
      if (!call)
        return error("native-proof-codec-limit");
      record.assign(call.getResults().take_front(codec.record.size()).begin(),
                    call.getResults().take_front(codec.record.size()).end());
      inputs.assign(1, proof);
      append_range(inputs, call.getResults().drop_front(codec.record.size()));
      auto sliced = invoke(participant, selected.slice, inputs, anchor);
      if (!sliced)
        return error("native-proof-codec-limit");
      append_range(chunks, sliced.getResults());
    }
    if (selected.wire) {
      inputs.assign(first.getInputs().begin(),
                    first.getInputs().begin() + plan.state.size());
      append_range(inputs, chunks);
      auto observed =
          invoke(participant, selected.wire->handler, inputs, anchor);
      if (!observed)
        return error("native-proof-codec-limit");
      for (unsigned i = 0; i < plan.state.size(); ++i)
        first->setOperand(i, observed.getResult(i));
    }
    if (!writing) {
      auto decoded =
          invoke(participant, selected.decode->handler, chunks, anchor);
      if (!decoded)
        return error("native-proof-codec-limit");
      for (auto [i, op] : enumerate(transport))
        op->getResult(0).replaceAllUsesWith(decoded.getResult(i));
      // Preserve one contiguous decode/observation sequence. Total
      // calculations between the original leaves now follow the observers.
      for (auto call : reverse(observations))
        call->moveAfter(decoded);
    }
    for (auto *op : transport)
      op->erase();
    return Error::success();
  }
  Error block(pir::ParticipantOp participant, Block &body,
              SmallVector<Value> record, Value proof, unsigned depth) {
    if (depth > 64 || !charge(record.size() + body.getNumArguments()))
      return error("native-proof-codec-limit");
    StringMap<SmallVector<pir::LocalCallOp>> calls;
    for (auto &op : body) {
      if (!charge(1 + op.getNumOperands() + op.getNumResults()))
        return error("native-proof-codec-limit");
      if (auto call = dyn_cast<pir::LocalCallOp>(op))
        calls[call.getCallee()].push_back(call);
    }
    SmallVector<Operation *> transport;
    for (auto cursor = body.begin(); cursor != body.end();) {
      auto &op = *cursor++;
      if (!charge())
        return error("native-proof-codec-limit");
      if (auto branch = dyn_cast<pir::ParticipantBranchOp>(op)) {
        if (!transport.empty())
          return error("native-proof-codec-group");
        if (branch.getNumRegions() > 512 ||
            !charge(branch.getNumOperands() + branch.getNumResults() +
                    2 * record.size() + unsigned(bool(proof)) +
                    branch.getNumRegions()))
          return error("native-proof-codec-limit");
        SmallVector<Value> inputs(branch.getInputs());
        append_range(inputs, record);
        if (proof)
          inputs.push_back(proof);
        SmallVector<Type> outputs(branch.getResultTypes());
        append_range(outputs, codec.record);
        builder.setInsertionPoint(branch);
        OperationState state(branch.getLoc(), branch->getName());
        state.addOperands(inputs);
        state.addTypes(outputs);
        state.addAttributes(branch->getAttrs());
        for (unsigned i = 0; i < branch.getNumRegions(); ++i)
          state.addRegion();
        auto replacement =
            cast<pir::ParticipantBranchOp>(builder.create(state));
        for (auto [source, target] :
             zip(branch.getArms(), replacement.getArms())) {
          target.takeBody(source);
          auto &child = target.front();
          if (!charge(child.getNumArguments() + record.size() +
                      unsigned(bool(proof))))
            return error("native-proof-codec-limit");
          // Payload formals and all existing transcript/replica captures keep
          // their actual order. Each arm starts from its own new formals.
          SmallVector<Value> nested;
          for (Type type : codec.record)
            nested.push_back(child.addArgument(type, branch.getLoc()));
          Value captured =
              proof ? child.addArgument(bytes, branch.getLoc()) : Value();
          if (auto e = block(participant, child, std::move(nested), captured,
                             depth + 1))
            return e;
        }
        for (auto [oldValue, newValue] :
             zip(branch.getResults(), replacement.getResults()))
          oldValue.replaceAllUsesWith(newValue);
        record.assign(
            replacement.getResults().take_back(codec.record.size()).begin(),
            replacement.getResults().take_back(codec.record.size()).end());
        branch.erase();
      } else if (auto loop = dyn_cast<pir::ProtocolLoopOp>(op)) {
        if (!transport.empty())
          return error("native-proof-codec-group");
        if (!charge(loop.getNumOperands() + loop.getNumResults() +
                    loop.getBody().front().getNumArguments() +
                    3 * record.size() + 2 * unsigned(bool(proof))))
          return error("native-proof-codec-limit");
        unsigned split = 1 + loop.getCarried();
        SmallVector<Value> inputs(loop.getInputs());
        inputs.insert(inputs.begin() + split, record.begin(), record.end());
        if (proof)
          inputs.push_back(proof);
        SmallVector<Type> outputs(loop.getResultTypes());
        append_range(outputs, codec.record);
        builder.setInsertionPoint(loop);
        auto replacement = pir::ProtocolLoopOp::create(
            builder, loop.getLoc(), outputs, inputs, loop.getSiteAttr(),
            builder.getI64IntegerAttr(loop.getCarried() + record.size()),
            loop.getCountAttr(), loop.getParameterAttr(),
            loop.getMaximumAttr());
        replacement.getBody().takeBody(loop.getBody());
        auto &child = replacement.getBody().front();
        SmallVector<Value> nested;
        for (auto [i, type] : enumerate(codec.record))
          nested.push_back(
              child.insertArgument(split + i, type, loop.getLoc()));
        Value captured =
            proof ? child.addArgument(bytes, loop.getLoc()) : Value();
        if (auto e = block(participant, child, std::move(nested), captured,
                           depth + 1))
          return e;
        for (auto [oldValue, newValue] :
             zip(loop.getResults(), replacement.getResults()))
          oldValue.replaceAllUsesWith(newValue);
        record.assign(
            replacement.getResults().take_back(codec.record.size()).begin(),
            replacement.getResults().take_back(codec.record.size()).end());
        loop.erase();
      } else if (auto yielded = dyn_cast<pir::ProtocolYieldOp>(op)) {
        if (!transport.empty())
          return error("native-proof-codec-group");
        if (!charge(record.size()))
          return error("native-proof-codec-limit");
        yielded->insertOperands(yielded.getNumOperands(), record);
      } else if (isa<pir::FinishOp, pir::FinishIfOp>(op)) {
        if (!transport.empty())
          return error("native-proof-codec-group");
        auto conditional = dyn_cast<pir::FinishIfOp>(op);
        bool writing = participant.getRole() == policy.producer;
        SmallVector<Value> inputs;
        if (conditional)
          inputs.push_back(conditional.getCondition());
        append_range(inputs, record);
        if (!writing)
          inputs.push_back(proof);
        builder.setInsertionPoint(&op);
        auto call = invoke(
            participant,
            conditional ? (writing ? conditionalWrite : conditionalFinish)
                        : (writing ? codec.write : codec.finish),
            inputs, conditional ? conditional.getSite() : "");
        if (!call)
          return error("native-proof-codec-limit");
        if (writing) {
          if (conditional) {
            SmallVector<Value> values(conditional.getValues());
            values.push_back(call.getResult(0));
            SmallVector<Type> outputs(conditional.getResultTypes());
            auto replacement = pir::FinishIfOp::create(
                builder, conditional.getLoc(), outputs,
                conditional.getCondition(), values, conditional.getSite(),
                conditional.getOwner());
            for (auto [oldValue, newValue] :
                 zip(conditional.getResults(), replacement.getResults()))
              oldValue.replaceAllUsesWith(newValue);
            conditional.erase();
          } else
            op.insertOperands(op.getNumOperands(), call.getResults());
        }
      } else if (auto site = op.getAttrOfType<StringAttr>("site");
                 site && isa<pir::EmitOp, pir::AwaitOp>(op)) {
        auto *selected = leaves.lookup(site.getValue());
        if (!selected)
          return error("native-proof-codec-coverage");
        if (transport.size() >= selected->encode->sites.size() ||
            site.getValue() != selected->encode->sites[transport.size()])
          return error("native-proof-codec-group");
        transport.push_back(&op);
        if (site.getValue() == selected->encode->sites.back()) {
          // Moving observer calls may invalidate the current list iterator.
          // Resume at the last transport's original successor after conversion.
          Operation *resume = cursor == body.end() ? nullptr : &*cursor;
          if (auto e = message(participant, *selected, transport, record, proof,
                               calls))
            return e;
          transport.clear();
          cursor = resume ? resume->getIterator() : body.end();
        }
      }
    }
    return transport.empty() ? Error::success()
                             : error("native-proof-codec-group");
  }

public:
  CodecEmitter(pir::ProtocolModuleOp module, const NativeProofPolicy &policy,
               const protocol::ConstructionPlan &plan, CodecCapacity &capacity)
      : module(module), policy(policy), plan(plan), codec(*plan.codec),
        builder(module.getContext()), symbols(module), capacity(capacity) {
    bytes = data::BytesType::get(module.getContext());
    index = builder.getIntegerType(64, false);
    module.walk([&](Operation *op) {
      if (auto site = op->getAttrOfType<StringAttr>("site"))
        occupied.insert(site.getValue());
    });
  }
  Expected<json::Array> run(ArrayRef<NativeTranscriptEvent> events,
                            const json::Array &transcript) {
    if (auto e = indexMessages(events, transcript))
      return std::move(e);
    bool needsConditional = false;
    module.walk([&](pir::FinishIfOp) { needsConditional = true; });
    if (needsConditional) {
      if (!charge(16 * codec.record.size() + 64))
        return error("native-proof-codec-limit");
      auto write = conditional(codec.write, true);
      if (!write)
        return write.takeError();
      conditionalWrite = *write;
      auto finish = conditional(codec.finish, false);
      if (!finish)
        return finish.takeError();
      conditionalFinish = *finish;
    }
    auto projection =
        *module.getBody().front().getOps<pir::ProjectionOp>().begin();
    auto original = cast<DictionaryAttr>(projection.getInterfaces()[0]);
    auto construction = original.getAs<DictionaryAttr>("construction");
    for (auto participant :
         module.getBody().front().getOps<pir::ParticipantOp>()) {
      bool writing = participant.getRole() == policy.producer;
      auto &body = participant.getBody().front();
      auto type = participant.getFunctionType();
      SmallVector<Type> inputs(type.getInputs()), outputs(type.getResults());
      Value proof;
      if (writing)
        outputs.push_back(bytes);
      else {
        inputs.push_back(bytes);
        proof = body.addArgument(bytes, participant.getLoc());
      }
      participant.setFunctionType(builder.getFunctionType(inputs, outputs));
      SmallVector<Value> layout;
      for (auto item : original.getAs<ArrayAttr>("participants")) {
        if (!charge())
          return error("native-proof-codec-limit");
        auto ports = cast<DictionaryAttr>(item);
        if (ports.getAs<FlatSymbolRefAttr>("participant") !=
            FlatSymbolRefAttr::get(participant))
          continue;
        auto originalInputs = ports.getAs<ArrayAttr>("inputs");
        // Index this role's original port identities once. Repeated linear
        // searches multiply the admitted input width by the codec width.
        if (!charge(originalInputs.size()) || !charge(codec.inputs.size()))
          return error("native-proof-codec-limit");
        llvm::DenseMap<Attribute, unsigned> positions;
        for (auto [position, input] : enumerate(originalInputs))
          positions.try_emplace(input, position);
        for (unsigned input : codec.inputs) {
          auto found = positions.find(builder.getI64IntegerAttr(input));
          if (found == positions.end())
            return error("native-proof-codec-layout");
          layout.push_back(body.getArgument(found->second));
        }
      }
      Operation *position = &body.front();
      StringRef anchor;
      unsigned roots =
          unsigned(plan.root == protocol::ConstructionPlan::Root::Local) +
          count_if(plan.rules, [](const Rule &rule) {
            return rule.kind == Rule::Kind::Start;
          });
      for (unsigned i = 0; i < roots; ++i) {
        auto call = dyn_cast_or_null<pir::LocalCallOp>(position);
        if (!call)
          return error("native-proof-codec-root");
        anchor = call.getSite();
        position = position->getNextNode();
      }
      if (!position)
        return error("native-proof-codec-root");
      builder.setInsertionPoint(position);
      auto initialized = invoke(participant, codec.initialize, layout, anchor,
                                !anchor.empty());
      if (!initialized)
        return error("native-proof-codec-limit");
      if (anchor.empty()) {
        prefix.push_back(before[""].back());
        before[""].pop_back();
      }
      if (auto e =
              block(participant, body,
                    SmallVector<Value>(initialized.getResults()), proof, 0))
        return std::move(e);
    }
    auto rewrite = [&](auto &&self, ArrayAttr actions, bool root,
                       unsigned depth) -> Expected<ArrayAttr> {
      if (depth > 64 || !charge(actions.size() +
                                (root ? prefix.size() + before[""].size() : 0)))
        return error("native-proof-codec-limit");
      SmallVector<Attribute> rewritten;
      if (root)
        append_range(rewritten, prefix);
      for (auto item : actions) {
        auto action = cast<DictionaryAttr>(item);
        auto site = action.getAs<StringAttr>("site");
        if (!charge(before[site.str()].size() + after[site.str()].size()))
          return error("native-proof-codec-limit");
        append_range(rewritten, before[site.str()]);
        if (!leaves.count(site.str())) {
          if (auto nested = action.getAs<ArrayAttr>("body")) {
            NamedAttrList fields(action);
            auto body = self(self, nested, false, depth + 1);
            if (!body)
              return body.takeError();
            fields.set("body", *body);
            action = fields.getDictionary(module.getContext());
          }
          if (auto arms = action.getAs<ArrayAttr>("arms")) {
            if (arms.size() > 512 || !charge(arms.size()))
              return error("native-proof-codec-limit");
            SmallVector<Attribute> rewrittenArms;
            for (auto item : arms) {
              auto arm = cast<DictionaryAttr>(item);
              NamedAttrList fields(arm);
              auto body =
                  self(self, arm.getAs<ArrayAttr>("body"), false, depth + 1);
              if (!body)
                return body.takeError();
              fields.set("body", *body);
              rewrittenArms.push_back(
                  fields.getDictionary(module.getContext()));
            }
            NamedAttrList fields(action);
            fields.set("arms", builder.getArrayAttr(rewrittenArms));
            action = fields.getDictionary(module.getContext());
          }
          rewritten.push_back(action);
        }
        append_range(rewritten, after[site.str()]);
      }
      if (root)
        append_range(rewritten, before[""]);
      return builder.getArrayAttr(rewritten);
    };
    NamedAttrList updated(construction);
    SmallVector<Attribute> allHelpers(
        construction.getAs<ArrayAttr>("helpers").getValue());
    for (auto helper : helpers) {
      if (!charge(allHelpers.size() + 1))
        return error("native-proof-codec-limit");
      if (!is_contained(allHelpers, helper))
        allHelpers.push_back(helper);
    }
    updated.set("helpers", builder.getArrayAttr(allHelpers));
    auto actions =
        rewrite(rewrite, construction.getAs<ArrayAttr>("actions"), true, 0);
    if (!actions)
      return actions.takeError();
    updated.set("actions", *actions);
    updated.set(
        "codec",
        builder.getDictionaryAttr(
            {builder.getNamedAttr("producer",
                                  builder.getStringAttr(policy.producer)),
             builder.getNamedAttr("validator",
                                  builder.getStringAttr(policy.validator)),
             builder.getNamedAttr("helpers", builder.getArrayAttr(helpers))}));
    NamedAttrList interface(original);
    interface.set("construction", updated.getDictionary(module.getContext()));
    projection.setInterfacesAttr(
        builder.getArrayAttr({interface.getDictionary(module.getContext())}));
    json::Array slots, inputs, associations;
    for (Type type : codec.record) {
      // Reserve the actual owned type/spelling expansion independently of IR.
      if (!capacity.type(type))
        return error("native-proof-codec-limit");
      auto logical = protocol::encodeBoundType(type, false);
      if (!logical)
        return logical.takeError();
      slots.push_back(logical->spelling());
    }
    for (unsigned input : codec.inputs)
      inputs.push_back(std::to_string(input));
    for (const auto &event : events) {
      auto found = messages.find(event.site);
      if (found == messages.end())
        continue;
      const auto &m = found->second;
      json::Array origins;
      for (const auto &origin : m.origins) {
        if (!capacity.text(origin))
          return error("native-proof-codec-limit");
        origins.push_back(origin);
      }
      associations.push_back(json::Array{
          m.encode->handler.getValue(), m.receive->handler.getValue(),
          m.decode->handler.getValue(),
          m.wire ? m.wire->handler.getValue() : StringRef(), m.slice.getValue(),
          std::move(origins)});
    }
    return json::Array{
        codec.provider,
        std::move(slots),
        codec.initialize.getValue(),
        codec.write.getValue(),
        codec.finish.getValue(),
        std::move(inputs),
        std::move(associations),
        conditionalWrite ? conditionalWrite.getValue() : StringRef(),
        conditionalFinish ? conditionalFinish.getValue() : StringRef()};
  }
};
} // namespace
Expected<json::Array>
constructNativeCodec(ModuleOp module, const NativeProofPolicy &policy,
                     const protocol::ConstructionPlan &plan,
                     ArrayRef<NativeTranscriptEvent> events,
                     const json::Array &transcript) {
  CodecCapacity capacity;
  if (!capacity.operation(module))
    return error("native-proof-codec-limit");
  capacity.finishNativePreflight();
  if (!capacity.inputs(policy, plan, events, transcript))
    return error("native-proof-codec-limit");
  return codecWithNativeWork(
      capacity, "native-proof-codec-limit", [&]() -> Expected<json::Array> {
        // Generated work and native callbacks can exhaust after setup. All
        // changes remain staged until the terminal check before publication.
        // Type/resource payloads stay stable; emission creates new handles.
        auto original = cast<pir::ProtocolModuleOp>(module.getBody()->front());
        OwningOpRef<pir::ProtocolModuleOp> staged(
            cast<pir::ProtocolModuleOp>(original->clone()));
        auto result = CodecEmitter(*staged, policy, plan, capacity)
                          .run(events, transcript);
        if (!result)
          return result.takeError();
        if (!capacity.charge(0))
          return error("native-proof-codec-limit");
        original.getBody().takeBody(staged->getBody());
        return std::move(*result);
      });
}
} // namespace zkc::detail
