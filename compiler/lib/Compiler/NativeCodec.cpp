#include "NativeCodec.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Support/Refusal.h"
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
  uint64_t remaining = 1000000;

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
    auto op = local::OperationBindingOp::create(builder, module.getLoc(),
                                                fresh(), contract,
                                                builder.getArrayAttr({}), "");
    symbols.insert(op);
    return FlatSymbolRefAttr::get(op);
  }
  Operation *kernel(StringRef contract, ValueRange inputs, TypeRange outputs) {
    auto selected = binding(contract);
    OperationState state(module.getLoc(),
                         protocol::boundOperationName(contract));
    state.addOperands(inputs);
    state.addTypes(outputs);
    state.addAttribute("binding", selected);
    state.addAttribute("site", builder.getStringAttr(fresh()));
    state.addAttribute("parameters", builder.getArrayAttr({}));
    return builder.create(state);
  }
  local::FuncOp function(TypeRange inputs, TypeRange outputs) {
    builder.setInsertionPointToEnd(&module.getBody().front());
    auto f = local::FuncOp::create(builder, module.getLoc(), fresh(),
                                   builder.getFunctionType(inputs, outputs));
    symbols.insert(f);
    f->setAttr("logical_origin",
               builder.getArrayAttr({builder.getStringAttr(f.getSymName()),
                                     builder.getArrayAttr({})}));
    builder.setInsertionPointToEnd(f.addEntryBlock());
    return f;
  }
  FlatSymbolRefAttr slicer(unsigned count) {
    auto found = slices.find(count);
    if (found != slices.end())
      return found->second;
    SmallVector<Type> inputs{bytes}, outputs(count, bytes);
    inputs.append(2 * count, index);
    auto f = function(inputs, outputs);
    auto args = f.getBody().front().getArguments();
    SmallVector<Value> values;
    for (unsigned i = 0; i < count; ++i)
      values.push_back(kernel("bytes.slice",
                              {args[0], args[1 + 2 * i], args[2 + 2 * i]},
                              {bytes})
                           ->getResult(0));
    local::ReturnOp::create(builder, module.getLoc(), values);
    auto result = FlatSymbolRefAttr::get(f);
    slices.emplace(count, result);
    return result;
  }
  Expected<FlatSymbolRefAttr> conditional(FlatSymbolRefAttr method,
                                          bool writing) {
    auto source = symbols.lookup<local::FuncOp>(method.getValue());
    if (!source || !source.getBody().hasOneBlock())
      return error("native-proof-codec-function");
    SmallVector<Type> inputs{builder.getI1Type()};
    append_range(inputs, source.getArgumentTypes());
    auto f = function(inputs, source.getResultTypes());
    auto branch = local::LocalIfOp::create(
        builder, module.getLoc(), source.getResultTypes(),
        f.getBody().front().getArguments(), fresh());
    for (bool taken : {true, false}) {
      auto &region = taken ? branch.getThenRegion() : branch.getElseRegion();
      auto *body = new Block;
      region.push_back(body);
      body->addArguments(
          source.getArgumentTypes(),
          SmallVector<Location>(source.getNumArguments(), module.getLoc()));
      builder.setInsertionPointToEnd(body);
      if (taken) {
        IRMapping env;
        env.map(source.getBody().front().getArguments(), body->getArguments());
        for (auto &op : source.getBody().front()) {
          auto walked = op.walk([&](Operation *) {
            if (!remaining)
              return WalkResult::interrupt();
            --remaining;
            return WalkResult::advance();
          });
          if (walked.wasInterrupted())
            return error("native-proof-codec-limit");
          if (auto returned = dyn_cast<local::ReturnOp>(op)) {
            SmallVector<Value> outputs;
            for (Value value : returned.getInputs())
              outputs.push_back(env.lookup(value));
            local::LocalYieldOp::create(builder, module.getLoc(), outputs);
          } else
            builder.clone(op, env);
        }
      } else {
        SmallVector<Value> outputs;
        if (writing)
          outputs.push_back(kernel("bytes.empty", {}, {bytes})->getResult(0));
        local::LocalYieldOp::create(builder, module.getLoc(), outputs);
      }
    }
    builder.setInsertionPointAfter(branch);
    local::ReturnOp::create(builder, module.getLoc(), branch.getResults());
    return FlatSymbolRefAttr::get(f);
  }
  local::CallOp invoke(pir::ParticipantOp participant,
                       FlatSymbolRefAttr reference, ValueRange inputs,
                       StringRef anchor, bool following = false) {
    auto f = symbols.lookup<local::FuncOp>(reference.getValue());
    auto location =
        builder.getInsertionPoint() == builder.getInsertionBlock()->end()
            ? participant.getLoc()
            : builder.getInsertionPoint()->getLoc();
    auto call =
        local::CallOp::create(builder, location, f.getResultTypes(), inputs,
                              reference, builder.getStringAttr(fresh()));
    if (!is_contained(helpers, reference))
      helpers.push_back(reference);
    auto target = builder.getDictionaryAttr(
        {builder.getNamedAttr("participant",
                              FlatSymbolRefAttr::get(participant)),
         builder.getNamedAttr("operation",
                              builder.getStringAttr("local.call"))});
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
    for (const auto &event : events)
      sites[event.origin] = event.site;
    for (const auto &item : *transcript[6].getAsArray()) {
      const auto &adapter = *item.getAsArray();
      for (const auto &origin : *adapter[2].getAsArray())
        observers[sites.lookup(*origin.getAsString())] = FlatSymbolRefAttr::get(
            module.getContext(), *adapter[0].getAsString());
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
      for (const auto &site : message.encode->sites) {
        leaves[site] = &message;
        auto observation = observers.lookup(site);
        if (!observation)
          return error("native-proof-codec-observation");
        if (!is_contained(message.observations, observation))
          message.observations.push_back(observation);
        auto event = find_if(
            events, [&](const auto &event) { return event.site == site; });
        if (event == events.end())
          return error("native-proof-codec-origin");
        message.origins.push_back(event->origin);
      }
    }
    return Error::success();
  }
  Error message(pir::ParticipantOp participant, Message &selected,
                ArrayRef<Operation *> transport, SmallVectorImpl<Value> &record,
                Value proof) {
    if (transport.size() != selected.encode->sites.size() ||
        !llvm::equal(
            transport, selected.encode->sites,
            [](Operation *op, const std::string &site) {
              return op->getAttrOfType<StringAttr>("site").getValue() == site;
            }))
      return error("native-proof-codec-group");
    bool writing = participant.getRole() == policy.producer;
    SmallVector<local::CallOp> observations;
    for (auto reference : selected.observations) {
      local::CallOp found;
      for (auto &op : *transport.front()->getBlock())
        if (auto call = dyn_cast<local::CallOp>(op);
            call && call.getCalleeAttr() == reference) {
          if (found)
            return error("native-proof-codec-observation");
          found = call;
        }
      if (!found)
        return error("native-proof-codec-observation");
      observations.push_back(found);
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
      record.assign(call.getResults().take_front(codec.record.size()).begin(),
                    call.getResults().take_front(codec.record.size()).end());
      append_range(chunks, call.getResults().drop_front(codec.record.size()));
    } else {
      inputs.push_back(proof);
      auto call =
          invoke(participant, selected.receive->handler, inputs, anchor);
      record.assign(call.getResults().take_front(codec.record.size()).begin(),
                    call.getResults().take_front(codec.record.size()).end());
      inputs.assign(1, proof);
      append_range(inputs, call.getResults().drop_front(codec.record.size()));
      auto sliced = invoke(participant, selected.slice, inputs, anchor);
      append_range(chunks, sliced.getResults());
    }
    if (selected.wire) {
      inputs.assign(first.getInputs().begin(),
                    first.getInputs().begin() + plan.state.size());
      append_range(inputs, chunks);
      auto observed =
          invoke(participant, selected.wire->handler, inputs, anchor);
      for (unsigned i = 0; i < plan.state.size(); ++i)
        first->setOperand(i, observed.getResult(i));
    }
    if (!writing) {
      auto decoded =
          invoke(participant, selected.decode->handler, chunks, anchor);
      for (auto [i, op] : enumerate(transport))
        op->getResult(0).replaceAllUsesWith(decoded.getResult(i));
    }
    for (auto *op : transport)
      op->erase();
    return Error::success();
  }
  Error block(pir::ParticipantOp participant, Block &body,
              SmallVector<Value> record, Value proof, unsigned depth) {
    if (depth > 64)
      return error("native-proof-codec-limit");
    SmallVector<Operation *> transport;
    for (auto cursor = body.begin(); cursor != body.end();) {
      auto &op = *cursor++;
      if (!remaining--)
        return error("native-proof-codec-limit");
      if (auto loop = dyn_cast<pir::ProtocolLoopOp>(op)) {
        if (!transport.empty())
          return error("native-proof-codec-group");
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
        transport.push_back(&op);
        if (site.getValue() == selected->encode->sites.back()) {
          // Moving observer calls may invalidate the current list iterator.
          // Resume at the last transport's original successor after conversion.
          Operation *resume = cursor == body.end() ? nullptr : &*cursor;
          if (auto e =
                  message(participant, *selected, transport, record, proof))
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
               const protocol::ConstructionPlan &plan)
      : module(module), policy(policy), plan(plan), codec(*plan.codec),
        builder(module.getContext()), symbols(module) {
    bytes = RankedTensorType::get({ShapedType::kDynamic},
                                  builder.getIntegerType(8, false));
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
        auto ports = cast<DictionaryAttr>(item);
        if (ports.getAs<FlatSymbolRefAttr>("participant") !=
            FlatSymbolRefAttr::get(participant))
          continue;
        auto originalInputs = ports.getAs<ArrayAttr>("inputs");
        for (unsigned input : codec.inputs) {
          auto found = find(originalInputs, builder.getI64IntegerAttr(input));
          if (found == originalInputs.end())
            return error("native-proof-codec-layout");
          layout.push_back(body.getArgument(found - originalInputs.begin()));
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
        auto call = dyn_cast_or_null<local::CallOp>(position);
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
      if (anchor.empty()) {
        prefix.push_back(before[""].back());
        before[""].pop_back();
      }
      if (auto e =
              block(participant, body,
                    SmallVector<Value>(initialized.getResults()), proof, 0))
        return std::move(e);
    }
    auto rewrite = [&](auto &&self, ArrayAttr actions, bool root) -> ArrayAttr {
      SmallVector<Attribute> rewritten;
      if (root)
        append_range(rewritten, prefix);
      for (auto item : actions) {
        auto action = cast<DictionaryAttr>(item);
        auto site = action.getAs<StringAttr>("site");
        append_range(rewritten, before[site.str()]);
        if (!leaves.count(site.str())) {
          if (auto nested = action.getAs<ArrayAttr>("body")) {
            NamedAttrList fields(action);
            fields.set("body", self(self, nested, false));
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
    for (auto helper : helpers)
      if (!is_contained(allHelpers, helper))
        allHelpers.push_back(helper);
    updated.set("helpers", builder.getArrayAttr(allHelpers));
    updated.set(
        "actions",
        rewrite(rewrite, construction.getAs<ArrayAttr>("actions"), true));
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
      for (const auto &origin : m.origins)
        origins.push_back(origin);
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
  return CodecEmitter(cast<pir::ProtocolModuleOp>(module.getBody()->front()),
                      policy, plan)
      .run(events, transcript);
}
} // namespace zkc::detail
