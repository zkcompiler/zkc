// Reach the independent reader while whole-candidate selected admission remains
// an integration gate. Capacity regressions below also call the public APIs.
#include "../lib/Compiler/NativeCodecVerification.cpp"
#include "mlir/IR/AsmState.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/StringMap.h"
#include <functional>
#include <limits>

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace pir = protocol_ir;
namespace {
// This is the actual transcript-side boundary exercised by the codec cases in
// language_constructions.cpp. Form it directly: selected NativeProof admission
// is a separate integration gate and must not be disabled to run codec tests.
// The fixture deliberately has a transcript capture and two same-typed ordinary
// captures before the new Record/proof captures, and different role result
// ABIs.
struct Options {
  bool zeroRecord = false;
  unsigned thenMessages = 2, elseMessages = 0;
  unsigned nesting = 0;
  bool completion = false, stop = false;
};
pir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<pir::ProtocolModuleOp>(module.getBody()->front());
}
OwningOpRef<ModuleOp> copy(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}
void success(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
void limit(Error error) {
  require(bool(error), "expected codec capacity refusal");
  require(namesIdentifier(toString(std::move(error)), "native-codec-limit"),
          "capacity must refuse before admission or correspondence");
}
void unchanged(ModuleOp actual, ModuleOp before, Operation *first) {
  require(&unit(actual).getBody().front().front() == first,
          "capacity refusal replaced original operations");
  require(OperationEquivalence::isEquivalentTo(
              actual, before, OperationEquivalence::IgnoreLocations),
          "capacity refusal mutated the module");
}
Operation *site(ModuleOp module, StringRef name, StringRef role) {
  Operation *result = nullptr;
  module.walk([&](Operation *op) {
    auto owner = op->getParentOfType<pir::ParticipantOp>();
    auto at = op->getAttrOfType<StringAttr>("site");
    if (owner && owner.getRole() == role && at && at.getValue() == name)
      result = op;
  });
  require(result != nullptr, "fixture site is missing");
  return result;
}
DenseResourceElementsAttr resource(MLIRContext &context,
                                   ArrayRef<int64_t> shape) {
  auto type = RankedTensorType::getChecked(
      [&] { return emitError(UnknownLoc::get(&context)); }, shape,
      IntegerType::get(&context, 8));
  require(bool(type), "resource fixture must have a valid tensor type");
  // The generic resource attribute intentionally permits a small physical
  // resource independently of its logical tensor size. Use the generic blob
  // API without materializing the tensor or requesting a typed element view.
  const char byte = 0;
  return DenseResourceElementsAttr::get(
      type, "codec_shape",
      HeapAsmResourceBlob::allocateAndCopyInferAlign(ArrayRef<char>(&byte, 1)));
}
struct Fixture {
  MLIRContext &context;
  OpBuilder builder;
  Options options;
  OwningOpRef<ModuleOp> source;
  NativeProofPolicy policy;
  protocol::ConstructionPlan plan{};
  SmallVector<zkc::detail::NativeTranscriptEvent> events;
  json::Array transcript;
  Type index, bytes;

  FlatSymbolRefAttr ref(StringRef name) {
    return FlatSymbolRefAttr::get(&context, name);
  }
  Value kernel(exec::ScopedExecutionBuilder &control, StringRef name,
               Type output, ArrayRef<Attribute> parameters = {}) {
    return control.invoke(
        "exec.apply", {output}, control.scoped({}),
        {builder.getNamedAttr("binding", ref(name)),
         builder.getNamedAttr("site", builder.getStringAttr(name)),
         builder.getNamedAttr("parameters",
                              builder.getArrayAttr(parameters))})[0];
  }
  void
  function(StringRef name, TypeRange inputs, TypeRange outputs,
           llvm::function_ref<void(exec::ScopedExecutionBuilder &, ValueRange)>
               body) {
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToEnd(&unit(*source).getBody().front());
    SmallVector<Type> arguments{runtime::ScopeType::get(&context)};
    append_range(arguments, inputs);
    auto f = func::FuncOp::create(
        builder, source->getLoc(), name,
        builder.getFunctionType(
            arguments,
            {exec::OutcomeType::get(&context, SmallVector<Type>(outputs))}));
    f.setPrivate();
    f.setNoInline(true);
    f->setAttr("runtime.origin",
               builder.getArrayAttr(
                   {builder.getStringAttr(name), builder.getArrayAttr({})}));
    builder.setInsertionPointToEnd(f.addEntryBlock());
    exec::ScopedExecutionBuilder control(builder, f);
    body(control, f.getArguments().drop_front());
  }
  std::string message(StringRef role, StringRef name, StringRef state) {
    std::string text;
    if (role == "P")
      text = "\"protocol.send\"(%x) {site=\"" + name.str() + "\",schema=\"" +
             name.str() + "\",peer=\"V\"} : (ui64)->()\n";
    else
      text = "%value_" + name.str() + " = \"protocol.receive\"() {site=\"" +
             name.str() + "\",schema=\"" + name.str() +
             "\",peer=\"P\"} : ()->ui64\n";
    std::string payload = role == "P" ? "%x" : "%value_" + name.str();
    text += "%state_" + name.str() + " = \"protocol.local_call\"(" +
            state.str() + "," + payload + ") {callee=@observe_" + name.str() +
            ",site=\"observe_" + name.str() + "_" + role.str() + "\",role=\"" +
            role.str() + "\"} : (ui64,ui64)->ui64\n";
    return text;
  }
  std::string branch(StringRef role, unsigned depth) {
    bool writing = role == "P";
    std::string types = writing ? "ui64" : "(ui64,ui64)";
    auto build = [&](auto &&self, unsigned level, const std::string &path,
                     StringRef choice, StringRef x, StringRef y, StringRef go,
                     StringRef state, StringRef result) -> std::string {
      std::string text = result.str() + (writing ? " = " : ":2 = ");
      text += "\"protocol.participant_branch\"(" + choice.str() + "," +
              x.str() + "," + y.str() + "," + go.str() + "," + state.str() +
              ") (";
      for (unsigned arm = 0; arm != 2; ++arm) {
        if (arm)
          text += ",";
        auto local = [&](StringRef name) {
          return "%" + path + std::to_string(arm) + "_" + name.str();
        };
        std::string ax = local("x"), ay = local("y"), ag = local("go"),
                    as = local("state");
        text += "{ ^arm(" + ax + ":ui64," + ay + ":ui64," + ag + ":i1," + as +
                ":ui64):\n";
        std::string current = as;
        if (!arm && level) {
          std::string n = local("n"), looped = local("looped"), i = local("i"),
                      ls = local("loop_state"), lx = local("loop_x"),
                      ly = local("loop_y"), lg = local("loop_go"),
                      lc = local("loop_choice"), joined = local("joined");
          text += n + " = \"data.index\"() {value=2:ui64} : ()->ui64\n";
          text += looped + " = \"protocol.loop\"(" + n + "," + as + "," + ax +
                  "," + ay + "," + ag + ") ({\n^loop(" + i + ":ui64," + ls +
                  ":ui64," + lx + ":ui64," + ly + ":ui64," + lg + ":i1):\n" +
                  lc + " = \"data.index_equal\"(" + i + "," + i +
                  ") : (ui64,ui64)->i1\n";
          text += self(self, level - 1, path + "nested_", lc, lx, ly, lg, ls,
                       joined);
          text +=
              "\"protocol.yield\"(" + joined + (writing ? "" : "#1") +
              ") : (ui64)->()\n}) {site=\"loop_" + std::to_string(level) +
              "\",carried=1:i64,count=\"\",parameter=false,maximum=2:i64} : "
              "(ui64,ui64,ui64,ui64,i1)->ui64\n";
          current = looped;
        } else if (!level) {
          unsigned count = arm ? options.elseMessages : options.thenMessages;
          for (unsigned j = 0; j < count; ++j) {
            std::string name =
                std::string(arm ? "else" : "then") + std::to_string(j);
            std::string event = message(role, name, current);
            for (size_t pos = 0;
                 (pos = event.find("%x", pos)) != std::string::npos;
                 pos += ax.size())
              event.replace(pos, 2, ax);
            text += event;
            current = "%state_" + name;
          }
          if (!arm && options.stop)
            text += "\"protocol.local_call\"() {callee=@stop,site=\"stop_" +
                    role.str() + "\",role=\"" + role.str() + "\"} : ()->()\n";
          if (!arm && options.completion) {
            std::string values = writing ? current : ag + "," + current;
            text += "\"protocol.finish_if\"(" + ag + "," + values +
                    ") {site=\"complete_" + role.str() + "\",owner=\"" +
                    role.str() +
                    "\"} : " + (writing ? "(i1,ui64)" : "(i1,i1,ui64)") +
                    "->()\n";
          }
        }
        text += "\"protocol.yield\"(" +
                (writing ? current : ay + "," + current) +
                ") : " + (writing ? "(ui64)" : types) + "->()\n}";
      }
      text +=
          ") {site=\"choose_" + std::to_string(level) +
          "\",alternatives=[\"then\",\"else\"]} : (i1,ui64,ui64,i1,ui64)->" +
          types + "\n";
      return text;
    };
    return build(build, depth, "arm_", "%choice", "%x", "%y", "%go", "%state",
                 "%joined");
  }
  std::string participant(StringRef role) {
    bool writing = role == "P";
    std::string text =
        "\"protocol.participant\"() ({\n"
        "^entry(%choice:i1,%x:ui64,%y:ui64,%go:i1):\n"
        "%state = \"protocol.local_call\"() {callee=@root,site=\"root_" +
        role.str() + "\",role=\"" + role.str() + "\"} : ()->ui64\n";
    text += branch(role, options.nesting);
    text += std::string("\"protocol.finish\"(") +
            (writing ? "%joined) : (ui64)" : "%go,%joined#1) : (i1,ui64)") +
            "->()\n"
            "}) {sym_name=\"" +
            role.str() + "\",instance=\"main\",role=\"" + role.str() +
            "\",function_type=(i1,ui64,ui64,i1)->" +
            (writing ? "ui64" : "(i1,ui64)") + "} : ()->()\n";
    return text;
  }
  // Derive retained action maps from these actual participant blocks, pairing
  // only explicitly identical sites. This is fixture setup, never the oracle
  // used by the codec correspondence checker.
  ArrayAttr actions(Block &p, Block &v) {
    SmallVector<Operation *> left, right;
    for (Operation &op : p)
      if (op.hasAttr("site"))
        left.push_back(&op);
    for (Operation &op : v)
      if (op.hasAttr("site"))
        right.push_back(&op);
    require(left.size() == right.size(), "fixture action shape differs");
    SmallVector<Attribute> result;
    auto target = [&](Operation *op, StringRef role) {
      return builder.getDictionaryAttr(
          {builder.getNamedAttr("participant", ref(role)),
           builder.getNamedAttr(
               "operation",
               builder.getStringAttr(op->getName().getStringRef()))});
    };
    for (auto pair : zip(left, right)) {
      auto &a = std::get<0>(pair);
      auto &b = std::get<1>(pair);
      auto make = [&](Operation *op, ArrayRef<Attribute> targets) {
        StringRef kind = op->getName().getStringRef();
        if (isa<pir::EmitOp, pir::AwaitOp>(op))
          kind = "protocol.exchange";
        if (isa<pir::ProtocolLoopOp>(op))
          kind = "protocol.repeat";
        if (isa<pir::ParticipantBranchOp>(op))
          kind = "protocol.branch";
        NamedAttrList fields;
        fields.set("site", op->getAttr("site"));
        fields.set("kind", builder.getStringAttr(kind));
        fields.set("targets", builder.getArrayAttr(targets));
        if (isa<pir::LocalCallOp>(op))
          fields.set("callee", op->getAttr("callee"));
        if (isa<pir::ProtocolLoopOp>(op)) {
          fields.set("maximum", op->getAttr("maximum"));
          fields.set("body",
                     actions(a->getRegion(0).front(), b->getRegion(0).front()));
        }
        if (auto branch = dyn_cast<pir::ParticipantBranchOp>(op)) {
          SmallVector<Attribute> arms;
          for (unsigned i = 0; i < branch.getNumRegions(); ++i)
            arms.push_back(builder.getDictionaryAttr(
                {builder.getNamedAttr("alternative",
                                      branch.getAlternatives()[i]),
                 builder.getNamedAttr("body",
                                      actions(a->getRegion(i).front(),
                                              b->getRegion(i).front()))}));
          fields.set("arms", builder.getArrayAttr(arms));
        }
        result.push_back(fields.getDictionary(&context));
      };
      if (a->getAttr("site") == b->getAttr("site"))
        make(a, {target(a, "P"), target(b, "V")});
      else {
        make(a, {target(a, "P")});
        make(b, {target(b, "V")});
      }
    }
    return builder.getArrayAttr(result);
  }
  Fixture(MLIRContext &context, Options options = {})
      : context(context), builder(&context), options(options) {
    index = builder.getIntegerType(64, false);
    bytes = data::BytesType::get(&context);
    std::string text =
        "module { \"protocol.module\"() ({" + participant("P") +
        participant("V") +
        "\"protocol.entry\"() "
        "{sym_name=\"main\",targets=[[\"P\",@P],[\"V\",@V]]} : ()->()"
        "}) {profile=#protocol.profile<participant>} : ()->() }";
    source = parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
    require(bool(source), "could not parse actual transcript fixture");
    builder.setInsertionPointToStart(&unit(*source).getBody().front());
    runtime::BindingOp::create(builder, source->getLoc(), "empty",
                               "bytes.empty", builder.getArrayAttr({}), "");
    runtime::BindingOp::create(builder, source->getLoc(), "zero",
                               "index.constant", builder.getArrayAttr({}), "");
    auto zero = [&](exec::ScopedExecutionBuilder &c) {
      return kernel(c, "zero", index, {builder.getIntegerAttr(index, 0)});
    };
    function("root", {}, {index},
             [&](auto &c, ValueRange) { c.returned({zero(c)}); });
    if (options.stop)
      function("stop", {}, {},
               [&](auto &c, ValueRange) { c.reject("reject", "stopped"); });
    SmallVector<Type> record;
    if (!options.zeroRecord)
      record.push_back(bytes);
    function("initialize", {}, record, [&](auto &c, ValueRange) {
      SmallVector<Value> output;
      if (!options.zeroRecord)
        output.push_back(kernel(c, "empty", bytes));
      c.returned(output);
    });
    function("write", record, {bytes}, [&](auto &c, ValueRange) {
      c.returned({kernel(c, "empty", bytes)});
    });
    SmallVector<Type> finishInputs(record);
    finishInputs.push_back(bytes);
    function("finish", finishInputs, {},
             [&](auto &c, ValueRange) { c.returned({}); });
    SmallVector<Type> encodeInputs(record), encodeOutputs(record);
    encodeInputs.push_back(index);
    encodeOutputs.push_back(bytes);
    function("encode", encodeInputs, encodeOutputs, [&](auto &c, ValueRange) {
      Value chunk = kernel(c, "empty", bytes);
      SmallVector<Value> output;
      if (!options.zeroRecord)
        output.push_back(chunk);
      output.push_back(chunk);
      c.returned(output);
    });
    SmallVector<Type> receiveOutputs(record);
    receiveOutputs.append({index, index});
    function("receive", finishInputs, receiveOutputs,
             [&](auto &c, ValueRange args) {
               SmallVector<Value> output;
               if (!options.zeroRecord)
                 output.push_back(args.back());
               Value offset = zero(c);
               output.append({offset, offset});
               c.returned(output);
             });
    function("decode", {bytes}, {index},
             [&](auto &c, ValueRange) { c.returned({zero(c)}); });
    function("wire", {index, bytes}, {index},
             [&](auto &c, ValueRange args) { c.returned(args.take_front(1)); });
    policy.entry = "main";
    policy.producer = "P";
    policy.validator = "V";
    policy.services = {4};
    plan.root = protocol::ConstructionPlan::Root::Local;
    plan.provider = "fixture";
    plan.symbol = ref("fixture");
    plan.target = ref("main");
    plan.initializer = ref("root");
    plan.nativeBase = false;
    plan.state = {index};
    plan.services = {4};
    plan.codec = protocol::ConstructionCodec{
        "fixture", record, ref("initialize"), ref("write"), ref("finish"), {}};
    json::Array observers;
    for (unsigned arm = 0; arm != 2; ++arm)
      for (unsigned i = 0;
           i < (arm ? options.elseMessages : options.thenMessages); ++i) {
        std::string name =
            std::string(arm ? "else" : "then") + std::to_string(i);
        std::string observer = "observe_" + name;
        function(
            observer, {index, index}, {index},
            [&](auto &c, ValueRange args) { c.returned(args.take_front(1)); });
        zkc::detail::NativeTranscriptEvent event{};
        event.site = name;
        event.origin = "fixture-origin-" + name;
        event.payload = index;
        events.push_back(event);
        observers.push_back(
            json::Array{observer, "", json::Array{event.origin}});
        for (auto [kind, handler] :
             {std::pair{protocol::ConstructionRule::Kind::Encode, "encode"},
              std::pair{protocol::ConstructionRule::Kind::Receive, "receive"},
              std::pair{protocol::ConstructionRule::Kind::Decode, "decode"},
              std::pair{protocol::ConstructionRule::Kind::Wire, "wire"}}) {
          protocol::ConstructionRule rule{};
          rule.kind = kind;
          rule.handler = ref(handler);
          rule.sites = {name};
          rule.payload = {index};
          rule.chunks = {bytes};
          plan.rules.push_back(rule);
        }
      }
    transcript =
        json::Array{"fixture",     json::Array{},       "", "", json::Array{},
                    json::Array{}, std::move(observers)};
    auto p = SymbolTable(unit(*source)).lookup<pir::ParticipantOp>("P");
    auto v = SymbolTable(unit(*source)).lookup<pir::ParticipantOp>("V");
    auto sequence = actions(p.getBody().front(), v.getBody().front());
    // Keep the ordinary source actions, and explicitly identify the internal
    // transcript result and removed verifier service in the retained interface.
    auto metadata = parseSourceString<ModuleOp>(R"mlir(module {
      "protocol.projection"() {calculations=[],interfaces=[{
        source="main",entry=@main,
        original_type=(i1,ui64,ui64,i1,!protocol.service_ref<"random.bls12-381.fr/0">)->i1,
        roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"],["P","V"],["V"]],output_roles=[["V"]],statements=[],actions=[],
        participants=[{participant=@P,role="P",inputs=[0:i64,1:i64,2:i64,3:i64],service_inputs=[],outputs=[]},
          {participant=@V,role="V",inputs=[0:i64,1:i64,2:i64,3:i64],service_inputs=[4:i64],outputs=[0:i64]}],
        construction={format="zkc.native-construction/0",state=[ui64],root="local",plan="fixture",helpers=[],removed_services=[4:i64],actions=[]}
      }]} : ()->()
    })mlir",
                                                ParserConfig(&context, false));
    require(bool(metadata), "could not parse fixture interface");
    auto projection = cast<pir::ProjectionOp>(metadata->getBody()->front());
    NamedAttrList interface(
        cast<DictionaryAttr>(projection.getInterfaces()[0]));
    NamedAttrList construction(
        cast<DictionaryAttr>(interface.get("construction")));
    construction.set("actions", sequence);
    interface.set("actions", sequence);
    interface.set("construction", construction.getDictionary(&context));
    projection.setInterfacesAttr(
        builder.getArrayAttr({interface.getDictionary(&context)}));
    projection->moveBefore(&unit(*source).getBody().front(),
                           unit(*source).getBody().front().end());
  }
  json::Array construct(ModuleOp candidate) {
    return take(zkc::detail::constructNativeCodec(candidate, policy, plan,
                                                  events, transcript));
  }
  Error read(ModuleOp candidate, const json::Array &codec) {
    zkc::detail::CodecCapacity capacity;
    if (!capacity.operation(*source) || !capacity.operation(candidate) ||
        !capacity.inputs(policy, plan, events, transcript) ||
        !capacity.jsonArray(codec))
      return zkc::error("native-codec-limit");
    auto execution = protocol::readSourceExecutionClosure(unit(candidate));
    if (!execution)
      return execution.takeError();
    zkc::detail::CodecCorrespondence checker(unit(candidate), policy, plan,
                                             *execution, capacity);
    if (!checker.check(unit(*source), unit(candidate), events, transcript,
                       codec))
      return zkc::error(checker.exhausted() ? "native-codec-limit"
                                            : "native-codec-correspondence",
                        checker.detail());
    return Error::success();
  }
  void check(ModuleOp candidate, const json::Array &codec) {
    success(read(candidate, codec));
  }
  void inputLayout(unsigned count, ArrayRef<unsigned> selected,
                   bool privatePort = false) {
    require(count >= 4, "fixture must retain its four used inputs");
    auto projection =
        *unit(*source).getBody().front().getOps<pir::ProjectionOp>().begin();
    NamedAttrList interface(
        cast<DictionaryAttr>(projection.getInterfaces()[0]));
    auto originalType = cast<FunctionType>(
        cast<TypeAttr>(interface.get("original_type")).getValue());
    SmallVector<Type> originalInputs(originalType.getInputs().take_front(4));
    originalInputs.append(count - 4, index);
    SmallVector<Attribute> owners;
    for (unsigned i = 0; i < count; ++i)
      owners.push_back(builder.getArrayAttr(
          privatePort && i == 4
              ? SmallVector<Attribute>{builder.getStringAttr("P")}
              : SmallVector<Attribute>{builder.getStringAttr("P"),
                                       builder.getStringAttr("V")}));
    SmallVector<Attribute> participants;
    for (auto item : cast<ArrayAttr>(interface.get("participants"))) {
      NamedAttrList ports(cast<DictionaryAttr>(item));
      auto role = cast<StringAttr>(ports.get("role"));
      auto participant =
          SymbolTable(unit(*source))
              .lookup<pir::ParticipantOp>(
                  cast<FlatSymbolRefAttr>(ports.get("participant")).getValue());
      SmallVector<Attribute> identities;
      SmallVector<Type> inputs;
      for (unsigned i = 0; i < count; ++i) {
        if (!is_contained(cast<ArrayAttr>(owners[i]), role))
          continue;
        identities.push_back(builder.getI64IntegerAttr(i));
        inputs.push_back(originalInputs[i]);
        if (i >= 4)
          participant.getBody().front().addArgument(originalInputs[i],
                                                    participant.getLoc());
      }
      participant.setFunctionType(builder.getFunctionType(
          inputs, participant.getFunctionType().getResults()));
      ports.set("inputs", builder.getArrayAttr(identities));
      ports.set(
          "service_inputs",
          builder.getArrayAttr(
              role.getValue() == "V"
                  ? SmallVector<Attribute>{builder.getI64IntegerAttr(count)}
                  : SmallVector<Attribute>{}));
      participants.push_back(ports.getDictionary(&context));
    }
    SmallVector<Type> initializeInputs{runtime::ScopeType::get(&context)};
    auto initialize =
        SymbolTable(unit(*source)).lookup<func::FuncOp>("initialize");
    for (unsigned input : selected) {
      require(input < count, "fixture selected an absent original port");
      initializeInputs.push_back(originalInputs[input]);
      initialize.getBody().front().addArgument(originalInputs[input],
                                               initialize.getLoc());
    }
    initialize.setFunctionType(builder.getFunctionType(
        initializeInputs, initialize.getFunctionType().getResults()));
    plan.codec->inputs.assign(selected.begin(), selected.end());
    originalInputs.push_back(originalType.getInputs().back());
    owners.push_back(builder.getArrayAttr({builder.getStringAttr("V")}));
    interface.set("original_type",
                  TypeAttr::get(builder.getFunctionType(
                      originalInputs, originalType.getResults())));
    interface.set("input_roles", builder.getArrayAttr(owners));
    interface.set("participants", builder.getArrayAttr(participants));
    NamedAttrList construction(
        cast<DictionaryAttr>(interface.get("construction")));
    construction.set("removed_services",
                     builder.getArrayAttr({builder.getI64IntegerAttr(count)}));
    interface.set("construction", construction.getDictionary(&context));
    projection.setInterfacesAttr(
        builder.getArrayAttr({interface.getDictionary(&context)}));
    policy.services = {count};
    plan.services = {count};
  }
  void variant(unsigned count, bool payload) {
    SmallVector<data::AlternativeAttr> alternatives;
    SmallVector<Attribute> labels;
    for (unsigned i = 0; i < count; ++i) {
      auto label = builder.getStringAttr("arm" + std::to_string(i));
      SmallVector<Type> fields;
      if (payload && i == 1)
        fields.push_back(index);
      alternatives.push_back(
          data::AlternativeAttr::get(&context, label, fields));
      labels.push_back(label);
    }
    auto type = data::VariantType::get(
        &context,
        data::importVariantIdentity(&context,
                                    protocol::VariantIdentity("CodecChoice")),
        alternatives);
    for (StringRef role : {"P", "V"}) {
      auto participant =
          SymbolTable(unit(*source)).lookup<pir::ParticipantOp>(role);
      auto oldType = participant.getFunctionType();
      SmallVector<Type> inputs(oldType.getInputs());
      inputs[0] = type;
      participant.setFunctionType(
          builder.getFunctionType(inputs, oldType.getResults()));
      participant.getBody().front().getArgument(0).setType(type);
      auto old =
          cast<pir::ParticipantBranchOp>(site(*source, "choose_0", role));
      builder.setInsertionPoint(old);
      OperationState state(old.getLoc(), old->getName());
      state.addOperands(old.getInputs());
      state.addTypes(old.getResultTypes());
      state.addAttributes(old->getAttrs());
      for (unsigned i = 0; i < count; ++i)
        state.addRegion();
      auto replacement = cast<pir::ParticipantBranchOp>(builder.create(state));
      replacement.setAlternativesAttr(builder.getArrayAttr(labels));
      for (unsigned i = 0; i < count; ++i) {
        IRMapping mapping;
        old.getArms()[1].cloneInto(&replacement.getArms()[i], mapping);
        if (payload && i == 1) {
          auto &block = replacement.getArms()[i].front();
          Value selected = block.insertArgument(0u, index, old.getLoc());
          if (role == "V")
            block.back().setOperand(0, selected);
        }
      }
      old->replaceAllUsesWith(replacement.getResults());
      old.erase();
    }
    auto p = SymbolTable(unit(*source)).lookup<pir::ParticipantOp>("P");
    auto v = SymbolTable(unit(*source)).lookup<pir::ParticipantOp>("V");
    auto sequence = actions(p.getBody().front(), v.getBody().front());
    auto projection =
        *unit(*source).getBody().front().getOps<pir::ProjectionOp>().begin();
    NamedAttrList interface(
        cast<DictionaryAttr>(projection.getInterfaces()[0]));
    auto oldType = cast<FunctionType>(
        cast<TypeAttr>(interface.get("original_type")).getValue());
    SmallVector<Type> inputs(oldType.getInputs());
    inputs[0] = type;
    interface.set("original_type", TypeAttr::get(builder.getFunctionType(
                                       inputs, oldType.getResults())));
    NamedAttrList construction(
        cast<DictionaryAttr>(interface.get("construction")));
    construction.set("actions", sequence);
    interface.set("actions", sequence);
    interface.set("construction", construction.getDictionary(&context));
    projection.setInterfacesAttr(
        builder.getArrayAttr({interface.getDictionary(&context)}));
  }
};
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  for (bool empty : {false, true})
    for (unsigned alternative : {0u, 1u})
      cases.run(
          Twine(empty ? "zero Record: " : "Record: ") +
              (alternative ? "unequal arms" : "event-free alternative"),
          [&] {
            Options options;
            options.zeroRecord = empty;
            options.elseMessages = alternative;
            Fixture fixture(context, options);
            auto candidate = copy(*fixture.source);
            auto codec = fixture.construct(*candidate);
            fixture.check(*candidate, codec);
            for (StringRef role : {"P", "V"}) {
              auto branch = cast<pir::ParticipantBranchOp>(
                  site(*candidate, "choose_0", role));
              unsigned record = unsigned(!empty), proof = unsigned(role == "V");
              require(branch.getNumOperands() == 5 + record + proof,
                      "branch did not append the exact Record/proof captures");
              require(branch.getNumResults() ==
                          (role == "P" ? 1u : 2u) + record,
                      "branch lost its role-specific result prefix");
              for (Region &arm : branch.getArms()) {
                require(arm.front().getNumArguments() == 4 + record + proof,
                        "arm formals differ from actual capture rows");
                require(isa<pir::ProtocolYieldOp>(arm.front().back()),
                        "codec replaced an existing arm yield");
              }
            }
          });
  cases.run("entirely event-free branches still capture Record and proof", [&] {
    Options options;
    options.thenMessages = 0;
    Fixture fixture(context, options);
    auto candidate = copy(*fixture.source);
    auto codec = fixture.construct(*candidate);
    fixture.check(*candidate, codec);
  });
  cases.run(
      "variant payload precedes original captures and codec captures", [&] {
        Options options;
        options.thenMessages = 0;
        Fixture fixture(context, options);
        fixture.variant(2, true);
        auto candidate = copy(*fixture.source);
        auto codec = fixture.construct(*candidate);
        fixture.check(*candidate, codec);
        auto branch =
            cast<pir::ParticipantBranchOp>(site(*candidate, "choose_0", "V"));
        auto &arm = branch.getArms()[1].front();
        require(arm.getNumArguments() == 7 &&
                    arm.back().getOperand(0) == arm.getArgument(0) &&
                    arm.back().getOperands().back() == arm.getArgument(5),
                "payload or Record row moved across captures");
        arm.back().setOperand(0, arm.getArgument(1));
        auto error = fixture.read(*candidate, codec);
        require(bool(error), "same-typed capture replaced selected payload");
        require(namesIdentifier(toString(std::move(error)),
                                "native-codec-correspondence"),
                "wrong payload correspondence refusal");
      });
  cases.run(
      "existing replica captures and outputs keep their actual positions", [&] {
        Fixture fixture(context);
        fixture.function(
            "replica", {fixture.index, fixture.index}, {fixture.index},
            [&](auto &c, ValueRange args) { c.returned(args.take_back(1)); });
        for (StringRef role : {"P", "V"}) {
          auto branch = cast<pir::ParticipantBranchOp>(
              site(*fixture.source, "choose_0", role));
          auto &builder = fixture.builder;
          builder.setInsertionPoint(branch);
          auto replica = pir::LocalCallOp::create(
              builder, branch.getLoc(), TypeRange{fixture.index},
              branch.getInputs().slice(1, 2), fixture.ref("replica"),
              builder.getStringAttr(("replica_" + role).str()),
              builder.getStringAttr(role));
          SmallVector<Value> inputs(branch.getInputs());
          inputs.insert(inputs.begin() + 4, replica.getResult(0));
          SmallVector<Type> outputs(branch.getResultTypes());
          outputs.insert(outputs.end() - 1, fixture.index);
          OperationState state(branch.getLoc(), branch->getName());
          state.addOperands(inputs);
          state.addTypes(outputs);
          state.addAttributes(branch->getAttrs());
          for (unsigned i = 0; i < branch.getNumRegions(); ++i)
            state.addRegion();
          auto replacement =
              cast<pir::ParticipantBranchOp>(builder.create(state));
          for (auto [before, after] :
               zip(branch.getArms(), replacement.getArms())) {
            after.takeBody(before);
            auto &body = after.front();
            Value captured =
                body.insertArgument(3, fixture.index, branch.getLoc());
            body.back().insertOperands(body.back().getNumOperands() - 1,
                                       ValueRange{captured});
          }
          for (unsigned i = 0; i < branch.getNumResults(); ++i)
            branch.getResult(i).replaceAllUsesWith(replacement.getResult(
                i + unsigned(i + 1 == branch.getNumResults())));
          branch.erase();
        }
        auto p =
            SymbolTable(unit(*fixture.source)).lookup<pir::ParticipantOp>("P");
        auto v =
            SymbolTable(unit(*fixture.source)).lookup<pir::ParticipantOp>("V");
        auto actions =
            fixture.actions(p.getBody().front(), v.getBody().front());
        auto projection = *unit(*fixture.source)
                               .getBody()
                               .front()
                               .getOps<pir::ProjectionOp>()
                               .begin();
        NamedAttrList interface(
            cast<DictionaryAttr>(projection.getInterfaces()[0]));
        NamedAttrList construction(
            cast<DictionaryAttr>(interface.get("construction")));
        construction.set("actions", actions);
        interface.set("actions", actions);
        interface.set("construction", construction.getDictionary(&context));
        projection.setInterfacesAttr(
            fixture.builder.getArrayAttr({interface.getDictionary(&context)}));
        auto candidate = copy(*fixture.source);
        auto codec = fixture.construct(*candidate);
        fixture.check(*candidate, codec);
        auto actual =
            cast<pir::ParticipantBranchOp>(site(*candidate, "choose_0", "V"));
        require(actual.getNumOperands() == 8 && actual.getNumResults() == 4,
                "codec did not preserve the pre-existing replica rows");
      });
  cases.run("codec structurally traverses 512 event-free variant arms", [&] {
    Options options;
    options.thenMessages = 0;
    Fixture fixture(context, options);
    fixture.variant(512, false);
    auto candidate = copy(*fixture.source);
    auto codec = fixture.construct(*candidate);
    fixture.check(*candidate, codec);
  });
  cases.run(
      "nested loops and branches preserve existing transcript captures", [&] {
        Options options;
        options.nesting = 2;
        Fixture fixture(context, options);
        auto candidate = copy(*fixture.source);
        auto codec = fixture.construct(*candidate);
        fixture.check(*candidate, codec);
        auto loop = cast<pir::ProtocolLoopOp>(site(*candidate, "loop_2", "V"));
        require(loop.getCarried() == 2 && loop.getNumOperands() == 7,
                "nested loop lost Record carry or proof capture");
      });
  for (bool empty : {false, true})
    cases.run(
        empty ? "zero Record conditional completion" : "conditional completion",
        [&] {
          Options options;
          options.zeroRecord = empty;
          options.completion = true;
          Fixture fixture(context, options);
          auto candidate = copy(*fixture.source);
          auto codec = fixture.construct(*candidate);
          fixture.check(*candidate, codec);
          auto execution =
              take(protocol::readSourceExecutionClosure(unit(*candidate)));
          for (unsigned slot : {7u, 8u}) {
            const auto &steps =
                execution.bodies.at(codec[slot].getAsString()->str());
            require(steps.size() == 2 && steps.front().regions.size() == 2,
                    "conditional finalizer has extra effects");
            auto taken = steps.front().regions[0],
                 continued = steps.front().regions[1];
            require(
                isa<func::CallOp>(execution.bodies.at(taken.getSymName().str())
                                      .front()
                                      .operation),
                "taken completion did not invoke the actual finalizer");
            for (const auto &step :
                 execution.bodies.at(continued.getSymName().str()))
              require(!isa<func::CallOp>(step.operation),
                      "false continuation invoked a finalizer");
          }
          for (StringRef role : {"P", "V"}) {
            auto completion = cast<pir::FinishIfOp>(
                site(*candidate, ("complete_" + role).str(), role));
            auto before = dyn_cast<pir::LocalCallOp>(completion->getPrevNode());
            require(before &&
                        before.getInputs().front() == completion.getCondition(),
                    "conditional finalizer is not at the actual completion");
            require(
                isa<pir::ProtocolYieldOp>(completion->getNextNode()),
                "codec inserted finalization or a synthetic yield at arm end");
            if (!empty) {
              auto yielded =
                  cast<pir::ProtocolYieldOp>(completion->getNextNode());
              require(yielded.getInputs().back() == before.getInputs()[1],
                      "false continuation changed the current Record");
            }
          }
        });
  cases.run(
      "dynamic stop remains before finalization without a fabricated arm exit",
      [&] {
        Options options;
        options.stop = true;
        Fixture fixture(context, options);
        auto candidate = copy(*fixture.source);
        auto codec = fixture.construct(*candidate);
        fixture.check(*candidate, codec);
        for (StringRef role : {"P", "V"})
          require(isa<pir::ProtocolYieldOp>(
                      site(*candidate, ("stop_" + role).str(), role)
                          ->getNextNode()),
                  "dynamic stop acquired an extra finalization");
      });
  for (StringRef mutation :
       {"proof capture", "record capture", "incoming yield",
        "same-typed captures", "selector", "arm successor"})
    cases.run("independent correspondence rejects " + mutation, [&] {
      Fixture fixture(context);
      auto candidate = copy(*fixture.source);
      auto codec = fixture.construct(*candidate);
      fixture.check(*candidate, codec);
      auto branch =
          cast<pir::ParticipantBranchOp>(site(*candidate, "choose_0", "V"));
      auto &arm = branch.getArms().front().front();
      auto yield = cast<pir::ProtocolYieldOp>(arm.back());
      if (mutation == "proof capture")
        branch->setOperand(6, branch.getInputs()[5]);
      else if (mutation == "record capture")
        branch->setOperand(5, branch.getInputs()[6]);
      else if (mutation == "incoming yield")
        yield->setOperand(yield.getNumOperands() - 1, arm.getArgument(4));
      else if (mutation == "same-typed captures") {
        Value x = branch.getInputs()[1], y = branch.getInputs()[2];
        branch->setOperand(1, y);
        branch->setOperand(2, x);
      } else if (mutation == "selector")
        branch->setOperand(0, branch.getInputs()[3]);
      else
        yield->setOperand(1, arm.getArgument(0));
      require(succeeded(admitStage(*candidate)),
              "mutation must remain independently formed");
      auto error = fixture.read(*candidate, codec);
      require(bool(error), "checker accepted a same-typed SSA substitution");
      require(namesIdentifier(toString(std::move(error)),
                              "native-codec-correspondence"),
              "mutation failed outside correspondence checking");
    });
  cases.run(
      "conditional helper arm swap changes exact completion outcomes", [&] {
        Options options;
        options.completion = true;
        Fixture fixture(context, options);
        auto candidate = copy(*fixture.source);
        auto codec = fixture.construct(*candidate);
        fixture.check(*candidate, codec);
        auto execution =
            take(protocol::readSourceExecutionClosure(unit(*candidate)));
        auto name = codec[7].getAsString()->str();
        const auto &branch = execution.bodies.at(name).front();
        auto first = FlatSymbolRefAttr::get(branch.regions[0]);
        auto second = FlatSymbolRefAttr::get(branch.regions[1]);
        auto function =
            SymbolTable(unit(*candidate)).lookup<func::FuncOp>(name);
        function.walk([&](func::CallOp call) {
          if (call.getCalleeAttr() == first)
            call.setCalleeAttr(second);
          else if (call.getCalleeAttr() == second)
            call.setCalleeAttr(first);
        });
        require(succeeded(admitStage(*candidate)),
                "swapped helper is still formed");
        auto error = fixture.read(*candidate, codec);
        require(bool(error), "checker accepted swapped completion outcomes");
        require(namesIdentifier(toString(std::move(error)),
                                "native-codec-correspondence"),
                "wrong conditional helper refusal");
      });
  cases.run("message group cannot be split across arms", [&] {
    Options options;
    options.thenMessages = options.elseMessages = 1;
    Fixture fixture(context, options);
    // Give the combined rule valid two-leaf signatures, so the structural
    // boundary, rather than an unrelated handler type mismatch, is tested.
    fixture.function(
        "encode_pair", {fixture.bytes, fixture.index, fixture.index},
        {fixture.bytes, fixture.bytes},
        [&](auto &c, ValueRange args) { c.returned({args[0], args[0]}); });
    fixture.function("decode_pair", {fixture.bytes},
                     {fixture.index, fixture.index}, [&](auto &c, ValueRange) {
                       Value zero = fixture.kernel(
                           c, "zero", fixture.index,
                           {fixture.builder.getIntegerAttr(fixture.index, 0)});
                       c.returned({zero, zero});
                     });
    fixture.plan.rules.erase(fixture.plan.rules.begin() + 4,
                             fixture.plan.rules.end());
    for (auto &rule : fixture.plan.rules) {
      rule.sites = {"then0", "else0"};
      rule.payload = {fixture.index, fixture.index};
      if (rule.kind == protocol::ConstructionRule::Kind::Encode)
        rule.handler = fixture.ref("encode_pair");
      if (rule.kind == protocol::ConstructionRule::Kind::Decode)
        rule.handler = fixture.ref("decode_pair");
    }
    auto candidate = copy(*fixture.source);
    refuses(zkc::detail::constructNativeCodec(*candidate, fixture.policy,
                                              fixture.plan, fixture.events,
                                              fixture.transcript),
            "native-proof-codec-group");
  });
  cases.run("a single-leaf observer cannot cross a stopping call", [&] {
    Options options;
    options.thenMessages = 1;
    options.stop = true;
    Fixture fixture(context, options);
    auto candidate = copy(*fixture.source);
    auto *observation = site(*candidate, "observe_then0_P", "P");
    observation->moveAfter(site(*candidate, "stop_P", "P"));
    refuses(zkc::detail::constructNativeCodec(*candidate, fixture.policy,
                                              fixture.plan, fixture.events,
                                              fixture.transcript),
            "native-proof-codec-group");
  });
  cases.run("wide codec input layouts use bounded role-local indexes", [&] {
    Fixture fixture(context);
    SmallVector<unsigned> selected;
    for (unsigned i = 512; i != 1536; ++i)
      selected.push_back(i);
    fixture.inputLayout(1536, selected);
    require(succeeded(admitStage(*fixture.source)),
            "wide layout must retain a valid original interface");
    auto candidate = copy(*fixture.source);
    auto codec = fixture.construct(*candidate);
    // Linear searches would perform 2,098,176 comparisons for these two
    // participants. A single charged index per role must still accept them.
    fixture.check(*candidate, codec);
    for (StringRef role : {"P", "V"}) {
      auto participant =
          SymbolTable(unit(*candidate)).lookup<pir::ParticipantOp>(role);
      auto initialized = dyn_cast<pir::LocalCallOp>(
          site(*candidate, ("root_" + role).str(), role)->getNextNode());
      require(initialized &&
                  initialized.getCalleeAttr() == fixture.ref("initialize") &&
                  initialized.getNumOperands() == selected.size(),
              "wide layout lost its initializer");
      for (auto [position, input] : enumerate(selected))
        require(initialized.getInputs()[position] ==
                    participant.getBody().front().getArgument(input),
                "wide layout changed original port identity or order");
    }
  });
  cases.run("codec layout identities differ from role-local positions", [&] {
    Fixture fixture(context);
    fixture.inputLayout(12, {6, 9, 11}, true);
    require(succeeded(admitStage(*fixture.source)),
            "private input must have a valid original interface");
    auto candidate = copy(*fixture.source);
    auto codec = fixture.construct(*candidate);
    fixture.check(*candidate, codec);
    for (StringRef role : {"P", "V"}) {
      auto participant =
          SymbolTable(unit(*candidate)).lookup<pir::ParticipantOp>(role);
      auto initialized = dyn_cast<pir::LocalCallOp>(
          site(*candidate, ("root_" + role).str(), role)->getNextNode());
      require(initialized &&
                  initialized.getCalleeAttr() == fixture.ref("initialize"),
              "role-local layout lost its initializer");
      for (auto [position, input] : enumerate(fixture.plan.codec->inputs))
        require(initialized.getInputs()[position] ==
                    participant.getBody().front().getArgument(
                        input - unsigned(role == "V")),
                "codec confused a shared identity with a local position");
    }
    auto initialized =
        cast<pir::LocalCallOp>(site(*candidate, "root_V", "V")->getNextNode());
    Value first = initialized.getInputs()[0];
    initialized->setOperand(0, initialized.getInputs()[1]);
    initialized->setOperand(1, first);
    require(succeeded(admitStage(*candidate)),
            "same-typed layout substitution must remain independently formed");
    auto error = fixture.read(*candidate, codec);
    require(bool(error), "reader accepted reordered original input identities");
    require(namesIdentifier(toString(std::move(error)),
                            "native-codec-correspondence"),
            "wrong layout identity refusal");
  });
  cases.run(
      "codec refuses a port absent from the actual role transactionally", [&] {
        Fixture fixture(context);
        fixture.inputLayout(12, {4}, true);
        require(
            succeeded(admitStage(*fixture.source)),
            "missing shared port must not invalidate the original interface");
        auto candidate = copy(*fixture.source);
        auto before = copy(*candidate);
        Operation *first = &unit(*candidate).getBody().front().front();
        refuses(zkc::detail::constructNativeCodec(*candidate, fixture.policy,
                                                  fixture.plan, fixture.events,
                                                  fixture.transcript),
                "native-proof-codec-layout");
        unchanged(*candidate, *before, first);
      });
  for (bool reading : {false, true})
    cases.run(
        reading ? "reader charges role indexes cumulatively after preflight"
                : "producer charges role indexes cumulatively after preflight",
        [&] {
          Options options;
          options.thenMessages = 0;
          Fixture fixture(context, options);
          fixture.inputLayout(2048, {2000, 2001, 2002, 2003});
          auto candidate = copy(*fixture.source);
          json::Array codec;
          if (reading) {
            codec = fixture.construct(*candidate);
            fixture.check(*candidate, codec);
          }
          // Leave room for one index, the first role's formal processing and
          // ordinary codec work. The second role must debit the same allowance;
          // without index charges these small selections fit easily.
          const uint64_t available = 2 * uint64_t(2048) + 4 + 512;
          auto fits = [&](size_t bytes) {
            fixture.plan.codec->provider.assign(bytes, 'p');
            if (reading)
              codec[0] = fixture.plan.codec->provider;
            zkc::detail::CodecCapacity capacity;
            return capacity.operation(*candidate) &&
                   (!reading || capacity.operation(*fixture.source)) &&
                   capacity.inputs(fixture.policy, fixture.plan, fixture.events,
                                   fixture.transcript) &&
                   (!reading || capacity.jsonArray(codec)) &&
                   capacity.charge(available);
          };
          size_t low = 0, high = 1000001;
          require(fits(low) && !fits(high), "invalid index capacity bracket");
          while (high - low > 1) {
            size_t middle = low + (high - low) / 2;
            if (fits(middle))
              low = middle;
            else
              high = middle;
          }
          require(fits(low), "index boundary must pass complete preflight");
          auto before = copy(*candidate);
          auto sourceBefore = copy(*fixture.source);
          Operation *first = &unit(*candidate).getBody().front().front();
          Operation *sourceFirst =
              &unit(*fixture.source).getBody().front().front();
          if (reading)
            limit(fixture.read(*candidate, codec));
          else
            refuses(zkc::detail::constructNativeCodec(
                        *candidate, fixture.policy, fixture.plan,
                        fixture.events, fixture.transcript),
                    "native-proof-codec-limit");
          unchanged(*candidate, *before, first);
          unchanged(*fixture.source, *sourceBefore, sourceFirst);
        });
  for (SmallVector<int64_t> shape :
       {SmallVector<int64_t>{4294967296LL, 4294967296LL},
        SmallVector<int64_t>{4294967296LL, 2147483648LL},
        SmallVector<int64_t>{std::numeric_limits<int64_t>::max(), 2},
        SmallVector<int64_t>{std::numeric_limits<int64_t>::max()},
        SmallVector<int64_t>{125000}, SmallVector<int64_t>{1000, 1000}})
    cases.run("codec bounds logical resource shape " + Twine(shape.front()) +
                  " through " + Twine(shape.back()) + " at rank " +
                  Twine(shape.size()),
              [&] {
                Fixture fixture(context);
                auto candidate = copy(*fixture.source);
                auto value = resource(context, shape);
                zkc::detail::CodecCapacity capacity;
                require(!capacity.attribute(value) && capacity.exhausted(),
                        "small blob hid an excessive logical element product");
                candidate->getOperation()->setAttr("capacity_fixture", value);
                auto before = copy(*candidate);
                auto sourceBefore = copy(*fixture.source);
                Operation *first = &unit(*candidate).getBody().front().front();
                Operation *sourceFirst =
                    &unit(*fixture.source).getBody().front().front();
                refuses(zkc::detail::constructNativeCodec(
                            *candidate, fixture.policy, fixture.plan,
                            fixture.events, fixture.transcript),
                        "native-proof-codec-limit");
                unchanged(*candidate, *before, first);
                limit(zkc::detail::verifyNativeCodec(
                    *fixture.source, *candidate, fixture.policy, fixture.plan,
                    fixture.events, fixture.transcript, json::Array{}));
                unchanged(*candidate, *before, first);
                unchanged(*fixture.source, *sourceBefore, sourceFirst);
                // Check the other independently preflighted subject as well.
                fixture.source->getOperation()->setAttr("capacity_fixture",
                                                        value);
                sourceBefore = copy(*fixture.source);
                limit(zkc::detail::verifyNativeCodec(
                    *fixture.source, *candidate, fixture.policy, fixture.plan,
                    fixture.events, fixture.transcript, json::Array{}));
                unchanged(*candidate, *before, first);
                unchanged(*fixture.source, *sourceBefore, sourceFirst);
              });
  for (SmallVector<int64_t> shape :
       {SmallVector<int64_t>{}, SmallVector<int64_t>{1},
        SmallVector<int64_t>{8, 16}, SmallVector<int64_t>{124000},
        SmallVector<int64_t>{0, std::numeric_limits<int64_t>::max(),
                             std::numeric_limits<int64_t>::max()},
        SmallVector<int64_t>{std::numeric_limits<int64_t>::max(), 0,
                             std::numeric_limits<int64_t>::max()},
        SmallVector<int64_t>{std::numeric_limits<int64_t>::max(),
                             std::numeric_limits<int64_t>::max(), 0}})
    cases.run("codec accepts bounded or empty resource at rank " +
                  Twine(shape.size()),
              [&] {
                zkc::detail::CodecCapacity capacity;
                require(capacity.attribute(resource(context, shape)) &&
                            !capacity.exhausted(),
                        "bounded or zero-extent resource was refused");
              });
  for (int64_t count : {int64_t(124000), int64_t(125000)})
    cases.run(
        "codec charges dense splat logical elements " + Twine(count), [&] {
          auto type = RankedTensorType::getChecked(
              [&] { return emitError(UnknownLoc::get(&context)); }, {count},
              IntegerType::get(&context, 8));
          require(bool(type), "dense fixture must have a valid tensor type");
          auto value = DenseElementsAttr::get(type, ArrayRef<uint8_t>{0});
          zkc::detail::CodecCapacity capacity;
          require(capacity.attribute(value) == (count == 124000),
                  "dense splat used physical rather than logical size");
          require(capacity.exhausted() == (count == 125000),
                  "dense logical limit did not retain its refusal");
        });
  cases.run(
      "codec charges capture and formal arrays before branch expansion", [&] {
        Options options;
        options.thenMessages = 0;
        Fixture fixture(context, options);
        auto candidate = copy(*fixture.source);
        auto branch =
            cast<pir::ParticipantBranchOp>(site(*candidate, "choose_0", "P"));
        SmallVector<Value> captures(200000, branch.getInputs()[1]);
        branch->insertOperands(branch.getNumOperands(), captures);
        for (Region &arm : branch.getArms())
          for (unsigned i = 0; i < captures.size(); ++i)
            arm.front().addArgument(fixture.index, branch.getLoc());
        refuses(zkc::detail::constructNativeCodec(*candidate, fixture.policy,
                                                  fixture.plan, fixture.events,
                                                  fixture.transcript),
                "native-proof-codec-limit");
      });
  cases.run("codec refuses structural nesting beyond 64", [&] {
    Options options;
    options.thenMessages = 0;
    options.nesting =
        33; // A branch and a loop at each level, never path expansion.
    Fixture fixture(context, options);
    auto candidate = copy(*fixture.source);
    refuses(zkc::detail::constructNativeCodec(*candidate, fixture.policy,
                                              fixture.plan, fixture.events,
                                              fixture.transcript),
            "native-proof-codec-limit");
  });
  for (StringRef field : {"string", "dictionary key", "symbol",
                          "opaque type payload", "native origin"})
    cases.run("codec preflights large native " + field, [&] {
      Fixture fixture(context);
      auto candidate = copy(*fixture.source);
      const std::string large(4 * 1024 * 1024, 'x');
      Attribute value;
      if (field == "string")
        value = fixture.builder.getStringAttr(large);
      else if (field == "dictionary key")
        value = fixture.builder.getDictionaryAttr({fixture.builder.getNamedAttr(
            large, fixture.builder.getUnitAttr())});
      else if (field == "symbol")
        value = fixture.ref(large);
      else if (field == "opaque type payload")
        value = TypeAttr::get(OpaqueType::get(
            fixture.builder.getStringAttr("capacity_test"), large));
      else
        // Native origins validate each name at construction, so use many
        // valid raw-string fields instead of manufacturing an invalid attr.
        value = fixture.builder.getArrayAttr(SmallVector<Attribute>(
            8192, runtime::StartOriginAttr::get(
                      &context, StringRef(large).take_front(128), "site")));
      // Both entry points must see the outer module, before any stage verifier
      // can diagnose this deliberately unadmitted metadata.
      candidate->getOperation()->setAttr("capacity_fixture", value);
      auto before = copy(*candidate);
      Operation *first = &unit(*candidate).getBody().front().front();
      refuses(zkc::detail::constructNativeCodec(*candidate, fixture.policy,
                                                fixture.plan, fixture.events,
                                                fixture.transcript),
              "native-proof-codec-limit");
      unchanged(*candidate, *before, first);
      limit(zkc::detail::verifyNativeCodec(
          *fixture.source, *candidate, fixture.policy, fixture.plan,
          fixture.events, fixture.transcript, json::Array{}));
      unchanged(*candidate, *before, first);
    });
  for (StringRef structure :
       {"deep attribute", "wide shared attribute", "deep type"})
    cases.run("codec bounds " + structure + " before setup", [&] {
      Fixture fixture(context);
      auto candidate = copy(*fixture.source);
      Attribute value = fixture.builder.getUnitAttr();
      if (structure == "deep attribute") {
        for (unsigned i = 0; i != 66; ++i)
          value = fixture.builder.getArrayAttr({value});
      } else if (structure == "wide shared attribute") {
        // Only a few uniqued nodes, but over a million expanded occurrences.
        for (unsigned i = 0; i != 20; ++i)
          value = fixture.builder.getArrayAttr({value, value});
      } else {
        Type type = fixture.bytes;
        for (unsigned i = 0; i != 66; ++i)
          type = TupleType::get(&context, {type});
        value = TypeAttr::get(type);
      }
      candidate->getOperation()->setAttr("capacity_fixture", value);
      auto before = copy(*candidate);
      Operation *first = &unit(*candidate).getBody().front().front();
      refuses(zkc::detail::constructNativeCodec(*candidate, fixture.policy,
                                                fixture.plan, fixture.events,
                                                fixture.transcript),
              "native-proof-codec-limit");
      unchanged(*candidate, *before, first);
      limit(zkc::detail::verifyNativeCodec(
          *fixture.source, *candidate, fixture.policy, fixture.plan,
          fixture.events, fixture.transcript, json::Array{}));
      unchanged(*candidate, *before, first);
    });
  cases.run("conditional codecPlan[7] is bounded before symbol interning", [&] {
    Options options;
    options.completion = true;
    Fixture fixture(context, options);
    auto candidate = copy(*fixture.source);
    auto codec = fixture.construct(*candidate);
    codec[7] = std::string(4 * 1024 * 1024, 'q');
    auto before = copy(*candidate);
    auto sourceBefore = copy(*fixture.source);
    Operation *first = &unit(*candidate).getBody().front().front();
    Operation *sourceFirst = &unit(*fixture.source).getBody().front().front();
    limit(zkc::detail::verifyNativeCodec(
        *fixture.source, *candidate, fixture.policy, fixture.plan,
        fixture.events, fixture.transcript, codec));
    unchanged(*candidate, *before, first);
    unchanged(*fixture.source, *sourceBefore, sourceFirst);
  });
  for (StringRef field : {"transcript string", "JSON key", "nested JSON",
                          "event origin", "rule site", "bound Record type"})
    cases.run("codec preflights " + field + " before rewriting", [&] {
      Fixture fixture(context);
      auto candidate = copy(*fixture.source);
      const std::string large(4 * 1024 * 1024, 'r');
      if (field == "transcript string")
        fixture.transcript[0] = large;
      else if (field == "JSON key")
        fixture.transcript[0] = json::Object{{large, nullptr}};
      else if (field == "nested JSON") {
        json::Value nested(nullptr);
        for (unsigned i = 0; i != 66; ++i) {
          json::Array array;
          array.push_back(std::move(nested));
          nested = std::move(array);
        }
        fixture.transcript[0] = std::move(nested);
      } else if (field == "event origin")
        fixture.events.front().origin = large;
      else if (field == "rule site")
        fixture.plan.rules.front().sites.front() = large;
      else
        fixture.plan.codec->record = {OpaqueType::get(
            fixture.builder.getStringAttr("capacity_test"), large)};
      auto before = copy(*candidate);
      Operation *first = &unit(*candidate).getBody().front().front();
      refuses(zkc::detail::constructNativeCodec(*candidate, fixture.policy,
                                                fixture.plan, fixture.events,
                                                fixture.transcript),
              "native-proof-codec-limit");
      unchanged(*candidate, *before, first);
      limit(zkc::detail::verifyNativeCodec(
          *fixture.source, *candidate, fixture.policy, fixture.plan,
          fixture.events, fixture.transcript, json::Array{}));
      unchanged(*candidate, *before, first);
    });
  cases.run("source and selected plan consume one cumulative allowance", [&] {
    Fixture fixture(context);
    auto candidate = copy(*fixture.source);
    auto codec = fixture.construct(*candidate);
    fixture.source->getOperation()->setAttr(
        "capacity_fixture",
        fixture.builder.getStringAttr(std::string(550000, 's')));
    codec[7] = std::string(550000, 't');
    zkc::detail::CodecCapacity sourceOnly, planOnly;
    require(sourceOnly.operation(*fixture.source) && planOnly.jsonArray(codec),
            "each input must fit separately to test cumulative accounting");
    auto before = copy(*candidate);
    Operation *first = &unit(*candidate).getBody().front().front();
    limit(zkc::detail::verifyNativeCodec(
        *fixture.source, *candidate, fixture.policy, fixture.plan,
        fixture.events, fixture.transcript, codec));
    unchanged(*candidate, *before, first);
  });
  cases.run("setup and generated work retain the preflight allowance", [&] {
    Fixture fixture(context);
    auto candidate = copy(*fixture.source);
    auto fits = [&](size_t bytes) {
      fixture.plan.codec->provider.assign(bytes, 'p');
      zkc::detail::CodecCapacity capacity;
      return capacity.operation(*candidate) &&
             capacity.inputs(fixture.policy, fixture.plan, fixture.events,
                             fixture.transcript);
    };
    // Leave fewer than eight units after preflight. The following construction
    // must exhaust during generated work, rather than reset its allowance.
    size_t low = 0, high = 1000001;
    require(fits(low) && !fits(high), "invalid capacity search bracket");
    while (high - low > 1) {
      size_t middle = low + (high - low) / 2;
      if (fits(middle))
        low = middle;
      else
        high = middle;
    }
    for (size_t slack : {size_t(0), size_t(128)}) {
      // The second attempt also permits slicer generation in the private
      // transaction before the later participant work exhausts the allowance.
      require(low >= slack && fits(low - slack),
              "boundary input must pass preflight");
      auto before = copy(*candidate);
      Operation *first = &unit(*candidate).getBody().front().front();
      refuses(zkc::detail::constructNativeCodec(*candidate, fixture.policy,
                                                fixture.plan, fixture.events,
                                                fixture.transcript),
              "native-proof-codec-limit");
      unchanged(*candidate, *before, first);
    }
  });
  return cases.result();
}
