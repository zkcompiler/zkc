#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace pir = protocol_ir;
namespace {
// Independent metadata fixtures: original actions are authored separately from
// the actual candidate operations, including helpers reached only in arms.
// These test metadata admission, not proof/codec source correspondence.
struct Fixture {
  MLIRContext &context;
  OpBuilder builder;
  OwningOpRef<ModuleOp> module;
  unsigned armCount;
  bool populated, variant;
  Type selector;
  ArrayAttr labels;

  DictionaryAttr fields(std::initializer_list<NamedAttribute> values) {
    return builder.getDictionaryAttr(ArrayRef<NamedAttribute>(values));
  }
  NamedAttribute field(StringRef name, Attribute value) {
    return builder.getNamedAttr(name, value);
  }
  StringAttr str(StringRef text) { return builder.getStringAttr(text); }
  FlatSymbolRefAttr ref(StringRef text) {
    return FlatSymbolRefAttr::get(&context, text);
  }
  pir::ProtocolModuleOp unit() {
    return cast<pir::ProtocolModuleOp>(module->getBody()->front());
  }
  pir::ProjectionOp projection() {
    return *unit().getBody().front().getOps<pir::ProjectionOp>().begin();
  }
  DictionaryAttr interface() {
    return cast<DictionaryAttr>(projection().getInterfaces()[0]);
  }
  DictionaryAttr construction() {
    return interface().getAs<DictionaryAttr>("construction");
  }
  void setInterface(DictionaryAttr value) {
    projection().setInterfacesAttr(builder.getArrayAttr({value}));
  }
  DictionaryAttr set(DictionaryAttr value, StringRef name, Attribute attr) {
    NamedAttrList updated(value);
    updated.set(name, attr);
    return updated.getDictionary(&context);
  }
  ArrayAttr replace(ArrayAttr values, unsigned index, Attribute value) {
    SmallVector<Attribute> updated(values.getValue());
    updated[index] = value;
    return builder.getArrayAttr(updated);
  }
  void setConstruction(StringRef key, Attribute value) {
    setInterface(
        set(interface(), "construction", set(construction(), key, value)));
  }
  ArrayAttr actions(bool source = false) {
    return (source ? interface() : construction()).getAs<ArrayAttr>("actions");
  }
  void setActions(ArrayAttr value, bool source = false) {
    if (source)
      setInterface(set(interface(), "actions", value));
    else
      setConstruction("actions", value);
  }
  ArrayAttr arms(bool source = false) {
    return cast<DictionaryAttr>(actions(source)[0]).getAs<ArrayAttr>("arms");
  }
  ArrayAttr body(unsigned arm, bool source = false) {
    return cast<DictionaryAttr>(arms(source)[arm]).getAs<ArrayAttr>("body");
  }
  void setArms(ArrayAttr value, bool source = false) {
    setActions(
        replace(actions(source), 0,
                set(cast<DictionaryAttr>(actions(source)[0]), "arms", value)),
        source);
  }
  void setBody(unsigned arm, ArrayAttr value, bool source = false) {
    setArms(
        replace(arms(source), arm,
                set(cast<DictionaryAttr>(arms(source)[arm]), "body", value)),
        source);
  }
  ArrayAttr targets(StringRef operation, StringRef role = {}) {
    SmallVector<Attribute> result;
    for (StringRef owner : {"P", "V"})
      if (role.empty() || role == owner)
        result.push_back(fields({field("participant", ref(owner)),
                                 field("operation", str(operation))}));
    return builder.getArrayAttr(result);
  }
  DictionaryAttr call(StringRef site, StringRef callee, StringRef role) {
    return fields({field("site", str(site)),
                   field("kind", str("protocol.local_call")),
                   field("targets", targets("protocol.local_call", role)),
                   field("callee", ref(callee))});
  }
  ArrayAttr sequence(unsigned depth, bool source) {
    SmallVector<Attribute> arms;
    for (unsigned i = 0; i < armCount; ++i) {
      SmallVector<Attribute> body;
      if (depth && i == 0) {
        auto loop = fields({field("site", str("loop" + std::to_string(depth))),
                            field("kind", str("protocol.repeat")),
                            field("targets", targets("protocol.loop")),
                            field("maximum", builder.getI64IntegerAttr(1)),
                            field("body", sequence(depth - 1, source))});
        body.push_back(loop);
      } else if (!depth && populated) {
        auto append = [&](StringRef prefix, StringRef callee) {
          for (StringRef role : {"P", "V"})
            body.push_back(
                call((prefix + Twine(i) + role).str(), callee, role));
        };
        append("keep", "authored");
        if (!source) {
          append("insert", "helper" + std::to_string(i));
          append("replica", "authored");
        }
        append("tail", "authored");
      }
      arms.push_back(fields({field("alternative", labels[i]),
                             field("body", builder.getArrayAttr(body))}));
    }
    return builder.getArrayAttr(
        {fields({field("site", str("choose" + std::to_string(depth))),
                 field("kind", str("protocol.branch")),
                 field("targets", targets("protocol.participant_branch")),
                 field("arms", builder.getArrayAttr(arms))})});
  }
  Operation *operation(StringRef name, ValueRange inputs, TypeRange outputs,
                       ArrayRef<NamedAttribute> attributes = {},
                       unsigned regions = 0) {
    OperationState state(builder.getUnknownLoc(), name);
    state.addOperands(inputs);
    state.addTypes(outputs);
    state.addAttributes(attributes);
    for (unsigned i = 0; i < regions; ++i)
      state.addRegion();
    return builder.create(state);
  }
  Value branch(Value choice, Value captured, StringRef role, unsigned depth) {
    auto *selected =
        operation("protocol.participant_branch", {choice, choice, captured},
                  {builder.getI1Type()},
                  {field("site", str("choose" + std::to_string(depth))),
                   field("alternatives", labels)},
                  armCount);
    for (unsigned i = 0; i < armCount; ++i) {
      auto *block = new Block;
      selected->getRegion(i).push_back(block);
      // The final variant alternative has a payload before the captures.
      if (variant && i + 1 == armCount)
        block->addArgument(builder.getIntegerType(64, false),
                           selected->getLoc());
      Value localChoice = block->addArgument(selector, selected->getLoc());
      Value local = block->addArgument(builder.getI1Type(), selected->getLoc());
      builder.setInsertionPointToEnd(block);
      if (depth && i == 0) {
        auto index = builder.getIntegerType(64, false);
        Value count =
            operation("data.index", {}, {index},
                      {field("value", builder.getIntegerAttr(index, 1))})
                ->getResult(0);
        auto *loop = operation(
            "protocol.loop", {count, local, localChoice}, {builder.getI1Type()},
            {field("site", str("loop" + std::to_string(depth))),
             field("carried", builder.getI64IntegerAttr(1)),
             field("count", str("")),
             field("parameter", builder.getBoolAttr(false)),
             field("maximum", builder.getI64IntegerAttr(1))},
            1);
        auto *body = new Block;
        loop->getRegion(0).push_back(body);
        body->addArgument(index, loop->getLoc());
        Value carried = body->addArgument(builder.getI1Type(), loop->getLoc());
        Value invariant = body->addArgument(selector, loop->getLoc());
        builder.setInsertionPointToEnd(body);
        Value result = branch(invariant, carried, role, depth - 1);
        operation("protocol.yield", {result}, {});
        builder.setInsertionPointAfter(loop);
        local = loop->getResult(0);
      } else if (!depth && populated) {
        for (StringRef prefix : {"keep", "insert", "replica", "tail"})
          operation("protocol.local_call", {}, {},
                    {field("site", str((prefix + Twine(i) + role).str())),
                     field("role", str(role)),
                     field("callee",
                           ref(prefix == "insert" ? "helper" + std::to_string(i)
                                                  : "authored"))});
      }
      operation("protocol.yield", {local}, {});
    }
    builder.setInsertionPointAfter(selected);
    return selected->getResult(0);
  }
  Fixture(MLIRContext &context, unsigned count = 2, bool populated = true,
          unsigned nesting = 0, bool variant = false)
      : context(context), builder(&context), armCount(count),
        populated(populated), variant(variant) {
    module = parseSourceString<ModuleOp>(R"mlir(module {
      "protocol.module"() ({
        func.func private @authored(%scope: !runtime.scope) -> !exec.outcome<> attributes {no_inline,runtime.origin=["authored",[]]} {
          %r = "exec.returned"() : ()->!exec.outcome<>
          func.return %r : !exec.outcome<>
        }
        "protocol.entry"() {sym_name="main",targets=[["P",@P],["V",@V]]} : ()->()
        "protocol.projection"() {calculations=[],interfaces=[{
          source="main",entry=@main,
          original_type=(i1,i1,!protocol.service_ref<"random.bls12-381.fr/0">)->i1,
          roles=["P","V"],input_roles=[["P","V"],["P","V"],["V"]],output_roles=[["P","V"]],statements=[],actions=[],
          participants=[{participant=@P,role="P",inputs=[0:i64,1:i64],service_inputs=[],outputs=[0:i64]},
            {participant=@V,role="V",inputs=[0:i64,1:i64],service_inputs=[2:i64],outputs=[0:i64]}],
          construction={format="zkc.native-construction/0",state=[],root="local",plan="fixture",helpers=[],removed_services=[2:i64],actions=[]}
        }]} : ()->()
      }) {profile=#protocol.profile<participant>} : ()->()
    })mlir",
                                         ParserConfig(&context, false));
    require(bool(module), "could not parse projection fixture");
    SmallVector<Attribute> names;
    SmallVector<data::AlternativeAttr> alternatives;
    for (unsigned i = 0; i < count; ++i) {
      auto name =
          str(variant ? "arm" + std::to_string(i) : (i == 0 ? "then" : "else"));
      names.push_back(name);
      SmallVector<Type> payload;
      if (variant && i + 1 == count)
        payload.push_back(builder.getIntegerType(64, false));
      alternatives.push_back(
          data::AlternativeAttr::get(&context, name, payload));
    }
    labels = builder.getArrayAttr(names);
    selector = builder.getI1Type();
    if (variant)
      selector = data::VariantType::get(
          &context,
          data::importVariantIdentity(
              &context, protocol::VariantIdentity("ProjectionChoice")),
          alternatives);
    auto original = cast<FunctionType>(
        interface().getAs<TypeAttr>("original_type").getValue());
    setInterface(set(interface(), "original_type",
                     TypeAttr::get(builder.getFunctionType(
                         {selector, builder.getI1Type(), original.getInput(2)},
                         original.getResults()))));
    auto authored = SymbolTable(unit()).lookup<func::FuncOp>("authored");
    SmallVector<Attribute> helpers;
    for (unsigned i = 0; i < (populated ? count : 0) + 1; ++i) {
      auto *clone = authored->clone();
      auto name =
          i == count || !populated ? "unused" : "helper" + std::to_string(i);
      SymbolTable::setSymbolName(clone, name);
      clone->setAttr(
          "runtime.origin",
          builder.getArrayAttr({str(name), builder.getArrayAttr({})}));
      unit().getBody().front().push_back(clone);
      if (name != "unused")
        helpers.push_back(ref(name));
    }
    for (StringRef role : {"P", "V"}) {
      builder.setInsertionPointToEnd(&unit().getBody().front());
      auto type = builder.getFunctionType({selector, builder.getI1Type()},
                                          {builder.getI1Type()});
      auto *participant =
          operation("protocol.participant", {}, {},
                    {field("sym_name", str(role)), field("role", str(role)),
                     field("instance", str("main")),
                     field("function_type", TypeAttr::get(type))},
                    1);
      auto *block = new Block;
      participant->getRegion(0).push_back(block);
      Value choice = block->addArgument(selector, participant->getLoc());
      Value captured =
          block->addArgument(builder.getI1Type(), participant->getLoc());
      builder.setInsertionPointToEnd(block);
      Value result = branch(choice, captured, role, nesting);
      operation("protocol.finish", {result}, {});
    }
    setActions(sequence(nesting, true), true);
    setActions(sequence(nesting, false));
    setConstruction("helpers", builder.getArrayAttr(helpers));
  }
  Operation *site(StringRef name, StringRef role = "P") {
    Operation *found = nullptr;
    module->walk([&](Operation *op) {
      auto owner = op->getParentOfType<pir::ParticipantOp>();
      if (owner && owner.getRole() == role && op->getAttr("site") == str(name))
        found = op;
    });
    require(found != nullptr, "missing fixture site");
    return found;
  }
  void accepts() {
    require(succeeded(admitStage(*module)), "valid projection fixture refused");
  }
  void refuses(StringRef detail = {}) {
    bool identified = false, explained = detail.empty();
    ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
      auto message = diagnostic.str();
      identified |= namesIdentifier(message, "mathematical-projection");
      explained |= StringRef(message).contains(detail);
      return success();
    });
    require(failed(mathematical::verifyProjectionMetadata(unit())) &&
                identified && explained,
            "projection mutation did not produce its expected refusal");
  }
};
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("source and inserted helpers reached only in arms", [&] {
    Fixture fixture(context);
    fixture.accepts();
  });
  cases.run("nested branch and loop metadata", [&] {
    Fixture fixture(context, 2, true, 2);
    fixture.accepts();
  });
  cases.run("event-free alternatives", [&] {
    Fixture fixture(context, 2, false);
    fixture.accepts();
  });
  for (unsigned count : {256u, 257u, 512u})
    cases.run("retained arm capacity " + Twine(count), [&] {
      Fixture fixture(context, count, false, 0, true);
      require(succeeded(verify(*fixture.module)),
              "variant must pass native formation");
      if (count == 256)
        fixture.accepts();
      else
        fixture.refuses("invalid retained selected arms");
    });
  for (bool source : {false, true})
    for (StringRef mutation :
         {"reorder", "alternative", "duplicate alternative", "missing body",
          "extra field", "empty arms"})
      cases.run(Twine(source ? "original " : "candidate ") + mutation, [&] {
        Fixture fixture(context);
        auto arms = fixture.arms(source);
        auto first = cast<DictionaryAttr>(arms[0]);
        if (mutation == "reorder")
          arms = fixture.builder.getArrayAttr({arms[1], arms[0]});
        else if (mutation == "empty arms")
          arms = fixture.builder.getArrayAttr({});
        else {
          if (mutation == "alternative")
            first = fixture.set(first, "alternative", fixture.str("forged"));
          else if (mutation == "duplicate alternative")
            first =
                fixture.set(first, "alternative",
                            cast<DictionaryAttr>(arms[1]).get("alternative"));
          else if (mutation == "missing body")
            first = fixture.fields(
                {fixture.field("alternative", first.get("alternative"))});
          else
            first = fixture.set(first, "authority", fixture.str("forged"));
          arms = fixture.replace(arms, 0, first);
        }
        fixture.setArms(arms, source);
        fixture.refuses();
      });
  for (StringRef mutation :
       {"omit", "duplicate", "reorder", "cross arm", "callee", "target"})
    cases.run("retained action " + mutation, [&] {
      Fixture fixture(context);
      SmallVector<Attribute> body(fixture.body(0).getValue());
      if (mutation == "omit")
        body.erase(body.begin());
      else if (mutation == "duplicate")
        body.insert(body.begin(), body.front());
      else if (mutation == "reorder")
        std::swap(body[0], body[1]);
      else if (mutation == "cross arm") {
        auto other = fixture.body(1);
        fixture.setBody(1, fixture.replace(other, 0, body[0]));
        body[0] = other[0];
      } else if (mutation == "callee")
        body[0] = fixture.set(cast<DictionaryAttr>(body[0]), "callee",
                              fixture.ref("unused"));
      else
        body[0] = fixture.set(cast<DictionaryAttr>(body[0]), "targets",
                              fixture.targets("protocol.local_call", "V"));
      fixture.setBody(0, fixture.builder.getArrayAttr(body));
      fixture.refuses();
    });
  for (StringRef mutation :
       {"unlisted", "unused", "duplicate", "missing occurrence",
        "changed actual callee", "cross arm operation"})
    cases.run("inserted helper " + mutation, [&] {
      Fixture fixture(context);
      if (mutation == "unlisted")
        fixture.setConstruction(
            "helpers", fixture.builder.getArrayAttr({fixture.ref("helper0")}));
      else if (mutation == "unused")
        fixture.setConstruction(
            "helpers", fixture.builder.getArrayAttr({fixture.ref("helper0"),
                                                     fixture.ref("helper1"),
                                                     fixture.ref("unused")}));
      else if (mutation == "duplicate") {
        auto body = fixture.body(0);
        auto extra = fixture.set(cast<DictionaryAttr>(body[2]), "site",
                                 fixture.str("extra"));
        SmallVector<Attribute> changed(body.getValue());
        changed.insert(changed.begin() + 3, extra);
        fixture.setBody(0, fixture.builder.getArrayAttr(changed));
        auto *call = fixture.site("insert0P");
        auto *clone = call->clone();
        clone->setAttr("site", fixture.str("extra"));
        fixture.builder.setInsertionPointAfter(call);
        fixture.builder.insert(clone);
      } else if (mutation == "missing occurrence")
        fixture.site("insert1P")->erase();
      else if (mutation == "changed actual callee")
        fixture.site("insert1P")->setAttr("callee", fixture.ref("unused"));
      else
        fixture.site("insert0P")->moveBefore(fixture.site("insert1P"));
      fixture.refuses();
    });
  cases.run("candidate metadata cannot omit an actual arm action", [&] {
    Fixture fixture(context);
    SmallVector<Attribute> body(fixture.body(0).getValue());
    // An existing-source replica is not inventoried as a new helper.
    body.erase(body.begin() + 4);
    fixture.setBody(0, fixture.builder.getArrayAttr(body));
    fixture.refuses("participant action is missing from retained occurrences");
  });
  cases.run("original actions cannot reuse a site across alternatives", [&] {
    Fixture fixture(context);
    auto original = fixture.body(0, true);
    fixture.setBody(1, fixture.replace(fixture.body(1, true), 0, original[0]),
                    true);
    fixture.refuses("invalid original construction action");
  });
  cases.run("jointly reordered labels still disagree with actual regions", [&] {
    Fixture fixture(context, 2, false);
    for (bool source : {false, true}) {
      auto arms = fixture.arms(source);
      fixture.setArms(fixture.builder.getArrayAttr({arms[1], arms[0]}), source);
    }
    fixture.refuses("selected arm identity differs");
  });
  for (StringRef mutation : {"capture", "yield"})
    cases.run("metadata grants no " + mutation + " authority", [&] {
      Fixture fixture(context);
      auto branch = cast<pir::ParticipantBranchOp>(fixture.site("choose0"));
      auto &arm = branch.getArms()[0].front();
      if (mutation == "capture")
        branch->eraseOperand(branch.getNumOperands() - 1);
      else
        arm.back().eraseOperands(0, 1);
      ScopedDiagnosticHandler handler(&context,
                                      [](Diagnostic &) { return success(); });
      require(failed(admitStage(*fixture.module)),
              "actual malformed branch was admitted from metadata");
    });
  for (bool split : {false, true})
    cases.run(
        split ? "challenge pairing cannot cross arms"
              : "removed challenges in both arms",
        [&] {
          Fixture fixture(context);
          auto query = [&](StringRef site) {
            return fixture.fields(
                {fixture.field("site", fixture.str(site)),
                 fixture.field("kind", fixture.str("protocol.query")),
                 fixture.field("targets",
                               fixture.targets("protocol.service_query", "V")),
                 fixture.field("service",
                               fixture.builder.getI64IntegerAttr(2))});
          };
          auto delivery = [&](StringRef site) {
            auto send = fixture.targets("protocol.send", "V")[0];
            auto receive = fixture.targets("protocol.receive", "P")[0];
            return fixture.fields(
                {fixture.field("site", fixture.str(site)),
                 fixture.field("kind", fixture.str("protocol.exchange")),
                 fixture.field("targets",
                               fixture.builder.getArrayAttr({send, receive}))});
          };
          for (unsigned arm = 0; arm < 2; ++arm) {
            SmallVector<Attribute> body(fixture.body(arm, true).getValue());
            if (!split || arm == 0)
              body.push_back(query("query" + std::to_string(arm)));
            if (!split || arm == 1)
              body.push_back(delivery("delivery" + std::to_string(arm)));
            fixture.setBody(arm, fixture.builder.getArrayAttr(body), true);
          }
          if (split)
            fixture.refuses("unpaired constructed challenges");
          else
            fixture.accepts();
        });
  for (unsigned count : {256u, 257u})
    cases.run("unconstructed metadata capacity " + Twine(count), [&] {
      Fixture fixture(context, count, false, 0, true);
      NamedAttrList original(fixture.interface());
      original.erase("construction");
      original.set("original_type",
                   TypeAttr::get(fixture.builder.getFunctionType(
                       {fixture.selector, fixture.builder.getI1Type()},
                       {fixture.builder.getI1Type()})));
      original.set("input_roles",
                   fixture.builder.getArrayAttr(
                       {fixture.builder.getArrayAttr(
                            {fixture.str("P"), fixture.str("V")}),
                        fixture.builder.getArrayAttr(
                            {fixture.str("P"), fixture.str("V")})}));
      auto participants = cast<ArrayAttr>(original.get("participants"));
      participants = fixture.replace(
          participants, 1,
          fixture.set(cast<DictionaryAttr>(participants[1]), "service_inputs",
                      fixture.builder.getArrayAttr({})));
      original.set("participants", participants);
      fixture.setInterface(original.getDictionary(&context));
      if (count == 256)
        fixture.accepts();
      else
        fixture.refuses("invalid retained selected arms");
    });
  cases.run("constructed arms independently enforce the retained capacity",
            [&] {
              Fixture fixture(context, 256, false, 0, true);
              SmallVector<Attribute> arms(fixture.arms().getValue());
              arms.push_back(fixture.set(cast<DictionaryAttr>(arms.back()),
                                         "alternative", fixture.str("extra")));
              fixture.setArms(fixture.builder.getArrayAttr(arms));
              fixture.refuses("invalid retained selected arms");
            });
  cases.run("metadata recursion is bounded", [&] {
    Fixture fixture(context, 2, false, 33);
    fixture.refuses("projection region depth exceeds 64");
  });
  cases.run("site-key setup consumes the work allowance", [&] {
    Fixture fixture(context);
    auto branch = cast<DictionaryAttr>(fixture.actions(true)[0]);
    branch =
        fixture.set(branch, "site", fixture.str(std::string(1000001, 'x')));
    fixture.setActions(fixture.builder.getArrayAttr({branch}), true);
    fixture.refuses("projection metadata work limit");
  });
  cases.run("actual capture environment setup consumes the work allowance",
            [&] {
              Fixture fixture(context);
              auto *branch = fixture.site("choose0");
              SmallVector<Value> captures(1000001, branch->getOperand(1));
              branch->insertOperands(branch->getNumOperands(), captures);
              fixture.refuses("projection metadata work limit");
            });
  return cases.result();
}
