#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/CommonControl.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Registry.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace {
namespace pir = protocol_ir;
std::string branch(StringRef selector, StringRef site = "choose") {
  return (Twine("\"protocol.branch\"(") + selector + R"mlir() ({
 "protocol.yield"() : ()->()
}, { "protocol.yield"() : ()->()
}) {site=")mlir" +
          site +
          R"mlir(",roles=["P","V"],output_roles=[],alternatives=["then","else"]} : (i1)->()
)mlir")
      .str();
}
std::string wrap(StringRef body, StringRef arguments = "", StringRef types = "",
                 StringRef placements = "", StringRef declarations = "") {
  return (Twine("module { \"protocol.module\"() ({\n") + declarations +
          "\"protocol.func\"() ({ ^entry(" + arguments + "):\n" + body +
          "\"protocol.return\"() : ()->()\n}) "
          "{sym_name=\"main\",function_type=(" +
          types + ")->(),roles=[\"P\",\"V\"],input_roles=[" + placements +
          "],output_roles=[]} : ()->()\n}) "
          "{profile=#protocol.profile<protocol>} : ()->() }")
      .str();
}
std::string loop(StringRef transition, unsigned count = 2,
                 StringRef after = "") {
  return wrap((Twine(R"mlir(%n = "data.index"() {value=)mlir") + Twine(count) +
               R"mlir(:ui64} : ()->ui64
%yes = arith.constant true
%no = arith.constant false
%out = "protocol.repeat"(%n,%yes,%no) ({ ^body(%i:ui64,%state:i1,%other:i1):
)mlir" + branch("%state") +
               transition + R"mlir(
}) {site="rounds",carried=1:i64,maximum=8:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,i1,i1)->i1
)mlir" + after)
                  .str());
}
OwningOpRef<ModuleOp> parse(MLIRContext &context, StringRef source) {
  auto result =
      parseSourceString<ModuleOp>(source, ParserConfig(&context, false));
  require(bool(result), "fixture syntax refused");
  return result;
}
pir::MathematicalOp program(ModuleOp module) {
  return SymbolTable(cast<pir::ProtocolModuleOp>(module.getBody()->front()))
      .lookup<pir::MathematicalOp>("main");
}
auto derive(ModuleOp module, uint64_t &remaining) {
  facts::Work work(remaining);
  return deriveCommonControlRequirements(program(module), work);
}
auto accepted(MLIRContext &context, StringRef source) {
  auto module = parse(context, source);
  require(succeeded(admitStage(*module)), "actual Protocol admission refused");
  uint64_t remaining = 1000000;
  return take(derive(*module, remaining));
}
void rejected(MLIRContext &context, StringRef source) {
  auto module = parse(context, source);
  uint64_t remaining = 1000000;
  refuses(derive(*module, remaining), "common-control-provenance");
  bool matched = false;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
    matched |= namesIdentifier(diagnostic.str(), "common-control-provenance");
    return success();
  });
  require(failed(admitStage(*module)) && matched,
          "actual Protocol admission did not reject common provenance");
}
std::string divergent() {
  return loop(
      R"mlir(%next = "protocol.assemble_roles"(%state,%other) {roles=["P","V"]} : (i1,i1)->i1
"protocol.yield"(%next) : (i1)->())mlir");
}
std::string replaceText(std::string text, StringRef from, StringRef to) {
  auto position = text.find(from.str());
  require(position != std::string::npos, "missing fixture fragment: " + from);
  text.replace(position, from.size(), to.str());
  return text;
}
void input(const CommonControlRequirement &requirement, unsigned port,
           ArrayRef<unsigned> path = {}, bool tagOnly = false,
           std::optional<unsigned> axis = {}) {
  require(requirement.components.size() == 2 &&
              requirement.components[0].input == port &&
              requirement.components[1].input == port &&
              requirement.components[0].role.getValue() == "P" &&
              requirement.components[1].role.getValue() == "V" &&
              requirement.components[0].path == path &&
              requirement.components[1].path == path &&
              requirement.tagOnly == tagOnly && requirement.extentAxis == axis,
          "exact native input observation differs");
}
std::string pure() {
  return wrap((Twine(R"mlir(%out = "protocol.repeat"(%n,%base,%step) ({
 ^body(%i:ui64,%state:i1,%delta:i1):
)mlir") + branch("%state") +
               R"mlir(%next = arith.xori %state,%delta : i1
 "protocol.yield"(%next) : (i1)->()
}) {site="rounds",carried=1:i64,maximum=8:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,i1,i1)->i1
)mlir" + branch("%out", "after"))
                  .str(),
              "%n:ui64,%base:i1,%step:i1", "ui64,i1,i1",
              "[\"P\",\"V\"],[\"P\",\"V\"],[\"P\",\"V\"]");
}
std::string cyclic(bool divergentBase, bool divergentStep = false) {
  return wrap(
      (Twine(R"mlir(%n = "data.index"() {value=3:ui64} : ()->ui64
%yes = arith.constant true
%no = arith.constant false
%base = "protocol.assemble_roles"(%yes,)mlir") +
       (divergentBase ? "%no" : "%yes") +
       R"mlir() {roles=["P","V"]} : (i1,i1)->i1
%out:2 = "protocol.repeat"(%n,%yes,%base) ({ ^body(%i:ui64,%x:i1,%y:i1):
)mlir" +
       branch("%x") +
       (divergentStep
            ? R"mlir(%bad = "protocol.assemble_roles"(%x,%y) {roles=["P","V"]} : (i1,i1)->i1
"protocol.yield"(%y,%bad) : (i1,i1)->())mlir"
            : "\"protocol.yield\"(%y,%x) : (i1,i1)->()") +
       R"mlir(
}) {site="rounds",carried=2:i64,maximum=8:i64,roles=["P","V"],carried_roles=[["P","V"],["P","V"]]} : (ui64,i1,i1)->(i1,i1)
)mlir")
          .str());
}
std::string nested(bool divergentStep) {
  return loop(
      (Twine(R"mlir(%two = "data.index"() {value=2:ui64} : ()->ui64
%inner = "protocol.repeat"(%two,%state,%other) ({ ^inner(%j:ui64,%x:i1,%fallback:i1):
)mlir") +
       branch("%x", "inner_choice") +
       (divergentStep
            ? R"mlir(%next = "protocol.assemble_roles"(%x,%fallback) {roles=["P","V"]} : (i1,i1)->i1
"protocol.yield"(%next) : (i1)->())mlir"
            : "\"protocol.yield\"(%x) : (i1)->()") +
       R"mlir(
}) {site="inner_rounds",carried=1:i64,maximum=8:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,i1,i1)->i1
"protocol.yield"(%inner) : (i1)->())mlir")
          .str());
}
constexpr StringLiteral choiceType =
    R"mlir(!Choice = !data.variant<#data.identity<["atom","RecurrenceChoice"]>, [#data.alternative<"left",[i1]>,#data.alternative<"right",[i1]>]>
)mlir";
std::string selectedObservation(bool payloadControl, bool divergentTag = false,
                                bool divergentPayload = false) {
  return (Twine(
              R"mlir(!Selected = !data.variant<#data.identity<["atom","SelectedObservation"]>, [#data.alternative<"some",[i1,i1]>,#data.alternative<"none">]>
)mlir") +
          wrap(
              (Twine(R"mlir(%yes = arith.constant true
%no = arith.constant false
%received = protocol.exchange %no {site="receive",sender="P",receiver="V"} : i1
%flag = "protocol.assemble_roles"(%yes,%received) {roles=["P","V"]} : (i1,i1)->i1
%left = "data.make"(%yes,%yes) {alternative="some"} : (i1,i1)->!Selected
)mlir") +
               (divergentTag
                    ? "%right = \"data.make\"() {alternative=\"none\"} : "
                      "()->!Selected\n"
                    : (Twine("%right = \"data.make\"(") +
                       (divergentPayload ? "%no" : "%yes") +
                       ",%no) {alternative=\"some\"} : (i1,i1)->!Selected\n")
                          .str()) +
               R"mlir(%chosen = "data.branch"(%flag,%left,%right) ({ ^then(%x:!Selected,%y:!Selected):
 "data.yield"(%x) : (!Selected)->()
}, { ^else(%x:!Selected,%y:!Selected):
 "data.yield"(%y) : (!Selected)->()
}) {alternatives=["then","else"]} : (i1,!Selected,!Selected)->!Selected
"protocol.branch"(%chosen) ({ ^some(%a:i1,%b:i1):
)mlir" + (payloadControl ? branch("%a", "payload") : "") +
               R"mlir("protocol.yield"() : ()->()
}, { "protocol.yield"() : ()->()
}) {site="match",roles=["P","V"],output_roles=[],alternatives=["some","none"]} : (!Selected)->()
)mlir")
                  .str()))
      .str();
}
std::string variant(bool payloadControl, bool divergentTag = false) {
  auto match = (Twine(R"mlir("protocol.branch"(%state) ({ ^left(%bit:i1):
)mlir") + (payloadControl ? branch("%bit", "left_bit") : "") +
                R"mlir("protocol.yield"() : ()->()
}, { ^right(%bit:i1):
)mlir" + (payloadControl ? branch("%bit", "right_bit") : "") +
                R"mlir("protocol.yield"() : ()->()
}) {site="choose",roles=["P","V"],output_roles=[],alternatives=["left","right"]} : (!Choice)->()
)mlir")
                   .str();
  return (Twine(choiceType) +
          wrap(
              (Twine(R"mlir(%n = "data.index"() {value=2:ui64} : ()->ui64
%yes = arith.constant true
%no = arith.constant false
%base = "data.make"(%yes) {alternative="left"} : (i1)->!Choice
%out = "protocol.repeat"(%n,%base,%yes,%no) ({ ^body(%i:ui64,%state:!Choice,%a:i1,%b:i1):
)mlir") + match +
               R"mlir(%payload = "protocol.assemble_roles"(%a,%b) {roles=["P","V"]} : (i1,i1)->i1
%left = "data.make"(%payload) {alternative="left"} : (i1)->!Choice
%right = "data.make"(%payload) {alternative=")mlir" +
               (divergentTag ? "right" : "left") + R"mlir("} : (i1)->!Choice
%next = "protocol.assemble_roles"(%left,%right) {roles=["P","V"]} : (!Choice,!Choice)->!Choice
"protocol.yield"(%next) : (!Choice)->()
}) {site="rounds",carried=1:i64,maximum=8:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,!Choice,i1,i1)->!Choice
)mlir")
                  .str()))
      .str();
}
std::string variantInputs(bool payloadControl) {
  auto match = (Twine(R"mlir("protocol.branch"(%state) ({ ^left(%bit:i1):
)mlir") + (payloadControl ? branch("%bit", "left_bit") : "") +
                R"mlir("protocol.yield"() : ()->()
}, { ^right(%bit:i1):
)mlir" + (payloadControl ? branch("%bit", "right_bit") : "") +
                R"mlir("protocol.yield"() : ()->()
}) {site="choose",roles=["P","V"],output_roles=[],alternatives=["left","right"]} : (!Choice)->()
)mlir")
                   .str();
  return (
             Twine(choiceType) +
             wrap((Twine(R"mlir(%n = "data.index"() {value=2:ui64} : ()->ui64
%out = "protocol.repeat"(%n,%base,%step) ({ ^body(%i:ui64,%state:!Choice,%delta:!Choice):
)mlir") + match + R"mlir("protocol.yield"(%delta) : (!Choice)->()
}) {site="rounds",carried=1:i64,maximum=8:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,!Choice,!Choice)->!Choice
)mlir")
                      .str(),
                  "%base:!Choice,%step:!Choice", "!Choice,!Choice",
                  "[\"P\",\"V\"],[\"P\",\"V\"]"))
      .str();
}
std::string extentInputs() {
  return wrap((Twine(R"mlir(%n = "data.index"() {value=2:ui64} : ()->ui64
%out = "protocol.repeat"(%n,%base,%step) ({ ^body(%i:ui64,%state:!data.bytes,%delta:!data.bytes):
%zero = "data.index"() {value=0:ui64} : ()->ui64
%size = "data.dim"(%state) {axis=0:i64} : (!data.bytes)->ui64
%bit = "data.index_less"(%zero,%size) : (ui64,ui64)->i1
)mlir") + branch("%bit") +
               R"mlir("protocol.yield"(%delta) : (!data.bytes)->()
}) {site="rounds",carried=1:i64,maximum=8:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,!data.bytes,!data.bytes)->!data.bytes
)mlir")
                  .str(),
              "%base:!data.bytes,%step:!data.bytes", "!data.bytes,!data.bytes",
              "[\"P\",\"V\"],[\"P\",\"V\"]");
}
// The two actual invocations of @inner have identical operation attributes.
// Its local recurrence deliberately compares their different dynamic clocks
// only after substitution into @main. This exercises the direct derivation;
// independent admission of @inner can already refuse its unbound outer clock.
std::string differentClocks() {
  auto inner = (Twine(R"mlir("protocol.func"() ({ ^entry(%n:ui64,%outer:ui64):
"protocol.repeat"(%n,%outer) ({ ^body(%i:ui64,%captured:ui64):
%zero = "data.index"() {value=0:ui64} : ()->ui64
%a = "data.index_equal"(%i,%zero) : (ui64,ui64)->i1
%b = "data.index_equal"(%captured,%zero) : (ui64,ui64)->i1
%bit = "protocol.assemble_roles"(%a,%b) {roles=["P","V"]} : (i1,i1)->i1
)mlir") + branch("%bit") +
                R"mlir("protocol.yield"() : ()->()
}) {site="rounds",carried=0:i64,maximum=8:i64,roles=["P","V"],carried_roles=[]} : (ui64,ui64)->()
"protocol.return"() : ()->()
}) {sym_name="inner",function_type=(ui64,ui64)->(),roles=["P","V"],input_roles=[["P","V"],["P","V"]],output_roles=[]} : ()->()
)mlir")
                   .str();
  return wrap(R"mlir(%n = "data.index"() {value=2:ui64} : ()->ui64
"protocol.repeat"(%n,%n) ({ ^body(%i:ui64,%count:ui64):
protocol.apply @inner(%count,%i) {site="first",roles=["P","V"]} : (ui64,ui64)->()
protocol.apply @inner(%count,%i) {site="second",roles=["P","V"]} : (ui64,ui64)->()
"protocol.yield"() : ()->()
}) {site="rounds",carried=0:i64,maximum=8:i64,roles=["P","V"],carried_roles=[]} : (ui64,ui64)->()
)mlir",
              "", "", "", inner);
}
std::string payloadCoordinates(bool differentAlternative) {
  auto compare =
      (Twine(
           R"mlir(%bit = "protocol.assemble_roles"(%outer,%inner) {roles=["P","V"]} : (i1,i1)->i1
)mlir") +
       branch("%bit", "payload_choice"))
          .str();
  auto inside =
      (Twine(
           R"mlir("protocol.branch"(%again,%left) ({ ^left(%inner:i1,%outer:i1):
)mlir") +
       (differentAlternative ? "" : compare) +
       R"mlir("protocol.yield"() : ()->()
}, { ^right(%inner:i1,%outer:i1):
)mlir" +
       (differentAlternative ? compare : "") +
       R"mlir("protocol.yield"() : ()->()
}) {site="inner_choice",roles=["P","V"],output_roles=[],alternatives=["left","right"]} : (!Choice,i1)->()
)mlir")
          .str();
  // bounded_at produces a genuine non-constructor variant expression, so
  // payload equality must compare its alternative as well as its ordinal.
  return (
             Twine(choiceType) +
             wrap((Twine(R"mlir(%zero = "data.index"() {value=0:ui64} : ()->ui64
%empty = "data.sequence_empty"() : ()->!data.sequence<!Choice>
%items = "data.sequence_append"(%empty,%input) : (!data.sequence<!Choice>,!Choice)->!data.sequence<!Choice>
%value = "data.bounded_at"(%items,%zero) : (!data.sequence<!Choice>,ui64)->!Choice
"protocol.branch"(%value,%value) ({ ^left(%left:i1,%again:!Choice):
)mlir") + inside + R"mlir("protocol.yield"() : ()->()
}, { ^right(%right:i1,%again:!Choice):
"protocol.yield"() : ()->()
}) {site="outer_choice",roles=["P","V"],output_roles=[],alternatives=["left","right"]} : (!Choice,!Choice)->()
)mlir")
                      .str(),
                  "%input:!Choice", "!Choice", "[\"P\",\"V\"]"))
      .str();
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("equal initializer cannot hide divergent second iteration",
            [&] { rejected(context, divergent()); });
  cases.run("pure forwarding recurrence remains common", [&] {
    require(accepted(context, loop("\"protocol.yield\"(%state) : (i1)->()"))
                .empty(),
            "static recurrence gained entry requirements");
  });
  cases.run("pure transition exports exact base and step requirements", [&] {
    auto module = parse(context, pure());
    require(succeeded(admitStage(*module)),
            "pure recurrence admission refused");
    uint64_t remaining = 1000000;
    auto requirements = take(derive(*module, remaining));
    require(requirements.size() == 3,
            "pure recurrence requirement count differs");
    for (const auto &requirement : requirements) {
      input(requirement, requirement.components[0].input);
      require(requirement.components[0].input < 3, "unexpected input port");
      require(isa<pir::RepeatOp>(requirement.control) ==
                  (requirement.components[0].input == 0),
              "requirement lost its actual establishing control");
    }
    for (unsigned port = 0; port < 3; ++port)
      require(count_if(requirements,
                       [&](const auto &r) {
                         return r.components[0].input == port;
                       }) == 1,
              "base/transition port omitted or duplicated");
  });
  cases.run(
      "repeated helper calls keep actual inputs and reversed role maps", [&] {
        auto helper =
            replaceText(pure(), "sym_name=\"main\"", "sym_name=\"helper\"");
        auto start = helper.find("\"protocol.func\"");
        auto end = helper.rfind("}) {profile=");
        require(start != std::string::npos && end != std::string::npos,
                "missing helper declaration");
        helper = helper.substr(start, end - start);
        auto requirements = accepted(
            context,
            wrap(R"mlir(
%two = "data.index"() {value=2:ui64} : ()->ui64
protocol.apply @helper(%two,%a,%b) {site="first",roles=["P","V"]} : (ui64,i1,i1)->()
protocol.apply @helper(%two,%c,%d) {site="second",roles=["V","P"]} : (ui64,i1,i1)->()
)mlir",
                 "%a:i1,%b:i1,%c:i1,%d:i1", "i1,i1,i1,i1",
                 "[\"P\",\"V\"],[\"P\",\"V\"],[\"P\",\"V\"],[\"P\",\"V\"]",
                 helper));
        require(requirements.size() == 4,
                "helper instances lost or shared obligations");
        unsigned ports = 0;
        for (const auto &requirement : requirements) {
          const auto &first = requirement.components[0];
          const auto &second = requirement.components[1];
          require(first.input < 4 && first.input == second.input &&
                      first.path.empty() && second.path.empty() &&
                      first.role.getValue() == (first.input < 2 ? "P" : "V") &&
                      second.role.getValue() == (first.input < 2 ? "V" : "P") &&
                      !requirement.tagOnly && !requirement.extentAxis,
                  "actual helper substitution changed component association");
          ports |= 1u << first.input;
        }
        require(ports == 15, "helper call input omitted");
      });
  cases.run("received transition cannot inherit its common initializer", [&] {
    rejected(
        context,
        loop(
            R"mlir(%next = protocol.exchange %state {site="receive",sender="P",receiver="V"} : i1
"protocol.yield"(%next) : (i1)->())mlir"));
  });
  cases.run("Local transition cannot inherit its common initializer", [&] {
    auto text = loop(
        R"mlir(%local = "protocol.local_call"(%state) {callee=@local,role="V",site="local"} : (i1)->i1
%next = "protocol.assemble_roles"(%state,%local) {roles=["P","V"]} : (i1,i1)->i1
"protocol.yield"(%next) : (i1)->())mlir");
    text = replaceText(text, "\"protocol.func\"", R"mlir(
func.func @local(%scope:!runtime.scope,%bit:i1)->!exec.outcome<(i1)>
 attributes {no_inline,runtime.origin=["local",[]]} {
 %done = "exec.returned"(%bit) : (i1)->!exec.outcome<(i1)>
 func.return %done : !exec.outcome<(i1)>
}
"protocol.func")mlir");
    require(accepted(context, replaceText(text, "value=2:ui64", "value=1:ui64"))
                .empty(),
            "Local fixture did not form independently of recurrence");
    rejected(context, text);
  });
  cases.run("service transition cannot inherit its common initializer", [&] {
    rejected(
        context,
        wrap(
            (Twine(R"mlir(%n = "data.index"() {value=2:ui64} : ()->ui64
%yes = arith.constant true
%out = "protocol.repeat"(%n,%yes,%service) ({ ^body(%i:ui64,%state:i1,%coins:!protocol.service_ref<"random.bls12-381.fr/0">):
)mlir") + branch("%state") +
             R"mlir(%random = "protocol.query"(%coins) {site="draw",owner="V",method="draw"} : (!protocol.service_ref<"random.bls12-381.fr/0">)->!algebra.field<"bls12-381.fr">
%bit = algebra.field_equal %random,%random : (!algebra.field<"bls12-381.fr">,!algebra.field<"bls12-381.fr">)->i1
%next = "protocol.assemble_roles"(%state,%bit) {roles=["P","V"]} : (i1,i1)->i1
"protocol.yield"(%next) : (i1)->()
}) {site="rounds",carried=1:i64,maximum=8:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,i1,!protocol.service_ref<"random.bls12-381.fr/0">)->i1
)mlir")
                .str(),
            "%service:!protocol.service_ref<\"random.bls12-381.fr/0\">",
            "!protocol.service_ref<\"random.bls12-381.fr/0\">", "[\"V\"]"));
  });
  cases.run("unknown unrelated private carry is not demanded", [&] {
    auto text = loop(
        R"mlir(%unknown = protocol.exchange %state {site="receive",sender="P",receiver="V"} : i1
"protocol.yield"(%state,%unknown) : (i1,i1)->())mlir");
    text = replaceText(text, "%out =", "%out:2 =");
    text = replaceText(text, "carried=1:i64", "carried=2:i64");
    text = replaceText(text, "carried_roles=[[\"P\",\"V\"]]",
                       "carried_roles=[[\"P\",\"V\"],[\"V\"]]");
    text = replaceText(text, ": (ui64,i1,i1)->i1", ": (ui64,i1,i1)->(i1,i1)");
    require(accepted(context, text).empty(), "unrelated state was demanded");
  });
  for (unsigned count : {0, 1}) {
    cases.run(
        Twine("body carry uses only base for count ") + Twine(count), [&] {
          require(
              accepted(
                  context,
                  replaceText(divergent(), "value=2:ui64",
                              (Twine("value=") + Twine(count) + ":ui64").str()))
                  .empty(),
              "unused transition became a body-control obligation");
        });
    cases.run(
        Twine("exit retains the actual zero/one path for count ") +
            Twine(count),
        [&] {
          auto text = loop(
              R"mlir(%next = "protocol.assemble_roles"(%state,%other) {roles=["P","V"]} : (i1,i1)->i1
"protocol.yield"(%next) : (i1)->())mlir",
              count, branch("%out", "after"));
          if (count)
            rejected(context, text);
          else
            require(accepted(context, text).empty(),
                    "zero path used a backedge");
        });
  }
  cases.run("at-most-one dynamic bound needs no transition for body control",
            [&] {
              auto text = replaceText(pure(), "maximum=8:i64", "maximum=1:i64");
              // Remove the exit demand; the body can execute only at its
              // initial carry.
              text = replaceText(text, branch("%out", "after"), "");
              auto requirements = accepted(context, text);
              require(requirements.size() == 2,
                      "one-trip body demanded a step input");
              input(requirements[0], 0);
              input(requirements[1], 1);
            });
  cases.run("tag-only recurrence permits divergent payloads", [&] {
    require(accepted(context, variant(false)).empty(), "tag demanded payload");
  });
  cases.run("payload-demanded recurrence rejects divergent payloads",
            [&] { rejected(context, variant(true)); });
  cases.run("tag-demanded recurrence rejects divergent constructor tags",
            [&] { rejected(context, variant(false, true)); });
  cases.run("tag recurrence retains no requirements for ordered payloads", [&] {
    auto text =
        replaceText(variant(false),
                    "%payload = \"protocol.assemble_roles\"(%a,%b) "
                    "{roles=[\"P\",\"V\"]} : (i1,i1)->i1",
                    "%payload = protocol.exchange %a "
                    "{site=\"receive\",sender=\"P\",receiver=\"V\"} : i1");
    require(accepted(context, text).empty(), "tag gained ordered provenance");
  });
  cases.run("guarded common payloads include statically inactive alternatives",
            [&] {
              auto text = replaceText(variant(true),
                                      "\"protocol.assemble_roles\"(%a,%b)",
                                      "\"protocol.assemble_roles\"(%a,%a)");
              require(accepted(context, text).empty(),
                      "inactive payload was treated as unknown");
            });
  for (bool payloadControl : {false, true})
    cases.run(payloadControl
                  ? "recurrence payload paths stay exact in both alternatives"
                  : "recurrence entry tags do not demand payloads",
              [&] {
                auto requirements =
                    accepted(context, variantInputs(payloadControl));
                require(requirements.size() == (payloadControl ? 6 : 2),
                        "variant recurrence observation count differs");
                for (unsigned port : {0, 1}) {
                  unsigned tags = 0, payloads = 0;
                  for (const auto &requirement : requirements)
                    if (requirement.components[0].input == port) {
                      if (requirement.tagOnly) {
                        input(requirement, port, {}, true);
                        ++tags;
                      } else {
                        auto path = requirement.components[0].path;
                        require(path.size() == 2 && path[0] < 2 && path[1] == 0,
                                "alternative or payload coordinate lost");
                        input(requirement, port, path);
                        payloads |= 1u << path[0];
                      }
                    }
                  require(tags == 1 && payloads == (payloadControl ? 3 : 0),
                          "base or transition observation omitted");
                }
              });
  cases.run("recurrence extent demands preserve the exact axis", [&] {
    auto requirements = accepted(context, extentInputs());
    require(requirements.size() == 2, "extent demanded collection contents");
    for (const auto &requirement : requirements)
      input(requirement, requirement.components[0].input, {}, false, 0);
    require(requirements[0].components[0].input !=
                requirements[1].components[0].input,
            "extent omitted either base or transition");
  });
  cases.run("nested recurrence payloads retain every projection step", [&] {
    auto text = replaceText(
        variantInputs(true), "module {",
        "!Box = !data.variant<#data.identity<[\"atom\",\"RecurrenceBox\"]>, "
        "[#data.alternative<\"box\",[!Choice]>]>\nmodule {");
    text = replaceText(text, "%base:!Choice,%step:!Choice",
                       "%base:!Box,%step:!Box");
    text = replaceText(text, "^body(%i:ui64,%state:!Choice,%delta:!Choice):",
                       "^body(%i:ui64,%state:!Box,%delta:!Box):\n%choice = "
                       "\"data.get\"(%state) {index=0:i64} : (!Box)->!Choice");
    text = replaceText(text, "\"protocol.branch\"(%state)",
                       "\"protocol.branch\"(%choice)");
    text = replaceText(text, "\"protocol.yield\"(%delta) : (!Choice)->()",
                       "\"protocol.yield\"(%delta) : (!Box)->()");
    text = replaceText(text, ": (ui64,!Choice,!Choice)->!Choice",
                       ": (ui64,!Box,!Box)->!Box");
    text = replaceText(text, "function_type=(!Choice,!Choice)",
                       "function_type=(!Box,!Box)");
    auto requirements = accepted(context, text);
    require(requirements.size() == 6, "nested projection obligation omitted");
    for (const auto &requirement : requirements) {
      auto path = requirement.components[0].path;
      require(path.size() == (requirement.tagOnly ? 2 : 4) && path[0] == 0 &&
                  path[1] == 0 &&
                  (requirement.tagOnly || (path[2] < 2 && path[3] == 0)),
              "nested alternative/payload path was truncated");
      input(requirement, requirement.components[0].input, path,
            requirement.tagOnly);
    }
  });
  cases.run("identical selected tags do not require common selection", [&] {
    require(accepted(context, selectedObservation(false)).empty(),
            "uniform tag depends on an unknown selector");
  });
  cases.run("identical selected payloads do not require common selection", [&] {
    require(accepted(context, selectedObservation(true)).empty(),
            "uniform payload depends on an unknown selector");
  });
  cases.run("distinct selected tags still require common selection",
            [&] { rejected(context, selectedObservation(false, true)); });
  cases.run("distinct selected payloads still require common selection",
            [&] { rejected(context, selectedObservation(true, false, true)); });
  cases.run("unknown identical payloads do not establish common control", [&] {
    auto text = replaceText(selectedObservation(true),
                            "(%yes,%yes) {alternative=\"some\"}",
                            "(%received,%yes) {alternative=\"some\"}");
    text = replaceText(text, "(%yes,%no) {alternative=\"some\"}",
                       "(%received,%no) {alternative=\"some\"}");
    rejected(context, text);
  });
  cases.run("protocol selection still demands a common header", [&] {
    auto text = selectedObservation(false);
    text = replaceText(text, "%chosen = \"data.branch\"",
                       branch("%flag") + "%chosen = \"data.branch\"");
    rejected(context, text);
  });
  cases.run("uniform result cannot erase its own Protocol header demand", [&] {
    auto text = replaceText(selectedObservation(false), "\"data.branch\"",
                            "\"protocol.branch\"");
    for (unsigned arm = 0; arm < 2; ++arm)
      text = replaceText(text, "\"data.yield\"", "\"protocol.yield\"");
    text = replaceText(text, "{alternatives=[\"then\",\"else\"]}",
                       "{site=\"selection\",roles=[\"P\",\"V\"],"
                       "output_roles=[[\"P\",\"V\"]],"
                       "alternatives=[\"then\",\"else\"]}");
    rejected(context, text);
  });
  cases.run("uniform selected observations retain exact work refusal", [&] {
    auto module = parse(context, selectedObservation(true));
    require(succeeded(admitStage(*module)),
            "uniform selection admission refused");
    uint64_t remaining = 1000000;
    take(derive(*module, remaining));
    uint64_t cost = 1000000 - remaining;
    for (uint64_t allowance = 0; allowance < cost; ++allowance) {
      auto available = allowance;
      refuses(derive(*module, available), "common-control-capacity");
    }
    take(derive(*module, cost));
    require(cost == 0, "exact selected-observation work boundary changed");
  });
  cases.run("selected transition preserves tags with unknown payloads", [&] {
    auto text =
        replaceText(variant(false),
                    "%payload = \"protocol.assemble_roles\"(%a,%b) "
                    "{roles=[\"P\",\"V\"]} : (i1,i1)->i1",
                    "%payload = protocol.exchange %a "
                    "{site=\"receive\",sender=\"P\",receiver=\"V\"} : i1");
    text = replaceText(
        text,
        "%next = \"protocol.assemble_roles\"(%left,%right) "
        "{roles=[\"P\",\"V\"]} : (!Choice,!Choice)->!Choice",
        R"mlir(%condition = "data.is"(%state) {alternative="left"} : (!Choice)->i1
%next = "data.branch"(%condition,%left,%right) ({ ^then(%x:!Choice,%y:!Choice):
 "data.yield"(%x) : (!Choice)->()
}, { ^else(%x:!Choice,%y:!Choice):
 "data.yield"(%y) : (!Choice)->()
}) {alternatives=["then","else"]} : (i1,!Choice,!Choice)->!Choice)mlir");
    require(accepted(context, text).empty(),
            "selected tag demanded unknown payload");
  });
  cases.run(
      "zero-trip dormant body still refuses direct received control", [&] {
        auto text = loop("\"protocol.yield\"(%state) : (i1)->()", 0);
        text = replaceText(
            text, branch("%state"),
            (Twine("%received = protocol.exchange %state "
                   "{site=\"receive\",sender=\"P\",receiver=\"V\"} : i1\n") +
             branch("%received"))
                .str());
        rejected(context, text);
      });
  cases.run("identical loop attributes cannot identify distinct dynamic clocks",
            [&] { rejected(context, differentClocks()); });
  cases.run("same alternative and ordinal preserve generic payload agreement",
            [&] {
              require(!accepted(context, payloadCoordinates(false)).empty(),
                      "generic payload lost its entry dependency");
            });
  cases.run("equal payload ordinals cannot collapse different alternatives",
            [&] { rejected(context, payloadCoordinates(true)); });
  cases.run(
      "actual yielded candidate mutation invalidates the recurrence", [&] {
        auto module =
            parse(context, loop("\"protocol.yield\"(%state) : (i1)->()"));
        require(succeeded(admitStage(*module)), "original candidate refused");
        pir::RepeatOp repeat;
        program(*module).walk([&](pir::RepeatOp op) { repeat = op; });
        auto &body = repeat.getBody().front();
        OpBuilder builder(&body.back());
        OperationState state(repeat.getLoc(), "protocol.assemble_roles");
        state.addOperands({body.getArgument(1), body.getArgument(2)});
        state.addTypes(builder.getI1Type());
        state.addAttribute("roles", builder.getStrArrayAttr({"P", "V"}));
        auto *assembly = builder.create(state);
        body.back().setOperand(0, assembly->getResult(0));
        uint64_t remaining = 1000000;
        refuses(derive(*module, remaining), "common-control-provenance");
        bool matched = false;
        ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
          matched |=
              namesIdentifier(diagnostic.str(), "common-control-provenance");
          return success();
        });
        require(failed(admitStage(*module)) && matched,
                "mutated actual candidate reused old provenance");
      });
  cases.run("simultaneous induction accepts grounded mutually recursive slots",
            [&] {
              require(accepted(context, cyclic(false)).empty(),
                      "safe cyclic swap refused");
            });
  cases.run("cyclic hypotheses cannot hide a divergent base in another slot",
            [&] { rejected(context, cyclic(true)); });
  cases.run("cyclic hypotheses cannot hide a divergent step", [&] {
    auto text =
        replaceText(cyclic(false, true), "(%n,%yes,%base)", "(%n,%yes,%no)");
    rejected(context, text);
  });
  cases.run("nested grounded induction remains common", [&] {
    require(accepted(context, nested(false)).empty(),
            "safe nested recurrence refused");
  });
  cases.run("inner recurrence cannot hide an enclosing demanded transition",
            [&] { rejected(context, nested(true)); });
  cases.run("every insufficient recurrence work allowance refuses exactly",
            [&] {
              auto module = parse(context, pure());
              require(succeeded(admitStage(*module)),
                      "capacity fixture admission refused");
              uint64_t remaining = 1000000;
              take(derive(*module, remaining));
              uint64_t cost = 1000000 - remaining;
              uint64_t exact = cost;
              take(derive(*module, exact));
              require(exact == 0, "exact work boundary changed");
              for (uint64_t allowance = 0; allowance < cost; ++allowance) {
                uint64_t limited = allowance;
                refuses(derive(*module, limited), "common-control-capacity");
              }
            });
  return cases.result();
}
