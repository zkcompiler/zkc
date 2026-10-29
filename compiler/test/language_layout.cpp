#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/SourceCorrespondence.h"
#include "zkc/Language/Companions.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/MemoryBuffer.h"
#include <random>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(StringRef source, Limits limits = {}) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured = capture({{"m", source.str(), "main.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
} // namespace
int main() {
  Cases cases;
  for (StringRef source :
       {"pub protocol Demo roles(P)() -> bool @P:\n    return false\n",
        "module Helpers:\n    pub def value() -> bool:\n        false\n",
        "section <N: nat>:\n    pub def value() -> bool:\n        false\n"})
    cases.run(
        "one declaration without a module header retains its body: " + source,
        [&] {
          auto written = take(
              json::parse(take(inspectWrittenSource(take(check(source))))));
          bool body = false;
          for (const auto &owner :
               *written.getAsObject()->getArray("declarations"))
            for (const auto &node : *owner.getAsObject()->getArray("nodes"))
              body |= node.getAsObject()->getString("kind") == "expr.boolean" &&
                      node.getAsObject()->getString("text") == "false";
          require(body, "file wrapper replaced the actual written body");
        });
  for (StringRef constructor :
       {"Random", "zkc::prelude::Random", "services::Random"})
    cases.run(
        "managed service resolves its installed constructor: " + constructor,
        [&] {
          auto project = take(check((R"(use zkc::prelude as services
domain F = field("bls12-381.fr")
pub protocol Demo roles(P)(coins: )" +
                                     constructor + R"(<F> @P) -> F @P:
    value <- coins.draw()
    return value
)")
                                        .str()));
          auto declaration =
              llvm::find_if(project.declarations(), [](const auto &decl) {
                return decl.qualifiedName == "m::Demo";
              });
          require(
              declaration != project.declarations().end() &&
                  declaration->inputs.empty() &&
                  declaration->services.size() == 1,
              "service constructor did not resolve through its declaration");
        });
  cases.run("ordinary type named Random keeps its ordinary meaning", [] {
    auto project = take(check(R"(type Random = bool
pub protocol Demo roles(P)(value: Random @P) -> Random @P:
    return value
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("static binder shadows implicit managed constructor", [] {
    take(check(
        R"(pub protocol Demo<Random: Type> roles(P)(value: Random @P) -> Random @P:
    return value
)"));
  });
  cases.run(
      "spec-free layout protocol reaches independent original comparison", [] {
        auto project =
            take(check(R"(pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    guard value
    return value
)"));
        auto entry = take(closeNativeRun(project, "m::Demo"));
        take(prepareOriginal(entry));
      });
  cases.run("layout definitions reuse callable and static inference", [] {
    auto project = take(check(R"(def identity<T: Type>(value: T) -> T:
    return value
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    result = identity(value)
    return result
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("ordered binding cannot conceal a pure expression", [] {
    refuses(check(R"(pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    result <- value
    return result
)"),
            "source.action");
  });
  cases.run("same scope immutable bindings cannot shadow", [] {
    refuses(check(R"(pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    result = value
    result = value
    return result
)"),
            "source.shadow");
  });
  cases.run(
      "randomness and communication use the selected service and payload owner",
      [] {
        auto project = take(check(R"(module m
domain F = field("bls12-381.fr")
pub protocol Draw roles(P, V)(coins: Random<F> @P) -> F @V:
    alias = coins
    value <- alias.draw()
    received <- send value to V
    return received
)"));
        take(prepareOriginal(take(closeNativeRun(project, "m::Draw"))));
        auto ast = take(json::parse(take(inspectWrittenSource(project))));
        bool omittedSender = false, unnamedResult = false, ordered = false;
        for (const auto &decl : *ast.getAsObject()->getArray("declarations"))
          if (decl.getAsObject()->getString("owner") == "m::Draw")
            for (const auto &node : *decl.getAsObject()->getArray("nodes")) {
              const auto &record = *node.getAsObject();
              if (auto *send = record.getObject("send"))
                omittedSender = send->get("from")->getAsNull().has_value();
              if (record.getString("kind") == "port" &&
                  record.get("name")->getAsNull())
                unnamedResult = true;
              ordered |= record.getString("evaluation") == "ordered";
            }
        require(omittedSender && unnamedResult && ordered,
                "written omissions and action binding were lost");
      });
  for (StringRef expression : {"coins.draw()", "identity(coins.draw())"})
    cases.run("pure binding refuses a random action: " + expression,
              [&] {
                refuses(check((R"(domain F = field("bls12-381.fr")
def identity(x: F) -> F:
    return x
pub protocol Draw roles(P)(coins: Random<F> @P) -> F @P:
    value = )" + expression + "\n    return value\n")
                                  .str()),
                        "source.action");
              });
  cases.run("recipient does not disambiguate a shared sender", [] {
    refuses(
        check(R"(pub protocol Send roles(P, V)(value: bool @(P, V)) -> bool @V:
    received <- send value to V
    return received
)"),
        "source.owner");
  });
  cases.run("explicit sending role resolves shared payload", [] {
    auto project = take(
        check(R"(pub protocol Send roles(P, V)(value: bool @(P, V)) -> bool @V:
    received <- send value from P to V
    return received
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Send"))));
  });
  cases.run(
      "Schnorr layout source closes and compares its actual native IR", [] {
        auto source = MemoryBuffer::getFile(ZKC_LAYOUT_FIXTURES "/schnorr.zkc");
        require(bool(source), "missing Schnorr fixture");
        CaptureOptions options;
        options.format = "zkc-layout";
        auto project =
            take(analyze(take(capture({{"schnorr", (*source)->getBuffer().str(),
                                        "schnorr.zkc"}},
                                      options)))
                     .checkedProject());
        take(prepareOriginal(
            take(closeSubject(project, "schnorr::Schnorr<schnorr::Curve>"))));
      });
  cases.run("section parameters expand once without creating a namespace", [] {
    auto project = take(check(R"(section <T: Type>:
    module Helpers<N: nat>:
        pub def identity(value: T) -> T:
            return value
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    result = Helpers<bool, 3>::identity(value)
    return result
)"));
    bool found = false;
    for (const auto &decl : project.declarations())
      if (decl.qualifiedName == "m::Helpers::identity") {
        require(decl.parameters.size() == 2,
                "section/module parameter duplicated");
        found = true;
      }
    require(found, "section inserted a namespace");
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
    auto ast = take(json::parse(take(inspectWrittenSource(project))));
    bool group = false;
    for (const auto &decl : *ast.getAsObject()->getArray("declarations"))
      for (const auto &node : *decl.getAsObject()->getArray("nodes"))
        group |= node.getAsObject()->getString("kind") == "section";
    require(group, "written section erased before export");
  });
  cases.run("unused section parameters remain explicit", [] {
    auto project = take(check(R"(section <N: nat>:
    def value() -> bool:
        return true
)"));
    bool found = false;
    for (const auto &decl : project.declarations())
      if (decl.qualifiedName == "m::value") {
        require(decl.parameters.size() == 1 && decl.parameters[0].name == "N",
                "unused explicit binder was removed");
        found = true;
      }
    require(found, "section declaration missing");
  });
  cases.run("section headers cannot silently discard constraints", [] {
    for (StringRef modifier : {"where N <= 1", "effects(stop)", "roles(P)"})
      refuses(check(("section <N: nat> " + modifier + R"(:
    def keep(value: bool) -> bool:
        value
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    result = keep<2>(value)
    return result
)")
                        .str()),
              "syntax.section");
  });
  cases.run("implicit results cannot silently discard action site labels", [] {
    refuses(check(R"(def keep(value: bool) -> bool:
    #[site(ignored)]
    value
)"),
            "source.site");
    refuses(check(R"(local def choose(flag: bool) -> bool:
    return if flag:
        #[site(ignored)]
        true
    else:
        false
)"),
            "source.site");
  });
  cases.run("non-callable declarations cannot carry native effect contracts",
            [] {
              for (StringRef source :
                   {"module m effects(stop)\ndef keep(value: bool) -> "
                    "bool:\n    value\n",
                    "module Helpers effects(stop):\n    def keep(value: "
                    "bool) -> bool:\n        value\n",
                    "interface Helpers effects(stop):\n    def keep(value: "
                    "bool) -> bool\n",
                    "struct Box effects(stop):\n    value: bool\n",
                    "enum Choice effects(stop):\n    Some(bool)\n    None()\n"})
                refuses(check(source), "source.effect");
            });
  cases.run("local branch expressions use the checked control graph", [] {
    auto project = take(check(
        R"(local def choose(flag: bool, first: bool, second: bool) -> bool:
    selected = if flag:
        first
    else:
        second
    return selected
pub protocol Demo roles(P)(flag: bool @P) -> bool @P:
    result <- choose(flag, true, false)
    return result
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("literal protocol loops infer maximum roster and sites", [] {
    auto project = take(check(R"(domain F = field("bls12-381.fr")
pub protocol Draw roles(P, V)(coins: Random<F> @P; value: bool @(P, V)) -> bool @(P, V):
    for round in 0..3:
        nonce <- coins.draw()
        received <- send nonce to V
    return value
)"));
    bool found = false;
    for (const auto &decl : project.declarations())
      if (decl.qualifiedName == "m::Draw")
        for (const auto &operation : decl.body->operations)
          if (auto *repeat = std::get_if<ProtocolRepeat>(&operation.action)) {
            found = true;
            require(operation.site == "round" &&
                        repeat->roles == std::vector<unsigned>({0, 1}) &&
                        repeat->maximum.closedValue() == 3,
                    "loop defaults differ from their specified local rules");
            std::set<std::string> names;
            for (const auto &nested : repeat->region->operations)
              if (nested.site)
                names.insert(*nested.site);
            require(names == std::set<std::string>({"nonce", "received"}),
                    "draw or send did not use its binding site");
          }
    require(found, "protocol loop was not retained");
    auto ast = take(inspectWrittenSource(project));
    require(!StringRef(ast).contains("\"site\":\"round\""),
            "inferred site became authored syntax");
    take(prepareOriginal(take(closeNativeRun(project, "m::Draw"))));
  });
  cases.run("dynamic protocol loops still require a maximum", [] {
    refuses(
        check(
            R"(pub protocol Demo roles(P)(count: index @P; value: bool @P) -> bool @P:
    for round in 0..count:
        guard @P value
    return value
)"),
        "source.bound");
  });
  cases.run("default loop roster still requires shared count knowledge", [] {
    refuses(
        check(
            R"(pub protocol Demo roles(P, V)(count: index @P; value: bool @(P, V)) -> bool @(P, V):
    for round in 0..count max 8:
        guard @P value
    return value
)"),
        "source.roles");
  });
  cases.run("explicit sites override defaults and collisions refuse", [] {
    auto text = R"(domain F = field("bls12-381.fr")
pub protocol Draw roles(P)(coins: Random<F> @P) -> F @P:
    #[site(second)]
    first <- coins.draw()
    second <- coins.draw()
    return second
)";
    refuses(check(text), "source.site");
  });
  cases.run("local loop mutation remains explicit", [] {
    auto project = take(check(R"(local def keep(value: bool) -> bool:
    mut result = value
    for i in 0..3:
        result := value
    return result
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    result <- keep(value)
    return result
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("records and patterns reuse field and resource checks", [] {
    auto project = take(check(R"(struct Pair:
    pub first: bool
    pub second: bool
local def swap(value: Pair) -> Pair:
    Pair {first, second} = value
    return Pair {first: second, second: first}
pub protocol Demo roles(P)(value: Pair @P) -> Pair @P:
    result <- swap(value)
    return result
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run(
      "owner spec resolves before its protocol without proving claims", [] {
        auto project = take(check(R"(use lean Proofs::{secure}
spec for Demo:
    requires true
    target statement: IsValid(value)
    security: secure(target.statement)
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    return value
)"));
        require(project.pendingSpecifications().size() == 1 &&
                    project.pendingSpecifications()[0].owner,
                "owner spec was not retained and resolved");
        auto entry = take(closeNativeRun(project, "m::Demo"));
        take(prepareOriginal(entry));
        refuses(inspectSourceClaims(entry), "source.assurance-unavailable");
        auto written = take(inspectWrittenSource(project));
        require(StringRef(written).contains("formal.specification") &&
                    StringRef(written).contains("security") &&
                    StringRef(written).contains("secure"),
                "formal request source was erased");
      });
  cases.run("formal export preserves authored arguments and clauses", [] {
    auto project = take(check(R"(ghost def proof(value: bool) -> bool:
    other(ghost evidence: value)
protocol Demo roles(P)(value: bool @P) -> bool @P:
    return value
spec for Demo:
    requires (true)
    ensures result: true
    reduces Input(value) to Output(value)
    security: secure(ghost evidence: value)
)"));
    auto parsed = take(json::parse(take(inspectWrittenSource(project))));
    const auto *declarations = parsed.getAsObject()->getArray("declarations");
    unsigned ghost = 0, ensures = 0, reductions = 0, groups = 0;
    for (const auto &declaration : *declarations)
      for (const auto &nodeValue :
           *declaration.getAsObject()->getArray("nodes")) {
        const auto &node = *nodeValue.getAsObject();
        require(!node.get("syntax_kind") && !node.get("tokens"),
                "parser representation escaped the authored contract");
        auto kind = node.getString("kind");
        if (kind == "formal.argument" && node.getBoolean("ghost") == true) {
          ++ghost;
          require(node.get("label") && !node.get("label")->getAsNull() &&
                      node.get("value") && !node.get("value")->getAsNull() &&
                      node.get("type")->getAsNull(),
                  "named ghost argument was confused with a parameter type");
        }
        if (kind == "formal.ensures")
          ++ensures;
        if (kind == "formal.group")
          ++groups;
        if (kind == "formal.reduces") {
          ++reductions;
          require(node.get("label")->getAsNull() &&
                      !node.get("residual")->getAsNull(),
                  "unlabeled reduction lost its relation operands");
        }
      }
    require(ghost == 2 && ensures == 1 && reductions == 1 && groups == 1,
            "authored formal shapes differ");
  });
  cases.run(
      "declared postconditions remain mandatory without a security request",
      [] {
        auto project =
            take(check(R"(protocol Demo roles(P)(value: bool @P) -> bool @P:
    return value
spec for Demo:
    requires true
    ensures true
    ensures named: true
)"));
        const auto &obligations =
            project.pendingSpecifications()[0].obligations;
        require(
            obligations.size() == 2 &&
                obligations[0].kind == PendingObligation::Kind::Postcondition &&
                obligations[0].ordinal == 0 && !obligations[0].label &&
                obligations[1].ordinal == 1 && obligations[1].label == "named",
            "unnamed or unrequested postcondition disappeared");
        require(
            obligations[0].companion ==
                    R"(["zkc.companion/0","m::Demo",["template"],"postcondition",["ordinal","0"]])" &&
                obligations[1].companion ==
                    R"(["zkc.companion/0","m::Demo",["template"],"postcondition",["label","named"]])",
            "companion key differs from shared contract");
      });
  cases.run("companion keys distinguish scopes roles and authored labels", [] {
    auto templateKey =
        take(companionIdentity("m::Demo", {}, ObligationRole::Request, {}, 0));
    auto labelKey =
        take(companionIdentity("m::Demo", {}, ObligationRole::Request, "0", 0));
    auto instanceKey = take(
        companionIdentity("m::Demo", "closed", ObligationRole::Request, {}, 0));
    auto roleKey = take(
        companionIdentity("m::Demo", {}, ObligationRole::Postcondition, {}, 0));
    require(std::set<std::string>({templateKey, labelKey, instanceKey, roleKey})
                    .size() == 4,
            "distinct lookup domains collided");
    refuses(companionIdentity("", {}, ObligationRole::Request, {}, 0),
            "source.companion");
    refuses(companionIdentity(StringRef("\xff", 1), {}, ObligationRole::Request,
                              {}, 0),
            "source.companion");
    auto limits = Limits{};
    limits.apiInspectionBytes = 1;
    refuses(companionIdentity("m::Demo", {}, ObligationRole::Request, {}, 0,
                              limits),
            "source.limit");
  });
  cases.run("owner attachment is unique by resolved identity", [] {
    refuses(check(R"(pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    return value
spec for Demo:
    target true
spec for Demo:
    ensures true
)"),
            "source.spec.owner");
  });
  cases.run("named audits cannot replace owner contracts", [] {
    auto project = take(check(R"(pub spec Audit for Demo:
    security: DesiredProperty()
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    return value
)"));
    require(project.pendingSpecifications().size() == 1 &&
                !project.pendingSpecifications()[0].owner &&
                project.pendingSpecifications()[0].isPublic,
            "named audit acquired owner authority");
  });
  cases.run("spec subject must be an actual protocol", [] {
    refuses(check(R"(def Demo(value: bool) -> bool:
    return value
spec for Demo:
    target true
)"),
            "source.spec.subject");
  });
  cases.run("section keeps source formal syntax and shares protocol telescope",
            [] {
              auto project = take(check(R"(section <T: Type>:
    spec for Demo:
        target HasProperty(value)
    pub protocol Demo roles(P)(value: T @P) -> T @P:
        return value
)"));
              require(project.pendingSpecifications().size() == 1 &&
                          project.pendingSpecifications()[0].owner,
                      "section spec lost its protocol owner");
              take(inspectWrittenSource(project));
            });
  cases.run("duplicate explicit request labels are rejected", [] {
    refuses(check(R"(protocol Demo roles(P)(value: bool @P) -> bool @P:
    return value
spec for Demo:
    security: First()
    security: Second()
)"),
            "source.spec.label");
  });
  cases.run("unnamed reduction relations are not clause labels", [] {
    take(check(R"(protocol Demo roles(P)(value: bool @P) -> bool @P:
    return value
spec for Demo:
    reduces Before to After
    reduces Before to Another
)"));
  });
  cases.run("qualified local subjects are request-only audits", [] {
    refuses(check(R"(protocol Demo roles(P)(value: bool @P) -> bool @P:
    return value
spec for m::Demo:
    target true
)"),
            "source.spec.audit");
  });
  cases.run("mathematical definitions use their final expression", [] {
    auto project = take(check(R"(def identity<T: Type + Copy>(value: T) -> T:
    value
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    return identity(value)
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
    auto written = take(json::parse(take(inspectWrittenSource(project))));
    bool tail = false;
    for (const auto &decl : *written.getAsObject()->getArray("declarations"))
      if (decl.getAsObject()->getString("owner") == "m::identity")
        for (const auto &node : *decl.getAsObject()->getArray("nodes"))
          tail |= node.getAsObject()->getString("terminal") == "tail";
    require(tail, "mathematical tail became an authored return");
  });
  cases.run("explicit interface members use native conformance", [] {
    auto project = take(check(R"(interface Identity:
    type Item: Copy + Drop
    def run(value: Item) -> Item
module BoolIdentity: Identity:
    type Item = bool
    def run(value: Item) -> Item:
        value
pub protocol Demo roles(P)(value: BoolIdentity::Item @P) -> BoolIdentity::Item @P:
    return BoolIdentity::run(value)
)"));
    refuses(closeNativeRun(project, "m::Demo"), "source.ingress");
  });
  cases.run("bodyless protocol is confined to interfaces", [] {
    refuses(check("protocol Demo roles(P)(value: bool @P) -> bool @P\n"),
            "source.conformance");
  });
  cases.run("interface owner specifications stay explicitly unavailable", [] {
    auto project = take(check(R"(interface API:
    protocol Demo roles(P)(value: bool @P) -> bool @P
    spec for Demo:
        target Good(value)
)"));
    require(project.pendingSpecifications().size() == 1 &&
                project.pendingSpecifications()[0].owner,
            "interface spec did not resolve to its member");
    take(inspectWrittenSource(project));
  });
  cases.run("external audits cannot inject provider premises", [] {
    CaptureOptions options;
    options.format = "zkc-layout";
    auto sources = std::vector<SourceBuffer>{
        {"provider", R"(pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    return value
)",
         "provider.zkc"},
        {"consumer", R"(use provider::{Demo}
spec for Demo:
    requires true
)",
         "consumer.zkc"}};
    auto captured = take(capture(std::move(sources), options));
    refuses(analyze(captured).checkedProject(), "source.spec.audit");
  });
  cases.run("imported notation supplies the body parse environment", [] {
    CaptureOptions options;
    options.format = "zkc-layout";
    auto project = take(
        analyze(
            take(capture({{"ops", R"(pub def first(a: bool, b: bool) -> bool:
    a
pub operator infixl(60) ⊕ = first
)",
                           "ops.zkc"},
                          {"m", R"(use ops::{operator ⊕}
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    return value ⊕ false
)",
                           "main.zkc"}},
                         options)))
            .checkedProject());
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run(
      "postfix, delimited and indexing notation reuse native call checking",
      [] {
        auto project = take(check(R"(def identity(value: bool) -> bool:
    value
def first(value: bool, ignored: bool) -> bool:
    value
operator postfix(90) ⊙ = identity
notation ⟦value⟧ = identity(value)
indexing value[ignored] = first(value, ignored)
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    return ⟦value⊙⟧[false]
)"));
        take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
      });
  cases.run("static requirements constrain closed selections", [] {
    auto source = R"(def identity<N: nat>(value: bool) -> bool where N <= 3:
    value
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    return identity<4>(value)
)";
    refuses(check(source), "source.bound");
  });
  cases.run("resource attributes are checked and preserved", [] {
    auto project = take(check(R"(#[affine]
pub struct Token:
    pub value: bool
pub protocol Demo roles(P)(value: Token @P) -> Token @P:
    return value
)"));
    refuses(closeNativeRun(project, "m::Demo"), "source.ingress");
    auto written = take(inspectWrittenSource(project));
    require(StringRef(written).contains("affine"),
            "authored resource restriction lost");
  });
  cases.run("unknown semantic attributes cannot disappear", [] {
    refuses(check(R"(#[mystery]
struct Token:
    value: bool
)"),
            "source.resource");
  });
  cases.run("contextual from in a payload is not a sender clause", [] {
    auto project =
        take(check(R"(pub protocol Demo roles(P, V)(from: bool @P) -> bool @V:
    received <- send from to V
    return received
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("written layout facts and actual rows reject mutations", [] {
    auto project = take(check(R"(section <T: Type>:
    def identity(value: T) -> T:
        value
pub protocol Demo roles(P, V)(value: bool @P) -> bool @V:
    received <- send identity(value) to V
    return received
spec for Demo:
    target Good(value)
)"));
    auto original =
        take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
    auto pristine =
        take(json::parse(take(exportSourceCorrespondence(original))));
    cantFail(
        checkSourceCorrespondenceExport(original, zkc::printJson(pristine)));
    for (StringRef field : {"evaluation", "send", "formal", "name"}) {
      auto mutated = pristine;
      auto &declarations = *mutated.getAsObject()
                                ->getObject("source_ast")
                                ->getArray("declarations");
      bool changed = false;
      for (auto &decl : declarations) {
        if (changed)
          break;
        for (auto &node : *decl.getAsObject()->getArray("nodes")) {
          auto *record = node.getAsObject();
          if (record->get(field)) {
            (*record)[field] = "changed";
            changed = true;
            break;
          }
        }
      }
      require(changed, "mutation did not select a written field");
      auto error =
          checkSourceCorrespondenceExport(original, zkc::printJson(mutated));
      require(bool(error), "mutated written facts were accepted");
      require(StringRef(toString(std::move(error)))
                  .contains("source.correspondence.export"),
              "mutation refused with an unrelated diagnostic");
    }
  });
  cases.run(
      "layout checking retains aggregate work and declaration ceilings", [] {
        auto limits = Limits{};
        limits.work = 10;
        refuses(
            check("def identity(value: bool) -> bool:\n    value\n", limits),
            "source.limit");
        auto project =
            take(check("def identity(value: bool) -> bool:\n    value\n"));
        limits = Limits{};
        limits.work = project.checkedWork() - 1;
        refuses(
            check("def identity(value: bool) -> bool:\n    value\n", limits),
            "source.limit");
      });
  cases.run("local match checks the resolved variant and all arms", [] {
    auto project = take(check(R"(enum Choice:
    Some(bool)
    None()
local def select(input: bool) -> bool:
    value = Choice::Some(input)
    return match value:
        case Some(item):
            item
        case None():
            false
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    result <- select(value)
    return result
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("qualified match constructors cannot lose their qualifier", [] {
    refuses(check(R"(enum Choice:
    Some(bool)
    None()
local def select(input: bool) -> bool:
    value = Choice::Some(input)
    return match value:
        case Missing::Some(item):
            item
        case Missing::None():
            false
)"),
            "source.name");
  });
  for (const std::vector<SourceBuffer> &sources :
       std::vector<std::vector<SourceBuffer>>{
           {{"m", "def identity(value: bool) -> bool:\n    value\n", "m.zkc"}},
           {{"m", R"(module m
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    return value
pub spec Audit for Demo:
    security: secure()
)",
             "m.zkc"}},
           {{"m", R"(def identity(value: bool) -> bool:
    value
operator postfix(90) ⊙ = identity
def apply(value: bool) -> bool:
    value⊙
)",
             "m.zkc"}},
           {{"ops", R"(pub def first(a: bool, b: bool) -> bool:
    a
pub operator infixl(60) ⊕ = first
)",
             "ops.zkc"},
            {"m", R"(use ops::{operator ⊕}
def apply(value: bool) -> bool:
    value ⊕ false
)",
             "m.zkc"}}})
    cases.run("every work cutoff safely refuses " + sources.back().text, [&] {
      CaptureOptions options;
      options.format = "zkc-layout";
      auto captured = take(capture(sources, options));
      auto project = take(analyze(captured).checkedProject());
      for (uint64_t work = 0; work < project.checkedWork(); ++work) {
        auto limits = Limits{};
        limits.work = work;
        refuses(analyze(captured, limits).checkedProject(), "source.limit");
      }
    });
  cases.run("protocol applications retain explicit role substitutions", [] {
    auto project =
        take(check(R"(protocol Deliver roles(A, B)(value: bool @A) -> bool @B:
    result <- send value to B
    return result
pub protocol Demo roles(P, V)(value: bool @P) -> bool @V:
    result <- Deliver(value) @(P, V)
    return result
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("protocol service arguments cannot silently change owners", [] {
    refuses(check(R"(domain F = field("bls12-381.fr")
protocol Draw roles(A)(coins: Random<F> @A) -> F @A:
    value <- coins.draw()
    return value
pub protocol Demo roles(P, V)(coins: Random<F> @V) -> F @P:
    value <- Draw(coins) @P
    return value
)"),
            "source.service");
  });
  cases.run("bounded protocol loops reuse checked repetition", [] {
    auto project = take(check(
        R"(pub protocol Demo roles(P)(value: bool @P; count: index @P) -> bool @P:
    mut result = value
    for i in 0..count roles(P) max 3:
        result := result
    return result
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("incomplete and mutated layout cannot evade native bounds", [] {
    std::mt19937 random(41);
    std::string original = R"(def identity<T: Type>(value: T) -> T:
    value
pub protocol Demo roles(P, V)(value: bool @P) -> bool @V:
    received <- send identity(value) to V
    return received
spec for Demo:
    target Good(value)
)";
    for (unsigned i = 0; i < 200; ++i) {
      auto text = original;
      unsigned at = random() % text.size();
      if (i % 3 == 0)
        text.resize(at);
      else if (i % 3 == 1)
        text.erase(at, 1);
      else
        text[at] = "()<>:;@= abc"[random() % 12];
      auto result = check(text);
      if (result) {
        take(inspectWrittenSource(*result));
      } else
        consumeError(result.takeError());
    }
  });
  for (StringRef argument : {"ghost value", "ghost input = value"})
    cases.run("ghost arguments cannot bind runtime inputs: " + argument, [&] {
      refuses(check((R"(def identity(input: bool) -> bool:
    input
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    result = identity()" +
                     argument + ")\n    return result\n")
                        .str()),
              "source.assurance-unavailable");
    });
  cases.run("oracle custody cannot become ordinary shared data", [] {
    refuses(
        check(R"(pub protocol Demo roles(P, V)(value: bool @P -> V) -> bool @V:
    return value
)"),
        "source.oracle-port");
  });
  for (StringRef qualifier : {"Choice", "m::Choice"})
    cases.run("qualified match resolves its nominal enum: " + qualifier, [&] {
      auto project = take(check((R"(enum Choice:
    Some(bool)
    None()
local def select(input: bool) -> bool:
    value = Choice::Some(input)
    return match value:
        case )" + qualifier + R"(::Some(item):
            item
        case Choice::None():
            false
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    result <- select(value)
    return result
)")
                                    .str()));
      take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
    });
  cases.run("same-spelled constructors from another enum refuse", [] {
    refuses(check(R"(enum Choice:
    Some(bool)
    None()
enum Other:
    Some(bool)
    None()
local def select(input: bool) -> bool:
    value = Choice::Some(input)
    return match value:
        case Other::Some(item):
            item
        case Choice::None():
            false
)"),
            "source.match");
  });
  cases.run("power syntax can bind an ordinary library callable", [] {
    auto project = take(check(R"(def select(left: bool, right: bool) -> bool:
    left
operator ^ = select
pub protocol Demo roles(P)(left: bool @P, right: bool @P) -> bool @P:
    return left ^ right
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  return cases.result();
}
