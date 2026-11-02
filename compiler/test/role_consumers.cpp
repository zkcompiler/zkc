#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/ApplicationMap.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <functional>
#include <string>

// Role-valued attributes through the consumers that read them, with fixtures
// written by hand rather than derived from the declared role table. Each
// fixture applies a callee whose roster (A, B) maps by position onto the
// caller's actual roles (V, P), so a consumer that matched names, sorted the
// actual roles or skipped one attribute sees a different role. Expected values
// are spelled out below. Application expansion, preparation correspondence,
// application-map checking, active-role validation and the expansion budget
// each run on actual source and candidate modules; every candidate mutation
// keeps formation valid and changes one role.

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace pir = zkc::protocol_ir;
namespace {
// A selected region whose result is placed at one role, an exchange inside
// it, a guard, and two role-like spellings that are not roles: the variant
// alternatives and the region's site.
constexpr StringLiteral controlFixture = R"mlir(
!V = !data.variant<#data.identity<["atom", "Pick"]>, [#data.alternative<"A">, #data.alternative<"B">]>
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%pick:!V,%flag:i1,%x:i1):
  %chosen = "protocol.branch"(%pick,%x) ({
  ^A(%cx:i1):
    %sent = protocol.exchange %cx {site="sent",sender="B",receiver="A"} : i1
    "protocol.yield"(%sent) : (i1)->()
  }, {
  ^B(%cx:i1):
    "protocol.yield"(%cx) : (i1)->()
  }) {site="A",roles=["A","B"],output_roles=[["A"]],alternatives=["A","B"]} : (!V,i1)->i1
  protocol.guard %flag {site="check",owner="B"}
  "protocol.return"(%x) : (i1)->()
 }) {sym_name="child",origin=["child",[]],function_type=(!V,i1,i1)->i1,roles=["A","B"],input_roles=[["A","B"],["A","B"],["A","B"]],output_roles=[["A"]]} : ()->()
 "protocol.func"() ({
 ^entry(%pick:!V,%flag:i1,%x:i1):
  %r = protocol.apply @child(%pick,%flag,%x) {roles=["V","P"],site="inner"} : (!V,i1,i1)->i1
  "protocol.return"(%r) : (i1)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!V,i1,i1)->i1,roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
// Oracle holders and receivers, a present owner, and a declaration whose
// query has no owner and a role-like site.
constexpr StringLiteral oracleFixture = R"mlir(
#K = #protocol.oracle_kind<"table", [ui64,4:ui64]>
!H = !protocol.oracle<#K>
!D = !data.indices
module { "protocol.module"() ({
 relation.declare @admissible {kind="external",key="test/role-consumers",revision="0",signature=(!D)->i1,purposes=["witness"]}
 "protocol.oracle"() ({
 ^entry(%handle:!H,%position:ui64):
  %answer = "protocol.oracle_query"(%handle,%position) {site="B"} : (!H,ui64)->ui64
  "protocol.oracle_yield"(%answer) : (ui64)->()
 }) {sym_name="view",function_type=(!H,ui64)->ui64,kind=#K,shape_arguments={},shape_bounds={},admissibility=@admissible} : ()->()
 "protocol.func"() ({
 ^entry(%data:!D,%anchor:!H,%position:ui64):
  %handle = "protocol.oracle_input"(%data,%anchor) {shape_bounds={},holder="A",receivers=["B"]} : (!D,!H)->!H
  %derived = "protocol.oracle_virtual"(%handle) {callee=@view,holder="A",receivers=["B"]} : (!H)->!H
  %parts:2 = "protocol.oracle_components"(%handle) {holder="A",receivers=["B"]} : (!H)->(!D,!H)
  %answer = "protocol.oracle_query"(%handle,%position) {owner="B",site="query"} : (!H,ui64)->ui64
  "protocol.return"(%parts#0,%parts#1) : (!D,!H)->()
 }) {sym_name="reader",origin=["reader",[]],function_type=(!D,!H,ui64)->(!D,!H),roles=["A","B"],input_roles=[["A"],["B"],["A","B"]],output_roles=[["A"],["B"]]} : ()->()
 "protocol.func"() ({
 ^entry(%data:!D,%anchor:!H,%position:ui64):
  %handle = "protocol.oracle_input"(%data,%anchor) {shape_bounds={},holder="V",receivers=["P"]} : (!D,!H)->!H
  %parts:2 = "protocol.oracle_components"(%handle) {holder="V",receivers=["P"]} : (!H)->(!D,!H)
  %r:2 = "protocol.apply"(%parts#0,%parts#1,%position) {callee=@reader,roles=["V","P"],site="inner"} : (!D,!H,ui64)->(!D,!H)
  "protocol.return"(%r#0,%r#1) : (!D,!H)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!D,!H,ui64)->(!D,!H),roles=["P","V"],input_roles=[["V"],["P"],["P","V"]],output_roles=[["V"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
// Selected control with a nested application, in a three-role protocol. The
// region's roles are A and B; text replacements move one role use to C.
constexpr StringLiteral activeFixture = R"mlir(module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%v:i1):
  "protocol.return"(%v) : (i1)->()
 }) {sym_name="pair",function_type=(i1)->i1,roles=["X","Y"],input_roles=[["X","Y"]],output_roles=[["X","Y"]]} : ()->()
 "protocol.func"() ({
 ^entry(%c:i1,%x:i1):
  %r = "protocol.branch"(%c,%x) ({
  ^then(%cx:i1):
    protocol.guard %cx {site="inside",owner="B"}
    %a = protocol.apply @pair(%cx) {roles=["B","A"],site="nested"} : (i1)->i1
    "protocol.yield"(%a) : (i1)->()
  }, {
  ^else(%cx:i1):
    "protocol.yield"(%cx) : (i1)->()
  }) {site="choose",roles=["A","B"],output_roles=[["A","B"]],alternatives=["then","else"]} : (i1,i1)->i1
  "protocol.return"(%r) : (i1)->()
 }) {sym_name="main",function_type=(i1,i1)->i1,roles=["A","B","C"],input_roles=[["A","B","C"],["A","B","C"]],output_roles=[["A","B"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";

std::string print(ModuleOp module) {
  std::string result;
  raw_string_ostream stream(result);
  module.print(stream, OpPrintingFlags().enableDebugInfo());
  stream << '\n';
  return result;
}
std::string replaceText(StringRef text, StringRef before, StringRef after) {
  auto position = text.find(before);
  require(position != StringRef::npos, "missing fixture fragment: " + before);
  return (text.take_front(position) + after +
          text.drop_front(position + before.size()))
      .str();
}
pir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<pir::ProtocolModuleOp>(module.getBody()->front());
}
pir::MathematicalOp definition(ModuleOp module, StringRef name) {
  auto found = SymbolTable(unit(module)).lookup<pir::MathematicalOp>(name);
  require(bool(found), "missing definition " + name);
  return found;
}
// The one operation of `main` with `site`.
Operation *occurrence(ModuleOp module, StringRef site) {
  Operation *found = nullptr;
  definition(module, "main").walk([&](Operation *op) {
    auto actual = op->getAttrOfType<StringAttr>("site");
    if (actual && actual.getValue() == site) {
      require(!found, "repeated occurrence " + site);
      found = op;
    }
  });
  require(found, "missing occurrence " + site);
  return found;
}
template <typename Op> Op only(ModuleOp module, StringRef function = "main") {
  Op found;
  definition(module, function).walk([&](Op op) {
    require(!found, "repeated " + Op::getOperationName());
    found = op;
  });
  require(bool(found), "missing " + Op::getOperationName());
  return found;
}
ArrayAttr names(MLIRContext &context, ArrayRef<StringRef> values) {
  SmallVector<Attribute> result;
  for (StringRef value : values)
    result.push_back(StringAttr::get(&context, value));
  return ArrayAttr::get(&context, result);
}
ArrayAttr slots(MLIRContext &context,
                ArrayRef<SmallVector<StringRef, 2>> values) {
  SmallVector<Attribute> result;
  for (const auto &value : values)
    result.push_back(names(context, value));
  return ArrayAttr::get(&context, result);
}
std::string expanded(StringRef site) {
  return mathematical::expandedApplicationSite("inner", site);
}
std::string digest(StringRef bytes) {
  return "sha256:" + toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
}

// An original, its unsimplified preparation, and the application map the
// producer derives for them; each consumer reads the actual modules.
struct Subject {
  MLIRContext &context;
  std::string original, candidate;
  OwningOpRef<ModuleOp> source, prepared;
  Subject(MLIRContext &context, StringRef text) : context(context) {
    source = parseSourceString<ModuleOp>(text, &context);
    require(bool(source) && succeeded(admitStage(*source)),
            "fixture formation refused");
    original = print(*source);
    prepared = mathematical::prepareProtocol(*source, false);
    require(bool(prepared), "preparation refused");
    candidate = print(*prepared);
  }
  // A candidate that differs from the prepared one by `mutate`, which must
  // keep formation valid so that each consumer, not formation, refuses it.
  OwningOpRef<ModuleOp> mutated(llvm::function_ref<void(ModuleOp)> mutate) {
    auto result = parseSourceString<ModuleOp>(candidate, &context);
    require(bool(result), "candidate does not parse");
    mutate(*result);
    require(succeeded(verify(*result)) && succeeded(admitStage(*result)),
            "a mutated candidate must remain formed");
    return result;
  }
};
// Captures whether a diagnostic names `code`.
struct Diagnosed {
  bool named = false;
  ScopedDiagnosticHandler handler;
  Diagnosed(MLIRContext &context, StringRef code)
      : handler(&context, [this, code = code.str()](Diagnostic &diagnostic) {
          named |= StringRef(diagnostic.str()).contains(code);
          return success();
        }) {}
};
void correspondenceRefuses(Subject &subject, ModuleOp candidate,
                           StringRef mutation) {
  Diagnosed diagnosed(subject.context, "mathematical-correspondence");
  require(failed(mathematical::verifyProtocolPreparationPreserved(
              unit(*subject.source), unit(candidate))) &&
              diagnosed.named,
          "preparation correspondence accepted " + mutation);
}
void mapRefuses(Subject &subject, ModuleOp candidate, StringRef mutation) {
  auto record = take(json::parse(take(protocol::produceApplicationMap(
      subject.original, subject.candidate, "main", subject.context))));
  auto bytes = print(candidate);
  (*record.getAsObject()->getObject("candidate"))["digest"] = digest(bytes);
  auto refusal = protocol::checkApplicationMap(
      subject.original, bytes, "main", printJson(record), subject.context);
  require(bool(refusal), "application map accepted " + mutation);
  auto message = toString(std::move(refusal));
  require(namesIdentifier(message, "application-map-correspondence"),
          "application map refused " + mutation +
              " for another reason: " + message);
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;

  cases.run("application expansion substitutes roles by position", [&] {
    Subject subject(context, controlFixture);
    // The callee roster (A, B) maps onto the actual roles (V, P).
    auto branch =
        cast<pir::BranchOp>(occurrence(*subject.prepared, expanded("A")));
    require(branch.getRoles() == names(context, {"V", "P"}),
            "selected region roles were not substituted in order");
    require(branch.getOutputRoles() == slots(context, {{"V"}}),
            "the placed selected result kept its callee role");
    auto exchange =
        cast<pir::ExchangeOp>(occurrence(*subject.prepared, expanded("sent")));
    require(exchange.getSender() == "P" && exchange.getReceiver() == "V",
            "exchange roles were not substituted by position");
    auto guard =
        cast<pir::GuardOp>(occurrence(*subject.prepared, expanded("check")));
    require(guard.getOwner() == "P", "guard owner was not substituted");
  });
  cases.run("role-like attributes that are not roles are unchanged", [&] {
    Subject subject(context, controlFixture);
    auto branch =
        cast<pir::BranchOp>(occurrence(*subject.prepared, expanded("A")));
    // Variant labels and sites only spell like roles.
    require(branch.getAlternatives() == names(context, {"A", "B"}),
            "variant alternatives were renamed as roles");
    require(branch.getSite() == "apply_5_inner_A",
            "a site was renamed as a role");
  });
  cases.run("roster binders are unchanged by expansion", [&] {
    for (StringRef text :
         {StringRef(controlFixture), StringRef(oracleFixture)}) {
      Subject subject(context, text);
      for (auto [name, roles] :
           {std::pair<StringRef, ArrayAttr>{"main", names(context, {"P", "V"})},
            {"child", names(context, {"A", "B"})},
            {"reader", names(context, {"A", "B"})}}) {
        auto before = SymbolTable(unit(*subject.source))
                          .lookup<pir::MathematicalOp>(name);
        if (!before)
          continue;
        auto after = definition(*subject.prepared, name);
        require(before.getRoles() == roles && after.getRoles() == roles &&
                    after.getInputRoles() == before.getInputRoles() &&
                    after.getOutputRoles() == before.getOutputRoles(),
                name + ": a roster or its interface changed");
      }
    }
  });
  cases.run("oracle holders, receivers and owners follow the roster", [&] {
    Subject subject(context, oracleFixture);
    // The entry's own bindings and the expanded callee's views all hold data
    // at V and handles at P.
    unsigned views = 0;
    definition(*subject.prepared, "main").walk([&](Operation *op) {
      auto holder = op->getAttrOfType<StringAttr>("holder");
      if (!holder)
        return;
      ++views;
      require(holder.getValue() == "V" &&
                  op->getAttr("receivers") == names(context, {"P"}),
              "an oracle holder or receiver kept its callee role");
    });
    require(views == 5, "oracle views were lost or added");
    auto query = cast<pir::OracleQueryOp>(
        occurrence(*subject.prepared, expanded("query")));
    require(query.getOwnerAttr() && *query.getOwner() == "P",
            "the present owner was not substituted");
    // The declaration's query has no owner and gains none.
    pir::OracleQueryOp declared;
    SymbolTable(unit(*subject.prepared))
        .lookup<pir::OracleDefinitionOp>("view")
        .walk([&](pir::OracleQueryOp op) { declared = op; });
    require(declared && !declared.getOwnerAttr() && declared.getSite() == "B",
            "the optional owner or its role-like site changed");
  });

  // Each mutation keeps formation valid and puts one wrong role into the
  // candidate. A consumer that renamed by name, sorted the actual roles or
  // skipped the attribute would accept it.
  using Mutation = std::function<void(ModuleOp)>;
  auto attribute = [&](StringRef site, StringRef name, Attribute value) {
    return Mutation([=, &context](ModuleOp module) {
      (void)context;
      occurrence(module, expanded(site))->setAttr(name, value);
    });
  };
  std::vector<std::tuple<StringRef, StringRef, Mutation>> mutations{
      {"guard owner", controlFixture,
       attribute("check", "owner", StringAttr::get(&context, "V"))},
      {"placed selected result", controlFixture,
       attribute("A", "output_roles", slots(context, {{"P"}}))},
      {"exchange sides", controlFixture,
       [&](ModuleOp module) {
         auto exchange =
             cast<pir::ExchangeOp>(occurrence(module, expanded("sent")));
         exchange.setSender("V");
         exchange.setReceiver("P");
       }},
      {"oracle owner", oracleFixture,
       attribute("query", "owner", StringAttr::get(&context, "V"))},
  };
  cases.run("preparation correspondence accepts the expansion", [&] {
    for (StringRef text :
         {StringRef(controlFixture), StringRef(oracleFixture)}) {
      Subject subject(context, text);
      require(succeeded(mathematical::verifyProtocolPreparationPreserved(
                  unit(*subject.source), unit(*subject.prepared))),
              "preparation correspondence refused the expansion");
    }
  });
  cases.run("the application map accepts the expansion", [&] {
    for (StringRef text :
         {StringRef(controlFixture), StringRef(oracleFixture)}) {
      Subject subject(context, text);
      auto record = take(protocol::produceApplicationMap(
          subject.original, subject.candidate, "main", context));
      if (auto error = protocol::checkApplicationMap(
              subject.original, subject.candidate, "main", record, context))
        throw std::runtime_error(toString(std::move(error)));
    }
  });
  for (const auto &mutation : mutations) {
    StringRef name = std::get<0>(mutation), text = std::get<1>(mutation);
    const Mutation &mutate = std::get<2>(mutation);
    cases.run("correspondence refuses a wrong " + name, [&] {
      Subject subject(context, text);
      auto candidate = subject.mutated(mutate);
      correspondenceRefuses(subject, *candidate, name);
    });
    cases.run("the application map refuses a wrong " + name, [&] {
      Subject subject(context, text);
      auto candidate = subject.mutated(mutate);
      mapRefuses(subject, *candidate, name);
    });
  }

  cases.run("active roles inside selected control", [&] {
    auto formed = [&](StringRef text, StringRef code) {
      auto module = parseSourceString<ModuleOp>(text, &context);
      require(bool(module), "active-role fixture does not parse");
      Diagnosed diagnosed(context, code);
      bool admitted = succeeded(admitStage(*module));
      return std::make_pair(admitted, diagnosed.named);
    };
    require(formed(activeFixture, "").first,
            "participating roles were refused");
    // One role use moves outside the region's roles.
    for (auto [before, after, detail] :
         {std::tuple<StringRef, StringRef, StringRef>{
              "{site=\"inside\",owner=\"B\"}", "{site=\"inside\",owner=\"C\"}",
              "action owner does not participate in control"},
          {"{roles=[\"B\",\"A\"],site=\"nested\"}",
           "{roles=[\"B\",\"C\"],site=\"nested\"}",
           "action adds a nonparticipating role"}}) {
      auto [admitted, named] =
          formed(replaceText(activeFixture, before, after), detail);
      require(!admitted && named,
              "a nonparticipating role was admitted: " + after);
    }
  });

  cases.run("the expansion budget charges role names", [&] {
    // A 1,000-role callee holds ten restrictions to its whole roster and is
    // applied `count` times. Its SSA slots stay in the thousands; its role
    // names alone decide whether the 1,000,000-slot budget holds.
    auto module = [](unsigned count) {
      std::string roster, actual, restrictions;
      for (unsigned i = 0; i < 1000; ++i) {
        roster += (i ? ",\"r" : "\"r") + std::to_string(i) + "\"";
        actual += (i ? ",\"p" : "\"p") + std::to_string(i) + "\"";
      }
      for (unsigned i = 0; i < 10; ++i)
        restrictions += "  %y" + std::to_string(i) +
                        " = protocol.restrict_roles %x {roles=[" + roster +
                        "]} : i1\n";
      std::string applications;
      for (unsigned i = 0; i < count; ++i)
        applications += "  %r" + std::to_string(i) +
                        " = protocol.apply @wide(%x) {roles=[" + actual +
                        "],site=\"s" + std::to_string(i) + "\"} : (i1)->i1\n";
      return "module { \"protocol.module\"() ({\n \"protocol.func\"() ({\n "
             "^entry(%x:i1):\n" +
             restrictions +
             "  \"protocol.return\"(%x) : (i1)->()\n }) "
             "{sym_name=\"wide\",function_type=(i1)->i1,roles=[" +
             roster + "],input_roles=[[" + roster + "]],output_roles=[[" +
             roster + "]]} : ()->()\n \"protocol.func\"() ({\n " +
             "^entry(%x:i1):\n" + applications +
             "  \"protocol.return\"(%x) : (i1)->()\n }) "
             "{sym_name=\"main\",function_type=(i1)->i1,roles=[" +
             actual + "],input_roles=[[" + actual + "]],output_roles=[[" +
             actual +
             "]]} : ()->()\n}) {profile=#protocol.profile<protocol>} "
             ": ()->() }";
    };
    for (auto [count, admitted] : {std::pair{60u, true}, {90u, false}}) {
      auto parsed = parseSourceString<ModuleOp>(module(count), &context);
      require(bool(parsed), "budget fixture does not parse");
      Diagnosed diagnosed(context, "exceeds SSA or site storage budget");
      bool formed = succeeded(admitStage(*parsed));
      require(formed == admitted && (admitted || diagnosed.named),
              Twine(count) + " applications: the role-name budget differs");
    }
  });
  return cases.result();
}
