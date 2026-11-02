#include "../lib/Compiler/LanguageInterface.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "support/SourceProject.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/LanguageInterface.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/CommonControl.h"
#include "zkc/Language/Layout.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/raw_ostream.h"
#include <functional>
#include <set>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
CheckedOriginal compile(StringRef source, bool layout = false) {
  CaptureOptions options;
  options.format = layout ? "zkc-layout" : "zkc";
  auto project =
      take(analyze(take(capture({{"m", source.str(), "common.zkc"}}, options)))
               .checkedProject());
  return take(prepareOriginal(take(closeNativeRun(project, "m::Run"))));
}
json::Object &protocol(json::Value &v, unsigned index = 0) {
  return *v.getAsObject()
              ->getArray("protocols")
              ->operator[](index)
              .getAsObject();
}
json::Array &inventory(json::Value &v, unsigned index = 0) {
  return *protocol(v, index).getArray("common_input_requirements");
}
json::Object &component(json::Value &v, unsigned group = 0, unsigned at = 0) {
  return *inventory(v)[group]
              .getAsObject()
              ->getArray("components")
              ->operator[](at)
              .getAsObject();
}
void mutate(const CheckedOriginal &original,
            function_ref<void(json::Value &)> change,
            StringRef code = "source.interface") {
  auto v = take(json::parse(original.interfaceJson()));
  change(v);
  refuses(readInterface(original.bytes(), zkc::printJson(v)), code);
}
constexpr StringLiteral booleanSource = R"(module m;
protocol Run roles(P,V)(flag:bool@(P,V),other:bool@(P,V))->(r:bool@(P,V)) {
 let r=if flag {if other {true}else{false}}else{false};return(r=r);
})";
constexpr StringLiteral custodySource = R"(#[affine]
struct State roles(A,B):
    pub flag: bool @(A,B)
pub protocol Run roles(P,V)(state:State roles(P,V)) -> bool @(P,V):
    result = if state.flag:
        true
    else:
        false
    return result
)";
CheckedOriginal custodyOriginal() {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto project = take(
      analyze(take(capture({{"m", custodySource.str(), "custody-fields.zkc"}},
                           options)))
          .checkedProject());
  return take(prepareOriginal(take(closeSubject(project, "m::Run"))));
}
} // namespace
int main(int argc, char **argv) {
  Cases cases;
  cases.run("current FRI retains complete source and native inventories", [] {
    auto project =
        take(analyze(take(capture(sourceProject(ZKC_SOURCE_PROJECT))))
                 .checkedProject());
    auto entry = take(closeSubject(project, "example::Fri"));
    Limits limits;
    uint64_t remaining = limits.work;
    unsigned protocols = 0, requirements = 0;
    for (const auto &decl : entry.declarations()) {
      if (!isClosedConcreteProtocol(decl))
        continue;
      ++protocols;
      requirements += take(zkc::language::detail::sourceCommonRequirements(
                               entry, decl, remaining, limits))
                          .size();
    }
    require(protocols > 1 && requirements > 0,
            "FRI did not exercise retained common inventories");
    // The production comparison maps every published inventory through the
    // component map and compares it with the actual native analysis.
    auto original = take(prepareOriginal(entry));
    auto view = take(readInterface(original.bytes(), original.interfaceJson()));
    require(view.protocols.size() == protocols,
            "interface and closure disagree on closed concrete Protocols");
    outs() << "FRI: " << protocols << " Protocols, " << requirements
           << " source classes, " << limits.work - remaining
           << " cumulative inventory work\n";
  });
  cases.run(
      "retained Protocol inventories debit derivation and layouts cumulatively",
      [] {
        // Make index setup dominate the small fixed Boolean canonicalization;
        // otherwise normalization charges could hide an uncharged observer.
        std::string source = "module m;";
        for (unsigned i = 0; i < 64; ++i)
          source += "struct InventoryPadding" + std::to_string(i) +
                    std::string(64, 'x') + "{pub ignored:bool}";
        source += R"(
struct State{pub empty:(),pub flag:bool}
protocol Choose roles(A,B)(s:State@(A,B))->(r:bool@(A,B)){
 let r=if s.flag{true}else{false};return(r=r);
}
protocol Run roles(P,V)(s:State@(P,V))->(r:bool@(P,V)){
 let r=Choose roles(V,P)(s);return(r=r);
})";
        auto original = compile(source);
        const auto &entry = original.entry();
        Limits limits;
        uint64_t total = 0;
        std::vector<DeclarationId> protocols;
        for (const auto &decl : entry.declarations()) {
          if (!isClosedConcreteProtocol(decl))
            continue;
          protocols.push_back(decl.id);
          uint64_t derivedRemaining = limits.work;
          auto derived = take(deriveCommonControlRequirements(
              entry, decl.id, limits, derivedRemaining));
          uint64_t layoutRemaining = limits.work;
          Layouts layouts(entry, limits, layoutRemaining);
          for (const auto &requirement : derived)
            take(layouts.get(requirement.type));
          uint64_t sourceRemaining = limits.work;
          auto inventory = take(zkc::language::detail::sourceCommonRequirements(
              entry, decl, sourceRemaining, limits));
          require(inventory.size() == 1,
                  "retained Protocol lost its inventory");
          auto spent = limits.work - sourceRemaining;
          require(spent >= (limits.work - derivedRemaining) +
                               (limits.work - layoutRemaining),
                  "source inventory did not debit its layout observer");
          total += spent;
        }
        require(protocols.size() == 2, "expected root and retained helper");
        uint64_t remaining = total;
        for (auto id : protocols)
          take(zkc::language::detail::sourceCommonRequirements(
              entry, entry.declarations()[id.index], remaining, limits));
        require(remaining == 0, "successful inventory work was not exact");
        remaining = total - 1;
        for (unsigned i = 0; i + 1 < protocols.size(); ++i)
          take(zkc::language::detail::sourceCommonRequirements(
              entry, entry.declarations()[protocols[i].index], remaining,
              limits));
        auto beforeFailure = remaining;
        refuses(zkc::language::detail::sourceCommonRequirements(
                    entry, entry.declarations()[protocols.back().index],
                    remaining, limits),
                "source.limit");
        require(remaining < beforeFailure, "failed inventory refunded work");
      });
  cases.run(
      "layout allowance includes nested semantics and failed observations", [] {
        auto original = custodyOriginal();
        const auto &entry = original.entry();
        const auto &port = entry.protocol().inputs.front();
        Limits limits;
        uint64_t remaining = limits.work;
        Layouts layouts(entry, limits, remaining);
        take(layouts.get(port.type));
        auto beforePlacement = remaining;
        require(port.placement.has_value(), "missing placed test input");
        take(layouts.placement(port.type, *port.placement, 2));
        require(remaining < beforePlacement,
                "nested semantic placement bypassed the enclosing allowance");
        auto beforeFailure = remaining;
        Type open(Type::Kind::Parameter, "unresolved");
        open.symbolic = true;
        refuses(layouts.get(open), "source.generic");
        require(remaining < beforeFailure, "failed layout refunded prior work");
        remaining = 2;
        refuses(layouts.get(port.type), "source.limit");
        require(remaining < 2, "failed bounded layout did not debit its work");
        remaining = 0;
        refuses(layouts.get(port.type), "source.limit");

        remaining = limits.work;
        limits.work = 1;
        Layouts capped(entry, limits, remaining);
        refuses(capped.get(port.type), "source.limit");
        require(remaining == Limits{}.work,
                "setup spent beyond its local ceiling");
        Layouts placementFirst(entry, limits, remaining);
        refuses(placementFirst.placement(port.type, *port.placement, 2),
                "source.limit");
        require(remaining == Limits{}.work,
                "placement indexed declarations before bounding setup");
        Limits raised;
        ++raised.work;
        Layouts invalidLimits(entry, raised, remaining);
        refuses(invalidLimits.get(port.type), "source.limit");
        require(remaining == Limits{}.work,
                "shared observer admitted a raised requested ceiling");
      });
  cases.run("placement validation debits partial work on errors", [] {
    auto original = compile(booleanSource);
    const auto &entry = original.entry();
    Limits limits;
    uint64_t remaining = limits.work;
    Layouts layouts(entry, limits, remaining);
    take(layouts.get(Type{}));
    remaining = 2;
    refuses(layouts.placement(Type{}, DataPlacement{{0, 1}}, 2),
            "source.limit");
    require(remaining == 0, "placement validation ignored shared remaining");
    remaining = 100;
    refuses(layouts.placement(Type{}, DataPlacement{{0, 0}}, 2),
            "source.roles");
    require(remaining == 95, "malformed placement lost its four helper units");
    remaining = 3;
    refuses(layouts.placement(Type{}, DataPlacement{{0, 0}}, 2),
            "source.limit");
    require(remaining == 1,
            "placement refunded its admitted validation prefix");
  });
  cases.run(
      "successful placement consumes exactly its enclosing allowance", [] {
        auto original = compile(booleanSource);
        const auto &entry = original.entry();
        Limits limits;
        auto observe = [&](uint64_t allowance, bool success) {
          uint64_t remaining = limits.work;
          Layouts layouts(entry, limits, remaining);
          take(layouts.get(Type{}));
          remaining = allowance;
          auto result = layouts.placement(Type{}, DataPlacement{{0, 1}}, 2);
          if (success)
            require(take(std::move(result)) ==
                        ValuePlacement(DataPlacement{{0, 1}}),
                    "successful placement changed its roles");
          else
            refuses(std::move(result), "source.limit");
          return remaining;
        };
        auto cost = limits.work - observe(limits.work, true);
        require(cost > 4, "placement omitted its validation cost");
        require(observe(cost, true) == 0,
                "successful placement was double charged");
        require(observe(cost - 1, false) < cost - 1,
                "failed placement refunded its earlier charges");
      });
  cases.run(
      "failed natural layout preserves overflow and normalization debits", [] {
        auto project = take(analyze(take(capture({{"m", R"(module m;
struct Sized<N:nat>{pub values:[bool;pow2(N)]}
protocol Run roles(P,V)()->(){return();})",
                                                   "normalization.zkc"}})))
                                .checkedProject());
        auto entry = take(closeSubject(project, "m::Run"));
        Limits limits;
        Type record(Type::Kind::Record, "m::Sized");
        Type actual(Type::Kind::Natural);
        actual.dimension = Natural::constant(64);
        record.arguments = {actual};
        uint64_t remaining = limits.work;
        Layouts layouts(entry, limits, remaining);
        take(layouts.get(Type{}));
        const Declaration *sized = nullptr;
        for (const auto &declaration : entry.declarations())
          if (declaration.qualifiedName == "m::Sized")
            sized = &declaration;
        require(sized && sized->fields.size() == 1,
                "missing retained natural field metadata");
        NaturalArithmetic standalone;
        const auto before = standalone.remainingWork();
        refuses(standalone.substitute(
                    sized->fields.front().type.dimension,
                    [&](const Natural::Factor &) { return &actual.dimension; }),
                "source.natural");
        const auto normalizationCost = before - standalone.remainingWork();
        require(normalizationCost == 24,
                "retained natural atom identity changed");
        remaining = 100;
        refuses(layouts.get(record), "source.natural");
        require(remaining == 100 - 70 - normalizationCost,
                "overflow lost its performed normalization work");
        remaining = 73;
        refuses(layouts.get(record), "source.limit");
        require(
            remaining == 3,
            "normalization ran its first identity charge without admission");
        remaining = 70 + normalizationCost - 1;
        refuses(layouts.get(record), "source.limit");
        require(remaining == 1,
                "failed normalization lost its admitted identity charge");
        remaining = 70;
        refuses(layouts.get(record), "source.limit");
        require(remaining == 0, "failed normalization refunded preceding work");
      });
  cases.run("natural layout refuses before exceeding shared remaining", [] {
    auto project = take(analyze(take(capture({{"m", R"(module m;
struct Sized<N:nat>{pub values:[bool;pow2(N)]}
protocol Run roles(P,V)()->(){return();})",
                                               "normalization.zkc"}})))
                            .checkedProject());
    auto entry = take(closeSubject(project, "m::Run"));
    Limits limits;
    Type record(Type::Kind::Record, "m::Sized");
    Type actual(Type::Kind::Natural);
    actual.dimension = Natural::constant(64);
    record.arguments = {actual};
    uint64_t remaining = limits.work;
    Layouts layouts(entry, limits, remaining);
    take(layouts.get(Type{}));
    remaining = 73;
    refuses(layouts.get(record), "source.limit");
    require(remaining == 3,
            "normalization admitted a 22-unit identity with only three left");
    remaining = 93;
    refuses(layouts.get(record), "source.limit");
    require(remaining == 1, "normalization lost its admitted 22-unit prefix");
  });
  cases.run("successful natural layout has exact shared work accounting", [] {
    auto project = take(analyze(take(capture({{"m", R"(module m;
struct Sized<N:nat>{pub values:[bool;pow2(N)]}
protocol Run roles(P,V)()->(){return();})",
                                               "normalization.zkc"}})))
                            .checkedProject());
    auto entry = take(closeSubject(project, "m::Run"));
    Limits limits;
    Type record(Type::Kind::Record, "m::Sized");
    Type actual(Type::Kind::Natural);
    actual.dimension = Natural::constant(2);
    record.arguments = {actual};
    auto observe = [&](uint64_t allowance, bool success) {
      uint64_t remaining = limits.work;
      Layouts layouts(entry, limits, remaining);
      take(layouts.get(Type{}));
      remaining = allowance;
      auto result = layouts.get(record);
      if (success)
        require(take(std::move(result))->leaves.size() == 4,
                "natural substitution changed the layout");
      else
        refuses(std::move(result), "source.limit");
      return remaining;
    };
    auto cost = limits.work - observe(limits.work, true);
    require(observe(cost, true) == 0,
            "natural work was omitted or double charged");
    require(observe(cost - 1, false) < cost - 1,
            "bounded natural layout refunded partial spending");
  });
  cases.run("natural source inventories retain combined budgets", [] {
    std::string text = "module m;";
    for (unsigned i = 0; i < 16; ++i)
      text += "struct NaturalInventoryPadding" + std::to_string(i) +
              std::string(32, 'x') + "{pub ignored:bool}";
    text += R"(struct Sized<N:nat>{pub values:[bool;pow2(N)]}
protocol Run roles(P,V)(s:Sized<1>@(P,V))->(r:bool@(P,V)){
 let r=if s.values[0]{true}else{false};return(r=r);
})";
    auto original = compile(text);
    const auto &entry = original.entry();
    Limits limits;
    uint64_t remaining = limits.work;
    auto source = take(deriveCommonControlRequirements(
        entry, entry.protocol().id, limits, remaining));
    auto derivationCost = limits.work - remaining;
    remaining = limits.work;
    Layouts requirements(entry, limits, remaining);
    for (const auto &requirement : source)
      take(requirements.get(requirement.type));
    const auto requiredLayoutCost = limits.work - remaining;
    remaining = limits.work;
    auto inventory = take(zkc::language::detail::sourceCommonRequirements(
        entry, entry.protocol(), remaining, limits));
    auto sourceCost = limits.work - remaining;
    require(!inventory.empty() &&
                sourceCost >= derivationCost + requiredLayoutCost,
            "natural source inventory omitted its observation work");
    remaining = sourceCost;
    take(zkc::language::detail::sourceCommonRequirements(
        entry, entry.protocol(), remaining, limits));
    require(remaining == 0, "natural source inventory work was not exact");
    remaining = sourceCost - 1;
    refuses(zkc::language::detail::sourceCommonRequirements(
                entry, entry.protocol(), remaining, limits),
            "source.limit");
    require(remaining < sourceCost - 1,
            "failed source inventory refunded work");
  });
  cases.run("source derivation and layouts share one inventory allowance", [] {
    auto original = compile(booleanSource);
    const auto &entry = original.entry();
    Limits limits;
    uint64_t remaining = limits.work;
    auto source = take(deriveCommonControlRequirements(
        entry, entry.protocol().id, limits, remaining));
    auto derivationCost = limits.work - remaining;
    remaining = limits.work;
    Layouts layouts(entry, limits, remaining);
    for (const auto &port : entry.protocol().inputs)
      take(layouts.protocolPort(port));
    for (const auto &requirement : source)
      take(layouts.get(requirement.type));
    auto layoutCost = limits.work - remaining;
    remaining = limits.work;
    require(take(zkc::language::detail::sourceCommonRequirements(
                     entry, entry.protocol(), remaining, limits))
                    .size() == 2,
            "positive inventory changed");
    limits.work = std::max(derivationCost, layoutCost);
    take(deriveCommonControlRequirements(entry, entry.protocol().id, limits));
    Layouts independent(entry, limits);
    for (const auto &port : entry.protocol().inputs)
      take(independent.protocolPort(port));
    remaining = limits.work;
    refuses(zkc::language::detail::sourceCommonRequirements(
                entry, entry.protocol(), remaining, limits),
            "source.limit");
  });
  cases.run(
      "irrelevant declaration metadata is bounded before index setup", [] {
        std::string source = "module m;";
        for (unsigned i = 0; i < 128; ++i) {
          source += "struct Irrelevant" + std::to_string(i) +
                    std::string(64, 'x') + "{";
          for (unsigned field = 0; field < 24; ++field)
            source += "pub field" + std::to_string(field) + ":bool,";
          source += "}";
        }
        source += "protocol Run roles(P,V)()->(){return();}";
        auto project = take(
            analyze(
                take(capture({{"m", source, "irrelevant-declarations.zkc"}})))
                .checkedProject());
        auto entry = take(closeNativeRun(project, "m::Run"));
        require(entry.declarations().size() >= 128,
                "closed test environment omitted irrelevant declarations");
        // The old root traversal fit this allowance while copying and indexing
        // the complete, deeply populated declaration environment before
        // charging.
        Limits limits;
        limits.work = entry.declarations().size() + 100;
        DeclarationId checkedTarget{};
        bool found = false;
        for (const auto &decl : project.declarations())
          if (decl.qualifiedName == "m::Run") {
            checkedTarget = decl.id;
            found = true;
          }
        require(found, "missing checked root Protocol");
        refuses(deriveCommonControlRequirements(project, checkedTarget, limits),
                "source.limit");
        refuses(deriveCommonControlRequirements(entry, limits), "source.limit");
        uint64_t inventoryRemaining = limits.work;
        refuses(zkc::language::detail::sourceCommonRequirements(
                    entry, entry.protocol(), inventoryRemaining, limits),
                "source.limit");
        limits.work = 1;
        refuses(deriveCommonControlRequirements(project, checkedTarget, limits),
                "source.limit");
        uint64_t remaining = 1;
        refuses(deriveCommonControlRequirements(entry, entry.protocol().id,
                                                limits, remaining),
                "source.limit");
        remaining = 1;
        refuses(zkc::language::detail::sourceCommonRequirements(
                    entry, entry.protocol(), remaining, limits),
                "source.limit");
      });
  cases.run("actual Boolean inventory and exact source comparison", [] {
    auto original = compile(booleanSource);
    require(
        take(deriveCommonControlRequirements(original.entry(), {})).size() == 2,
        "existing braced root Limits call changed meaning");
    auto view = take(readInterface(original.bytes(), original.interfaceJson()));
    require(view.selectedProtocol().commonInputRequirements.size() == 2,
            "dormant selector requirement was omitted");
    if (auto e = compareInterface(original.entry(), view))
      throw std::runtime_error(toString(std::move(e)));
    view.protocols[view.selected].commonInputRequirements.pop_back();
    auto result = compareInterface(original.entry(), view);
    require(bool(result), "source comparison accepted removed inventory");
    require(
        namesIdentifier(toString(std::move(result)), "source.correspondence"),
        "wrong source comparison refusal");
  });
  cases.run(
      "a self-hashed replacement original does not authenticate source", [] {
        auto original = compile(booleanSource);
        auto replacement = compile(R"(module m;
protocol Run roles(P,V)(flag:bool@(P,V),other:bool@(P,V))->(r:bool@(P,V)) {
 return(r=flag);
})");
        auto decoded = take(
            readInterface(replacement.bytes(), replacement.interfaceJson()));
        require(decoded.selectedProtocol().commonInputRequirements.empty(),
                "replacement body unexpectedly has a common control");
        refuses(admitOriginal(original.entry(), replacement.bytes(),
                              replacement.interfaceJson()),
                "source.correspondence");
      });
  for (StringRef name :
       {"missing-member", "missing", "extra", "groups", "roles", "duplicate",
        "input", "field", "payload", "alternative", "negative", "fraction",
        "unknown", "observation", "axis", "same-role"})
    cases.run("actual Boolean inventory tamper: " + name, [&] {
      auto original = compile(booleanSource);
      mutate(original, [&](auto &v) {
        auto &rs = inventory(v);
        auto &c = component(v);
        if (name == "missing-member")
          protocol(v).erase("common_input_requirements");
        else if (name == "missing")
          rs.pop_back();
        else if (name == "extra")
          rs.push_back(rs[0]);
        else if (name == "groups")
          std::swap(rs[0], rs[1]);
        else if (name == "roles") {
          auto &cs = *rs[0].getAsObject()->getArray("components");
          std::swap(cs[0], cs[1]);
        } else if (name == "duplicate")
          rs[0]
              .getAsObject()
              ->getArray("components")
              ->push_back(json::Object(c));
        else if (name == "input")
          c["input"] = 1;
        else if (name == "negative")
          c["input"] = -1;
        else if (name == "fraction")
          c["input"] = 0.5;
        else if (name == "unknown")
          c["native"] = 0;
        else if (name == "same-role")
          c["role"] = "V";
        else if (name == "field" || name == "payload" || name == "alternative")
          c["path"] =
              json::Array{json::Object{{"kind", name.str()}, {"index", 0}}};
        else
          rs[0].getAsObject()->operator[]("observation") =
              name == "axis" ? json::Object{{"kind", "value"}, {"axis", 0}}
                             : json::Object{{"kind", "extent"}, {"axis", 0}};
      });
    });
  // The production comparison maps the published inventory through the
  // component map and compares it with the actual native analysis, so a
  // component-map or native-body mutation refuses.
  for (StringRef name : {"native", "role", "guard"})
    cases.run("product inventory tamper: " + name, [&] {
      auto original = compile(R"(module m;
struct State{pub flag:bool,pub other:bool}
protocol Run roles(P,V)(s:State@(P,V))->(r:bool@(P,V)) {
 let r=if s.flag {if s.other {true}else{false}}else{false};return(r=r);
})");
      take(readInterface(original.bytes(), original.interfaceJson()));
      if (name != "guard") {
        mutate(original, [&](auto &v) {
          auto &components =
              *protocol(v).getArray("inputs")->front().getAsObject()->getArray(
                  "components");
          auto at = [&](int64_t field, int64_t role) -> json::Object & {
            for (auto &value : components) {
              auto &component = *value.getAsObject();
              if ((*component.getArray("path"))[0].getAsInteger() == field &&
                  component.getInteger("role") == role)
                return component;
            }
            throw std::runtime_error("missing published component");
          };
          if (name == "native")
            std::swap(at(0, 0)["native"], at(1, 0)["native"]);
          else
            at(0, 1)["role"] = 0;
        });
        return;
      }
      mlir::DialectRegistry registry;
      zkc::registerDialects(registry);
      mlir::MLIRContext context(registry);
      context.loadAllAvailableDialects();
      auto module =
          mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
      require(bool(module), "original did not parse");
      zkc::protocol_ir::BranchOp outer;
      module->walk([&](zkc::protocol_ir::BranchOp op) {
        if (mlir::isa<zkc::protocol_ir::MathematicalOp>(op->getParentOp()))
          outer = op;
      });
      require(bool(outer), "original has no guard");
      auto root = outer->getParentOfType<zkc::protocol_ir::MathematicalOp>();
      outer->setOperand(0, root.getBody().front().getArgument(1));
      std::string bytes;
      raw_string_ostream stream(bytes);
      module->print(stream);
      auto v = take(json::parse(original.interfaceJson()));
      v.getAsObject()->operator[]("original") =
          toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
      refuses(readInterface(bytes, zkc::printJson(v)), "source.interface");
    });
  cases.run(
      "one closed concrete Protocol predicate selects derivation and "
      "publication",
      [] {
        auto project = take(analyze(take(capture({{"m", R"(module m;
protocol Pick<N:nat> roles(P,V)(xs:[bool;N]@(P,V))->(r:bool@(P,V)){
 let r=if xs[0] {true}else{false};return(r=r);
}
protocol Run roles(P,V)(xs:[bool;2]@(P,V))->(r:bool@(P,V)){
 let r=Pick<2> roles(P,V)(xs);return(r=r);
})",
                                                   "closed-concrete.zkc"}})))
                                .checkedProject());
        // A checked template is not closed; project derivation keeps its
        // wider generic admission.
        DeclarationId pick{};
        for (const auto &decl : project.declarations())
          if (decl.qualifiedName == "m::Pick")
            pick = decl.id;
        require(!isClosedConcreteProtocol(project.declarations()[pick.index]),
                "an open template counted as closed concrete");
        take(deriveCommonControlRequirements(project, pick));
        auto entry = take(closeNativeRun(project, "m::Run"));
        std::set<std::string> concrete;
        for (const auto &decl : entry.declarations()) {
          if (isClosedConcreteProtocol(decl)) {
            concrete.insert(decl.symbol);
            take(deriveCommonControlRequirements(entry, decl.id, {}));
          } else if (decl.kind == Declaration::Kind::Protocol)
            refuses(deriveCommonControlRequirements(entry, decl.id, {}),
                    "source.common-provenance");
        }
        require(concrete.size() == 2, "closure lost a concrete instance");
        auto original = take(prepareOriginal(entry));
        std::set<std::string> published;
        for (const auto &protocol : original.interface().protocols)
          published.insert(protocol.symbol);
        require(published == concrete,
                "publication selected other Protocols than derivation");
        if (auto error = compareInterface(entry, original.interface()))
          throw std::runtime_error(toString(std::move(error)));
      });
  cases.run("bounds precede projection and sorting", [] {
    auto original = compile(booleanSource);
    mutate(
        original,
        [](auto &v) {
          auto r = inventory(v)[0];
          inventory(v).clear();
          for (unsigned i = 0; i < 1025; ++i)
            inventory(v).push_back(r);
        },
        "source.limit");
    mutate(
        original,
        [](auto &v) {
          json::Array path;
          for (unsigned i = 0; i < 33; ++i)
            path.push_back(json::Object{{"kind", "field"}, {"index", 0}});
          component(v)["path"] = std::move(path);
        },
        "source.limit");
    auto v = take(json::parse(original.interfaceJson()));
    Limits limits;
    limits.work = 100;
    refuses(readInterface(original.bytes(), zkc::printJson(v), limits),
            "source.limit");
  });
  cases.run("tag and conditional payload observations remain distinct", [] {
    auto original = compile(R"(module m;
enum Inner{Some(bool),None()}
struct Payload{pub empty:(),pub nested:Inner}
enum Outer{Some(Payload),None()}
protocol Run roles(P,V)(choice:Outer@(P,V))->(r:bool@(P,V)){
 let r=match choice {Some(p)=>{match p.nested {Some(flag)=>{if flag {true}else{false}},None()=>{false}}},None()=>{false}};return(r=r);
})");
    auto view = take(readInterface(original.bytes(), original.interfaceJson()));
    const auto &rs = view.selectedProtocol().commonInputRequirements;
    require(rs.size() == 3 &&
                std::holds_alternative<InterfaceCommonTag>(rs[0].observation) &&
                std::holds_alternative<InterfaceCommonTag>(rs[1].observation) &&
                !std::holds_alternative<InterfaceCommonTag>(rs[2].observation),
            "nested tags and conditional value were merged");
    require(rs[2].components[0].path.size() == 5,
            "nested payload path lost its placed field");
    mutate(original, [](auto &v) {
      component(v, 2)["path"] =
          json::Array{json::Object{{"kind", "alternative"}, {"index", 0}},
                      json::Object{{"kind", "payload"}, {"index", 0}},
                      json::Object{{"kind", "field"}, {"index", 0}}};
    });
    mutate(original, [](auto &v) {
      inventory(v)[0].getAsObject()->operator[]("observation") =
          json::Object{{"kind", "value"}};
    });
  });
  cases.run(
      "equal payload storage in distinct alternatives stays conditional", [] {
        auto original = compile(R"(module m;
enum Choice{Left(bool),Right(bool)}
protocol Run roles(P,V)(choice:Choice@(P,V))->(r:bool@(P,V)){
 let r=match choice {Left(x)=>{if x{true}else{false}},Right(y)=>{if y{false}else{true}}};
 return(r=r);
})");
        const auto &rs =
            original.interface().selectedProtocol().commonInputRequirements;
        require(rs.size() == 3 && rs[1].components[0].path[0].index == 0 &&
                    rs[2].components[0].path[0].index == 1,
                "conditional payload coordinates merged through equal storage");
        mutate(original, [](auto &v) { inventory(v).pop_back(); });
      });
  cases.run("extent observes the original collection and exact axis", [] {
    auto original = compile(
        R"(module m;domain Fr=field("koala-bear");type Vector<F:Field>=builtin("vector",F);
math fn size(x:Vector<Fr>)->index{return intrinsic<Fr>("vector.length",x);}
protocol Run roles(P,V)(xs:Vector<Fr>@(P,V),x:bool@(P,V))->(r:bool@(P,V)){
 let n=size(xs);let mut y=x;for _ in 0..n roles(P,V) max 4 {y=y;}return(r=y);
})");
    const auto &rs =
        original.interface().selectedProtocol().commonInputRequirements;
    require(rs.size() == 1 &&
                std::get<InterfaceCommonExtent>(rs[0].observation).axis == 0 &&
                !std::holds_alternative<InterfaceCommonTag>(rs[0].observation),
            "extent was replaced by content equality");
    mutate(original, [](auto &v) {
      inventory(v)[0]
          .getAsObject()
          ->getObject("observation")
          ->operator[]("axis") = 1;
    });
    mutate(original, [](auto &v) {
      inventory(v)[0].getAsObject()->operator[]("observation") =
          json::Object{{"kind", "value"}};
    });
  });
  cases.run("managed services retain ordinary control input coordinates", [] {
    auto original = compile(R"(module m;domain Fr=field("bls12-381.fr");
protocol Run roles(P,V)(flag:bool@(P,V),coins:Random<Fr>@P)->(r:Fr@P){
 let r=if flag {coins.draw()}else{coins.draw()};return(r=r);
})");
    const auto &p = original.interface().selectedProtocol();
    require(p.services.size() == 1 && p.services[0].native == 1 &&
                p.commonInputRequirements.size() == 1 &&
                p.commonInputRequirements[0].components[0].input == 0,
            "service authority displaced or supplied common data");
  });
  cases.run(
      "setup association stays separate from ordinary common admission", [] {
        auto project = take(analyze(take(capture({{"m", R"(module m;
domain C=commitment("multilinear.kzg.bls12-381/0");
type PK=builtin("prover_key",C);type VK=builtin("verifier_key",C);
protocol Run roles(P,V)(vk:VK@V,pk:PK@P,flag:bool@(P,V))->(ok:bool@V){
 let ok=if flag {true}else{false};return(ok=ok);
}
proof Main=Run{setup pcs{vk,pk};prover P;verifier V;public{vk,flag};accept ok;construction authored;}
)",
                                                   "setup-common.zkc"}})))
                                .checkedProject());
        auto original =
            take(prepareOriginal(take(closeEntry(project, "m::Main"))));
        const auto &view = original.interface();
        require(view.setups.size() == 1 && view.proof &&
                    view.selectedProtocol().commonInputRequirements.size() ==
                        1 &&
                    view.selectedProtocol()
                            .commonInputRequirements[0]
                            .components[0]
                            .input == 2,
                "setup metadata supplied or renumbered a common input");
      });
  cases.run("scoped total mathematics retains captured input obligations", [] {
    auto original = compile(R"(module m;
math fn apply(x:bool,body:math fn(bool)->bool)->bool{return body(x);}
math fn choose(flag:bool,x:bool)->bool{return if flag{x}else{false};}
protocol Run roles(P,V)(flag:bool@(P,V),other:bool@(P,V))->(r:bool@(P,V)){
 let condition=apply(flag,fn(y)=>choose(y,other));
 let r=if condition {true}else{false};return(r=r);
})");
    require(original.interface()
                    .selectedProtocol()
                    .commonInputRequirements.size() == 2,
            "scoped helper captures lost independent input requirements");
  });
  cases.run(
      "every concrete generic helper derives its own role-permuted inventory",
      [] {
        auto original = compile(R"(module m;
struct State{pub empty:(),pub flag:bool}
protocol Choose<T:Type+Copy+Drop> roles(A,B)(s:State@(A,B),x:T@(A,B))->(r:T@(A,B)){
 let r=if s.flag{x}else{x};return(r=r);
}
protocol Run roles(P,V)(s:State@(P,V),x:bool@(P,V),n:index@(P,V))->(r:bool@(P,V),t:index@(P,V)){
 let r=Choose<bool> roles(V,P)(s,x);let t=Choose<index> roles(P,V)(s,n);return(r=r,t=t);
})");
        auto view =
            take(readInterface(original.bytes(), original.interfaceJson()));
        require(view.protocols.size() == 3,
                "closed helper instantiations were omitted");
        for (const auto &p : view.protocols)
          require(
              p.commonInputRequirements.size() == 1 &&
                  p.commonInputRequirements[0].components[0].path[0].index == 1,
              "helper inventory used root slots or lost zero-width field");
        auto v = take(json::parse(original.interfaceJson()));
        unsigned helper = view.selected == 0 ? 1 : 0;
        inventory(v, helper).clear();
        refuses(readInterface(original.bytes(), zkc::printJson(v)),
                "source.interface");
      });
  cases.run(
      "nested placed records keep exact role applications and empty fields",
      [] {
        auto original = compile(R"(struct Inner roles(A,B):
    pub unrelated: bool @B
    pub flag: bool @(A,B)
    pub empty: () @A
struct Outer roles(X,Y):
    pub prefix: bool @X
    pub nested: Inner roles(Y,X)
    pub empty: () @Y
pub protocol Run roles(P,V)(state: Outer roles(V,P)) -> bool @(P,V):
    result = if state.nested.flag:
        true
    else:
        false
    return result
)",
                                true);
        auto view =
            take(readInterface(original.bytes(), original.interfaceJson()));
        const auto &rs = view.selectedProtocol().commonInputRequirements;
        require(
            rs.size() == 1 && rs[0].components[0].path.size() == 2 &&
                rs[0].components[0].path[0].index == 1 &&
                rs[0].components[0].path[1].index == 1,
            "placed source path was flattened or role-permuted incorrectly");
        mutate(original, [](auto &v) {
          component(v)["path"] =
              json::Array{json::Object{{"kind", "field"}, {"index", 0}}};
        });
      });
  cases.run(
      "ordinary children preserve independence from enclosing custody", [] {
        auto original = custodyOriginal();
        const auto &p = original.interface().selectedProtocol();
        require(p.inputs[0].schema->custody == 2 &&
                    p.commonInputRequirements.size() == 1 &&
                    p.commonInputRequirements[0].components[0].path.size() == 1,
                "ordinary field was identified with enclosing custody");
      });
  cases.run("connected equality classes do not depend on spanning edges", [] {
    std::vector<InterfaceCommonRequirement> expected;
    for (bool chain : {true, false}) {
      std::string second = chain ? "@(V=b,Q=c)" : "@(P=a,Q=c)";
      std::string roles = chain ? "V,Q" : "P,Q";
      auto original = compile(
          "module m;protocol Run roles(P,V,Q)(a:bool@P,b:bool@V,c:bool@Q)->(){"
          "let f=@(P=a,V=b);let g=" +
          second +
          ";if f roles(P,V) {}else{}"
          "if g roles(" +
          roles + ") {}else{}return();}");
      const auto &rs =
          original.interface().selectedProtocol().commonInputRequirements;
      require(rs.size() == 1 && rs[0].components.size() == 3,
              "connected class was not completed");
      if (chain)
        expected = rs;
      else
        require(rs[0].components == expected[0].components,
                "chain and star produced different canonical classes");
      mutate(original, [](auto &v) {
        auto r = inventory(v)[0];
        auto &cs = *inventory(v)[0].getAsObject()->getArray("components");
        cs.pop_back();
        auto &other = *r.getAsObject()->getArray("components");
        other.erase(other.begin());
        inventory(v).push_back(std::move(r));
      });
    }
    auto original = compile(booleanSource);
    mutate(original, [](auto &v) {
      auto &rs = inventory(v);
      auto cs = *rs[1].getAsObject()->getArray("components");
      for (auto &c : cs)
        rs[0].getAsObject()->getArray("components")->push_back(std::move(c));
      rs.pop_back();
    });
  });
  int result = cases.result();
  if (!result && argc == 2) {
    auto emit = [&](StringRef stem, StringRef source,
                    const CheckedOriginal &original) {
      for (auto [suffix, bytes] :
           {std::pair<StringRef, StringRef>{".zkc", source},
            {".mlir", original.bytes()},
            {".json", original.interfaceJson()}}) {
        std::error_code ec;
        raw_fd_ostream out(
            std::string(argv[1]) + "/" + stem.str() + suffix.str(), ec);
        require(!ec, "cannot write fresh common-input fixture");
        out << bytes;
      }
    };
    emit("boolean", booleanSource, compile(booleanSource));
    emit("custody-fields", custodySource, custodyOriginal());
  }
  return result;
}
