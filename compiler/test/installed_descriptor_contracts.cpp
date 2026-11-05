#include "../lib/Language/Checker.h"
#include "support/NativeCases.h"
#include "zkc/Language/Builtins.h"

using namespace llvm;
using namespace zkc::language;
using namespace zkc::language::detail;
using namespace zkc::protocol;
using zkc::test::require;
using zkc::test::take;

namespace {
Expected<CheckedProject> check(StringRef source) {
  CaptureOptions options;
  options.format = "zkc-layout";
  return analyze(take(capture({{"m", source.str(), "descriptor-index.zkc"}},
                              options)))
      .checkedProject();
}
SyntaxType named(StringRef name, std::vector<SyntaxType> arguments = {}) {
  SyntaxType result;
  result.name = name.str();
  result.arguments = std::move(arguments);
  return result;
}
SyntaxType leaf(StringRef name = "bool") {
  auto result = named("finite", {named(name)});
  result.kind = SyntaxType::Kind::Builtin;
  return result;
}
SyntaxType natural(StringRef value) {
  auto result = named(value);
  result.kind = SyntaxType::Kind::Natural;
  return result;
}
ResolvedReference select(const CheckedProject &project, StringRef name) {
  auto module = project.declarationIndex().canonical("m");
  require(bool(module), "missing test module");
  auto result = project.declarationIndex().lookup(SourceAccess{*module}, name);
  require(std::holds_alternative<ResolvedReference>(result),
          "lookup refused " + name);
  return std::get<ResolvedReference>(result);
}
std::optional<Type> form(CheckedProject &project, const SyntaxType &term,
                         StringRef diagnostic = {}) {
  auto storage = DeclarationAccess::storage(project);
  Limits limits;
  Work work{limits};
  auto module = *project.declarationIndex().canonical("m");
  Checker checker(storage, work, SourceAccess{module});
  auto result = checker.type(storage.declarations[module.index], term);
  if (!diagnostic.empty()) {
    require(!result && bool(checker.types.diagnostic), "expected head refusal");
    auto message = checker.types.diagnostic->code + ": " +
                   checker.types.diagnostic->message;
    require(namesIdentifier(message, diagnostic),
            "unexpected refusal: " + message);
  } else if (!result) {
    throw std::runtime_error(checker.types.diagnostic->code + ": " +
                             checker.types.diagnostic->message);
  }
  return result;
}
} // namespace

int main() {
  zkc::test::Cases cases;
  cases.run(
      "ordinary import routes retain the exact immutable association", [] {
        auto project = take(check("use zkc::descriptor as ds\n"
                                  "use ds as again\n"
                                  "use ds::{Product, fold}\n"));
        const auto &index = project.declarationIndex();
        for (StringRef route : {"Product", "again::Product", "ds::Product",
                                "zkc::descriptor::Product"}) {
          auto ref = select(project, route);
          auto id = *index.canonical("zkc::descriptor::Product");
          require(ref.target.index == id.index &&
                      ref.category == ResolutionCategory::ContractConstructor &&
                      index.association(id) ==
                          frontendDeclaration("zkc::descriptor::Product") &&
                      index.constructorAssociation(id) ==
                          index.association(id)->contractHead(),
                  "alias changed installed head authority");
        }
        auto scheme = select(project, "again::fold");
        require(scheme.category == ResolutionCategory::ViewScheme &&
                    index.schemeAssociation(scheme.target) &&
                    index.schemeDefinition(scheme.target)->form ==
                        DescriptorForm::Fold &&
                    index.schemeAssociation(scheme.target) ==
                        index.association(scheme.target)->viewScheme() &&
                    !index.ruleAssociation(scheme.target),
                "scheme did not join through the same index");
        auto storage = DeclarationAccess::storage(project);
        const auto &shell = storage.declarations[scheme.target.index];
        require(shell.inputs.empty() && shell.outputs.empty() && !shell.body &&
                    shell.parameters.size() == 1 &&
                    shell.parameters[0].sort == Parameter::Sort::Natural,
                "scheme acquired a concrete telescope or fake result");
        Limits limits;
        Work work{limits};
        auto module = *index.canonical("m");
        Checker checker(storage, work, SourceAccess{module});
        require(
            !checker.callable(storage.declarations[module.index], "fold", {}),
            "bare scheme became a concrete callable");
        require(namesIdentifier(checker.types.diagnostic->code + ": " +
                                    checker.types.diagnostic->message,
                                "source.descriptor-scheme"),
                "scheme consumer handoff lost its typed refusal");
      });
  cases.run(
      "head formation preserves order, nesting and exact optional Nat", [] {
        auto project = take(check("use zkc::descriptor as ds\n"));
        auto unit = *form(project, named("ds::Product"));
        auto pair =
            *form(project, named("ds::Product", {leaf(), leaf("index")}));
        auto reverse =
            *form(project, named("ds::Product", {leaf("index"), leaf()}));
        auto unsized = *form(project, named("ds::Sequence", {leaf()}));
        auto zero =
            *form(project, named("ds::Sequence", {leaf(), natural("0")}));
        auto two =
            *form(project, named("ds::Sequence", {leaf(), natural("2")}));
        auto nested = *form(
            project, named("ds::Product", {named("ds::Sequence", {leaf()}),
                                           named("ds::Product")}));
        require(unit.kind == Type::Kind::DescriptorProduct &&
                    unit.arguments.empty() && pair.arguments.size() == 2 &&
                    isDescriptor(nested) &&
                    typeIdentity(pair) != typeIdentity(reverse) &&
                    typeIdentity(unsized) != typeIdentity(zero) &&
                    typeIdentity(zero) != typeIdentity(two),
                "structural contract identity collapsed");
        auto old = *form(project, leaf("index"));
        require(typeIdentity(old) == "22:0:0:0:1:01:11:3:0:0:1:00:",
                "valid old Finite identity changed");
      });
  cases.run("real layout application reaches the indexed head", [] {
    auto project = take(check("use zkc::descriptor as ds\n"
                              "type Leaf = builtin(\"finite\", bool)\n"
                              "type Pair = ds::Product<Leaf, Leaf>\n"
                              "type Fixed = ds::Sequence<Leaf, 2>\n"));
    const auto &storage = DeclarationAccess::storage(project);
    for (StringRef name : {"m::Pair", "m::Fixed"}) {
      auto id = *project.declarationIndex().canonical(name);
      require(isDescriptor(storage.declarations[id.index].domain),
              "layout parser bypassed head formation");
    }
  });
  cases.run(
      "head arguments refuse categories arities holes and named slots", [] {
        auto project = take(check("use zkc::descriptor as ds\n"));
        for (auto term :
             {named("ds::Product", {named("bool")}), named("ds::Sequence"),
              named("ds::Sequence", {leaf(), natural("1"), natural("2")}),
              named("ds::Sequence", {leaf(), named("bool")}),
              named("ds::Sequence", {leaf(), leaf()})})
          form(project, term, "source.descriptor");
        auto hole = named("_");
        hole.kind = SyntaxType::Kind::Hole;
        form(project, named("ds::Product", {hole}), "source.inference");
        auto labeled = named("ds::Product", {leaf()});
        labeled.labels.push_back({0, "child", {}});
        form(project, labeled, "source.descriptor");
        form(project, named("ds::append"), "source.descriptor-scheme");
        zkc::test::refuses(builtinType("descriptor_product", {}),
                           "source.descriptor");
        zkc::test::refuses(builtinType("descriptor_sequence", {}),
                           "source.descriptor");
      });
  cases.run(
      "foreign homonyms retain ordinary categories and selected routes are "
      "terminal",
      [] {
        auto project = take(check("use zkc::descriptor as ds\n"
                                  "type Product = bool\n"
                                  "type append = bool\n"));
        auto head = select(project, "Product");
        auto scheme = select(project, "append");
        require(
            !project.declarationIndex().association(head.target) &&
                !project.declarationIndex().schemeAssociation(scheme.target) &&
                head.category == ResolutionCategory::Type &&
                *form(project, named("Product")) == Type(Type::Kind::Boolean),
            "foreign source spelling gained installation authority");
        auto miss = project.declarationIndex().lookup(
            SourceAccess{*project.declarationIndex().canonical("m")},
            "ds::Missing");
        require(std::holds_alternative<LookupFailure>(miss) &&
                    std::get<LookupFailure>(miss).selected &&
                    std::get<LookupFailure>(miss).selected->index ==
                        project.declarationIndex()
                            .canonical("zkc::descriptor")
                            ->index,
                "selected installed root fell back");
      });
  cases.run("private import aliases use ordinary visibility", [] {
    CaptureOptions options;
    options.format = "zkc-layout";
    auto project =
        take(analyze(take(capture({{"m", "use library as lib\n", "client.zkc"},
                                   {"library", "use zkc::descriptor as ds\n",
                                    "library.zkc"}},
                                  options)))
                 .checkedProject());
    auto result = project.declarationIndex().lookup(
        SourceAccess{*project.declarationIndex().canonical("m")},
        "lib::ds::Product");
    require(std::holds_alternative<LookupFailure>(result) &&
                std::get<LookupFailure>(result).kind ==
                    LookupFailureKind::Inaccessible,
            "private alias became an alternate descriptor namespace");
  });
  cases.run(
      "a copied row cannot authorize a captured or installed homonym", [] {
        auto project = take(check("use zkc::descriptor as ds\n"));
        const auto &storage = DeclarationAccess::storage(project);
        auto target =
            *project.declarationIndex().canonical("zkc::descriptor::Product");
        auto copied = *storage.declarations[target.index].installedDeclaration;
        for (bool captured : {false, true}) {
          DeclarationIndex index;
          for (unsigned i = 0; i <= target.index; ++i) {
            auto declaration = storage.declarations[i];
            auto origin =
                (*storage.sources)[declaration.span.source.index].origin;
            if (i != target.index) {
              require(index.add(declaration, origin),
                      "control index formation failed");
              continue;
            }
            declaration.installedDeclaration = &copied;
            require(!index.add(declaration,
                               captured ? SourceOrigin::Captured : origin),
                    "copied catalog value granted installation authority");
            require(!index.association(target) &&
                        !index.canonical(declaration.qualifiedName),
                    "failed index admission retained a partial association");
            require(index.add(storage.declarations[i], origin),
                    "refused row corrupted ordinary index formation");
          }
        }
      });
  for (StringRef name : {"Product", "Sequence", "append", "fold"})
    for (unsigned mutation = 0; mutation < 22; ++mutation)
      cases.run("installation drift " + name + " " + Twine(mutation), [&] {
        auto project = take(check("use zkc::descriptor as ds\n"));
        auto &storage =
            const_cast<CheckedStorage &>(DeclarationAccess::storage(project));
        auto id = *project.declarationIndex().canonical(
            ("zkc::descriptor::" + name).str());
        auto &decl = storage.declarations[id.index];
        auto copied = *decl.installedDeclaration;
        if (mutation == 0)
          decl.installedDeclaration = &copied;
        if (mutation == 1)
          decl.installedDeclaration = nullptr;
        if (mutation == 2)
          decl.kind = Declaration::Kind::View;
        if (mutation == 3) {
          auto sources =
              std::make_shared<std::vector<SourceBuffer>>(*storage.sources);
          (*sources)[decl.span.source.index].module = "foreign";
          storage.sources = std::move(sources);
        }
        if (mutation == 4)
          decl.outputs.push_back({"fake", Type(Type::Kind::Boolean), {}, {}});
        if (mutation == 5)
          decl.domain = Type(Type::Kind::Field);
        if (mutation == 6)
          decl.descriptorResult =
              DescriptorContract(Type(Type::Kind::DescriptorProduct));
        if (mutation == 7) {
          Parameter parameter;
          parameter.sort = Parameter::Sort::Type;
          parameter.name = "fake";
          decl.parameters.push_back(std::move(parameter));
        }
        if (mutation == 8)
          decl.origin = DeclarationId{0};
        if (mutation == 9)
          decl.staticArguments.push_back(Type(Type::Kind::Boolean));
        if (mutation == 10)
          decl.scopedArguments.push_back(DeclarationId{0});
        if (mutation == 11)
          decl.symbol = "foreign";
        if (mutation == 12)
          decl.target = DeclarationId{0};
        if (mutation == 13)
          decl.specificationBlock = Span{};
        if (mutation == 14)
          decl.oraclePredicateOwner = DeclarationId{0};
        if (mutation == 15)
          decl.closureLayout.inputs.push_back(0);
        if (mutation == 16)
          decl.closureLayout.captures.push_back(0);
        if (mutation == 17)
          decl.scopedOrigin = std::make_pair(DeclarationId{0}, uint32_t(0));
        if (mutation == 18)
          decl.configuration = ProofEntry{};
        if (mutation == 19)
          decl.proofFormat = ProofFormat::Native;
        if (mutation == 20) {
          Declaration::Generated generated;
          generated.target = DeclarationId{0};
          decl.generated = std::move(generated);
        }
        if (mutation == 21)
          decl.body = std::make_shared<const Body>();
        auto error = checkScopedElaboration(project);
        require(bool(error) && namesIdentifier(toString(std::move(error)),
                                               "source.installation"),
                "installation drift retained authority");
      });
  return cases.result();
}
