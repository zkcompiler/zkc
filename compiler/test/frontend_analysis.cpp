#include "../lib/Frontend/Resolution/Project.h"
#include "Names.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Compile.h"
#include "zkc/Frontend/Inspection.h"
#include "zkc/Frontend/Loading.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Source/Codec.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc;
using namespace zkc::frontend;

namespace {
unsigned checks = 0;
void require(bool condition, StringRef message) {
  ++checks;
  if (!condition) {
    errs() << "frontend analysis: " << message << '\n';
    std::exit(1);
  }
}
template <typename T> T take(Expected<T> result) {
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
const Declaration &named(const Analysis &analysis, StringRef name) {
  auto found = analysis.lookup(ScopeId{0}, name);
  require(bool(found), "declaration found in module scope");
  return *analysis.declaration(*found);
}

void retainedTypes() {
  std::string text = R"(
module {
  struct Left<F: domain Field>(value: F::Element);
  struct Right<F: domain Field>(value: F::Element);
  fn KeepLeft<F: Field>(value: Left<F>) -> Left<F> { return value; }
  fn KeepRight<F: Field>(value: Right<F>) -> Right<F> { return value; }
  fn Make<F: Field>(value: F::Element) -> Left<F> {
    let result = Left(value = value); return result;
  }
  fn Use<F: Field>(value: F::Element) -> Left<F> {
    let result = Make(value); return result;
  }
})";
  auto analysis = analyzeProtocol(text, "owned.pir");
  require(analysis.complete(), "valid nominal source analyzes");
  auto saved = analysis;
  text.assign("replaced by caller");
  require(saved.sourceText().contains("struct Left"), "snapshot owns spelling");
  const auto &left = named(saved, "KeepLeft");
  const auto &right = named(saved, "KeepRight");
  require(left.inputs.size() == 1 && right.inputs.size() == 1,
          "authored input positions retained");
  const auto *leftType = saved.type(left.inputs[0].type);
  const auto *rightType = saved.type(right.inputs[0].type);
  require(leftType && rightType && leftType->kind == Type::Kind::Record &&
              rightType->kind == Type::Kind::Record,
          "nominal records retained before lowering");
  require(leftType->declaration != rightType->declaration,
          "same-layout records keep distinct declaration identity");
  require(left.parameters.size() == 1 && right.parameters.size() == 1 &&
              left.parameters[0] != right.parameters[0],
          "same-spelled generic parameters belong to different binders");
  require(saved.domain(leftType->arguments[0])->parameter == left.parameters[0],
          "record argument resolves to enclosing function parameter");
  require(!saved.lookup(left.members, "KeepRight"), "lookup is scope-specific");
  require(!saved.type(TypeId{}) && !saved.declaration(DeclId{}),
          "invalid identifiers do not index storage");

  bool foundCall = false, foundConstructor = false;
  for (const auto &use : saved.uses()) {
    require(saved.declaration(use.target) != nullptr, "use target is resolved");
    foundCall |= use.kind == ResolvedUse::Kind::Call &&
                 use.target == named(saved, "Make").id;
    foundConstructor |= use.kind == ResolvedUse::Kind::Construct &&
                        use.target == named(saved, "Left").id;
  }
  require(foundCall && foundConstructor,
          "calls and record constructions resolved");
  auto common = take(saved.lower());
  const auto &module = std::get<source::Module>(common);
  require(module.definitions[0].arguments[0].name == "value.value",
          "emission lays out authored record input");
  source::Document document(common);
  if (auto error = checkProtocolDocument(document)) {
    errs() << toString(std::move(error)) << '\n';
    require(false, "emitted source independently admits");
  }
  require(source::encode(take(saved.lower())) == source::encode(common),
          "repeated lowering is deterministic");
  require(saved.type(left.inputs[0].type)->kind == Type::Kind::Record,
          "lowering does not destroy source type");
}

void checkedSnapshotAndLexicalTypes() {
  const Input input(R"(module {
    struct Pair { x: index, y: index }
    fn Choose(flag: bool, x: index) -> (Pair, ()) {
      let pair = Pair { y: x, x };
      if flag { let inner = pair.x; } else { let inner = pair.y; }
      (pair, ())
    }
  })",
                    "snapshot.pir");
  auto checked = [&] {
    auto analysis = analyzeProtocol(input);
    require(analysis.state() == AnalysisState::SourceChecked,
            "checked state is explicit");
    ScopeId a, b;
    for (const auto &binding : analysis.bindings()) {
      require(binding.scope.valid() &&
                  binding.scope.index < analysis.scopes().size(),
              "binding has a valid lexical scope");
      require(analysis.type(binding.type) != nullptr,
              "binding has a retained source type");
      if (binding.name == "pair")
        require(analysis.type(binding.type)->kind == Type::Kind::Record &&
                    binding.leaves.size() == 2,
                "record binding retains nominal identity and layout");
      if (binding.name == "inner") {
        if (!a.valid())
          a = binding.scope;
        else
          b = binding.scope;
      }
    }
    require(a.valid() && b.valid() && a != b,
            "sibling lexical bindings have distinct scopes");
    for (const auto &use : analysis.valueUses())
      require(use.binding.index < analysis.bindings().size(),
              "value uses resolve to bindings");
    return take(analysis.checkedModule());
  }();
  auto emitted = take(frontend::lower(checked));
  require(std::holds_alternative<source::Module>(emitted),
          "checked snapshot survives analysis destruction");
}

void incompleteCannotEmit() {
  auto analysis = analyzeProtocol(R"(module {
    fn Before(x: bool) -> bool { return x; }
    fn Broken(x: bool) -> bool { let value = ; }
    fn After(x: bool) -> bool { return x; }
  })");
  require(!analysis.complete(), "recovered syntax is not complete analysis");
  require(!analysis.diagnostics().empty(), "recovery retains errors");
  require(bool(analysis.lookup({0}, "Before")),
          "preceding declaration retained");
  require(bool(analysis.lookup({0}, "After")),
          "following declaration retained");
  auto checked = analysis.checkedModule();
  require(!checked, "incomplete analysis cannot manufacture a checked handle");
  consumeError(checked.takeError());
  auto emitted = analysis.lower();
  require(!emitted, "recovery cannot produce complete common source");
  consumeError(emitted.takeError());
  auto view = inspectAnalysis(analysis);
  require(view.getAsObject()->getString("state") == StringRef("incomplete"),
          "tooling reports incomplete state explicitly");
}
void malformedProjectRefuses() {
  auto project = take(ProjectInput::capture(
      {{{{{}, Input("module {}", "root.pir")},
         {{"missing", "child"},
          Input("module { use super::Absent; }", "child.pir")}}}}));
  auto analysis = analyzeProject(project);
  require(!analysis.complete(), "a missing parent is incomplete, not a crash");
  bool missingParent = false;
  for (const auto &diagnostic : analysis.diagnostics())
    missingParent |= diagnostic.code == "source-module-undeclared";
  require(missingParent, "missing parent has a module diagnostic");
  auto lowered = analysis.lower();
  require(!lowered, "malformed project cannot emit code");
  consumeError(lowered.takeError());

  resolution::Context context(project);
  library::Environment environment;
  library::LibraryId owner{"example", "owner", "1", "exact"};
  library::QualifiedDecl declaration{owner, {}, "Visible"};
  environment.libraries.push_back({owner, {declaration}});
  auto unavailable = context.environment(environment, declaration);
  require(unavailable.libraries.empty(),
          "an unknown owner receives no captured declarations");
}
template <typename T>
void refused(Expected<T> result, StringRef code, StringRef what) {
  if (result) {
    require(false, what);
    return;
  }
  auto text = toString(result.takeError());
  require(namesIdentifier(text, code), (what + ": " + text).str());
}
// Capture and resolution guard their inputs even where the command line
// cannot produce the bad shape: these are the direct callers' refusals.
void capturedProjectShapes() {
  refused(ProjectInput::capture({{{{{}, Input("module {}", "m.pir")}}}},
                                {{1, "a.json", ""}}),
          "project-asset-owner", "asset owned by a file that was not captured");
  // Text with no file has no directory to find child modules or assets in.
  refused(captureProject(Input::withoutFile("module {}")),
          "project-source-base", "a project root without a file");
  refused(loadProtocolFile(Input::withoutFile("module {}")),
          "relation-asset-base", "relation assets of a source without a file");
  // Two roots at one canonical path must carry the same bytes.
  refused(captureProject(Input("module {}", __FILE__),
                         {Input("module { }", __FILE__)}),
          "project-source-conflict", "one path captured with two contents");
  auto project = take(ProjectInput::capture(
      {{{{{}, Input("module { mod c; }", "r.pir")},
         {{"c"},
          Input("module { library(namespace=\"t\", name=\"c\", "
                "version=\"1\", resolution=\"r1\"); }",
                "c.pir")}}}}));
  auto analysis = analyzeProject(project);
  bool root = false;
  std::string seen;
  for (const auto &diagnostic : analysis.diagnostics()) {
    root |= diagnostic.code == "source-library-root";
    seen += " " + diagnostic.code;
  }
  require(root, "a child module cannot declare a library identity:" + seen);
}
void constructionSelectorBounds() {
  auto project = ProjectInput::single(Input("module {}", "empty.pir"));
  source::Construction descriptor;
  descriptor.draws.resize(32769, {"Unused", "draw"});
  auto bound = bindConstruction(project, source::Module{}, descriptor);
  require(!bound, "too many selectors fail before project traversal");
  require(toString(bound.takeError()) == "construction-descriptor-limit",
          "selector limit has a stable diagnostic");
}
} // namespace

int main() {
  retainedTypes();
  checkedSnapshotAndLexicalTypes();
  incompleteCannotEmit();
  malformedProjectRefuses();
  capturedProjectShapes();
  constructionSelectorBounds();
  outs() << "frontend semantic analysis: " << checks << " checks passed\n";
}
