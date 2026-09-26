#include "../lib/Frontend/Lowering/LibrarySource.h"
#include "../lib/Frontend/Resolution/Project.h"
#include "../lib/Frontend/Semantics/Libraries.h"
#include "../lib/Frontend/Semantics/Provenance.h"

using namespace zkc;
using namespace zkc::frontend;

int main() {
  // A generated adapter has a declaration location for navigation. It must not
  // turn a diagnostic at that declaration into an authored call-site claim.
  // An actual body call, at a distinct location, retains its related target.
  for (bool generated : {false, true}) {
    model::Module module;
    module.resolution = std::make_shared<const resolution::Context>(
        ProjectInput::single(Input::withoutFile("module {}")));
    const source::Span declaration{10, 20, 0};
    const source::Span call = generated ? declaration : source::Span{15, 3, 0};
    auto owner =
        module.add(Declaration::Kind::Function, {0}, "Alias", declaration);
    auto target = module.add(Declaration::Kind::Function, {0}, "Target",
                             source::Span{50, 10, 0});
    ResolvedUse use;
    use.owner = owner;
    use.target = target;
    use.location = call;
    module.uses.push_back(use);
    module.diagnostics.push_back({"source-type", "test refusal", call});
    semantics::retainQueryMetadata(module);
    const auto &related = module.diagnostics.front().related;
    if (generated ? !related.empty() : related.size() != 1)
      return 1;
    if (!generated && related.front().location->offset != 50)
      return 2;
  }

  // Header formation diagnoses type nodes, not the enclosing function. Every
  // nested node generated for an aggregate alias must retain its source span.
  const char *text = R"(module {
    library(namespace="test", name="locations", version="1", resolution="one");
    fn Echo(x: (Array<bool, 0>, (bool, bool))) -> (Array<bool, 0>, (bool, bool)) {
      return x;
    }
    link Closed = Echo<>;
  })";
  auto project = ProjectInput::single(Input::withoutFile(text));
  auto resolved = resolution::resolve(project);
  if (!resolved.diagnostics.empty())
    return 3;
  WorkBudget budget;
  auto library =
      semantics::elaborateLibraries(std::get<syntax::Module>(resolved.content),
                                    *resolved.context, text, "<input>", budget);
  if (!library.content) {
    llvm::consumeError(library.content.takeError());
    return 4;
  }
  auto &formed = *library.content;
  auto collisionSyntax = formed.ordinary;
  auto prepared = lowering::emitLibrarySource(
      std::move(formed.ordinary), formed.environment, formed.programs,
      formed.entryAliases, formed.reservedNames, *resolved.context, budget);
  if (!prepared) {
    llvm::consumeError(prepared.takeError());
    return 4;
  }
  const auto &entries = prepared->generated.entries;
  if (entries.size() != 2)
    return 5;
  for (const auto &entry : entries) {
    const auto location = entry.header.location;
    if (!location)
      return 6;
    auto located = [&](auto &&self, const syntax::Type &type) -> bool {
      if (!type.location || type.location->offset != location->offset ||
          type.location->length != location->length ||
          type.location->file != location->file)
        return false;
      for (const auto &child : type.arguments)
        if (!self(self, child))
          return false;
      return true;
    };
    for (const auto &argument : entry.header.arguments)
      if (!located(located, argument.type))
        return 7;
    for (const auto &result : entry.header.results)
      if (!located(located, result))
        return 8;
  }

  // Public resolution reserves generated prefixes. Exercise the emitter's
  // defensive collision check directly with the captured offending declaration,
  // without weakening that earlier admission boundary.
  const auto symbol = formed.programs.front().entry();
  std::string collisionText = text;
  collisionText.insert(collisionText.rfind('}'),
                       "fn " + symbol + "(x: bool) -> bool { return x; }\n");
  auto collisionProject =
      ProjectInput::single(Input::withoutFile(collisionText, "collision.pir"));
  auto collisionContext = resolution::resolve(collisionProject);
  bool reserved = false;
  for (const auto &diagnostic : collisionContext.diagnostics)
    reserved |= diagnostic.code == "source-name-reserved";
  if (!reserved)
    return 9;
  formed.reservedNames.insert(symbol);
  WorkBudget collisionBudget;
  auto collision = lowering::emitLibrarySource(
      std::move(collisionSyntax), formed.environment, formed.programs,
      formed.entryAliases, formed.reservedNames, *collisionContext.context,
      collisionBudget);
  if (collision)
    return 10;
  bool located = false;
  llvm::handleAllErrors(collision.takeError(), [&](const SourceDiagnostic &d) {
    located = d.code == "library-source-collision" && d.location.file == 0 &&
              d.location.offset == collisionText.find("fn " + symbol);
  });
  if (!located)
    return 11;
}
