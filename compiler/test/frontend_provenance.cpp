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
  auto library = semantics::elaborateLibraries(
      std::get<syntax::Module>(resolved.content), text, "<input>");
  if (!library.content) {
    llvm::consumeError(library.content.takeError());
    return 4;
  }
  const auto &entries = library.content->generated.entries;
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
}
