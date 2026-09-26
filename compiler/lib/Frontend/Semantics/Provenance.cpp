#include "Provenance.h"
#include "../Model/Libraries.h"
#include "../Resolution/Project.h"
#include "llvm/ADT/STLExtras.h"

using namespace llvm;
namespace zkc::frontend::semantics {
void retainQueryMetadata(model::Module &module) {
  auto &dependencies = module.dependencies;
  const auto &resolution = module.resolution;
  const auto &libraries = module.libraries;
  auto &declarations = module.declarations;
  auto &diagnostics = module.diagnostics;
  const auto &uses = module.uses;
  dependencies.clear();
  auto definitionReference = [&](const auto &reference) {
    const auto *d = resolution->lookup(reference.source);
    return reference.source == reference.target && d && d->location &&
           reference.location &&
           d->location->file == reference.location->file &&
           d->location->offset == reference.location->offset &&
           d->location->length == reference.location->length;
  };
  if (resolution) {
    for (const auto &reference : resolution->references) {
      if (definitionReference(reference))
        continue;
      const auto *from = resolution->lookup(reference.source);
      const auto *to = resolution->lookup(reference.target);
      if (from && to)
        dependencies.push_back(
            {reference.signature ? SemanticDependency::Kind::Interface
                                 : SemanticDependency::Kind::Body,
             library::identity(from->identity), library::identity(to->identity),
             reference.location});
    }
    for (auto &d : declarations)
      if (d.scope == ScopeId{0})
        if (const auto *origin = resolution->lookup(d.name)) {
          d.identity = library::identity(origin->identity);
          d.displayName.clear();
          for (const auto &part : origin->identity.module)
            d.displayName += part + "::";
          d.displayName += origin->identity.name;
          dependencies.push_back(
              {SemanticDependency::Kind::DiagnosticProvenance, d.identity,
               d.identity, origin->location});
        }
    for (auto &diagnostic : diagnostics) {
      if (!diagnostic.location)
        continue;
      const resolution::Declaration *owner = nullptr;
      for (const auto &d : resolution->declarations)
        if (d.location && d.location->file == diagnostic.location->file &&
            d.location->offset <= diagnostic.location->offset &&
            diagnostic.location->offset - d.location->offset <
                std::max(size_t(1), d.location->length) &&
            (!owner || d.location->length < owner->location->length))
          owner = &d;
      if (owner && diagnostic.causes.empty())
        diagnostic.causes.push_back(
            {DiagnosticCause::Kind::Declaration,
             library::identity(owner->identity),
             "declaration containing the primary location", owner->location});
      for (const auto &reference : resolution->references) {
        if (definitionReference(reference) || !reference.location ||
            reference.location->file != diagnostic.location->file ||
            reference.location->offset > diagnostic.location->offset ||
            diagnostic.location->offset - reference.location->offset >=
                std::max(size_t(1), reference.location->length))
          continue;
        const auto *target = resolution->lookup(reference.target);
        if (!target || !target->location)
          continue;
        if (llvm::any_of(diagnostic.causes, [&](const auto &cause) {
              return cause.subject == library::identity(target->identity) &&
                     cause.explanation ==
                         "resolved reference containing the primary location";
            }))
          continue;
        diagnostic.related.push_back(
            {"referenced declaration " + target->identity.name,
             target->location});
        diagnostic.causes.push_back(
            {DiagnosticCause::Kind::Declaration,
             library::identity(target->identity),
             "resolved reference containing the primary location",
             target->location});
      }
      // A resolved call is concrete provenance even when checking that call
      // failed. Do not guess a target from the diagnostic's rendered text.
      for (const auto &use : uses) {
        if (!use.location || use.location->file != diagnostic.location->file ||
            use.location->offset != diagnostic.location->offset ||
            use.target.index >= declarations.size())
          continue;
        // Generated forwarding uses inherit their owner's declaration span.
        // That is useful for navigation, but it is not an authored call site
        // from which a diagnostic should infer a referenced declaration.
        if (use.owner.index < declarations.size()) {
          const auto &ownerLocation = declarations[use.owner.index].location;
          if (ownerLocation && ownerLocation->file == use.location->file &&
              ownerLocation->offset == use.location->offset &&
              ownerLocation->length == use.location->length)
            continue;
        }
        const auto &target = declarations[use.target.index];
        if (target.location && diagnostic.related.empty())
          diagnostic.related.push_back(
              {"referenced declaration " + (target.displayName.empty()
                                                ? target.name
                                                : target.displayName),
               target.location});
      }
    }
  }
  for (const auto &use : uses)
    if (use.owner.index < declarations.size() &&
        use.target.index < declarations.size()) {
      const auto &owner = declarations[use.owner.index];
      const auto &target = declarations[use.target.index];
      if (!owner.identity.empty() && !target.identity.empty())
        dependencies.push_back({SemanticDependency::Kind::Body, owner.identity,
                                target.identity, use.location});
    }
  if (!libraries)
    return;
  auto bodyDependencies = [&](const auto &bodies) {
    for (const auto &[name, body] : bodies)
      for (const auto &import : body.imports())
        dependencies.push_back({SemanticDependency::Kind::Interface,
                                library::identity(body.body().id),
                                import.interface.identity(),
                                {}});
  };
  bodyDependencies(libraries->clients);
  bodyDependencies(libraries->componentBodies);
  for (const auto &[name, link] : libraries->links) {
    // Link/layout depends on exact implementation and capture content. The
    // fingerprints in the library view are conveniences, not equality keys.
    for (const auto &d : link.dependencies()) {
      dependencies.push_back({SemanticDependency::Kind::Interface,
                              d.normalizedSelection,
                              d.interfaceIdentity,
                              {}});
      dependencies.push_back({SemanticDependency::Kind::LinkLayout,
                              d.normalizedSelection,
                              d.implementationIdentity,
                              {}});
      dependencies.push_back({SemanticDependency::Kind::LinkLayout,
                              d.normalizedSelection,
                              d.captureIdentity,
                              {}});
    }
    for (const auto &e : link.evidence())
      if (!e.subject.empty())
        dependencies.push_back(
            {SemanticDependency::Kind::Evidence,
             resolution && resolution->lookup(name)
                 ? library::identity(resolution->lookup(name)->identity)
                 : link.identity(),
             e.subject,
             {}});
  }
}
} // namespace zkc::frontend::semantics
