#include "Checker.h"

using namespace llvm;
namespace zkc::language::detail {
using K = syntax::Kind;

bool Checker::layoutSpecifications() {
  std::map<unsigned, Span> owners;
  std::set<std::pair<unsigned, std::string>> names;
  for (const auto &module : output.declarations) {
    auto moduleId = module.id;
    for (const auto &formal : sources[moduleId.index]->formalSyntax) {
      if (!formal.subject)
        continue;
      const auto &tree = formal.tree;
      auto span = tree.span(formal.node);
      if (!types.charge(1, span))
        return false;
      auto target = resolve(module, formal.subject->name, formal.subject->span);
      if (!target)
        return false;
      const auto &protocol = output.declarations[target->index];
      if (protocol.kind != Declaration::Kind::Protocol)
        return types.fail("source.spec.subject",
                          "spec subject is not a protocol", span);
      bool owner = formal.name.empty() && protocol.parent &&
                   protocol.parent->index == moduleId.index &&
                   !StringRef(formal.subject->name).contains("::") &&
                   formal.subject->arguments.empty();
      if (owner && !owners.emplace(target->index, span).second)
        return types.fail("source.spec.owner",
                          "protocol has more than one owner spec", span);
      if (!formal.name.empty() &&
          !names.emplace(moduleId.index, formal.name).second)
        return types.fail("source.spec.name",
                          "duplicate named spec in this module", span);
      std::set<std::pair<unsigned, std::string>> labels;
      for (auto child : tree.children(formal.node))
        if (tree.node(child).kind == K::Suite)
          for (auto clause : tree.children(child)) {
            auto kind = tree.node(clause).kind;
            bool contract = kind == K::Requires || kind == K::Ensures ||
                            kind == K::Target || kind == K::Reduces;
            if (contract && !owner)
              return types.fail("source.spec.audit",
                                "consumer specs may request goals but cannot "
                                "change a protocol contract",
                                tree.span(clause));
            // Explicit labels have separate clause, alias and request
            // namespaces.
            auto parts = tree.children(clause);
            if (parts.size() == (kind == K::Reduces ? 3u : 2u) &&
                tree.node(parts.front()).kind == K::Name) {
              unsigned space = contract ? 0 : kind == K::Request ? 1 : 2;
              auto label = tree.text(parts.front()).str();
              if (!labels.emplace(space, label).second)
                return types.fail(
                    "source.spec.label",
                    "duplicate explicit label in this spec namespace",
                    tree.span(parts.front()));
            }
          }
      output.pendingSpecifications.push_back(
          {moduleId, *target, formal.name, owner, formal.isPublic, span});
    }
  }
  return true;
}

} // namespace zkc::language::detail
