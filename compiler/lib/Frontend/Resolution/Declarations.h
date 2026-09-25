#ifndef ZKC_FRONTEND_RESOLUTION_DECLARATIONS_H
#define ZKC_FRONTEND_RESOLUTION_DECLARATIONS_H
#include "Project.h"
namespace zkc::frontend::resolution {
template <typename Module, typename Fn>
void declarationLists(Module &m, Fn each) {
  using K = Declaration::Kind;
  each(m.libraryAssociations, K::Association);
  each(m.libraryInterfaces, K::Interface);
  each(m.libraryComponents, K::Component);
  each(m.libraryLinks, K::Link);
  each(m.librarySelections, K::Selection);
  each(m.constants, K::Constant);
  each(m.functions, K::Function);
  each(m.protocols, K::Protocol);
  each(m.bindings, K::Binding);
  each(m.bundles, K::Bundle);
  each(m.structs, K::Record);
  each(m.enums, K::Enum);
  each(m.imports, K::Relation);
  each(m.relations, K::Relation);
  each(m.relationViews, K::View);
  each(m.configurations, K::Configuration);
  each(m.instances, K::Instance);
  each(m.entries, K::Entry);
}
template <typename Module, typename Fn> void declarations(Module &m, Fn fn) {
  declarationLists(m, [&](auto &items, auto kind) {
    for (auto &item : items)
      fn(item, kind);
  });
}
inline void append(syntax::Module &to, syntax::Module from) {
  auto move = [](auto &target, auto &source) {
    target.insert(target.end(), std::make_move_iterator(source.begin()),
                  std::make_move_iterator(source.end()));
  };
  move(to.libraryIdentities, from.libraryIdentities);
  move(to.libraryAssociations, from.libraryAssociations);
  move(to.libraryInterfaces, from.libraryInterfaces);
  move(to.libraryComponents, from.libraryComponents);
  move(to.libraryLinks, from.libraryLinks);
  move(to.librarySelections, from.librarySelections);
  move(to.constants, from.constants);
  move(to.functions, from.functions);
  move(to.protocols, from.protocols);
  move(to.bindings, from.bindings);
  move(to.bundles, from.bundles);
  move(to.structs, from.structs);
  move(to.enums, from.enums);
  move(to.imports, from.imports);
  move(to.relations, from.relations);
  move(to.relationViews, from.relationViews);
  move(to.configurations, from.configurations);
  move(to.instances, from.instances);
  move(to.entries, from.entries);
  to.entryArguments.merge(from.entryArguments);
  to.instanceParameterAtoms.merge(from.instanceParameterAtoms);
  to.instanceProtocolTerms.merge(from.instanceProtocolTerms);
  to.configurationTerms.merge(from.configurationTerms);
  to.relationViewHeights.merge(from.relationViewHeights);
  to.quotedBases.merge(from.quotedBases);
  to.quotedRelations.merge(from.quotedRelations);
  to.quotedInstances.merge(from.quotedInstances);
  to.quotedInstanceDependencies.merge(from.quotedInstanceDependencies);
  to.quotedSelectors.merge(from.quotedSelectors);
}
} // namespace zkc::frontend::resolution
#endif
