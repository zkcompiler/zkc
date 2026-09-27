#ifndef ZKC_FRONTEND_SEMANTICS_PLACES_H
#define ZKC_FRONTEND_SEMANTICS_PLACES_H

#include "../Syntax/Tree.h"
#include "llvm/ADT/ArrayRef.h"

namespace zkc::frontend::places {
enum class AggregateKind { Record, Product, Array, Scalar };
struct Selection {
  unsigned index = 0;
  std::string key;
};
// Each semantic model keeps its own type and permission judgments. This owns
// only the source projection kinds and their static bounds: `.field` selects
// a record field, `.N` a product element and `[N]` a structural array element.
inline std::optional<Selection>
select(const syntax::Projection &step, AggregateKind kind, size_t arity,
       llvm::ArrayRef<std::string> fields = {}) {
  using P = syntax::Projection::Kind;
  if (step.kind == P::Field) {
    if (kind != AggregateKind::Record)
      return std::nullopt;
    for (unsigned i = 0; i < fields.size(); ++i)
      if (fields[i] == step.key)
        return Selection{i, step.key};
    return std::nullopt;
  }
  if (!(step.kind == P::Product && kind == AggregateKind::Product) &&
      !(step.kind == P::Index && kind == AggregateKind::Array))
    return std::nullopt;
  unsigned index;
  if (llvm::StringRef(step.key).getAsInteger(10, index) || index >= arity)
    return std::nullopt;
  return Selection{index, std::to_string(index)};
}
/// The captured alias whose place is the longest ancestor of `place`.
template <typename Alias>
const Alias *capturedAncestor(llvm::ArrayRef<Alias> aliases,
                              const syntax::Place &place) {
  const Alias *best = nullptr;
  for (const auto &alias : aliases)
    if (syntax::ancestor(alias.place, place) &&
        (!best || alias.place.steps.size() > best->place.steps.size()))
      best = &alias;
  return best;
}
} // namespace zkc::frontend::places
#endif
