#ifndef ZKC_LANGUAGE_FREEPLACES_H
#define ZKC_LANGUAGE_FREEPLACES_H
#include "Internal.h"
#include "Semantics.h"
namespace zkc::language::detail {
struct FreePlace {
  BindingId binding;
  std::vector<unsigned> path;
  bool operator<(const FreePlace &other) const {
    return binding == other.binding ? path < other.path
                                    : binding < other.binding;
  }
};
struct RegionInputs {
  std::set<FreePlace> places;
  std::set<BindingId> writes, services, scoped, domains;
  std::map<FreePlace, Span> occurrences;
};
struct FreePlaceEnvironment {
  std::set<BindingId> data, services, scoped, domains;
  std::function<std::optional<std::pair<BindingId, std::vector<unsigned>>>(
      uint32_t)>
      place;
};
/// Shared control/scoped query. Deferred bodies contribute free places without
/// contributing execution flow. Occurrences survive projection minimization.
std::optional<RegionInputs> queryFreePlaces(Semantics &,
                                            const SyntaxDeclaration &,
                                            const Expression &,
                                            const FreePlaceEnvironment &);
} // namespace zkc::language::detail
#endif
