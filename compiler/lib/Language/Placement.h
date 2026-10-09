#ifndef ZKC_LANGUAGE_PLACEMENT_H
#define ZKC_LANGUAGE_PLACEMENT_H
#include "Semantics.h"
namespace zkc::language::detail {
/// A temporary availability formula: roles intersected with singleton owners.
/// Mathematical bodies use roles as parameter dependencies and have no owners.
struct Components {
  std::vector<unsigned> roles;
  std::vector<unsigned> owners;
  Components(std::initializer_list<unsigned> roles) : roles(roles) {}
  Components(std::vector<unsigned> roles = {}) : roles(std::move(roles)) {}
};

/// One authored statement. Selection constraints choose owners; formation
/// obligations only admit the already selected solution. Neither survives into
/// the checked Body.
class Placement {
public:
  Placement(Semantics &types, const Declaration &decl,
            std::vector<unsigned> roster, const Placement *enclosing = nullptr)
      : enclosing(enclosing), types(types), decl(decl),
        roster(std::move(roster)) {}
  std::optional<Components> owner(Span);
  std::optional<Components> intersect(llvm::ArrayRef<Components>, Span);
  bool form(const Components &, Span);
  bool demand(const Components &, llvm::ArrayRef<unsigned>, Span);
  bool together(const Components &, const Components &, Span);
  bool solve();
  std::vector<unsigned> resolve(const Components &);
  unsigned selected(unsigned variable);
  std::map<unsigned, Components> values;
  std::vector<std::pair<unsigned, unsigned>> calls;
  std::vector<unsigned> applications;
  const Placement *enclosing;

private:
  struct Variable {
    unsigned parent, rank = 0;
    std::vector<unsigned> domain;
    Span origin, reason;
  };
  Semantics &types;
  const Declaration &decl;
  std::vector<unsigned> roster;
  std::vector<Variable> variables;
  std::vector<std::pair<Components, Span>> formation;
  unsigned root(unsigned);
  bool narrow(unsigned, llvm::ArrayRef<unsigned>, Span);
  bool unite(unsigned, unsigned, Span);
  bool nonempty(const Components &, Span);
};
} // namespace zkc::language::detail
#endif
