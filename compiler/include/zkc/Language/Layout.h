#ifndef ZKC_LANGUAGE_LAYOUT_H
#define ZKC_LANGUAGE_LAYOUT_H
#include "zkc/Contracts/Bindings.h"
#include "zkc/Language/Project.h"
#include <map>
#include <variant>
namespace zkc::language {
namespace detail {
class Semantics;
}
struct PolynomialLayout {
  std::string field;
  uint64_t arity;
};
struct QuotientLayout {
  uint64_t modulus;
  uint64_t degree;
};
/// One mathematical SSA leaf: executable native data or a formal algebraic
/// value. The variant makes it impossible to pass a formal type as a BoundType
/// string.
class LayoutLeaf {
public:
  LayoutLeaf(std::string data) : value(std::move(data)) {}
  LayoutLeaf(const char *data) : value(std::string(data)) {}
  LayoutLeaf(PolynomialLayout polynomial) : value(std::move(polynomial)) {}
  LayoutLeaf(QuotientLayout quotient) : value(quotient) {}
  const std::string *data() const { return std::get_if<std::string>(&value); }
  const PolynomialLayout *polynomial() const {
    return std::get_if<PolynomialLayout>(&value);
  }
  const QuotientLayout *quotient() const {
    return std::get_if<QuotientLayout>(&value);
  }
  uint64_t cost() const {
    return data()         ? data()->size() + 1
           : polynomial() ? polynomial()->field.size() + 2
                          : 3;
  }

private:
  std::variant<std::string, PolynomialLayout, QuotientLayout> value;
};
struct Layout;
struct LayoutField {
  std::string name;
  std::shared_ptr<const Layout> layout;
  unsigned offset = 0;
};
struct LayoutAlternative {
  std::string name;
  std::vector<LayoutField> fields;
};
/// A logical source value has one deterministic, bounded native layout.
/// Products flatten in declaration order; variants retain their closed tag.
/// Custody, when present, is the first leaf and is never a user data field.
struct Layout {
  Type type;
  /// Generated nominal identity binds exact source, family and installation.
  std::string generatedIdentity;
  Permissions permissions;
  std::vector<LayoutLeaf> leaves;
  std::vector<LayoutField> fields;
  std::vector<LayoutAlternative> alternatives;
  bool custody = false;
  bool constructible = false;
  /// Includes formal element meaning even when an array has zero leaves.
  bool formal = false;
};
/// Full logical schemas, including nominal identity and member names, are
/// significant across captures. Cache only within an immutable layout phase.
class LayoutIdentities {
  uint64_t &remaining;
  std::map<const Layout *, std::string> cache;

public:
  explicit LayoutIdentities(uint64_t &remaining) : remaining(remaining) {}
  llvm::Expected<std::string> get(const Layout &);
};
struct LayoutSlice {
  unsigned offset;
  std::shared_ptr<const Layout> layout;
};
/// Contextual single-value carrier. Products use one alternative whose payload
/// is exactly flat->leaves in order, including the empty payload for unit.
/// This representation conveys no source constructor or field-access authority.
struct PackedLayout {
  std::shared_ptr<const Layout> flat;
  protocol::BoundType carrier;
  bool product = false;
  std::string alternative;
};
/// A phase-local cache borrowing an immutable checked project or closed Entry.
/// Keep the owner alive. Work accounting and cache state do not move or copy.
class Layouts {
public:
  explicit Layouts(const CheckedProject &, const Limits & = {});
  explicit Layouts(const ClosedEntry &, const Limits & = {});
  ~Layouts();
  Layouts(const Layouts &) = delete;
  Layouts &operator=(const Layouts &) = delete;
  llvm::Expected<std::shared_ptr<const Layout>> get(const Type &);
  llvm::Expected<PackedLayout> packed(const Type &);
  llvm::Expected<std::vector<std::string>>
      kernelArguments(llvm::StringRef, llvm::ArrayRef<Type>);
  /// Select a checked logical product component in the flattened signature.
  /// This computes representation only, not source field-access authority.
  llvm::Expected<LayoutSlice> select(const Declaration &,
                                     const SpecificationSelector &);
  llvm::Expected<LayoutSlice> selectInput(const Declaration &,
                                          const InputSelector &);

private:
  friend class detail::Semantics;
  Layouts(const std::vector<Declaration> &, const Limits &);
  llvm::ArrayRef<Declaration> definitions;
  Limits limits;
  struct State;
  std::unique_ptr<State> state;
  std::map<std::string, std::string> slots;
  std::map<std::string, std::shared_ptr<const Layout>> cache;
  llvm::Error charge(uint64_t);
  llvm::Expected<LayoutSlice> select(llvm::ArrayRef<Port>, unsigned,
                                     llvm::ArrayRef<unsigned>);
  llvm::Expected<std::shared_ptr<const Layout>> build(const Type &, unsigned);
  llvm::Expected<PackedLayout> pack(std::shared_ptr<const Layout>);
  llvm::Expected<Type>
  substitute(const Type &, const std::map<std::string, Type> &, unsigned);
};
} // namespace zkc::language
#endif
