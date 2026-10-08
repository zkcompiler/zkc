#ifndef ZKC_LANGUAGE_LAYOUT_H
#define ZKC_LANGUAGE_LAYOUT_H
#include "zkc/Language/Project.h"
#include <map>
#include <variant>
namespace zkc::language {
struct PolynomialLayout {
  std::string field;
  uint64_t arity;
};
/// One mathematical SSA leaf: executable native data or a formal polynomial.
/// The variant makes it impossible to pass a formal type as a BoundType string.
class LayoutLeaf {
public:
  LayoutLeaf(std::string data) : value(std::move(data)) {}
  LayoutLeaf(const char *data) : value(std::string(data)) {}
  LayoutLeaf(PolynomialLayout polynomial) : value(std::move(polynomial)) {}
  const std::string *data() const { return std::get_if<std::string>(&value); }
  const PolynomialLayout *polynomial() const {
    return std::get_if<PolynomialLayout>(&value);
  }
  uint64_t cost() const {
    return data() ? data()->size() + 1 : polynomial()->field.size() + 2;
  }

private:
  std::variant<std::string, PolynomialLayout> value;
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
  Permissions permissions;
  std::vector<LayoutLeaf> leaves;
  std::vector<LayoutField> fields;
  std::vector<LayoutAlternative> alternatives;
  bool custody = false;
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
  /// Select a checked logical product component in the flattened signature.
  /// This computes representation only, not source field-access authority.
  llvm::Expected<LayoutSlice> select(const Declaration &,
                                     const SpecificationSelector &);
  llvm::Expected<LayoutSlice> selectInput(const Declaration &,
                                          const EntryInput &);

private:
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
  llvm::Expected<Type>
  substitute(const Type &, const std::map<std::string, Type> &, unsigned);
};
} // namespace zkc::language
#endif
