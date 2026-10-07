#ifndef ZKC_LANGUAGE_LAYOUT_H
#define ZKC_LANGUAGE_LAYOUT_H
#include "zkc/Language/Project.h"
#include <map>
namespace zkc::language {
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
  std::vector<std::string> leaves;
  std::vector<LayoutField> fields;
  std::vector<LayoutAlternative> alternatives;
  bool custody = false;
};
class Layouts {
public:
  explicit Layouts(const CheckedProject &, const Limits & = {});
  explicit Layouts(const ClosedEntry &, const Limits & = {});
  llvm::Expected<std::shared_ptr<const Layout>> get(const Type &);

private:
  llvm::ArrayRef<Declaration> definitions;
  Limits limits;
  uint64_t remaining;
  bool initialized = false;
  std::map<std::string, const Declaration *> declarations;
  std::map<std::string, std::string> slots;
  std::map<std::string, std::shared_ptr<const Layout>> cache;
  llvm::Error charge(uint64_t);
  llvm::Expected<std::shared_ptr<const Layout>> build(const Type &, unsigned);
  llvm::Expected<Type>
  substitute(const Type &, const std::map<std::string, Type> &, unsigned);
  const Declaration *declaration(llvm::StringRef) const;
};
} // namespace zkc::language
#endif
