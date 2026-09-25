#ifndef ZKC_FRONTEND_INSTANTIATION_SELECT_H
#define ZKC_FRONTEND_INSTANTIATION_SELECT_H

#include "../Syntax/Tree.h"

namespace zkc::frontend::instantiation {
struct DomainArgument {
  std::string name;
  std::string domain;
};
/// Source-only provenance: ordered by emission; arguments follow declaration
/// parameter order. Locations are diagnostic and never enter generated names.
struct Specialization : source::Node {
  std::string definition;
  std::string emitted;
  std::vector<DomainArgument> arguments;
};
struct Selection {
  syntax::Content content;
  std::vector<Specialization> specializations;
  std::map<std::string, uint64_t> constants;
};
/// Pure bounded static construction on a copied syntax snapshot. This performs
/// no dependency loading and does not replace subsequent type/PIR admission.
/// Reserve entry headers supplied separately by prior library elaboration.
llvm::Expected<Selection> select(const syntax::Content &, llvm::StringRef text,
                                 llvm::StringRef filename,
                                 llvm::ArrayRef<std::string> reservedNames);
} // namespace zkc::frontend::instantiation
#endif
