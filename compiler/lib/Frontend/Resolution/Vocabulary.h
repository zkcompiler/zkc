#ifndef ZKC_FRONTEND_RESOLUTION_VOCABULARY_H
#define ZKC_FRONTEND_RESOLUTION_VOCABULARY_H
#include "../Syntax/Types.h"
#include "Names.h"
#include "zkc/Contracts/Bindings.h"
#include "llvm/ADT/STLExtras.h"

namespace zkc::frontend::resolution {
// Read the installed catalogs instead of granting authority to a string prefix.
inline bool installedOperation(llvm::StringRef name) {
  static const auto names = [] {
    std::set<std::string> result;
    for (const auto &op : protocol::boundOperationContracts())
      result.insert(op.name);
    return result;
  }();
  return names.count(name.str());
}
inline bool installedType(llvm::StringRef name) {
  if (name == "Array" || name == "Vector" || name == "Matrix" ||
      name == "ResourceUnit")
    return true;
  for (const auto &t : typeSpellings)
    if (name == t.surface)
      return true;
  return llvm::any_of(protocol::boundTypeConstructors(),
                      [&](const auto &t) { return name == t.name; });
}
inline bool installedName(llvm::StringRef name, ReferenceKind kind,
                          bool quoted) {
  if (kind == ReferenceKind::Call || kind == ReferenceKind::QualifiedCall)
    return installedOperation(name);
  if (kind == ReferenceKind::Type) {
    if (!quoted && installedType(name))
      return true;
    // Closed wire type spellings are admitted by the installed type parser.
    if (quoted) {
      auto parsed = protocol::parseBoundType(name, false);
      if (parsed)
        return true;
      llvm::consumeError(parsed.takeError());
    }
  }
  if (kind == ReferenceKind::Static || kind == ReferenceKind::Type)
    return !protocol::installedIdentitySort(name).empty();
  if (kind == ReferenceKind::Predicate) {
    if (name == "=" || name == "nat" || name == "association")
      return true;
    generic::Signature signature;
    signature.requirements.push_back(
        requirements::Predicate::holds(name.str(), {}));
    auto error = protocol::checkStaticVocabulary(signature);
    return !error ||
           llvm::toString(std::move(error)) != "generic-declared-predicate";
  }
  return false;
}
} // namespace zkc::frontend::resolution
#endif
