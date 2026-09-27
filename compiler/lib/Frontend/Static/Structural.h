#ifndef ZKC_FRONTEND_STATIC_STRUCTURAL_H
#define ZKC_FRONTEND_STATIC_STRUCTURAL_H

#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include <optional>

namespace zkc::frontend {
// Symbolic counterpart of the common logical spelling. Leaves may refer to
// scoped parameters; closed admission remains the common reader's judgment.
using LogicalSpelling = protocol::TypeApplication;
inline std::optional<LogicalSpelling> splitLogical(llvm::StringRef text,
                                                   unsigned depth = 0) {
  if (depth > 8)
    return {};
  const auto head = text.take_front(text.find_first_of(":<@"));
  if (const auto *declaration = protocol::typeDeclaration(head);
      head == "variant" || (declaration && !declaration->common)) {
    // Core carriers own their payload grammar and reader bounds. In
    // particular, a variant's encoded nominal table is not a type argument.
    auto carrier = protocol::parseBoundType(text, false, depth);
    if (!carrier) {
      llvm::consumeError(carrier.takeError());
      return {};
    }
    LogicalSpelling result{carrier->kind, {}};
    if (!carrier->identity.empty())
      result.arguments.push_back(carrier->identity);
    return result;
  }
  auto parsed = protocol::splitTypeApplication(text);
  if (!parsed) {
    llvm::consumeError(parsed.takeError());
    return {};
  }
  if (const auto *declaration = protocol::typeDeclaration(parsed->constructor);
      declaration && declaration->common)
    for (size_t i = 0; i < parsed->arguments.size(); ++i) {
      if (i >= declaration->parameters.size())
        return {};
      if (declaration->parameters[i].kind == protocol::StaticKind::Type &&
          !splitLogical(parsed->arguments[i], depth + 1))
        return {};
    }
  return *parsed;
}
inline std::string logicalSpelling(llvm::StringRef constructor,
                                   llvm::ArrayRef<std::string> arguments) {
  if (arguments.empty())
    return constructor.str();
  const auto *declaration = protocol::typeDeclaration(constructor);
  if (arguments.size() == 1 &&
      (!declaration || !declaration->common ||
       (declaration->parameters.size() == 1 &&
        declaration->parameters[0].kind == protocol::StaticKind::Domain)))
    return constructor.str() + ":" + arguments.front();
  std::string result = constructor.str() + "<";
  for (const auto &argument : arguments) {
    if (result.back() != '<')
      result += ",";
    result += argument;
  }
  return result + ">";
}
} // namespace zkc::frontend
#endif
