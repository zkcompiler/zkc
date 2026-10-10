#ifndef ZKC_LANGUAGE_ARGUMENTS_H
#define ZKC_LANGUAGE_ARGUMENTS_H
#include "Internal.h"
#include "Semantics.h"

namespace zkc::language::detail {
/// Bind authored positions to declaration positions. This never reorders source
/// expressions or evaluates arguments. Missing slots are allowed only when the
/// caller will infer them; a runtime application always requires full coverage.
std::optional<std::vector<unsigned>>
bindArguments(Semantics &, llvm::ArrayRef<llvm::StringRef> parameters,
              unsigned count, llvm::ArrayRef<ArgumentLabel> labels,
              bool complete, Span, llvm::StringRef diagnostic);

template <typename T>
std::vector<llvm::StringRef> argumentNames(llvm::ArrayRef<T> parameters) {
  std::vector<llvm::StringRef> result;
  for (const auto &parameter : parameters)
    result.push_back(parameter.name);
  return result;
}
std::vector<llvm::StringRef> inputNames(const Declaration &);
} // namespace zkc::language::detail
#endif
