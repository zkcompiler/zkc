#ifndef ZKC_SUPPORT_MLIR_INPUT_H
#define ZKC_SUPPORT_MLIR_INPUT_H

#include "llvm/ADT/StringRef.h"

namespace zkc {
/// Bound textual nesting before the recursive MLIR parser runs. This is only a
/// resource preflight: MLIR still owns syntax and semantic validation. Quoted
/// strings and comments do not contribute delimiters; arrows and affine
/// comparisons do not close/open angle brackets.
inline bool mlirNestingWithinLimit(llvm::StringRef text, unsigned limit = 64) {
  unsigned depth = 0;
  for (size_t i = 0; i < text.size(); ++i) {
    char c = text[i];
    if (c == '"') {
      while (++i < text.size() && text[i] != '"')
        if (text[i] == '\\' && i + 1 < text.size())
          ++i;
      continue;
    }
    if (c == '/' && i + 1 < text.size() && text[i + 1] == '/') {
      while (i + 1 < text.size() && text[i + 1] != '\n')
        ++i;
      continue;
    }
    // Only line comments are skipped; the parser decides other syntax.
    if ((c == '<' || c == '>') &&
        ((i + 1 < text.size() && text[i + 1] == '=') ||
         (c == '>' && i && text[i - 1] == '-')))
      continue;
    if (c == '(' || c == '[' || c == '{' || c == '<') {
      if (++depth > limit)
        return false;
    } else if (c == ')' || c == ']' || c == '}' || c == '>') {
      if (depth)
        --depth;
    }
  }
  return true;
}
} // namespace zkc
#endif
