// A refusal names its stable identifier, and a test compares that identifier
// whole. A substring test passes on a longer identifier that contains the
// expected one -- `library-call` inside `library-call-arity` -- and on a
// rendered file path that happens to contain it.
#ifndef ZKC_TEST_NAMES_H
#define ZKC_TEST_NAMES_H

#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringRef.h"

inline bool namesIdentifier(llvm::StringRef text, llvm::StringRef identifier) {
  auto continues = [](char c) {
    return llvm::isAlnum(c) || c == '_' || c == '-' || c == '.' || c == '/';
  };
  for (size_t at = text.find(identifier); at != llvm::StringRef::npos;
       at = text.find(identifier, at + 1)) {
    size_t end = at + identifier.size();
    if ((at == 0 || !continues(text[at - 1])) &&
        (end == text.size() || !continues(text[end])))
      return true;
  }
  return false;
}

#endif
