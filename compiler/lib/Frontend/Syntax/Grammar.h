#ifndef ZKC_FRONTEND_SYNTAX_GRAMMAR_H
#define ZKC_FRONTEND_SYNTAX_GRAMMAR_H

#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/StringSwitch.h"

namespace zkc::frontend::grammar {
inline bool identifierStart(char c) {
  return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '_';
}
inline bool identifierContinue(char c) {
  return identifierStart(c) || (c >= '0' && c <= '9');
}
inline bool identifier(llvm::StringRef value) {
  if (value.empty() || !identifierStart(value.front()))
    return false;
  for (char c : value)
    if (!identifierContinue(c))
      return false;
  return true;
}
inline bool reserved(llvm::StringRef word) {
  return llvm::StringSwitch<bool>(word)
      .Cases({"true", "false", "let", "mut", "return"}, true)
      .Cases({"yield", "if", "else", "match", "for", "in"}, true)
      .Cases({"local", "message", "invoke", "loop", "stop"}, true)
      .Cases({"finish", "map", "fold"}, true)
      .Default(false);
}
inline bool declarationStart(llvm::StringRef word) {
  return llvm::StringSwitch<bool>(word)
      .Cases({"pub", "library", "mod", "dependency", "use"}, true)
      .Cases({"association", "interface", "component", "select", "seal"}, true)
      .Cases({"link", "const", "bind", "relation", "derive"}, true)
      .Cases({"configure", "bundle", "struct", "checked", "enum"}, true)
      .Cases({"fn", "protocol", "instance", "entry", "root"}, true)
      .Case("mathematical", true)
      .Default(false);
}
/// These clauses own a parenthesized list rather than calling a declaration.
inline bool listPrefix(llvm::StringRef word) {
  return llvm::StringSwitch<bool>(word)
      .Cases({"roles", "parameters", "dependencies", "inputs", "outputs"}, true)
      .Cases({"carry", "capture", "return", "yield", "at", "requires"}, true)
      .Cases({"using", "attributes", "let", "constructors", "owners"}, true)
      .Case("roots", true)
      .Default(false);
}
inline bool expressionPrefix(llvm::StringRef word) {
  return reserved(word) && word != "true" && word != "false";
}
} // namespace zkc::frontend::grammar
#endif
