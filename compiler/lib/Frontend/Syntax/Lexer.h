#ifndef ZKC_FRONTEND_SYNTAX_LEXER_H
#define ZKC_FRONTEND_SYNTAX_LEXER_H

#include "zkc/Frontend/Diagnostic.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/Error.h"
#include <string>
#include <vector>

namespace zkc::frontend {
enum class TokenKind { Name, Number, String, Punctuation, Comment, End };
struct Token {
  TokenKind kind;
  llvm::StringRef spelling;
  size_t offset;
  bool is(llvm::StringRef value) const {
    return kind != TokenKind::String && kind != TokenKind::Comment &&
           spelling == value;
  }
};

llvm::Expected<std::vector<Token>> lex(llvm::StringRef text,
                                       llvm::StringRef filename);
llvm::Expected<std::string> formatTokens(llvm::ArrayRef<Token> tokens);
bool isName(llvm::StringRef value);
} // namespace zkc::frontend

#endif
