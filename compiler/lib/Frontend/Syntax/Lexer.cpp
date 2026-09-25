#include "Lexer.h"
#include "zkc/Target/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>

using namespace llvm;
namespace zkc::frontend {
bool isName(StringRef value) {
  return !value.empty() && (isAlpha(value.front()) || value.front() == '_') &&
         all_of(value, [](char c) {
           return isAlnum(c) || c == '_' || c == '.' || c == '-';
         });
}

Expected<std::vector<Token>> lex(StringRef text, StringRef filename) {
  if (text.size() > 1024 * 1024)
    return diagnostic(text, filename, 0, "source-limit",
                      "source exceeds 1 MiB");
  std::vector<Token> tokens;
  for (size_t i = 0; i < text.size();) {
    if (isSpace(text[i])) {
      ++i;
      continue;
    }
    size_t start = i;
    TokenKind kind = TokenKind::Punctuation;
    if (text.substr(i).starts_with("//")) {
      kind = TokenKind::Comment;
      i = text.find('\n', i);
      if (i == StringRef::npos)
        i = text.size();
    } else if (text.substr(i).starts_with("/*")) {
      kind = TokenKind::Comment;
      i += 2;
      unsigned depth = 1;
      while (i < text.size() && depth) {
        if (text.substr(i).starts_with("/*")) {
          if (++depth > 64)
            return diagnostic(text, filename, i, "source-depth",
                              "block comment nesting exceeds 64");
          i += 2;
        } else if (text.substr(i).starts_with("*/")) {
          --depth;
          i += 2;
        } else
          ++i;
      }
      if (depth)
        return diagnostic(text, filename, start, "source-comment",
                          "unterminated block comment");
    } else if (text[i] == '"') {
      kind = TokenKind::String;
      bool closed = false;
      ++i;
      while (i < text.size()) {
        if (text[i] == '\\') {
          i += 2;
          continue;
        }
        if (text[i++] == '"') {
          closed = true;
          break;
        }
      }
      if (!closed || i > text.size())
        return diagnostic(text, filename, start, "source-string",
                          "unterminated string");
      StringRef spelling = text.slice(start, i);
      if (!validStringEncoding(spelling))
        return diagnostic(text, filename, start, "source-string",
                          "invalid Unicode in quoted string");
      auto decoded = json::parse(spelling);
      if (!decoded) {
        consumeError(decoded.takeError());
        return diagnostic(text, filename, start, "source-string",
                          "invalid quoted string or escape");
      }
    } else if (isAlpha(text[i]) || text[i] == '_') {
      kind = TokenKind::Name;
      do {
        ++i;
      } while (i < text.size() &&
               (isAlnum(text[i]) || text[i] == '_' ||
                (text[i] == '.' && !text.substr(i).starts_with("..")) ||
                (text[i] == '-' && !text.substr(i).starts_with("->"))));
    } else if (isDigit(text[i])) {
      kind = TokenKind::Number;
      while (i < text.size() && isDigit(text[i]))
        ++i;
      if (i - start > 1 && text[start] == '0')
        return diagnostic(text, filename, start, "source-number",
                          "natural numbers cannot have leading zeroes");
    } else if (text.substr(i).starts_with("->") ||
               text.substr(i).starts_with("::") ||
               text.substr(i).starts_with("==") ||
               text.substr(i).starts_with("=>") ||
               text.substr(i).starts_with(".."))
      i += 2;
    else if (StringRef("{}()[]<>,:;=+*-/%|").contains(text[i]))
      ++i;
    else
      return diagnostic(text, filename, i, "source-character",
                        "unexpected character");
    tokens.push_back({kind, text.slice(start, i), start});
    if (tokens.size() > 262144)
      return diagnostic(text, filename, start, "source-limit",
                        "too many tokens");
  }
  tokens.push_back({TokenKind::End, {}, text.size()});
  return tokens;
}
} // namespace zkc::frontend
