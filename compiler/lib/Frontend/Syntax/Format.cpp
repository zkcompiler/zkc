#include "Grammar.h"
#include "Lexer.h"
#include "zkc/Support/Json.h"

using namespace llvm;
namespace zkc::frontend {
namespace {
bool nameToken(const Token &token) {
  return token.kind == TokenKind::Name ||
         token.kind == TokenKind::RawIdentifier;
}
bool endsExpression(const Token &token, bool member) {
  return (nameToken(token) &&
          (member || token.kind == TokenKind::RawIdentifier ||
           !grammar::expressionPrefix(token.spelling))) ||
         token.kind == TokenKind::Number || token.kind == TokenKind::String ||
         token.is(")") || token.is("]") || token.is("}");
}
bool spaceBetween(const Token *previous, const Token &next, bool member) {
  if (!previous)
    return false;
  StringRef a = previous->spelling, b = next.spelling;
  // Never join two tokens into an arrow, path, range, operator or comment.
  if ((a == "-" && b == ">") || (a == ":" && b == ":") ||
      (a == "." && b == ".") || (a == "=" && (b == "=" || b == ">")) ||
      (a == "/" && (b == "/" || b == "*")) || (a == "*" && b == "/"))
    return true;
  if ((a == "#" && b == "[") || a == "::" || b == "::" || a == "." ||
      b == "." || a == ".." || b == "..")
    return false;
  if (b == "," || b == ";" || b == ":" || b == ")" || b == "]" || b == ">")
    return false;
  if (a == "(" || a == "[" || a == "<" || b == "<")
    return false;
  if (b == "[" && endsExpression(*previous, member))
    return false;
  if (b == "(" &&
      (nameToken(*previous) || previous->kind == TokenKind::String || a == ">"))
    return previous->kind == TokenKind::Name && !member &&
           grammar::listPrefix(a);
  return true;
}
bool continuation(const Token &token) {
  return token.is("else") || token.is(";") || token.is(",") || token.is(")") ||
         token.is("]") || token.is(".") || token.is("[") || token.is("+") ||
         token.is("-") || token.is("*") || token.is("/") || token.is("==");
}
} // namespace

Expected<std::string> formatTokens(ArrayRef<Token> tokens) {
  // Delimiter and path roles come from tokens, independently of declaration
  // nesting. In particular a record literal and a declaration can occur at any
  // depth without relying on a fictitious outer module brace.
  std::vector<size_t> close(tokens.size(), tokens.size()), stack;
  std::vector<bool> member(tokens.size(), false);
  std::vector<bool> siteIntroducer(tokens.size(), false);
  const Token *significant = nullptr;
  for (size_t i = 0; i < tokens.size(); ++i) {
    if (tokens[i].kind == TokenKind::Comment)
      continue;
    member[i] = significant && (significant->is("::") || significant->is("."));
    siteIntroducer[i] = tokens[i].kind == TokenKind::Name &&
                        (tokens[i].is("pure") || tokens[i].is("query") ||
                         tokens[i].is("guard")) &&
                        (!significant || significant->is("{") ||
                         significant->is("}") || significant->is(";"));
    significant = &tokens[i];
    if (tokens[i].is("(") || tokens[i].is("[") || tokens[i].is("<") ||
        tokens[i].is("{"))
      stack.push_back(i);
    else if (tokens[i].is(")") || tokens[i].is("]") || tokens[i].is(">") ||
             tokens[i].is("}")) {
      if (stack.empty())
        return zkc::error("source-format", "unbalanced formatting input");
      close[stack.back()] = i;
      stack.pop_back();
    }
  }
  if (!stack.empty())
    return zkc::error("source-format", "unbalanced formatting input");
  struct Group {
    bool multiline;
    unsigned indent;
  };
  std::vector<Group> groups;
  std::vector<size_t> braceGroups;
  std::optional<size_t> attributeEnd;
  std::string output;
  unsigned indent = 0;
  size_t column = 0;
  const Token *previous = nullptr;
  bool unaryMinus = false;
  constexpr size_t outputLimit = 1024 * 1024;
  bool outputExceeded = false;
  auto newline = [&] {
    // Emitted layout never trails a token. Spaces at this point can belong to
    // a line-comment token and must remain byte-for-byte intact.
    if (!output.empty() && output.back() != '\n')
      output += '\n';
    column = 0;
    previous = nullptr;
  };
  auto emit = [&](StringRef value, bool space) {
    const size_t padding = column == 0 ? indent * 2 : size_t(space);
    if (output.size() > outputLimit || padding > outputLimit - output.size() ||
        value.size() > outputLimit - output.size() - padding) {
      outputExceeded = true;
      return;
    }
    if (column == 0) {
      output.append(indent * 2, ' ');
      column = indent * 2;
    } else if (space) {
      output += ' ';
      ++column;
    }
    output.append(value.data(), value.size());
    auto last = value.rfind('\n');
    column = last == StringRef::npos ? column + value.size()
                                     : value.size() - last - 1;
  };
  for (size_t i = 0; i < tokens.size(); ++i) {
    if (outputExceeded)
      return zkc::error("source-limit", "formatted source exceeds 1 MiB");
    const Token &token = tokens[i];
    if (token.kind == TokenKind::End)
      break;
    if (token.is("#") && i + 1 < tokens.size() && tokens[i + 1].is("["))
      attributeEnd = close[i + 1];
    if (token.kind == TokenKind::Comment) {
      newline();
      emit(token.spelling, false);
      newline();
      continue;
    }
    if (token.is("}")) {
      newline();
      if (!indent || braceGroups.empty())
        return zkc::error("source-format", "unbalanced brace");
      --indent;
      braceGroups.pop_back();
      emit("}", false);
      if (i + 1 < tokens.size() && continuation(tokens[i + 1]))
        previous = &token;
      else
        newline();
      continue;
    }
    if (token.is(")") || token.is("]") || token.is(">")) {
      if (groups.empty())
        return zkc::error("source-format", "unbalanced list");
      auto group = groups.back();
      groups.pop_back();
      if (group.multiline) {
        indent = group.indent;
        newline();
      }
    }
    const bool afterUnaryMinus = unaryMinus;
    unaryMinus = token.is("-") &&
                 !(previous &&
                   endsExpression(*previous, member[previous - tokens.data()]));
    emit(token.spelling,
         !afterUnaryMinus &&
             ((previous && token.is("[") &&
               siteIntroducer[previous - tokens.data()]) ||
              spaceBetween(previous, token,
                           previous && member[previous - tokens.data()])));
    previous = &token;
    if (attributeEnd && *attributeEnd == i) {
      attributeEnd.reset();
      newline();
    }
    if (token.is("{")) {
      braceGroups.push_back(groups.size());
      ++indent;
      newline();
    } else if (token.is(";")) {
      newline();
    } else if (token.is("(") || token.is("[") || token.is("<")) {
      bool multiline = false;
      if (token.is("(")) {
        size_t width = column;
        size_t end = close[i];
        if (end + 2 < tokens.size() && tokens[end + 1].is("->") &&
            tokens[end + 2].is("("))
          end = close[end + 2];
        for (size_t j = i + 1; j <= end && j < tokens.size(); ++j) {
          if (tokens[j].kind == TokenKind::Comment) {
            multiline = true;
            break;
          }
          width += tokens[j].spelling.size() +
                   spaceBetween(&tokens[j - 1], tokens[j], member[j - 1]);
          if (width > 100) {
            multiline = true;
            break;
          }
        }
      }
      groups.push_back({multiline, indent});
      if (multiline) {
        ++indent;
        newline();
      }
    } else if (token.is(",") &&
               ((!groups.empty() && groups.back().multiline) ||
                (!braceGroups.empty() && groups.size() == braceGroups.back())))
      newline();
  }
  if (output.empty() || output.back() != '\n')
    output += '\n';
  if (outputExceeded || output.size() > outputLimit)
    return zkc::error("source-limit", "formatted source exceeds 1 MiB");
  // Layout must preserve every token, including comments and raw spellings.
  // Re-lexing is sufficient here: no second source parse or semantic analysis.
  auto formatted = lex(output, "<formatter>");
  if (!formatted)
    return formatted.takeError();
  if (formatted->size() != tokens.size())
    return zkc::error("source-format-token-loss");
  for (size_t i = 0; i < tokens.size(); ++i)
    if ((*formatted)[i].kind != tokens[i].kind ||
        (*formatted)[i].spelling != tokens[i].spelling)
      return zkc::error("source-format-token-loss");
  return output;
}
} // namespace zkc::frontend
