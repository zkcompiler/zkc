#include "Lexer.h"
#include "zkc/Target/Json.h"
#include "llvm/ADT/StringSwitch.h"
#include <algorithm>

using namespace llvm;
namespace zkc::frontend {
namespace {
bool keywordList(StringRef value) {
  return StringSwitch<bool>(value)
      .Cases({"roles", "parameters", "dependencies"}, true)
      .Cases({"inputs", "outputs", "carry", "capture"}, true)
      .Cases({"return", "yield", "at", "requires", "using", "attributes"}, true)
      .Cases({"let", "constructors"}, true)
      .Default(false);
}
bool spaceBetween(const Token *previous, const Token &next,
                  bool previousIsPathMember) {
  if (!previous)
    return false;
  StringRef a = previous->spelling, b = next.spelling;
  // Joining a trailing '-' to '>' would change a name plus delimiter into
  // an arrow token (for example the static argument F- in <F- >).
  if (b == ">" && previous->kind == TokenKind::Name && a.ends_with("-"))
    return true;
  if (a == "::" || b == "::" || a == ".." || b == "..")
    return false;
  if (b == "," || b == ";" || b == ":" || b == ")" || b == "]" || b == ">")
    return false;
  if (a == "(" || a == "[" || a == "<")
    return false;
  if (b == "[" && (previous->kind == TokenKind::Name || a == "]") &&
      !StringSwitch<bool>(a)
           .Cases({"local", "message", "invoke", "loop", "if", "for", "stop"},
                  true)
           .Default(false))
    return false;
  if (b == "<")
    return false;
  if (b == "(" && (previous->kind == TokenKind::Name ||
                   previous->kind == TokenKind::String || a == ">"))
    return previous->kind == TokenKind::Name && !previousIsPathMember &&
           keywordList(a);
  return true;
}
} // namespace

Expected<std::string> formatTokens(ArrayRef<Token> tokens) {
  // This function only receives lexed, parsed documents. Match delimiters once;
  // bounded lookahead then decides which parenthesized lists need line breaks.
  std::vector<size_t> close(tokens.size(), tokens.size()), stack;
  std::vector<bool> pathMember(tokens.size(), false);
  const Token *significant = nullptr;
  for (size_t i = 0; i < tokens.size(); ++i) {
    // Comments and layout do not change a name's role in a qualified path.
    if (tokens[i].kind != TokenKind::Comment) {
      pathMember[i] = significant && significant->is("::") &&
                      tokens[i].kind == TokenKind::Name;
      significant = &tokens[i];
    }
    if (tokens[i].is("(") || tokens[i].is("[") || tokens[i].is("<"))
      stack.push_back(i);
    else if (tokens[i].is(")") || tokens[i].is("]") || tokens[i].is(">")) {
      if (!stack.empty()) {
        close[stack.back()] = i;
        stack.pop_back();
      }
    }
  }
  struct Group {
    bool multiline;
    unsigned indent;
  };
  std::vector<Group> groups;
  std::vector<size_t> braceGroups;
  std::string output;
  unsigned indent = 0, braces = 0;
  size_t column = 0;
  const Token *previous = nullptr;
  bool unaryMinus = false, brokenDeclaration = false, dataDeclaration = false;
  auto newline = [&] {
    while (!output.empty() && output.back() == ' ')
      output.pop_back();
    if (!output.empty() && output.back() != '\n')
      output += '\n';
    column = 0;
    previous = nullptr;
  };
  auto emit = [&](StringRef value, bool space) {
    if (column == 0) {
      output.append(indent * 2, ' ');
      column = indent * 2;
    } else if (space) {
      output += ' ';
      ++column;
    }
    output += value.str();
    auto last = value.rfind('\n');
    column = last == StringRef::npos ? column + value.size()
                                     : value.size() - last - 1;
  };
  for (size_t i = 0; i < tokens.size(); ++i) {
    const Token &token = tokens[i];
    if (token.kind == TokenKind::End)
      break;
    if (token.kind == TokenKind::Comment) {
      newline();
      emit(token.spelling, false);
      newline();
      continue;
    }
    if (token.is("}")) {
      newline();
      --indent;
      --braces;
      braceGroups.pop_back();
      emit("}", false);
      if (i + 1 < tokens.size() &&
          (tokens[i + 1].is("else") || tokens[i + 1].is(";") ||
           tokens[i + 1].is(",") || tokens[i + 1].is(")") ||
           tokens[i + 1].is("]"))) {
        previous = &token;
        continue;
      }
      newline();
      if (braces == 1) {
        output += '\n';
        brokenDeclaration = dataDeclaration = false;
      }
      continue;
    }
    if (token.is(")") || token.is("]") || token.is(">")) {
      if (!groups.empty()) {
        auto group = groups.back();
        groups.pop_back();
        if (group.multiline) {
          indent = group.indent;
          newline();
        }
      }
    }
    if (column == 0 && braces == 1 &&
        (token.is("struct") || token.is("checked") || token.is("bundle")))
      dataDeclaration = true;
    // A minus after a value subtracts; anywhere else it negates and binds to
    // its operand without a space.
    const bool afterUnaryMinus = unaryMinus;
    unaryMinus = token.is("-") &&
                 !(previous && (previous->kind == TokenKind::Name ||
                                previous->kind == TokenKind::Number ||
                                previous->kind == TokenKind::String ||
                                previous->is(")") || previous->is("]")));
    emit(token.spelling,
         !afterUnaryMinus &&
             spaceBetween(previous, token,
                          previous && pathMember[previous - tokens.data()]));
    previous = &token;
    if (token.is("{")) {
      braceGroups.push_back(groups.size());
      ++braces;
      ++indent;
      newline();
    } else if (token.is(";")) {
      newline();
      // A struct or bundle laid out over several lines reads as a block, so
      // it is followed by a blank line as a braced declaration is.
      if (brokenDeclaration && braces == 1)
        output += '\n';
      brokenDeclaration = dataDeclaration = false;
    } else if (token.is("(") || token.is("[") || token.is("<")) {
      bool multiline = false;
      if (token.is("(")) {
        size_t width = column;
        size_t end = close[i];
        // Keep a short return signature with its arguments when possible. If
        // the whole signature is long, break the argument list first.
        if (end + 2 < tokens.size() &&
            (tokens[end + 1].is("->") || tokens[end + 1].is("constructors")) &&
            tokens[end + 2].is("("))
          end = close[end + 2];
        for (size_t j = i + 1; j <= end && j < tokens.size(); ++j) {
          if (tokens[j].kind == TokenKind::Comment) {
            multiline = true;
            break;
          }
          width +=
              tokens[j].spelling.size() +
              (spaceBetween(&tokens[j - 1], tokens[j], pathMember[j - 1]) ? 1
                                                                          : 0);
          if (width > 100) {
            multiline = true;
            break;
          }
        }
      }
      groups.push_back({multiline, indent});
      if (multiline) {
        brokenDeclaration |= dataDeclaration;
        ++indent;
        newline();
      }
    } else if (token.is(",") &&
               ((!groups.empty() && groups.back().multiline) ||
                (!braceGroups.empty() && groups.size() == braceGroups.back())))
      newline();
  }
  while (!output.empty() && (output.back() == ' ' || output.back() == '\n'))
    output.pop_back();
  output += '\n';
  // Do not emit a successful formatting result that our own reader refuses.
  if (output.size() > 1024 * 1024)
    return zkc::error("source-limit", "formatted source exceeds 1 MiB");
  return output;
}
} // namespace zkc::frontend
