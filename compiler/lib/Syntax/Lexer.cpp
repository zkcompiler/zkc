#include "Storage.h"
#include "zkc/Source/Names.h"
#include "llvm/ADT/StringExtras.h"
#include <algorithm>
#include <limits>

using namespace llvm;
namespace zkc::syntax::detail {
void lex(Work &work) {
  auto &out = work.storage.tokens;
  StringRef text = work.storage.revision.text();
  size_t offset = 0;
  const size_t end = std::min<size_t>(text.size(), UINT32_MAX);
  auto error = [&](StringRef code, StringRef message, size_t begin) {
    work.error(code, message, uint32_t(begin), uint32_t(offset));
  };
  if (text.size() > work.budget.bytes || text.size() > UINT32_MAX)
    work.exhaust(0);
  while (offset < end && work.charge(1, uint32_t(offset))) {
    if (out.size() + 2 >= work.budget.tokens) {
      work.exhaust(uint32_t(offset));
      break;
    }
    size_t begin = offset;
    TokenKind kind = TokenKind::Punctuation;
    auto scalar = source::decodeSourceScalar(text, offset);
    if (!scalar) {
      ++offset;
      kind = TokenKind::Invalid;
      error("source.unicode", "invalid UTF-8 scalar", begin);
    } else if (text[offset] == ' ' || text[offset] == '\t') {
      kind = TokenKind::Space;
      while (offset < end && (text[offset] == ' ' || text[offset] == '\t')) {
        if (text[offset++] == '\t')
          error("syntax.tab", "tabs are only permitted in strings and comments",
                offset - 1);
      }
    } else if (text[offset] == '\n' || text[offset] == '\r') {
      kind = TokenKind::Newline;
      if (text[offset++] == '\r') {
        if (offset < end && text[offset] == '\n')
          ++offset;
        else
          error("syntax.newline", "expected LF or CRLF line ending", begin);
      }
    } else if (text.substr(offset).starts_with("//")) {
      kind = TokenKind::Comment;
      while (offset < end && text[offset] != '\r' && text[offset] != '\n')
        ++offset;
    } else if (source::sourceIdentifierStart(scalar->value)) {
      kind = TokenKind::Word;
      offset += scalar->bytes;
      while (offset < end) {
        auto next = source::decodeSourceScalar(text, offset);
        if (!next || !source::sourceIdentifierContinue(next->value))
          break;
        offset += next->bytes;
      }
      if (offset - begin > work.budget.identifierBytes)
        error("source.limit", "identifier byte limit exceeded", begin);
      else if (!source::isSourceNFC(text.slice(begin, offset)))
        error("source.nfc", "source identifiers require NFC spelling", begin);
    } else if (isDigit(text[offset])) {
      kind = TokenKind::Number;
      while (offset < end && isDigit(text[offset]))
        ++offset;
    } else if (text[offset] == '"') {
      kind = TokenKind::String;
      ++offset;
      bool closed = false;
      while (offset < end && text[offset] != '\n' && text[offset] != '\r') {
        if (text[offset++] == '"') {
          closed = true;
          break;
        }
        unsigned char byte = text[offset - 1];
        if ((byte < 32 && byte != '\t') || byte > 126 || byte == '\\')
          error("source.string", "expected an unescaped ASCII string",
                offset - 1);
      }
      if (!closed)
        error("source.string", "unterminated string", begin);
    } else {
      offset += scalar->bytes;
      if (scalar->value > 127) {
        if (!source::isMathematicalSymbol(scalar->value) &&
            !source::matchingSourceDelimiter(scalar->value) &&
            !source::isSourceDelimiterCloser(scalar->value)) {
          kind = TokenKind::Invalid;
          error("source.unicode",
                "character is outside the source token profile", begin);
        }
      } else {
        StringRef pair = text.substr(begin, 2);
        if (pair == "::" || pair == ":=" || pair == "->" || pair == "<-" ||
            pair == "==" || pair == "!=" || pair == "=>" || pair == "<=" ||
            pair == ">=" || pair == "&&" || pair == "||" || pair == ".." ||
            pair == "++")
          ++offset;
        else if (!StringRef(";,:(){}@=+-*/^<>[]!.#?|&%")
                      .contains(text[begin])) {
          kind = TokenKind::Invalid;
          error("source.token", "unsupported source character", begin);
        }
      }
    }
    // Trivia and invalid bytes are retained too; malformed UTF-8 cannot hide
    // in comments or strings and later enter a source identity unnoticed.
    if (kind == TokenKind::Comment || kind == TokenKind::String) {
      for (size_t i = begin; i < offset;) {
        auto item = source::decodeSourceScalar(text, i);
        if (!item) {
          work.error("source.unicode", "invalid UTF-8 scalar", i, i + 1);
          ++i;
        } else {
          i += item->bytes;
        }
      }
    }
    if (kind != TokenKind::Space && kind != TokenKind::Comment &&
        offset - begin > work.budget.tokenBytes)
      error("source.limit", "token byte limit exceeded", begin);
    out.push_back({kind, uint32_t(begin), uint32_t(offset)});
    work.charge(offset - begin, uint32_t(begin));
  }
  if (offset < end)
    out.push_back({TokenKind::Invalid, uint32_t(offset), uint32_t(end)});
  out.push_back({TokenKind::End, uint32_t(end), uint32_t(end)});
}

void layout(Work &work) {
  if (work.stopped())
    return;
  auto input = std::move(work.storage.tokens);
  auto &out = work.storage.tokens;
  StringRef text = work.storage.revision.text();
  std::vector<unsigned> indents{0};
  struct Delimiter {
    std::string close;
    unsigned indent;
    uint32_t begin;
  };
  std::vector<Delimiter> delimiters;
  bool lineStart = true, lineHasCode = false, sectionHead = false;
  unsigned column = 0, lineIndent = 0;
  std::optional<Token> previous;
  auto spelling = [&](Token t) { return text.slice(t.begin, t.end); };
  auto marker = [&](TokenKind kind, uint32_t offset) {
    if (out.size() + 4 >= work.budget.tokens) {
      work.exhaust(offset);
      return;
    }
    out.push_back({kind, offset, offset});
  };
  auto outerHead = [](StringRef word) {
    return word == "pub" || word == "#" || declarationKind(word).has_value();
  };
  auto sectionParameters = [&](size_t at) {
    bool parameter = false;
    for (; at < input.size(); ++at) {
      if (!work.charge(1, input[at].begin))
        return false;
      if (input[at].trivia())
        continue;
      if (parameter)
        return spelling(input[at]) == ":";
      if (spelling(input[at]) == ">")
        return true;
      if (input[at].kind != TokenKind::Word)
        return false;
      parameter = true;
    }
    return false;
  };
  for (size_t index = 0; index < input.size(); ++index) {
    auto token = input[index];
    if (out.size() + 4 >= work.budget.tokens)
      work.exhaust(token.begin);
    if (!work.charge(1, token.begin)) {
      if (token.begin < input.back().end)
        out.push_back({TokenKind::Invalid, token.begin, input.back().end});
      out.push_back(input.back());
      break;
    }
    auto value = spelling(token);
    if (token.kind == TokenKind::End) {
      if (lineHasCode)
        marker(TokenKind::LineEnd, token.begin);
      while (indents.size() > 1) {
        marker(TokenKind::Dedent, token.begin);
        indents.pop_back();
      }
      for (const auto &open : delimiters)
        work.error("syntax.delimiter", "unclosed delimiter", open.begin,
                   open.begin);
      out.push_back(token);
      break;
    }
    if (token.kind == TokenKind::Space) {
      if (lineStart)
        column += value.size();
      out.push_back(token);
      continue;
    }
    if (token.kind == TokenKind::Comment) {
      out.push_back(token);
      if (value.contains('\n')) {
        if (delimiters.empty() && lineHasCode)
          marker(TokenKind::LineEnd, token.end);
        lineStart = true;
        lineHasCode = false;
        sectionHead = false;
        column = 0;
      }
      continue;
    }
    if (token.kind == TokenKind::Newline) {
      out.push_back(token);
      if (delimiters.empty() && lineHasCode)
        marker(TokenKind::LineEnd, token.end);
      lineStart = true;
      lineHasCode = false;
      sectionHead = false;
      column = 0;
      continue;
    }
    if (lineStart && !delimiters.empty() &&
        column <= delimiters.front().indent && outerHead(value)) {
      work.error("syntax.delimiter", "unclosed delimiter before declaration",
                 delimiters.front().begin, token.begin);
      delimiters.clear();
      marker(TokenKind::LineEnd, token.begin);
    }
    if (lineStart && delimiters.empty()) {
      if (column > indents.back()) {
        if (column != indents.back() + 4)
          work.error("syntax.indent", "a suite indents by four spaces",
                     token.begin - column, token.begin);
        indents.push_back(column);
        marker(TokenKind::Indent, token.begin);
      } else {
        while (column < indents.back()) {
          indents.pop_back();
          marker(TokenKind::Dedent, token.begin);
        }
        if (column != indents.back())
          work.error("syntax.indent",
                     "dedentation must match an enclosing suite",
                     token.begin - column, token.begin);
      }
    }
    // A spaced section header starts with a typed binder. An ordinary value
    // named section still follows the comparison spacing rule.
    bool tightStatic =
        value == "<" && previous &&
        ((previous->end == token.begin &&
          (previous->kind == TokenKind::Word || spelling(*previous) == ">")) ||
         (sectionHead && sectionParameters(index + 1)));
    sectionHead = lineStart && delimiters.empty() && value == "section";
    if (lineStart)
      lineIndent = column;
    lineStart = false;
    lineHasCode = true;
    std::string closer;
    if (value == "(")
      closer = ")";
    if (value == "[")
      closer = "]";
    if (value == "{")
      closer = "}";
    if (tightStatic)
      closer = ">";
    if (closer.empty()) {
      auto scalar = source::decodeSourceScalar(value, 0);
      auto paired = scalar && scalar->value > 127
                        ? source::matchingSourceDelimiter(scalar->value)
                        : std::nullopt;
      if (paired) {
        // The matching token is encoded from the pinned Unicode scalar.
        uint32_t c = *paired;
        if (c < 0x800) {
          closer += char(0xc0 | (c >> 6));
          closer += char(0x80 | (c & 63));
        } else if (c < 0x10000) {
          closer += char(0xe0 | (c >> 12));
          closer += char(0x80 | ((c >> 6) & 63));
          closer += char(0x80 | (c & 63));
        } else {
          closer += char(0xf0 | (c >> 18));
          closer += char(0x80 | ((c >> 12) & 63));
          closer += char(0x80 | ((c >> 6) & 63));
          closer += char(0x80 | (c & 63));
        }
      }
    }
    if (!closer.empty()) {
      if (delimiters.size() >= work.budget.depth)
        work.exhaust(token.begin);
      else
        delimiters.push_back({closer, lineIndent, token.begin});
    } else if ((!delimiters.empty() && delimiters.back().close == value) ||
               value == ")" || value == "]" || value == "}" ||
               (value == ">" && !delimiters.empty() &&
                delimiters.back().close == ">")) {
      if (delimiters.empty() || delimiters.back().close != value)
        work.error("syntax.delimiter", "unmatched closing delimiter",
                   token.begin, token.end);
      else
        delimiters.pop_back();
    }
    out.push_back(token);
    previous = token;
  }
  if (out.empty() || out.back().kind != TokenKind::End)
    out.push_back(input.back());
}
} // namespace zkc::syntax::detail
