#include "Internal.h"
#include "llvm/ADT/StringExtras.h"
#include <algorithm>

using namespace llvm;
namespace zkc::language::detail {
Error lex(const SourceBuffer &source, ModuleId module, Work &work,
          std::vector<Token> &tokens) {
  StringRef text = source.text;
  size_t offset = 0;
  while (offset < text.size()) {
    size_t begin = offset;
    TokenKind kind;
    char c = text[offset++];
    if (isSpace(c)) {
      kind = TokenKind::Whitespace;
      while (offset < text.size() && isSpace(text[offset]))
        ++offset;
    } else if (c == '/' && offset < text.size() && text[offset] == '/') {
      kind = TokenKind::Comment;
      while (offset < text.size() && text[offset] != '\n')
        ++offset;
    } else if (isAlpha(c) || c == '_') {
      kind = TokenKind::Word;
      while (offset < text.size() &&
             (isAlnum(text[offset]) || text[offset] == '_'))
        ++offset;
      if (isUnsupported(text.slice(begin, offset)))
        return failure("source.unsupported",
                       "feature is outside this source fragment: " +
                           text.slice(begin, offset),
                       Span{module, uint32_t(begin), uint32_t(offset)});
      if (offset - begin > work.limits.identifierBytes)
        return failure("source.limit", "identifier byte limit exceeded",
                       Span{module, uint32_t(begin), uint32_t(offset)});
    } else if (isDigit(c)) {
      kind = TokenKind::Decimal;
      while (offset < text.size() && isDigit(text[offset]))
        ++offset;
    } else if (c == '"') {
      kind = TokenKind::String;
      while (offset < text.size() && text[offset] != '"') {
        unsigned char byte = text[offset++];
        if (byte < 32 || byte > 126 || byte == '\\')
          return failure(
              "source.string",
              "expected unescaped printable ASCII in a domain identity",
              Span{module, uint32_t(begin), uint32_t(offset)});
      }
      if (offset == text.size())
        return failure("source.string", "unterminated string",
                       Span{module, uint32_t(begin), uint32_t(offset)});
      ++offset;
    } else {
      kind = TokenKind::Punctuation;
      if (offset < text.size() && ((c == ':' && text[offset] == ':') ||
                                   (c == '-' && text[offset] == '>') ||
                                   (c == '=' && text[offset] == '=')))
        ++offset;
      else if (StringRef("<>[]!").contains(c))
        return failure("source.unsupported",
                       "generic, aggregate, or effect syntax is not enabled",
                       Span{module, uint32_t(begin), uint32_t(offset)});
      else if (!StringRef(";,:(){}@=+-*").contains(c))
        return failure("source.token", "unsupported source character",
                       Span{module, uint32_t(begin), uint32_t(offset)});
    }
    Span span{module, uint32_t(begin), uint32_t(offset)};
    if (kind != TokenKind::Whitespace && kind != TokenKind::Comment &&
        offset - begin > work.limits.tokenBytes)
      return failure("source.limit", "token byte limit exceeded", span);
    if (auto error =
            work.count(work.tokens, work.limits.tokens, "token count", span))
      return error;
    if (auto error = work.charge(1, span))
      return error;
    tokens.push_back({kind, span});
  }
  Span end{module, uint32_t(offset), uint32_t(offset)};
  if (auto error =
          work.count(work.tokens, work.limits.tokens, "token count", end))
    return error;
  tokens.push_back({TokenKind::End, end});
  return Error::success();
}
namespace {
class Parser {
public:
  Parser(const SourceBuffer &source, ModuleId module, ArrayRef<Token> input,
         Work &work)
      : source(source), module(module), work(work) {
    for (const auto &token : input)
      if (token.kind != TokenKind::Whitespace &&
          token.kind != TokenKind::Comment)
        tokens.push_back(token);
  }
  Expected<SyntaxModule> run() {
    SyntaxModule output{module, {}, {}};
    std::string moduleName;
    if (!expect("module") || !path(moduleName) || !expect(";"))
      return takeError();
    if (moduleName != source.module) {
      fail("source.module",
           "module declaration does not match captured logical name");
      return takeError();
    }
    while (!atEnd() && !diagnostic) {
      if (at("use")) {
        Import import;
        import.span = current().span;
        advance();
        if (!name(import.module))
          break;
        bool separator = false;
        while (take("::")) {
          if (at("{")) {
            separator = true;
            break;
          }
          std::string part;
          if (!name(part))
            break;
          import.module += "::" + part;
        }
        if (diagnostic)
          break;
        if (!separator) {
          fail("source.syntax", "expected '::' before import list");
          break;
        }
        if (!expect("{"))
          break;
        if (at("}")) {
          fail("source.syntax", "import list must be nonempty");
          break;
        }
        do {
          std::string value;
          if (!name(value))
            break;
          import.names.push_back(std::move(value));
        } while (take(",") && !at("}"));
        if (diagnostic || !expect("}") || !expect(";"))
          break;
        import.span.end = previousEnd;
        if (import.module.size() > work.limits.moduleBytes) {
          fail("source.limit", "module path byte limit exceeded");
          break;
        }
        output.imports.push_back(std::move(import));
        continue;
      }
      SyntaxDeclaration declaration;
      declaration.span = current().span;
      declaration.isPublic = take("pub");
      if (take("domain")) {
        declaration.kind = Declaration::Kind::Domain;
        if (!name(declaration.name) || !expect("=") || !expect("field") ||
            !expect("("))
          break;
        if (current().kind != TokenKind::String) {
          fail("source.syntax", "expected installed field identity string");
          break;
        }
        declaration.domain = text().drop_front().drop_back().str();
        advance();
        if (!expect(")") || !expect(";"))
          break;
      } else if (take("entry")) {
        declaration.kind = Declaration::Kind::Entry;
        if (!name(declaration.name) || !expect("=") ||
            !path(declaration.target) || !expect(";"))
          break;
      } else if (take("math")) {
        declaration.kind = Declaration::Kind::Math;
        if (!expect("fn") || !name(declaration.name) ||
            !ports(declaration.inputs, false) || !expect("->"))
          break;
        SyntaxType result;
        if (!type(result))
          break;
        declaration.outputs.push_back(
            {"result", std::move(result), {}, current().span});
        if (!body(declaration, false))
          break;
      } else if (take("protocol")) {
        declaration.kind = Declaration::Kind::Protocol;
        if (!name(declaration.name) || !expect("roles") ||
            !roleList(declaration.roles, true) ||
            !ports(declaration.inputs, true) || !expect("->") ||
            !ports(declaration.outputs, true) || !body(declaration, true))
          break;
      } else {
        fail("source.syntax",
             "expected domain, math fn, protocol, or entry declaration");
        break;
      }
      declaration.span.end = previousEnd;
      if (!accept(work.count(work.declarations, work.limits.declarations,
                             "declaration count", declaration.span)))
        break;
      output.declarations.push_back(std::move(declaration));
    }
    if (diagnostic)
      return takeError();
    return output;
  }

private:
  const SourceBuffer &source;
  ModuleId module;
  Work &work;
  std::vector<Token> tokens;
  size_t cursor = 0;
  uint32_t previousEnd = 0;
  std::optional<Diagnostic> diagnostic;
  const Token &current() const { return tokens[cursor]; }
  StringRef text() const {
    auto span = current().span;
    return StringRef(source.text).slice(span.begin, span.end);
  }
  bool at(StringRef value) const { return text() == value; }
  bool atEnd() const { return current().kind == TokenKind::End; }
  void advance() {
    previousEnd = current().span.end;
    if (!atEnd())
      ++cursor;
  }
  bool take(StringRef value) {
    if (!at(value))
      return false;
    advance();
    return true;
  }
  bool fail(StringRef code, const Twine &message) {
    if (!diagnostic)
      diagnostic = Diagnostic{code.str(), message.str(), current().span, {}};
    return false;
  }
  bool expect(StringRef value) {
    return take(value) || fail("source.syntax", "expected '" + value + "'");
  }
  bool accept(Error error) {
    bool success = !error;
    handleAllErrors(std::move(error), [&](const DiagnosticError &value) {
      diagnostic = value.diagnostic();
    });
    return success;
  }
  Error takeError() { return make_error<DiagnosticError>(*diagnostic); }
  bool name(std::string &output) {
    if (current().kind != TokenKind::Word || isReserved(text()))
      return fail("source.name", "expected non-reserved identifier");
    output = text().str();
    advance();
    return true;
  }
  bool path(std::string &output) {
    if (!name(output))
      return false;
    while (take("::")) {
      std::string part;
      if (!name(part))
        return false;
      output += "::" + part;
    }
    return output.size() <=
               work.limits.moduleBytes + work.limits.identifierBytes + 2 ||
           fail("source.limit", "qualified name byte limit exceeded");
  }
  bool type(SyntaxType &output) {
    output.span = current().span;
    if (take("bool"))
      output.name = "bool";
    else if (!path(output.name))
      return false;
    output.span.end = previousEnd;
    return true;
  }
  bool roleList(std::vector<std::string> &roles, bool parenthesized = false) {
    bool parens = take("(");
    if (parenthesized && !parens)
      return fail("source.syntax", "expected parenthesized role roster");
    do {
      std::string role;
      if (!name(role))
        return false;
      roles.push_back(std::move(role));
    } while (parens && take(",") && !at(")"));
    return !parens || expect(")");
  }
  bool ports(std::vector<SyntaxPort> &output, bool roles) {
    if (!expect("("))
      return false;
    if (take(")"))
      return true;
    do {
      SyntaxPort port;
      port.span = current().span;
      if (!name(port.name) || !expect(":") || !type(port.type))
        return false;
      if (roles && (!expect("@") || !roleList(port.roles)))
        return false;
      port.span.end = previousEnd;
      output.push_back(std::move(port));
    } while (take(",") && !at(")"));
    return expect(")");
  }
  std::optional<uint32_t> expression(SyntaxDeclaration &decl,
                                     unsigned depth = 1, unsigned minimum = 0) {
    if (depth > work.limits.parseDepth) {
      fail("source.limit", "parse depth limit exceeded");
      return {};
    }
    if (!accept(work.charge(1, current().span)))
      return {};
    Span span = current().span;
    std::optional<uint32_t> left;
    if (take("(")) {
      left = expression(decl, depth + 1);
      if (!left || !expect(")"))
        return {};
    } else {
      Expression value;
      value.span = span;
      if (current().kind == TokenKind::Decimal) {
        value.kind = Expression::Kind::Decimal;
        value.text = text().str();
        advance();
      } else if (at("true") || at("false")) {
        value.kind = Expression::Kind::Boolean;
        value.text = text().str();
        advance();
      } else {
        value.kind = Expression::Kind::Name;
        if (!path(value.text))
          return {};
        if (take("(")) {
          value.kind = Expression::Kind::Call;
          if (!at(")"))
            do {
              auto arg = expression(decl, depth + 1);
              if (!arg)
                return {};
              value.children.push_back(*arg);
            } while (take(",") && !at(")"));
          if (!expect(")"))
            return {};
        }
      }
      value.span.end = previousEnd;
      left = decl.expressions.size();
      decl.expressions.push_back(std::move(value));
    }
    bool equality = false;
    while (!diagnostic) {
      unsigned precedence = at("==")             ? 1
                            : at("+") || at("-") ? 2
                            : at("*")            ? 3
                                                 : 0;
      if (!precedence || precedence < minimum)
        break;
      if (precedence == 1 && equality) {
        fail("source.syntax", "chained equality requires parentheses");
        return {};
      }
      auto kind = at("==")  ? Expression::Kind::Equal
                  : at("+") ? Expression::Kind::Add
                  : at("-") ? Expression::Kind::Subtract
                            : Expression::Kind::Multiply;
      equality |= precedence == 1;
      advance();
      auto right = expression(decl, depth + 1, precedence + 1);
      if (!right)
        return {};
      uint32_t result = decl.expressions.size();
      decl.expressions.push_back(
          {kind, {}, {*left, *right}, {module, span.begin, previousEnd}});
      left = result;
    }
    return left;
  }
  bool body(SyntaxDeclaration &decl, bool protocol) {
    if (!expect("{"))
      return false;
    while (take("let")) {
      Statement statement;
      statement.span = current().span;
      if (!name(statement.name))
        return false;
      if (take(":")) {
        SyntaxType value;
        if (!type(value))
          return false;
        statement.type = std::move(value);
      }
      if (take("@")) {
        statement.roles.emplace();
        if (!protocol)
          return fail("source.roles",
                      "math bindings do not have participant roles");
        if (!roleList(*statement.roles))
          return false;
      }
      if (!expect("="))
        return false;
      if (take("send")) {
        if (!protocol)
          return fail("source.send",
                      "send is allowed only in a protocol binding");
        std::string from, to;
        if (!name(from) || !expect("->") || !name(to) || !expect("("))
          return false;
        statement.exchange = std::make_pair(std::move(from), std::move(to));
      }
      auto value = expression(decl);
      if (!value)
        return false;
      statement.expression = *value;
      if (statement.exchange && !expect(")"))
        return false;
      if (!expect(";"))
        return false;
      statement.span.end = previousEnd;
      decl.statements.push_back(std::move(statement));
    }
    if (!expect("return"))
      return false;
    if (protocol) {
      if (!expect("("))
        return false;
      if (!at(")"))
        do {
          std::string nameValue;
          if (!name(nameValue) || !expect("="))
            return false;
          auto value = expression(decl);
          if (!value)
            return false;
          decl.results.emplace_back(std::move(nameValue), *value);
        } while (take(",") && !at(")"));
      if (!expect(")"))
        return false;
    } else {
      auto value = expression(decl);
      if (!value)
        return false;
      decl.results.emplace_back("result", *value);
    }
    return expect(";") && expect("}");
  }
};
} // namespace
Expected<SyntaxModule> parse(const SourceBuffer &source, ModuleId module,
                             ArrayRef<Token> tokens, Work &work) {
  return Parser(source, module, tokens, work).run();
}
} // namespace zkc::language::detail
