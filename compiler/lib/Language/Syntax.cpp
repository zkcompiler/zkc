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
                                   (c == '=' && text[offset] == '=') ||
                                   (c == '=' && text[offset] == '>') ||
                                   (c == '<' && text[offset] == '=') ||
                                   (c == '.' && text[offset] == '.')))
        ++offset;
      else if (!StringRef(";,:(){}@=+-*<>[]!.").contains(c))
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
      if (take("use")) {
        Import import;
        import.span = current().span;
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
        if (!separator || !expect("{")) {
          fail("source.syntax", "expected import list");
          break;
        }
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
      } else {
        auto decl = declaration(false, false, 1);
        if (!decl)
          break;
        output.declarations.push_back(std::move(*decl));
      }
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
    auto s = current().span;
    return StringRef(source.text).slice(s.begin, s.end);
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
  bool bounded(unsigned depth) {
    return depth <= work.limits.parseDepth
               ? accept(work.charge(1, current().span))
               : fail("source.limit", "parse depth limit exceeded");
  }
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
  bool permission(Permissions &p) {
    if (take("Copy"))
      p.copy = true;
    else if (take("Drop"))
      p.drop = true;
    else if (take("Share"))
      p.share = true;
    else if (take("Wire"))
      p.wire = true;
    else
      return fail("source.permission", "expected Copy, Drop, Share, or Wire");
    return true;
  }
  bool permissionList(std::optional<Permissions> &p) {
    if (!take(":"))
      return true;
    p.emplace();
    do {
      if (!permission(*p))
        return false;
    } while (take("+"));
    return true;
  }
  bool type(SyntaxType &out, unsigned depth = 1, unsigned minimum = 0) {
    if (!bounded(depth))
      return false;
    out.span = current().span;
    if (take("builtin")) {
      out.kind = SyntaxType::Kind::Builtin;
      if (!expect("(") || current().kind != TokenKind::String)
        return fail("source.syntax", "builtin requires a constructor string");
      out.name = text().drop_front().drop_back().str();
      advance();
      while (take(",")) {
        SyntaxType argument;
        if (!type(argument, depth + 1))
          return false;
        out.arguments.push_back(std::move(argument));
      }
      if (!expect(")"))
        return false;
    } else if (take("[")) {
      out.kind = SyntaxType::Kind::Array;
      SyntaxType element, count;
      if (!type(element, depth + 1) || !expect(";") ||
          !type(count, depth + 1) || !expect("]"))
        return false;
      out.arguments = {std::move(element), std::move(count)};
    } else if (take("(")) {
      out.kind = SyntaxType::Kind::Tuple;
      bool comma = false;
      if (!at(")"))
        do {
          SyntaxType child;
          if (!type(child, depth + 1))
            return false;
          out.arguments.push_back(std::move(child));
        } while ((comma = take(",")) && !at(")"));
      if (!expect(")"))
        return false;
      if (out.arguments.size() == 1 && !comma) {
        auto inner = std::move(out.arguments.front());
        out = std::move(inner);
      }
    } else if (current().kind == TokenKind::Decimal) {
      out.kind = SyntaxType::Kind::Natural;
      out.name = text().str();
      advance();
    } else {
      if (at("bool") || at("index") || at("nat") || at("Type") || at("Field") ||
          at("Group")) {
        out.name = text().str();
        advance();
      } else if (!path(out.name))
        return false;
      if (take("<")) {
        if (at(">"))
          return fail("source.syntax", "empty static argument list");
        do {
          SyntaxType arg;
          if (!type(arg, depth + 1))
            return false;
          out.arguments.push_back(std::move(arg));
        } while (take(",") && !at(">"));
        if (!expect(">"))
          return false;
      }
    }
    out.span.end = previousEnd;
    while (!diagnostic) {
      unsigned precedence = at("+") ? 1 : at("*") ? 2 : 0;
      if (!precedence || precedence < minimum)
        break;
      auto kind = at("+") ? SyntaxType::Kind::Add : SyntaxType::Kind::Multiply;
      advance();
      SyntaxType rhs;
      if (!type(rhs, depth + 1, precedence + 1))
        return false;
      SyntaxType combined;
      combined.kind = kind;
      combined.span = out.span;
      combined.span.end = previousEnd;
      combined.arguments.push_back(std::move(out));
      combined.arguments.push_back(std::move(rhs));
      out = std::move(combined);
    }
    return true;
  }
  bool parameters(std::vector<SyntaxParameter> &parameters) {
    if (!take("<"))
      return true;
    if (at(">"))
      return fail("source.syntax", "empty static parameter list");
    do {
      SyntaxParameter p;
      p.span = current().span;
      if (!name(p.name) || !expect(":") || !type(p.constraint, 1, 2))
        return false;
      while (take("+"))
        if (!permission(p.permissions))
          return false;
      p.span.end = previousEnd;
      parameters.push_back(std::move(p));
    } while (take(",") && !at(">"));
    return expect(">");
  }
  bool requirements(SyntaxDeclaration &decl) {
    if (!take("where"))
      return true;
    do {
      SyntaxRequirement req;
      req.span = current().span;
      if (at("Copy") || at("Drop") || at("Share") || at("Wire")) {
        req.permission = text().str();
        advance();
        if (!expect("(") || !type(req.lhs) || !expect(")"))
          return false;
      } else if (!type(req.lhs) || !expect("<=") || !type(req.rhs))
        return false;
      req.span.end = previousEnd;
      decl.requirements.push_back(std::move(req));
    } while (take(",") && !at("{") && !at(";") && !at("!"));
    return true;
  }
  bool effects(SyntaxDeclaration &decl) {
    if (!take("!"))
      return true;
    decl.effects = Effects{};
    if (!expect("{"))
      return false;
    if (!at("}"))
      do {
        bool *flag = nullptr;
        if (take("stop"))
          flag = &decl.effects->mayStop;
        else if (take("opaque"))
          flag = &decl.effects->opaque;
        else
          return fail("source.effect", "expected stop or opaque effect");
        if (*flag)
          return fail("source.duplicate", "duplicate effect");
        *flag = true;
      } while (take(",") && !at("}"));
    return expect("}");
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
  bool ports(std::vector<SyntaxPort> &ports, bool roles) {
    if (!expect("("))
      return false;
    if (!at(")"))
      do {
        SyntaxPort p;
        p.span = current().span;
        if (!name(p.name) || !expect(":") || !type(p.type))
          return false;
        if (roles && (!expect("@") || !roleList(p.roles)))
          return false;
        p.span.end = previousEnd;
        ports.push_back(std::move(p));
      } while (take(",") && !at(")"));
    return expect(")");
  }
  std::optional<SyntaxDeclaration> declaration(bool member, bool abstract,
                                               unsigned depth) {
    if (!bounded(depth))
      return {};
    SyntaxDeclaration d;
    d.span = current().span;
    d.isPublic = take("pub") || member;
    if (take("domain")) {
      d.kind = Declaration::Kind::Domain;
      if (member) {
        fail("source.syntax", "declaration is not an interface member");
        return {};
      }
      if (!name(d.name) || !expect("="))
        return {};
      if (take("field"))
        d.target = "Field";
      else if (take("group"))
        d.target = "Group";
      else {
        fail("source.domain", "expected installed field or group");
        return {};
      }
      if (!expect("(") || current().kind != TokenKind::String) {
        fail("source.syntax", "expected installed domain identity string");
        return {};
      }
      d.domain = text().drop_front().drop_back().str();
      advance();
      if (!expect(")") || !expect(";"))
        return {};
    } else if (take("entry")) {
      d.kind = Declaration::Kind::Entry;
      if (member) {
        fail("source.syntax", "declaration is not an interface member");
        return {};
      }
      if (!name(d.name) || !expect("="))
        return {};
      SyntaxType target;
      if (!type(target) || !expect(";"))
        return {};
      d.target = target.name;
      d.targetArguments = std::move(target.arguments);
    } else if (take("type")) {
      d.kind =
          member ? Declaration::Kind::Associated : Declaration::Kind::Alias;
      if (!name(d.name) || !parameters(d.parameters))
        return {};
      if (member && take(":")) {
        d.permissions.emplace();
        if (at("Type") || at("Field") || at("Group")) {
          d.associatedSort = text().str();
          advance();
          if (d.associatedSort != "Type")
            d.permissions->copy = d.permissions->drop = true;
          if (take("+"))
            do {
              if (!permission(*d.permissions))
                return {};
            } while (take("+"));
        } else
          do {
            if (!permission(*d.permissions))
              return {};
          } while (take("+"));
      }
      d.abstract = abstract;
      if (!requirements(d))
        return {};
      if (!abstract) {
        SyntaxType repr;
        if (!expect("=") || !type(repr))
          return {};
        d.definition = std::move(repr);
      }
      if (!expect(";"))
        return {};
    } else if (at("struct") || at("enum")) {
      if (member) {
        fail("source.syntax", "nominal declarations belong at module scope");
        return {};
      }
      bool variant = take("enum");
      if (!variant)
        advance();
      d.kind = variant ? Declaration::Kind::Variant : Declaration::Kind::Record;
      if (!name(d.name) || !parameters(d.parameters) ||
          !permissionList(d.permissions) || !requirements(d) || !expect("{"))
        return {};
      if (!at("}"))
        do {
          if (variant) {
            SyntaxAlternative alt;
            alt.span = current().span;
            if (!name(alt.name) || !expect("("))
              return {};
            if (!at(")"))
              do {
                SyntaxPort p;
                p.span = current().span;
                p.name = std::to_string(alt.fields.size());
                if (!type(p.type))
                  return {};
                p.span.end = previousEnd;
                alt.fields.push_back(std::move(p));
              } while (take(",") && !at(")"));
            if (!expect(")"))
              return {};
            alt.span.end = previousEnd;
            d.alternatives.push_back(std::move(alt));
          } else {
            SyntaxPort p;
            p.span = current().span;
            p.isPublic = take("pub");
            if (!name(p.name) || !expect(":") || !type(p.type))
              return {};
            p.span.end = previousEnd;
            d.fields.push_back(std::move(p));
          }
        } while (take(",") && !at("}"));
      if (!expect("}"))
        return {};
    } else if (at("interface") || at("component")) {
      if (member) {
        fail("source.syntax", "nested component declarations are not admitted");
        return {};
      }
      bool interface = take("interface");
      if (!interface)
        advance();
      d.kind = interface ? Declaration::Kind::Interface
                         : Declaration::Kind::Component;
      if (!name(d.name) || !parameters(d.parameters))
        return {};
      if (!interface) {
        SyntaxType target;
        if (!expect(":") || !type(target))
          return {};
        d.definition = std::move(target);
      }
      if (!requirements(d) || !expect("{"))
        return {};
      while (!at("}") && !atEnd()) {
        auto child = declaration(true, interface, depth + 1);
        if (!child)
          return {};
        d.members.push_back(std::move(*child));
      }
      if (!expect("}"))
        return {};
    } else {
      bool math = take("math");
      bool fn = take("fn");
      if (math && !fn) {
        fail("source.syntax", "expected fn after math");
        return {};
      }
      bool protocol = !fn && take("protocol");
      if (!fn && !protocol) {
        fail("source.syntax", "expected a source declaration");
        return {};
      }
      if (protocol && member) {
        fail("source.unsupported",
             "protocol component members belong to protocol composition");
        return {};
      }
      d.kind = protocol ? Declaration::Kind::Protocol
               : math   ? Declaration::Kind::Math
                        : Declaration::Kind::Local;
      if (!name(d.name) || !parameters(d.parameters))
        return {};
      if (protocol && (!expect("roles") || !roleList(d.roles, true)))
        return {};
      if (!ports(d.inputs, protocol))
        return {};
      if (take("using")) {
        if (!protocol || !ports(d.services, true)) {
          fail("source.service", "managed ports require protocol mode");
          return {};
        }
      }
      if (!expect("->"))
        return {};
      if (protocol) {
        if (!ports(d.outputs, true))
          return {};
      } else {
        SyntaxPort p;
        p.name = "result";
        p.span = current().span;
        if (!type(p.type))
          return {};
        p.span.end = previousEnd;
        d.outputs.push_back(std::move(p));
      }
      if (take("completes")) {
        if (!protocol) {
          fail("source.mode", "completes requires a protocol");
          return {};
        }
        d.completes = true;
      }
      if (!requirements(d) || !effects(d))
        return {};
      d.abstract = abstract;
      if (abstract) {
        if (!expect(";"))
          return {};
      } else if (!body(d, protocol, false, 1))
        return {};
    }
    d.span.end = previousEnd;
    if (!accept(work.count(work.declarations, work.limits.declarations,
                           "declaration count", d.span)))
      return {};
    return d;
  }
  bool names(std::vector<std::string> &out) {
    if (!expect("("))
      return false;
    if (!at(")"))
      do {
        std::string n;
        if (!name(n))
          return false;
        out.push_back(std::move(n));
      } while (take(",") && !at(")"));
    return expect(")");
  }
  std::optional<uint32_t> expression(SyntaxDeclaration &decl,
                                     unsigned depth = 1, unsigned minimum = 0) {
    if (!bounded(depth))
      return {};
    Span span = current().span;
    Expression value;
    value.span = span;
    if (at("apply") && tokens[cursor + 1].kind == TokenKind::Word) {
      advance();
      value.kind = Expression::Kind::Apply;
      SyntaxType target;
      if (!type(target, depth + 1))
        return {};
      if (target.kind != SyntaxType::Kind::Name) {
        fail("source.syntax", "application requires a named protocol");
        return {};
      }
      value.text = std::move(target.name);
      value.arguments = std::move(target.arguments);
      if (take("roles")) {
        value.roles.emplace();
        if (!names(*value.roles))
          return {};
      }
      if (!expect("("))
        return {};
      if (!at(")"))
        do {
          auto argument = expression(decl, depth + 1);
          if (!argument)
            return {};
          value.children.push_back(*argument);
        } while (take(",") && !at(")"));
      if (!expect(")"))
        return {};
      if (take("using") && !names(value.services))
        return {};
    } else if (take("kernel")) {
      value.kind = Expression::Kind::Kernel;
      if (take("<")) {
        do {
          SyntaxType argument;
          if (!type(argument, depth + 1))
            return {};
          value.arguments.push_back(std::move(argument));
        } while (take(","));
        if (!expect(">"))
          return {};
      }
      if (!expect("(") || current().kind != TokenKind::String) {
        fail("source.syntax", "kernel requires an installed contract string");
        return {};
      }
      value.text = text().drop_front().drop_back().str();
      advance();
      while (take(",")) {
        auto input = expression(decl, depth + 1);
        if (!input)
          return {};
        value.children.push_back(*input);
      }
      if (take(";")) {
        do {
          if (current().kind != TokenKind::String) {
            fail("source.syntax", "kernel parameters must be literal strings");
            return {};
          }
          value.labels.push_back(text().drop_front().drop_back().str());
          advance();
        } while (take(","));
      }
      if (!expect(")"))
        return {};
    } else if (take("finish_if")) {
      value.kind = Expression::Kind::FinishIf;
      if (!expect("@") || !name(value.text) || !expect("("))
        return {};
      auto condition = expression(decl, depth + 1);
      if (!condition || !expect(")") || !expect("("))
        return {};
      value.children.push_back(*condition);
      if (!at(")"))
        do {
          std::string name;
          if (!this->name(name) || !expect("="))
            return {};
          auto output = expression(decl, depth + 1);
          if (!output)
            return {};
          value.labels.push_back(std::move(name));
          value.children.push_back(*output);
        } while (take(",") && !at(")"));
      if (!expect(")"))
        return {};
    } else if (take("repeat")) {
      value.kind = Expression::Kind::Repeat;
      value.roles.emplace();
      if (!expect("roles") || !roleList(*value.roles, true) || !expect("(") ||
          !name(value.text) || !expect("<"))
        return {};
      auto count = expression(decl, depth + 1);
      SyntaxType maximum;
      if (!count || !expect(",") || !expect("max") ||
          !type(maximum, depth + 1) || !expect(")") || !expect("carry") ||
          !expect("("))
        return {};
      value.children.push_back(*count);
      value.arguments.push_back(std::move(maximum));
      if (!at(")"))
        do {
          std::string n;
          if (!name(n) || !expect("="))
            return {};
          auto initial = expression(decl, depth + 1);
          if (!initial)
            return {};
          value.labels.push_back(std::move(n));
          value.children.push_back(*initial);
          std::optional<std::vector<std::string>> roles;
          if (take("@")) {
            roles.emplace();
            if (!roleList(*roles))
              return {};
          }
          value.carriedRoles.push_back(std::move(roles));
        } while (take(",") && !at(")"));
      if (!expect(")") || !expect("capture") || !names(value.captures))
        return {};
      if (take("using") && !names(value.services))
        return {};
      auto region = body(decl, true, true, depth + 1);
      if (!region)
        return {};
      value.regions.push_back(*region);
    } else if (take("if")) {
      value.kind = Expression::Kind::If;
      auto condition = expression(decl, depth + 1);
      if (!condition)
        return {};
      value.children.push_back(*condition);
      if (!expect("capture") || !names(value.captures))
        return {};
      auto first = body(decl, false, true, depth + 1);
      if (!first || !expect("else"))
        return {};
      auto second = body(decl, false, true, depth + 1);
      if (!second)
        return {};
      value.regions = {*first, *second};
    } else if (take("match")) {
      value.kind = Expression::Kind::Match;
      auto subject = expression(decl, depth + 1);
      if (!subject)
        return {};
      value.children.push_back(*subject);
      if (!expect("capture") || !names(value.captures) || !expect("{"))
        return {};
      if (!at("}"))
        do {
          std::string label;
          std::vector<std::string> payload;
          if (!name(label) || !names(payload) || !expect("=>"))
            return {};
          auto arm = body(decl, false, true, depth + 1);
          if (!arm)
            return {};
          value.labels.push_back(std::move(label));
          value.payloads.push_back(std::move(payload));
          value.regions.push_back(*arm);
        } while (take(",") && !at("}"));
      if (!expect("}"))
        return {};
    } else if (take("for")) {
      value.kind = Expression::Kind::For;
      if (!name(value.text) || !expect("in"))
        return {};
      auto lower = expression(decl, depth + 1);
      if (!lower || !expect(".."))
        return {};
      auto upper = expression(decl, depth + 1);
      if (!upper || !expect("carry") || !expect("("))
        return {};
      value.children = {*lower, *upper};
      if (!at(")"))
        do {
          std::string n;
          if (!name(n) || !expect("="))
            return {};
          auto initial = expression(decl, depth + 1);
          if (!initial)
            return {};
          value.labels.push_back(std::move(n));
          value.children.push_back(*initial);
        } while (take(",") && !at(")"));
      if (!expect(")") || !expect("capture") || !names(value.captures))
        return {};
      auto region = body(decl, false, true, depth + 1);
      if (!region)
        return {};
      value.regions.push_back(*region);
    } else if (take("(")) {
      value.kind = Expression::Kind::Tuple;
      bool comma = false;
      if (!at(")"))
        do {
          auto x = expression(decl, depth + 1);
          if (!x)
            return {};
          value.children.push_back(*x);
        } while ((comma = take(",")) && !at(")"));
      if (!expect(")"))
        return {};
      if (value.children.size() == 1 && !comma)
        return postfix(decl, value.children.front(), span, depth, minimum);
    } else if (take("[")) {
      value.kind = Expression::Kind::Array;
      if (!at("]"))
        do {
          auto x = expression(decl, depth + 1);
          if (!x)
            return {};
          value.children.push_back(*x);
        } while (take(",") && !at("]"));
      if (!expect("]"))
        return {};
    } else if (current().kind == TokenKind::Decimal) {
      value.kind = Expression::Kind::Decimal;
      value.text = text().str();
      advance();
    } else if (at("true") || at("false")) {
      value.kind = Expression::Kind::Boolean;
      value.text = text().str();
      advance();
    } else {
      value.kind = Expression::Kind::Name;
      if (at("index")) {
        value.text = "index";
        advance();
      } else if (!path(value.text))
        return {};
      if (take("<")) {
        do {
          SyntaxType arg;
          if (!type(arg, depth + 1))
            return {};
          value.arguments.push_back(std::move(arg));
        } while (take(",") && !at(">"));
        if (!expect(">"))
          return {};
      }
      if (take("(")) {
        value.kind = Expression::Kind::Call;
        if (!at(")"))
          do {
            auto x = expression(decl, depth + 1);
            if (!x)
              return {};
            value.children.push_back(*x);
          } while (take(",") && !at(")"));
        if (!expect(")"))
          return {};
      } else if (take("{")) {
        value.kind = Expression::Kind::Record;
        if (!at("}"))
          do {
            std::string label;
            if (!name(label) || !expect(":"))
              return {};
            auto x = expression(decl, depth + 1);
            if (!x)
              return {};
            value.labels.push_back(std::move(label));
            value.children.push_back(*x);
          } while (take(",") && !at("}"));
        if (!expect("}"))
          return {};
      } else if (!value.arguments.empty()) {
        fail("source.syntax",
             "static application requires a call or constructor");
        return {};
      }
    }
    value.span.end = previousEnd;
    auto left = uint32_t(decl.expressions.size());
    decl.expressions.push_back(std::move(value));
    return postfix(decl, left, span, depth, minimum);
  }
  std::optional<uint32_t> postfix(SyntaxDeclaration &decl, uint32_t left,
                                  Span span, unsigned depth, unsigned minimum) {
    while (take(".") || take("[")) {
      bool bracket = source.text[previousEnd - 1] == '[';
      Expression projection;
      projection.kind = Expression::Kind::Projection;
      projection.children = {left};
      projection.span = span;
      if (current().kind == TokenKind::Decimal) {
        projection.text = text().str();
        advance();
      } else if (!name(projection.text))
        return {};
      if (bracket && !expect("]"))
        return {};
      if (!bracket && take("(")) {
        projection.kind = Expression::Kind::MethodCall;
        if (!at(")"))
          do {
            auto arg = expression(decl, depth + 1);
            if (!arg)
              return {};
            projection.children.push_back(*arg);
          } while (take(",") && !at(")"));
        if (!expect(")"))
          return {};
      }
      projection.span.end = previousEnd;
      left = decl.expressions.size();
      decl.expressions.push_back(std::move(projection));
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
      Expression binary;
      binary.span = span;
      binary.kind = at("==")  ? Expression::Kind::Equal
                    : at("+") ? Expression::Kind::Add
                    : at("-") ? Expression::Kind::Subtract
                              : Expression::Kind::Multiply;
      equality |= precedence == 1;
      advance();
      auto right = expression(decl, depth + 1, precedence + 1);
      if (!right)
        return {};
      binary.children = {left, *right};
      binary.span.end = previousEnd;
      left = decl.expressions.size();
      decl.expressions.push_back(std::move(binary));
    }
    return left;
  }
  std::optional<uint32_t> body(SyntaxDeclaration &decl, bool protocol,
                               bool region, unsigned depth) {
    if (!bounded(depth) || !expect("{"))
      return {};
    uint32_t id = decl.bodies.size();
    decl.bodies.emplace_back();
    SyntaxBody b;
    b.span = current().span;
    while (!at("return") && !at("yield") && !at("stop") && !atEnd() &&
           !at("}")) {
      Statement s;
      s.span = current().span;
      if (take("local")) {
        std::string owner;
        if (!protocol || !name(owner)) {
          fail("source.mode", "owned local statements require protocol mode");
          return {};
        }
        s.owner = std::move(owner);
      }
      if (take("using")) {
        s.kind = Statement::Kind::Alias;
        if (!name(s.name) || !expect("="))
          return {};
      } else if (take("guard")) {
        if (s.owner) {
          fail("source.mode", "guard declares its own owner");
          return {};
        }
        s.kind = Statement::Kind::Guard;
        s.owner.emplace();
        if (!expect("@") || !name(*s.owner))
          return {};
      } else if (take("let")) {
        if (at("(")) {
          s.resultNames.emplace();
          if (!names(*s.resultNames))
            return {};
        } else if (!name(s.name))
          return {};
        if (take(":")) {
          SyntaxType t;
          if (!type(t))
            return {};
          s.type = std::move(t);
        }
        if (take("@")) {
          s.roles.emplace();
          if (!protocol || !roleList(*s.roles)) {
            fail("source.roles", "role annotation requires protocol mode");
            return {};
          }
        }
        if (!expect("="))
          return {};
        if (take("send")) {
          if (!protocol || s.owner) {
            fail("source.send", "send requires a protocol binding");
            return {};
          }
          std::string from, to;
          if (!name(from) || !expect("->") || !name(to) || !expect("("))
            return {};
          s.exchange = std::make_pair(std::move(from), std::move(to));
        }
      } else if (take("drop"))
        s.kind = Statement::Kind::Drop;
      else if (take("consume"))
        s.kind = Statement::Kind::Consume;
      else if (take("require"))
        s.kind = Statement::Kind::Require;
      else {
        fail("source.syntax",
             "expected let, drop, consume, require, or body terminator");
        return {};
      }
      auto expr = expression(decl, depth);
      if (!expr)
        return {};
      s.expression = *expr;
      if (s.exchange && !expect(")"))
        return {};
      if (!expect(";"))
        return {};
      s.span.end = previousEnd;
      b.statements.push_back(std::move(s));
    }
    if (take("stop")) {
      if (protocol || current().kind != TokenKind::String) {
        fail("source.mode", "local stop requires a reason string");
        return {};
      }
      b.stopped = true;
      b.stopReason = text().drop_front().drop_back().str();
      advance();
    } else {
      if (!expect(region ? "yield" : "return"))
        return {};
      if (protocol) {
        if (!expect("("))
          return {};
        if (!at(")"))
          do {
            std::string n;
            if (!name(n) || !expect("="))
              return {};
            auto value = expression(decl, depth);
            if (!value)
              return {};
            b.results.emplace_back(std::move(n), *value);
          } while (take(",") && !at(")"));
        if (!expect(")"))
          return {};
      } else {
        auto value = expression(decl, depth);
        if (!value)
          return {};
        b.results.emplace_back("result", *value);
      }
    }
    if (!expect(";") || !expect("}"))
      return {};
    b.span.end = previousEnd;
    decl.bodies[id] = std::move(b);
    return id;
  }
};
} // namespace
Expected<SyntaxModule> parse(const SourceBuffer &source, ModuleId module,
                             ArrayRef<Token> tokens, Work &work) {
  return Parser(source, module, tokens, work).run();
}
} // namespace zkc::language::detail
