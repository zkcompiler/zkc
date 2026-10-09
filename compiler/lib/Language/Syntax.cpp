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
          return failure("source.string",
                         "expected an unescaped printable ASCII string",
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
  bool path(std::string &output, bool allowSort = false,
            bool allowAbsolute = false) {
    bool absolute = allowAbsolute && take("::");
    if (!name(output))
      return false;
    while (take("::")) {
      std::string part;
      // Field and Group are also qualified catalog capability exports.
      // They remain reserved as declaration and unqualified names.
      if (allowSort && (at("Field") || at("Group"))) {
        part = text().str();
        advance();
      } else if (!name(part))
        return false;
      output += "::" + part;
    }
    if (absolute)
      output.insert(0, "::");
    return output.size() <= work.limits.moduleBytes +
                                work.limits.identifierBytes + 2 +
                                (absolute ? 2 : 0) ||
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
  bool typeTreeBound(SyntaxType &type) {
    type.height = 1;
    for (const auto &argument : type.arguments)
      type.height = std::max(type.height, argument.height + 1);
    return type.height <= work.limits.parseDepth ||
           fail("source.limit", "type syntax depth limit exceeded");
  }
  bool type(SyntaxType &out, unsigned depth = 1, unsigned minimum = 0) {
    if (!bounded(depth))
      return false;
    out.span = current().span;
    if (take("_")) {
      out.kind = SyntaxType::Kind::Hole;
    } else if (take("pow2")) {
      out.kind = SyntaxType::Kind::PowerOfTwo;
      SyntaxType exponent;
      if (!expect("(") || !type(exponent, depth + 1) || !expect(")"))
        return false;
      out.arguments.push_back(std::move(exponent));
    } else if (at("builtin") || at("formal")) {
      out.kind =
          take("formal") ? SyntaxType::Kind::Formal : SyntaxType::Kind::Builtin;
      if (out.kind == SyntaxType::Kind::Builtin)
        advance();
      if (!expect("(") || current().kind != TokenKind::String)
        return fail("source.syntax", "type constructor requires a name string");
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
      } else if (!path(out.name, true, true))
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
    if (!typeTreeBound(out))
      return false;
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
      if (!typeTreeBound(combined))
        return false;
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
      if (!name(p.name) || !expect(":") || !type(p.constraint, 1, 3))
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
    decl.explicitRequirements = true;
    if (take("("))
      return expect(")");
    do {
      SyntaxRequirement req;
      req.span = current().span;
      if (at("Copy") || at("Drop") || at("Share") || at("Wire")) {
        req.permission = text().str();
        advance();
        if (!expect("(") || !type(req.lhs) || !expect(")"))
          return false;
      } else {
        if (!type(req.lhs))
          return false;
        if (take("(")) {
          if (req.lhs.kind != SyntaxType::Kind::Name ||
              !req.lhs.arguments.empty())
            return fail("source.capability",
                        "expected a capability export name");
          req.capability = req.lhs.name;
          if (!at(")"))
            do {
              SyntaxType argument;
              if (!type(argument))
                return false;
              req.arguments.push_back(std::move(argument));
            } while (take(",") && !at(")"));
          if (!expect(")"))
            return false;
        } else if (!expect("<=") || !type(req.rhs))
          return false;
      }
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
  bool string(std::string &value) {
    if (current().kind != TokenKind::String)
      return fail("source.syntax", "expected an explicit string");
    value = text().drop_front().drop_back().str();
    advance();
    return true;
  }
  bool selectorPath(SyntaxSelector &value) {
    while (take(".")) {
      if (current().kind == TokenKind::Decimal) {
        value.path.push_back(text().str());
        advance();
      } else {
        std::string field;
        if (!name(field))
          return false;
        value.path.push_back(std::move(field));
      }
      if (value.path.size() > work.limits.typeDepth)
        return fail("source.limit", "selector path depth exceeded");
    }
    return true;
  }
  bool selector(SyntaxSelector &value) {
    value.span = current().span;
    if (take("out"))
      value.output = true;
    else if (take("in"))
      value.output = false;
    else
      return fail("source.specification", "selector must start with in or out");
    if (!expect(".") || !name(value.port))
      return false;
    if (!selectorPath(value))
      return false;
    if (take("@")) {
      std::string role;
      if (!name(role))
        return false;
      value.role = std::move(role);
    }
    value.span.end = previousEnd;
    return true;
  }
  bool named(SyntaxName &value) {
    value.span = current().span;
    if (!name(value.name))
      return false;
    value.span.end = previousEnd;
    return true;
  }
  bool entryChoices(SyntaxDeclaration &decl) {
    SyntaxProofEntry value;
    value.span = current().span;
    if (!expect("{"))
      return false;
    decl.entryBlock = true;
    std::set<std::string> choices;
    while (!at("}") && !atEnd()) {
      if (take("setup")) {
        SyntaxSetupSlot slot;
        slot.span = current().span;
        if (!named(slot.name) || !expect("{"))
          return false;
        if (!at("}"))
          do {
            SyntaxSelector input;
            input.span = current().span;
            if (!name(input.port) || !selectorPath(input))
              return false;
            input.span.end = previousEnd;
            slot.inputs.push_back(std::move(input));
          } while (take(",") && !at("}"));
        if (!expect("}") || !expect(";"))
          return false;
        slot.span.end = previousEnd;
        decl.setups.push_back(std::move(slot));
        continue;
      }
      auto key = text().str();
      if (!choices.insert(key).second)
        return fail("source.entry", "duplicate Entry choice");
      advance();
      if (key == "prover" || key == "verifier") {
        if (!named(key == "prover" ? value.prover : value.verifier) ||
            !expect(";"))
          return false;
      } else if (key == "public") {
        if (!expect("{"))
          return false;
        if (!at("}"))
          do {
            SyntaxName port;
            if (!named(port))
              return false;
            value.publicInputs.push_back(std::move(port));
          } while (take(",") && !at("}"));
        if (!expect("}") || !expect(";"))
          return false;
      } else if (key == "accept" || key == "complete") {
        auto &selected =
            key == "accept" ? value.acceptance : value.completion.emplace();
        selected.output = true;
        selected.span = current().span;
        if (!name(selected.port) || !selectorPath(selected))
          return false;
        selected.span.end = previousEnd;
        if (!expect(";"))
          return false;
      } else if (key == "target") {
        value.target.emplace();
        if (!named(*value.target) || !expect(";"))
          return false;
      } else if (key == "construction") {
        if (take("authored")) {
          value.construction = ProofEntry::Construction::Authored;
          if (!expect(";"))
            return false;
        } else if (take("fiat_shamir")) {
          value.construction = ProofEntry::Construction::FiatShamir;
          value.service.emplace();
          if (!expect("(") || !string(value.suite) || !expect(")") ||
              !expect("{") || !expect("derive") || !named(*value.service) ||
              !expect(";") || !expect("}"))
            return false;
        } else
          return fail("source.entry",
                      "expected authored or fiat_shamir construction");
      } else
        return fail("source.entry", "unknown Entry choice");
    }
    if (choices.empty() && decl.setups.empty())
      return fail("source.entry", "empty Entry choice block");
    if (!choices.empty())
      for (StringRef key :
           {"prover", "verifier", "public", "accept", "construction"})
        if (!choices.count(key.str()))
          return fail("source.entry", "missing Entry choice: " + key);
    if (!expect("}"))
      return false;
    value.span.end = previousEnd;
    if (!choices.empty())
      decl.proof = std::move(value);
    return true;
  }
  bool purpose(RelationPurpose &value) {
    if (take("parameter"))
      value = RelationPurpose::Parameter;
    else if (take("statement"))
      value = RelationPurpose::Statement;
    else if (take("witness"))
      value = RelationPurpose::Witness;
    else
      return fail("source.relation",
                  "relation formals need an explicit purpose");
    return true;
  }
  void booleanResult(SyntaxDeclaration &d) {
    SyntaxPort result;
    result.name = "result";
    result.span = d.span;
    result.type.name = "bool";
    result.type.span = d.span;
    d.outputs.push_back(std::move(result));
  }
  bool subject(SyntaxSubject &value, SyntaxDeclaration &owner) {
    value.span = current().span;
    if (take("relation")) {
      SyntaxDeclaration definition;
      definition.kind = Declaration::Kind::Relation;
      definition.name = "clause_" + std::to_string(owner.members.size());
      definition.anonymous = true;
      definition.span = value.span;
      definition.relation.emplace();
      if (!expect("("))
        return false;
      if (!at(")"))
        do {
          SyntaxPort port;
          port.span = current().span;
          RelationPurpose role;
          SyntaxSelector operand;
          if (!purpose(role) || !this->name(port.name) || !expect("=") ||
              !selector(operand))
            return false;
          port.span.end = previousEnd;
          port.purpose = role;
          port.binding = std::move(operand);
          definition.inputs.push_back(std::move(port));
        } while (take(",") && !at(")"));
      if (!expect(")"))
        return false;
      booleanResult(definition);
      if (!body(definition, false, false, 1))
        return false;
      definition.span.end = previousEnd;
      if (!accept(work.count(work.declarations, work.limits.declarations,
                             "relation count", definition.span)))
        return false;
      value.inlineMember = owner.members.size();
      value.relation.span = value.span;
      for (const auto &parameter : owner.parameters) {
        SyntaxType argument;
        argument.name = parameter.name;
        argument.span = parameter.span;
        value.relation.arguments.push_back(std::move(argument));
      }
      owner.members.push_back(std::move(definition));
      value.span.end = previousEnd;
      return true;
    }
    if (!type(value.relation) ||
        value.relation.kind != SyntaxType::Kind::Name || !expect("("))
      return fail("source.specification", "expected a relation application");
    if (!at(")"))
      do {
        SyntaxSelector operand;
        if (!selector(operand))
          return false;
        value.operands.push_back(std::move(operand));
      } while (take(",") && !at(")"));
    if (!expect(")"))
      return false;
    value.span.end = previousEnd;
    return true;
  }
  bool specifications(SyntaxDeclaration &d) {
    if (!at("spec"))
      return true;
    d.specificationBlock = current().span;
    advance();
    if (!expect("{"))
      return false;
    std::set<std::string> clauseNames;
    while (!at("}") && !atEnd()) {
      SyntaxClause clause;
      clause.span = current().span;
      using K = SpecificationClause::Kind;
      if (take("target"))
        clause.kind = K::Target;
      else if (take("input"))
        clause.kind = K::Input;
      else if (take("output"))
        clause.kind = K::Output;
      else if (take("continuation"))
        clause.kind = K::Continuation;
      else
        return fail("source.specification",
                    "expected target, input, output or continuation");
      if (!name(clause.name))
        return false;
      if (!clauseNames.insert(clause.name).second)
        return fail("source.duplicate", "duplicate specification clause");
      if (!expect("=") || !subject(clause.subject, d))
        return false;
      if (take("residual")) {
        SyntaxSubject value;
        if (!subject(value, d))
          return false;
        clause.residual = std::move(value);
      }
      if (take("accept")) {
        SyntaxSelector decision;
        if (!selector(decision))
          return false;
        clause.decision = std::move(decision);
      }
      if (!expect(";"))
        return false;
      clause.span.end = previousEnd;
      if (!accept(work.count(work.operations, work.limits.operations,
                             "specification count", clause.span)))
        return false;
      d.specifications.push_back(std::move(clause));
    }
    if (!expect("}"))
      return false;
    d.specificationBlock->end = previousEnd;
    return true;
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
      if (current().kind != TokenKind::Word) {
        fail("source.domain", "expected a domain sort");
        return {};
      }
      d.target = text().str();
      advance();
      if (!expect("("))
        return {};
      // An asset domain names captured bytes; a catalog domain names an
      // installed identity.
      d.assetDomain = d.target == "ring" || d.target == "bundle";
      if (d.assetDomain) {
        if (!expect("asset") || !path(d.domain))
          return {};
      } else if (current().kind != TokenKind::String) {
        fail("source.syntax", "expected installed domain identity string");
        return {};
      } else {
        d.domain = text().drop_front().drop_back().str();
        advance();
      }
      if (!expect(")") || !expect(";"))
        return {};
    } else if (take("relation")) {
      if (member) {
        fail("source.syntax", "relations belong at module scope");
        return {};
      }
      d.kind = Declaration::Kind::Relation;
      d.relation.emplace();
      if (!name(d.name) || !parameters(d.parameters) || !expect("("))
        return {};
      if (!at(")"))
        do {
          SyntaxPort port;
          port.span = current().span;
          RelationPurpose purpose;
          if (!this->purpose(purpose))
            return {};
          if (!name(port.name) || !expect(":") || !type(port.type))
            return {};
          port.span.end = previousEnd;
          port.purpose = purpose;
          d.inputs.push_back(std::move(port));
        } while (take(",") && !at(")"));
      if (!expect(")") || !requirements(d))
        return {};
      booleanResult(d);
      if (take("=")) {
        if (take("opaque")) {
          d.relation->kind = RelationDefinition::Kind::Opaque;
          if (!expect("(") || !string(d.relation->externalKind) ||
              !expect(",") || !string(d.relation->key) || !expect(",") ||
              !string(d.relation->revision) || !expect(")"))
            return {};
        } else {
          if (take("r1cs"))
            d.relation->kind = RelationDefinition::Kind::R1CS;
          else if (take("air"))
            d.relation->kind = RelationDefinition::Kind::AIR;
          else if (take("bundle"))
            d.relation->kind = RelationDefinition::Kind::Bundle;
          else {
            fail("source.relation",
                 "expected opaque, r1cs, air or bundle definition");
            return {};
          }
          if (!expect("(") || !expect("asset") || !path(d.relation->asset) ||
              !expect(")"))
            return {};
        }
        if (!expect(";"))
          return {};
      } else if (!body(d, false, false, 1))
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
      if (!type(target) || target.kind != SyntaxType::Kind::Name) {
        fail("source.entry", "expected a protocol or complete Entry name");
        return {};
      }
      d.target = target.name;
      d.targetArguments = std::move(target.arguments);
      if (at("{")) {
        if (!entryChoices(d))
          return {};
      } else if (!expect(";"))
        return {};
    } else if (take("type")) {
      d.kind =
          member ? Declaration::Kind::Associated : Declaration::Kind::Alias;
      if (!name(d.name) || !parameters(d.parameters))
        return {};
      if (member && take(":")) {
        d.permissions.emplace();
        if (!at("Copy") && !at("Drop") && !at("Share") && !at("Wire")) {
          if (current().kind != TokenKind::Word) {
            fail("source.type", "expected an associated sort or permission");
            return {};
          }
          d.associatedSort = text().str();
          advance();
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
      if (protocol) {
        auto ports = std::move(d.inputs);
        d.inputs.clear();
        for (auto &port : ports) {
          bool service = port.type.kind == SyntaxType::Kind::Name &&
                         port.type.name == "Random";
          auto &selected = service ? d.services : d.inputs;
          d.inputOrder.push_back({service
                                      ? Declaration::InputSlot::Kind::Service
                                      : Declaration::InputSlot::Kind::Data,
                                  unsigned(selected.size())});
          selected.push_back(std::move(port));
        }
      }
      if (protocol) {
        if (!expect("->") || !ports(d.outputs, true))
          return {};
      } else if (take("->")) {
        SyntaxPort p;
        p.name = "result";
        p.span = current().span;
        if (!type(p.type))
          return {};
        p.span.end = previousEnd;
        d.outputs.push_back(std::move(p));
      } else if (abstract) {
        fail("source.inference", "abstract functions require a result type");
        return {};
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
      if (protocol && !specifications(d))
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
                                     unsigned depth = 1, unsigned minimum = 0,
                                     bool records = true,
                                     bool statementStart = false) {
    if (!bounded(depth))
      return {};
    Span span = current().span;
    Expression value;
    value.span = span;
    if (at("kernel") || at("intrinsic")) {
      value.kind = take("intrinsic") ? Expression::Kind::Intrinsic
                                     : Expression::Kind::Kernel;
      if (value.kind == Expression::Kind::Kernel)
        advance();
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
        fail("source.syntax",
             "operation hook requires an installed identity string");
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
          if (current().kind == TokenKind::String) {
            value.labels.push_back(text().drop_front().drop_back().str());
            advance();
          } else if (value.kind == Expression::Kind::Kernel) {
            // A kernel parameter can be a static asset term; its identity is
            // written when the enclosing body closes.
            SyntaxType term;
            if (!type(term, depth + 1))
              return {};
            value.assetParameters.emplace(value.labels.size(), std::move(term));
            value.labels.emplace_back();
          } else {
            fail("source.syntax",
                 "intrinsic parameters must be literal strings");
            return {};
          }
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
    } else if (take("if")) {
      value.kind = Expression::Kind::If;
      auto condition = expression(decl, depth + 1, 0, false);
      if (!condition)
        return {};
      value.children.push_back(*condition);
      auto first = body(decl, false, true, depth + 1);
      if (!first)
        return {};
      value.regions.push_back(*first);
      if (take("else")) {
        auto second = body(decl, false, true, depth + 1);
        if (!second)
          return {};
        value.regions.push_back(*second);
      } else {
        SyntaxBody empty;
        empty.region = true;
        empty.span = span;
        value.regions.push_back(decl.bodies.size());
        decl.bodies.push_back(std::move(empty));
      }
    } else if (take("match")) {
      value.kind = Expression::Kind::Match;
      auto subject = expression(decl, depth + 1, 0, false);
      if (!subject)
        return {};
      value.children.push_back(*subject);
      if (!expect("{"))
        return {};
      if (!at("}"))
        do {
          std::string label;
          std::vector<Pattern> payload;
          if (!name(label) || !expect("("))
            return {};
          if (!at(")"))
            do {
              auto item = pattern(depth + 1);
              if (!item)
                return {};
              payload.push_back(std::move(*item));
            } while (take(",") && !at(")"));
          if (!expect(")") || !expect("=>"))
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
      value.index.span = current().span;
      if (!name(value.index.name) || !expect("in"))
        return {};
      value.index.kind =
          value.index.name == "_" ? Pattern::Kind::Ignore : Pattern::Kind::Name;
      auto lower = expression(decl, depth + 1, 0, false);
      if (!lower || !expect(".."))
        return {};
      auto upper = expression(decl, depth + 1, 0, false);
      if (!upper)
        return {};
      value.children = {*lower, *upper};
      if (take("roles")) {
        value.roles.emplace();
        SyntaxType maximum;
        if (!roleList(*value.roles, true) || !expect("max") ||
            !type(maximum, depth + 1))
          return {};
        value.arguments.push_back(std::move(maximum));
      }
      auto region = body(decl, value.roles.has_value(), true, depth + 1);
      if (!region)
        return {};
      value.regions.push_back(*region);
    } else if (at("{")) {
      value.kind = Expression::Kind::Block;
      auto region =
          body(decl, decl.kind == Declaration::Kind::Protocol, true, depth + 1);
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
        return postfix(decl, value.children.front(), span, depth, minimum,
                       records);
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
      } else if (!path(value.text, false, true))
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
      if (records && take("roles")) {
        value.roles.emplace();
        if (!names(*value.roles))
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
      } else if (records && take("{")) {
        value.kind = Expression::Kind::Record;
        if (!at("}"))
          do {
            std::string label;
            Span fieldSpan = current().span;
            if (!name(label))
              return {};
            std::optional<uint32_t> x;
            if (take(":"))
              x = expression(decl, depth + 1);
            else {
              Expression shorthand;
              shorthand.kind = Expression::Kind::Name;
              shorthand.text = label;
              shorthand.span = fieldSpan;
              x = decl.expressions.size();
              decl.expressions.push_back(std::move(shorthand));
            }
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
    bool blockLike = value.kind == Expression::Kind::Block ||
                     value.kind == Expression::Kind::If ||
                     value.kind == Expression::Kind::Match ||
                     value.kind == Expression::Kind::For;
    decl.expressions.push_back(std::move(value));
    if (statementStart && blockLike)
      return left;
    return postfix(decl, left, span, depth, minimum, records);
  }
  std::optional<uint32_t> postfix(SyntaxDeclaration &decl, uint32_t left,
                                  Span span, unsigned depth, unsigned minimum,
                                  bool records) {
    while (take(".") || take("[")) {
      bool bracket = source.text[previousEnd - 1] == '[';
      Expression projection;
      projection.kind = Expression::Kind::Projection;
      projection.bracket = bracket;
      projection.children = {left};
      projection.span = span;
      // `index` is reserved, so `.index` can only name the managed method,
      // whose static arguments precede its call.
      bool method = !bracket && at("index");
      if (method) {
        projection.text = "index";
        advance();
        if (take("<")) {
          do {
            SyntaxType argument;
            if (!type(argument, depth + 1))
              return {};
            projection.arguments.push_back(std::move(argument));
          } while (take(",") && !at(">"));
          if (!expect(">"))
            return {};
        }
        if (!at("(")) {
          fail("source.syntax", "index requires a method call");
          return {};
        }
      } else if (current().kind == TokenKind::Decimal) {
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
      auto right = expression(decl, depth + 1, precedence + 1, records);
      if (!right)
        return {};
      binary.children = {left, *right};
      binary.span.end = previousEnd;
      left = decl.expressions.size();
      decl.expressions.push_back(std::move(binary));
    }
    return left;
  }
  std::optional<Pattern> pattern(unsigned depth) {
    if (!bounded(depth))
      return {};
    Pattern result;
    result.span = current().span;
    if (take("_")) {
      result.kind = Pattern::Kind::Ignore;
    } else if (take("(")) {
      result.kind = Pattern::Kind::Tuple;
      bool comma = false;
      if (!at(")"))
        do {
          auto child = pattern(depth + 1);
          if (!child)
            return {};
          result.children.push_back(std::move(*child));
        } while ((comma = take(",")) && !at(")"));
      if (!expect(")"))
        return {};
      if (result.children.empty())
        result.kind = Pattern::Kind::Unit;
      else if (result.children.size() == 1 && !comma)
        return std::move(result.children.front());
    } else {
      SyntaxType term;
      if (!type(term, depth))
        return {};
      if (term.kind != SyntaxType::Kind::Name) {
        fail("source.binding", "expected a binding name or record pattern");
        return {};
      }
      result.name = term.name;
      if (take("{")) {
        result.kind = Pattern::Kind::Record;
        result.type = std::move(term);
        if (!at("}"))
          do {
            Span fieldSpan = current().span;
            std::string label;
            if (!name(label))
              return {};
            std::optional<Pattern> child;
            if (take(":"))
              child = pattern(depth + 1);
            else {
              child.emplace();
              child->name = label;
              child->span = fieldSpan;
            }
            if (!child)
              return {};
            result.labels.push_back(std::move(label));
            result.children.push_back(std::move(*child));
          } while (take(",") && !at("}"));
        if (!expect("}"))
          return {};
      } else if (!term.arguments.empty() ||
                 term.name.find("::") != std::string::npos) {
        fail("source.binding", "type path requires a record pattern");
        return {};
      }
    }
    result.span.end = previousEnd;
    return result;
  }
  std::optional<uint32_t> body(SyntaxDeclaration &decl, bool protocol,
                               bool region, unsigned depth) {
    if (!bounded(depth) || !expect("{"))
      return {};
    uint32_t id = decl.bodies.size();
    decl.bodies.emplace_back();
    SyntaxBody b;
    b.span = current().span;
    b.region = region;
    while (!atEnd() && !at("}")) {
      if (take("stop")) {
        if (protocol || current().kind != TokenKind::String) {
          fail("source.mode", "local stop requires a reason string");
          return {};
        }
        b.stopped = true;
        b.stopReason = text().drop_front().drop_back().str();
        advance();
        if (!expect(";"))
          return {};
        break;
      }
      if (take("return")) {
        b.returned = true;
        if (region) {
          fail("source.return", "nested blocks use a final expression");
          return {};
        }
        bool named = protocol && at("(") &&
                     (decl.outputs.size() != 1 ||
                      (cursor + 2 < tokens.size() &&
                       StringRef(source.text)
                               .slice(tokens[cursor + 2].span.begin,
                                      tokens[cursor + 2].span.end) == "="));
        if (named) {
          advance();
          if (!at(")"))
            do {
              Span itemSpan = current().span;
              std::string n;
              if (!name(n))
                return {};
              std::optional<uint32_t> value;
              if (take("="))
                value = expression(decl, depth);
              else {
                Expression shorthand;
                shorthand.kind = Expression::Kind::Name;
                shorthand.text = n;
                shorthand.span = itemSpan;
                value = decl.expressions.size();
                decl.expressions.push_back(std::move(shorthand));
              }
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
          b.results.emplace_back(protocol ? std::string{} : "result", *value);
        }
        if (!expect(";"))
          return {};
        break;
      }
      Statement s;
      s.span = current().span;
      if (take("require")) {
        s.kind = Statement::Kind::Require;
        if (take("@")) {
          s.owner.emplace();
          if (!protocol) {
            fail("source.roles", "require owner belongs to protocol mode");
            return {};
          }
          if (!name(*s.owner))
            return {};
        }
      } else if (take("let")) {
        s.mutableBinding = take("mut");
        auto p = pattern(depth);
        if (!p)
          return {};
        s.pattern = std::move(*p);
        if (s.mutableBinding && s.pattern.kind != Pattern::Kind::Name) {
          fail("source.binding", "let mut requires one binding name");
          return {};
        }
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
      } else if (take("drop"))
        s.kind = Statement::Kind::Drop;
      else if (take("consume"))
        s.kind = Statement::Kind::Consume;
      else if (current().kind == TokenKind::Word &&
               cursor + 1 < tokens.size() &&
               StringRef(source.text)
                       .slice(tokens[cursor + 1].span.begin,
                              tokens[cursor + 1].span.end) == "=") {
        s.kind = Statement::Kind::Assign;
        s.pattern.span = current().span;
        if (!name(s.pattern.name) || !expect("="))
          return {};
      } else
        s.kind = Statement::Kind::Expression;
      if (take("send")) {
        if (!protocol || (s.kind != Statement::Kind::Let &&
                          s.kind != Statement::Kind::Assign &&
                          s.kind != Statement::Kind::Expression)) {
          fail("source.send", "send requires a protocol statement");
          return {};
        }
        std::string from, to;
        if (!name(from) || !expect("->") || !name(to) || !expect("("))
          return {};
        s.exchange = std::make_pair(std::move(from), std::move(to));
      }
      auto expr =
          expression(decl, depth, 0, true,
                     s.kind == Statement::Kind::Expression && !s.exchange);
      if (!expr)
        return {};
      s.expression = *expr;
      if (s.exchange && !expect(")"))
        return {};
      s.terminated = take(";");
      auto kind = decl.expressions[*expr].kind;
      bool blockLike =
          kind == Expression::Kind::Block || kind == Expression::Kind::If ||
          kind == Expression::Kind::Match || kind == Expression::Kind::For;
      if (!s.terminated) {
        if (region && at("}") && s.kind == Statement::Kind::Expression &&
            !s.exchange) {
          b.results.emplace_back("result", *expr);
          break;
        }
        if (s.kind != Statement::Kind::Expression || !blockLike) {
          fail("source.syntax", "expected ';' or a block result");
          return {};
        }
      }
      s.span.end = previousEnd;
      b.statements.push_back(std::move(s));
    }
    if (!expect("}"))
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
