#include "Lexer.h"
#include "Tree.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>
#include <set>

using namespace llvm;
namespace zkc::frontend {
namespace {
class Parser {
  StringRef text, filename;
  uint32_t file = 0;
  ArrayRef<Token> tokens;
  size_t cursor = 0, errorOffset = 0, lastEnd = 0;
  std::string errorCode, message;
  bool explicitBindings = false;
  bool recovering = false;
  bool recordLiteral = true;
  std::vector<syntax::ParseDiagnostic> diagnostics;
  std::set<std::string> explicitSites;
  std::vector<bool> anonymousSites;
  // Whether the last name read was written quoted, for clauses whose common
  // records keep only the spelling.
  bool quotedName = false;

  const Token &token() const { return tokens[cursor]; }
  bool failed() const { return !errorCode.empty(); }
  bool fail(StringRef code, const Twine &why) {
    if (!failed()) {
      errorOffset = token().offset;
      errorCode = code.str();
      message = why.str();
    }
    return false;
  }
  void advance() {
    lastEnd = token().offset + token().spelling.size();
    if (cursor + 1 < tokens.size())
      ++cursor;
    skipComments();
  }
  void skipComments() {
    while (token().kind == TokenKind::Comment)
      ++cursor;
  }
  bool eat(StringRef value) {
    if (failed() || !token().is(value))
      return false;
    advance();
    return true;
  }
  bool expect(StringRef value) {
    return eat(value) || fail("source-syntax", "expected '" + value + "'");
  }
  std::string keyword() {
    if (failed())
      return {};
    if (token().kind != TokenKind::Name) {
      fail("source-syntax", "expected a bare keyword");
      return {};
    }
    auto result = token().spelling.str();
    advance();
    return result;
  }
  const Token &nextToken(unsigned count = 1) const {
    size_t next = cursor;
    while (count--)
      do {
        if (next + 1 == tokens.size())
          return tokens[next];
        ++next;
      } while (tokens[next].kind == TokenKind::Comment);
    return tokens[next];
  }
  std::string name() {
    quotedName = false;
    if (failed())
      return {};
    Token t = token();
    if (t.kind != TokenKind::Name && t.kind != TokenKind::String) {
      fail("source-syntax", "expected a name or quoted string");
      return {};
    }
    advance();
    if (t.kind == TokenKind::String) {
      quotedName = true;
      // The lexer has already validated quoted strings.
      auto value = json::parse(t.spelling);
      if (!value) {
        consumeError(value.takeError());
        fail("source-string", "invalid quoted string");
        return {};
      }
      return value->getAsString()->str();
    }
    return t.spelling.str();
  }
  syntax::Atom atom() {
    syntax::Atom result;
    size_t start = token().offset;
    result.kind = token().kind == TokenKind::String ? syntax::Atom::Kind::String
                  : token().kind == TokenKind::Number
                      ? syntax::Atom::Kind::Number
                      : syntax::Atom::Kind::Name;
    result.value = token().kind == TokenKind::Number ? number() : name();
    return record(std::move(result), start);
  }
  syntax::StaticTerm staticTerm() {
    syntax::StaticTerm result;
    result.root = atom();
    while (eat("::")) {
      result.members.push_back(name());
      if (result.members.size() > 32768)
        fail("source-limit", "static path exceeds 32768 members");
    }
    return result;
  }
  std::string termSpelling(const syntax::StaticTerm &term) {
    std::string out = term.root.value;
    for (const auto &member : term.members)
      out += "." + member;
    return out;
  }
  std::string number() {
    if (failed())
      return {};
    if (token().kind != TokenKind::Number) {
      fail("source-syntax", "expected a natural number");
      return {};
    }
    std::string result = token().spelling.str();
    advance();
    return result;
  }
  // Only authored :: separators become dots; dotted/quoted roots are opaque.
  std::string path(bool *qualified = nullptr,
                   bool *trailingSeparator = nullptr) {
    if (trailingSeparator)
      *trailingSeparator = false;
    std::string result = name();
    size_t members = 0;
    while (eat("::")) {
      if (trailingSeparator && token().is("<")) {
        *trailingSeparator = true;
        break;
      }
      if (++members > 32768) {
        fail("source-limit", "path exceeds 32768 members");
        break;
      }
      if (qualified)
        *qualified = true;
      result += "." + name();
    }
    return result;
  }
  template <typename T> T record(T value, size_t offset) {
    value.location =
        source::Span{offset, std::max(offset, lastEnd) - offset, file};
    return value;
  }
  template <typename F> auto list(StringRef open, StringRef close, F element) {
    std::vector<decltype(element())> result;
    expect(open);
    if (eat(close))
      return result;
    while (!failed()) {
      result.push_back(element());
      if (result.size() > 32768) {
        fail("source-limit", "list exceeds 32768 entries");
        break;
      }
      if (eat(close))
        break;
      expect(",");
      if (eat(close))
        break;
    }
    return result;
  }
  source::Names staticTerms(std::vector<syntax::StaticTerm> &terms) {
    return list("<", ">", [&] {
      terms.push_back(staticTerm());
      return termSpelling(terms.back());
    });
  }
  source::Names atoms(std::vector<syntax::Atom> &out) {
    return list("(", ")", [&] {
      out.push_back(atom());
      return out.back().value;
    });
  }
  syntax::Type type(unsigned depth = 0) {
    size_t start = token().offset;
    syntax::Type result;
    if (depth > 64) {
      fail("source-depth", "type nesting exceeds 64");
      return result;
    }
    if (token().is("(")) {
      advance();
      result.product = true;
      if (eat(")"))
        return record(std::move(result), start);
      auto first = type(depth + 1);
      if (!eat(",")) {
        expect(")");
        return first;
      }
      result.arguments.push_back(std::move(first));
      while (!failed() && !eat(")")) {
        result.arguments.push_back(type(depth + 1));
        if (result.arguments.size() > 32768) {
          fail("source-limit", "product exceeds 32768 elements");
          break;
        }
        if (eat(")"))
          break;
        expect(",");
      }
      return record(std::move(result), start);
    }
    result.quoted = token().kind == TokenKind::String;
    result.natural = token().kind == TokenKind::Number;
    result.name = result.natural ? number() : name();
    if (token().is("<"))
      result.arguments = list("<", ">", [&] { return type(depth + 1); });
    while (eat("::")) {
      result.members.push_back(name());
      if (result.members.size() > 32768)
        fail("source-limit", "type path exceeds 32768 members");
    }
    return record(std::move(result), start);
  }
  source::Names names() {
    return list("(", ")", [&] { return name(); });
  }
  source::Assignments pairs(bool numeric = false, bool statics = false) {
    return list("(", ")", [&] {
      auto key = name();
      expect("=");
      auto value = numeric ? number() : statics ? path() : name();
      return std::make_pair(std::move(key), std::move(value));
    });
  }
  std::string site() {
    bool anonymous = !eat("[");
    anonymousSites.push_back(anonymous);
    if (anonymous)
      return {};
    auto result = name();
    expect("]");
    explicitSites.insert(result);
    return result;
  }
  void resolveAnonymous(syntax::Body &content) {
    // A definition, including nested loops, has one preorder site namespace.
    size_t index = 0, next = 0;
    auto visit = [&](auto &&self, syntax::Body &body) -> void {
      for (auto &instruction : body) {
        if (!std::holds_alternative<syntax::Finish>(instruction.value) &&
            !std::holds_alternative<syntax::Exit>(instruction.value) &&
            !std::holds_alternative<source::Return>(instruction.value) &&
            !std::holds_alternative<source::Yield>(instruction.value)) {
          if (anonymousSites[index++]) {
            do {
              instruction.site = "__site_" + std::to_string(next++);
            } while (explicitSites.count(instruction.site));
          }
        }
        if (auto *placement =
                std::get_if<syntax::Placement>(&instruction.value))
          self(self, placement->body);
        if (auto *loop = std::get_if<syntax::Loop>(&instruction.value))
          self(self, loop->body);
        if (auto *loop = std::get_if<syntax::For>(&instruction.value))
          self(self, loop->body);
        if (auto *loop =
                std::get_if<syntax::ArrayTraversal>(&instruction.value))
          self(self, loop->body);
        if (auto *match = std::get_if<syntax::Match>(&instruction.value))
          for (auto &arm : match->arms)
            self(self, arm.body);
        if (auto *branch =
                std::get_if<syntax::Conditional>(&instruction.value)) {
          self(self, branch->thenBody);
          self(self, branch->elseBody);
        }
        auto expression = [&](auto &&walk, syntax::Expression &e) -> void {
          for (auto &operand : e.operands)
            walk(walk, operand);
          if (e.traversal)
            self(self, e.traversal->body);
        };
        if (auto *binding = std::get_if<syntax::Binding>(&instruction.value))
          expression(expression, binding->expression);
        if (auto *exit = std::get_if<syntax::Exit>(&instruction.value))
          expression(expression, exit->expression);
        if (auto *branch = std::get_if<syntax::Conditional>(&instruction.value))
          expression(expression, branch->condition);
        if (auto *loop = std::get_if<syntax::For>(&instruction.value)) {
          expression(expression, loop->lower);
          expression(expression, loop->upper);
        }
      }
    };
    visit(visit, content);
  }
  std::vector<syntax::Parameter> arguments() {
    return list("(", ")", [&] {
      auto argument = name();
      expect(":");
      return syntax::Parameter{std::move(argument), type()};
    });
  }
  std::vector<syntax::OwnedParameter> ownedArguments() {
    return list("(", ")", [&] {
      auto role = name();
      auto argument = name();
      expect(":");
      return syntax::OwnedParameter{std::move(argument), std::move(role),
                                    type()};
    });
  }
  std::vector<syntax::Type> results() { return {type()}; }
  source::Names values() {
    if (token().is(";"))
      return {};
    return token().is("(") ? names() : source::Names{name()};
  }
  // Operators have a fixed table: unary minus binds tightest, then `*`, then
  // `+` and `-`; binary operators associate to the left.
  syntax::Expression expression(unsigned depth = 0) { return binary(depth, 0); }
  syntax::Expression binary(unsigned depth, unsigned level) {
    if (level == 2)
      return unary(depth);
    size_t start = token().offset;
    auto result = binary(depth, level + 1);
    while (!failed() && (level == 0 ? token().is("+") || token().is("-")
                                    : (token().is("*") || token().is("/") ||
                                       token().is("%")))) {
      if (++depth > 64) {
        fail("source-depth", "expression nesting exceeds 64");
        break;
      }
      syntax::Expression operation;
      operation.kind = syntax::Expression::Kind::Operator;
      operation.name = token().spelling.str();
      advance();
      operation.operands.push_back(std::move(result));
      operation.operands.push_back(binary(depth, level + 1));
      result = record(std::move(operation), start);
    }
    return result;
  }
  syntax::Expression unary(unsigned depth) {
    if (!token().is("-"))
      return primary(depth);
    size_t start = token().offset;
    if (depth > 64) {
      fail("source-depth", "expression nesting exceeds 64");
      return {};
    }
    syntax::Expression operation;
    operation.kind = syntax::Expression::Kind::Operator;
    operation.name = "-";
    advance();
    operation.operands.push_back(unary(depth + 1));
    return record(std::move(operation), start);
  }
  syntax::Expression primary(unsigned depth) {
    using Kind = syntax::Expression::Kind;
    size_t start = token().offset;
    syntax::Expression result;
    if (depth > 64) {
      fail("source-depth", "expression nesting exceeds 64");
      return result;
    }
    if ((token().is("map") || token().is("fold")) && !nextToken().is("(")) {
      bool fold = eat("fold");
      if (!fold)
        expect("map");
      result.kind = fold ? Kind::Fold : Kind::Map;
      result.traversal = std::make_shared<syntax::LexicalTraversal>();
      bool allowRecord = recordLiteral;
      recordLiteral = true; // The following pipe delimits the operand.
      result.operands.push_back(expression(depth + 1));
      if (fold) {
        expect("with");
        result.operands.push_back(expression(depth + 1));
      }
      expect("|");
      if (fold) {
        result.traversal->state = name();
        expect(",");
      }
      result.traversal->element = name();
      expect("|");
      expect("{");
      recordLiteral = true;
      result.traversal->body = body(true, depth + 1);
      recordLiteral = allowRecord;
    } else if (token().is("(")) {
      advance();
      bool allowRecord = recordLiteral;
      recordLiteral = true;
      if (eat(")")) {
        result.kind = Kind::Product;
      } else {
        result = expression(depth + 1);
        if (eat(",")) {
          syntax::Expression tuple;
          tuple.kind = Kind::Product;
          tuple.operands.push_back(std::move(result));
          while (!failed() && !eat(")")) {
            tuple.operands.push_back(expression(depth + 1));
            if (tuple.operands.size() > 32768)
              fail("source-limit", "product exceeds 32768 elements");
            if (eat(")"))
              break;
            expect(",");
          }
          result = std::move(tuple);
        } else
          expect(")");
      }
      recordLiteral = allowRecord;
    } else if (token().kind == TokenKind::Number) {
      result.kind = Kind::Index;
      result.name = number();
    } else if (token().is("true") || token().is("false")) {
      result.kind = Kind::Boolean;
      result.name = keyword();
    } else if (token().is("[")) {
      result.kind = Kind::Vector;
      result.operands = list("[", "]", [&] { return expression(depth + 1); });
    } else {
      bool trailing = false;
      bool quoted = token().kind == TokenKind::String;
      result.quoted = quoted;
      result.name = path(&result.qualified, &trailing);
      if (trailing)
        result.staticArguments = staticTerms(result.staticTerms);
      if (recordLiteral && token().is("{") && !result.qualified && !quoted) {
        result.kind = Kind::Struct;
        result.operands = list("{", "}", [&] {
          auto field = name();
          result.fields.push_back(field);
          if (eat(":"))
            return expression(depth + 1);
          syntax::Expression value;
          value.name = field;
          value.location = record(syntax::Expression{}, start).location;
          return value;
        });
      } else if (token().is("(") && !result.qualified && !quoted &&
                 (nextToken().kind == TokenKind::Name ||
                  nextToken().kind == TokenKind::String) &&
                 nextToken(2).is("=")) {
        // A keyed list constructs a struct; a call's operands are never keyed.
        result.kind = Kind::Struct;
        result.operands = list("(", ")", [&] {
          result.fields.push_back(name());
          expect("=");
          return expression(depth + 1);
        });
      } else if (token().is("(")) {
        result.kind = Kind::Call;
        result.operands = list("(", ")", [&] {
          if (nextToken().is(":")) {
            result.argumentNames.push_back(name());
            expect(":");
          } else
            result.argumentNames.push_back({});
          return expression(depth + 1);
        });
        if (llvm::all_of(result.argumentNames,
                         [](const auto &s) { return s.empty(); }))
          result.argumentNames.clear();
        if (!quoted && !result.qualified && !result.staticArguments &&
            StringRef(result.name).ends_with(".len") &&
            result.operands.empty()) {
          result.kind = Kind::Length;
          syntax::Expression collection;
          collection.name = StringRef(result.name).drop_back(4).str();
          collection.location = record(syntax::Expression{}, start).location;
          result.operands.push_back(std::move(collection));
          result.name.clear();
        }
        if (eat("attributes")) {
          if (result.kind != Kind::Call)
            fail("source-expression",
                 "only an operation call accepts attributes");
          result.attributes = atoms(result.attributeAtoms);
        }
      } else if (trailing || result.qualified)
        fail("source-expression", "a qualified expression must be a call");
    }
    unsigned suffixDepth = depth;
    while (!failed() && eat("[")) {
      if (++suffixDepth > 64) {
        fail("source-depth", "expression nesting exceeds 64");
        break;
      }
      syntax::Expression indexed;
      indexed.kind = Kind::Get;
      indexed.operands.push_back(std::move(result));
      indexed.operands.push_back(expression(depth + 1));
      expect("]");
      result = std::move(indexed);
    }
    return record(std::move(result), start);
  }
  syntax::Instruction localInstruction(unsigned depth) {
    size_t start = token().offset;
    syntax::Instruction result;
    if (eat("match")) {
      result.site = site();
      result.explicitSite = !anonymousSites.back();
      syntax::Match match;
      match.input = name();
      if (eat("capture")) {
        match.explicitCaptures = true;
        match.captures = names();
      }
      expect("->");
      match.outputs = names();
      expect("{");
      while (!failed() && !eat("}")) {
        size_t armStart = token().offset;
        syntax::MatchArm arm;
        arm.alternative = name();
        arm.payload = names();
        expect("=>");
        expect("{");
        arm.body = body(true, depth + 1);
        match.arms.push_back(record(std::move(arm), armStart));
        if (match.arms.size() > 32)
          fail("library-source-match", "match exceeds 32 alternatives");
        if (!token().is("}"))
          expect(",");
      }
      result.value = std::move(match);
    } else if (eat("if")) {
      result.site = site();
      result.explicitSite = !anonymousSites.back();
      syntax::Conditional branch;
      recordLiteral = false;
      branch.condition = expression();
      recordLiteral = true;
      if (eat("capture")) {
        branch.explicitCaptures = true;
        branch.explicitRegion = true;
        branch.captures = names();
        expect("->");
        branch.outputs = names();
      } else if (eat("->")) {
        branch.explicitRegion = true;
        branch.outputs = names();
      }
      expect("{");
      branch.thenBody = body(true, depth + 1);
      if (eat("else")) {
        expect("{");
        branch.elseBody = body(true, depth + 1);
      } else if (branch.explicitRegion)
        fail("source-control", "an explicit conditional requires both regions");
      result.value = std::move(branch);
    } else if (eat("for")) {
      result.site = site();
      result.explicitSite = !anonymousSites.back();
      syntax::For loop;
      loop.induction = name();
      expect("in");
      recordLiteral = false;
      loop.lower = expression();
      recordLiteral = true;
      if (token().is("carry")) {
        syntax::ArrayTraversal traversal;
        traversal.element = loop.induction;
        if (loop.lower.kind != syntax::Expression::Kind::Name ||
            loop.lower.quoted)
          fail("library-source-traversal", "traversal requires a named array");
        traversal.input = loop.lower.name;
        expect("carry");
        traversal.carried = pairs();
        if (eat("capture")) {
          traversal.explicitCaptures = true;
          traversal.captures = names();
        }
        expect("->");
        traversal.outputs = names();
        expect("{");
        traversal.body = body(true, depth + 1);
        result.value = std::move(traversal);
        return record(std::move(result), start);
      }
      expect("..");
      recordLiteral = false;
      loop.upper = expression();
      recordLiteral = true;
      if (eat("carry")) {
        loop.explicitRegion = true;
        loop.carried = pairs();
        if (eat("capture")) {
          loop.explicitCaptures = true;
          loop.captures = names();
        }
        expect("->");
        loop.outputs = names();
      }
      expect("{");
      loop.body = body(true, depth + 1);
      result.value = std::move(loop);
    } else {
      result.site = site();
      result.explicitSite = !anonymousSites.back();
      syntax::Binding binding;
      if (eat("let")) {
        binding.mutableBinding = eat("mut");
        binding.destructure = token().is("(");
        binding.outputs = binding.destructure ? names() : source::Names{name()};
        if (eat(":"))
          binding.annotation = results();
        expect("=");
        binding.expression = expression();
      } else if ((token().kind == TokenKind::Name ||
                  token().kind == TokenKind::String) &&
                 nextToken().is("=")) {
        binding.assignment = true;
        binding.outputs = {name()};
        expect("=");
        binding.expression = expression();
      } else
        binding.expression = expression();
      if (token().is("}") && binding.outputs.empty() && !binding.assignment) {
        anonymousSites.pop_back();
        result.site.clear();
        result.value = syntax::Exit{std::move(binding.expression)};
        return record(std::move(result), start);
      }
      expect(";");
      // Preserve existing inspection and profile handling for ordinary calls.
      const auto &expr = binding.expression;
      // An operator over names is the flat call it is declared to be, so both
      // spellings bind the same temporaries afterwards.
      const bool isOperator = expr.kind == syntax::Expression::Kind::Operator;
      bool flatCall =
          (expr.kind == syntax::Expression::Kind::Call || isOperator) &&
          !binding.mutableBinding && !binding.assignment;
      for (const auto &operand : expr.operands)
        flatCall &= operand.kind == syntax::Expression::Kind::Name;
      if (flatCall) {
        syntax::Call call;
        call.location = expr.location;
        call.callee = expr.name;
        call.qualified = expr.qualified;
        call.quoted = expr.quoted;
        call.staticTerms = expr.staticTerms;
        call.attributeAtoms = expr.attributeAtoms;
        call.staticArguments = expr.staticArguments;
        call.attributes = expr.attributes;
        call.argumentNames = expr.argumentNames;
        call.isOperator = isOperator;
        call.outputs = binding.outputs;
        call.destructure = binding.destructure;
        call.annotation = binding.annotation;
        for (const auto &operand : expr.operands) {
          call.inputs.push_back(operand.name);
          syntax::Atom atom;
          atom.kind = operand.quoted ? syntax::Atom::Kind::String
                                     : syntax::Atom::Kind::Name;
          atom.value = operand.name;
          atom.location = operand.location;
          call.inputAtoms.push_back(std::move(atom));
        }
        result.value = std::move(call);
      } else {
        binding.location = expr.location;
        result.value = std::move(binding);
      }
    }
    return record(std::move(result), start);
  }
  syntax::Call call() {
    size_t start = token().offset;
    syntax::Call result;
    if (eat("let")) {
      result.destructure = token().is("(");
      result.outputs = result.destructure ? names() : source::Names{name()};
      if (eat(":"))
        result.annotation = results();
      expect("=");
    }
    bool trailingSeparator = false;
    result.quoted = token().kind == TokenKind::String;
    result.callee = path(&result.qualified, &trailingSeparator);
    // path consumes the turbofish separator, but never accepts bare <...>.
    if (trailingSeparator)
      result.staticArguments = staticTerms(result.staticTerms);
    result.inputs = atoms(result.inputAtoms);
    if (eat("attributes"))
      result.attributes = atoms(result.attributeAtoms);
    return record(std::move(result), start);
  }
  std::vector<syntax::OwnedResult> ownedResults() {
    return list("(", ")", [&] {
      auto role = name();
      std::string port;
      if (nextToken().is(":")) {
        port = name();
        expect(":");
      }
      return syntax::OwnedResult{std::move(role), type(), std::move(port)};
    });
  }
  std::vector<source::Dependency> dependencies(syntax::Protocol &owner) {
    return list("(", ")", [&] {
      size_t start = token().offset;
      source::Dependency result;
      result.name = name();
      expect(":");
      result.protocol = name();
      if (quotedName)
        owner.quotedDependencies.insert(result.name);
      if (eat("::")) {
        syntax::Protocol::DependencyArguments args;
        args.arguments = list("<", ">", [&] {
          auto key = name();
          expect("=");
          args.terms.push_back(staticTerm());
          return std::make_pair(key, termSpelling(args.terms.back()));
        });
        if (!owner.dependencyArguments.emplace(result.name, std::move(args))
                 .second)
          fail("source-duplicate", "duplicate specialised dependency");
      }
      result.agreements = pairs();
      return record(std::move(result), start);
    });
  }
  syntax::Instruction instruction(bool local, unsigned depth) {
    size_t start = token().offset;
    syntax::Instruction result;
    if (!local && eat("let")) {
      result.site = site();
      result.explicitSite = !anonymousSites.back();
      syntax::Placement placement;
      placement.destructure = token().is("(");
      placement.outputs =
          placement.destructure ? names() : source::Names{name()};
      if (eat(":"))
        placement.annotation = type();
      expect("=");
      expect("local");
      placement.role = name();
      expect("{");
      placement.body = body(true, depth + 1);
      expect(";");
      result.value = std::move(placement);
      return record(std::move(result), start);
    }
    if (!local && eat("finish")) {
      syntax::Finish finish;
      finish.values = list("{", "}", [&] {
        auto port = name();
        auto value = eat(":") ? name() : port;
        return std::make_pair(port, value);
      });
      expect(";");
      result.value = std::move(finish);
      return record(std::move(result), start);
    }
    if (token().is("return") || token().is("yield")) {
      bool isReturn = eat("return");
      if (!isReturn)
        expect("yield");
      if (isReturn && local) {
        syntax::Expression value;
        value.kind = syntax::Expression::Kind::Product;
        if (!token().is(";"))
          value = expression();
        result.value = syntax::Exit{std::move(value)};
      } else if (isReturn)
        result.value = source::Return{values()};
      else
        result.value = source::Yield{values()};
      expect(";");
      return record(std::move(result), start);
    }
    if (local && !token().is("stop")) {
      return localInstruction(depth);
    }
    auto tag = keyword();
    result.site = site();
    result.explicitSite = !anonymousSites.back();
    if (tag == "local") {
      auto role = name();
      if (eat("{")) {
        syntax::Placement placement;
        placement.role = role;
        placement.body = body(true, depth + 1);
        expect(";");
        result.value = std::move(placement);
        return record(std::move(result), start);
      }
      expect(":");
      auto value = call();
      value.role = std::move(role);
      result.value = std::move(value);
    } else if (tag == "message") {
      source::Message message;
      message.schema = name();
      expect(":");
      message.sender = name();
      expect("(");
      message.input = name();
      expect(")");
      expect("->");
      message.receiver = name();
      expect("(");
      message.output = name();
      expect(")");
      result.value = std::move(message);
    } else if (tag == "invoke") {
      syntax::Invocation call;
      call.callee = name();
      call.inputs = names();
      expect("->");
      if (token().is("{")) {
        call.outputs = list("{", "}", [&] {
          auto port = name();
          call.resultNames.push_back(port);
          return eat(":") ? name() : port;
        });
      } else
        call.outputs = names();
      result.value = std::move(call);
    } else if (tag == "stop") {
      source::Stop stop;
      auto first = name();
      if (token().is(";"))
        stop.reason = std::move(first);
      else {
        stop.role = std::move(first);
        stop.reason = name();
      }
      result.value = std::move(stop);
    } else if (tag == "loop") {
      syntax::Loop loop;
      loop.countAtom = atom();
      loop.count.kind = loop.countAtom->kind == syntax::Atom::Kind::Number
                            ? source::LoopCount::Kind::Constant
                            : source::LoopCount::Kind::Parameter;
      loop.count.value = loop.countAtom->value;
      expect("carry");
      loop.carried = pairs();
      if (eat("capture")) {
        loop.explicitCaptures = true;
        loop.captures = names();
      }
      expect("->");
      loop.outputs = names();
      expect("{");
      loop.body = body(false, depth + 1);
      result.value = std::move(loop);
      return record(std::move(result), start);
    } else
      fail("source-syntax",
           "expected local, message, invoke, loop, stop, or return");
    expect(";");
    return record(std::move(result), start);
  }
  syntax::Body body(bool local, unsigned depth = 0) {
    syntax::Body result;
    if (depth == 0) {
      explicitSites.clear();
      anonymousSites.clear();
    }
    if (depth > 64) {
      fail("source-depth", "body nesting exceeds 64");
      return result;
    }
    while (!failed() && !eat("}")) {
      result.push_back(instruction(local, depth));
      if (result.size() > 32768)
        fail("source-limit", "body exceeds 32768 instructions");
    }
    if (depth == 0 && !failed())
      resolveAnonymous(result);
    return result;
  }
  std::vector<syntax::StaticParameter> staticParameters() {
    return list("<", ">", [&] {
      size_t offset = token().offset;
      syntax::StaticParameter parameter;
      parameter.name = name();
      expect(":");
      if (eat("domain"))
        parameter.sort = name();
      else {
        do {
          parameter.bounds.push_back(name());
        } while (eat("+"));
      }
      return record(std::move(parameter), offset);
    });
  }
  void structure(syntax::Module &module, size_t start, bool checked) {
    syntax::Struct result;
    result.checked = checked;
    result.name = name();
    if (token().is("<"))
      result.parameters = staticParameters();
    auto constructors = [&] {
      return list("(", ")", [&] {
        auto constructor = name();
        if (quotedName)
          result.quotedConstructors.insert(constructor);
        return constructor;
      });
    };
    if (eat("constructors")) {
      result.checked = true;
      result.constructors = constructors();
    }
    bool braces = token().is("{");
    if (braces)
      result.fields = list("{", "}", [&] {
        auto field = name();
        expect(":");
        return syntax::Parameter{std::move(field), type()};
      });
    else
      result.fields = arguments();
    if (checked) {
      if (!eat("constructors"))
        fail("source-syntax", "a checked struct names its constructors");
      result.constructors = constructors();
    }
    if (braces)
      eat(";");
    else
      expect(";");
    module.structs.push_back(record(std::move(result), start));
  }
  std::vector<source::Requirement> requirementList(
      std::vector<std::vector<syntax::StaticTerm>> *metadata = nullptr) {
    return list("(", ")", [&] {
      size_t offset = token().offset;
      source::Requirement requirement;
      requirement.predicate = name();
      std::vector<syntax::StaticTerm> terms;
      requirement.arguments = list("(", ")", [&] {
        terms.push_back(staticTerm());
        return termSpelling(terms.back());
      });
      if (metadata)
        metadata->push_back(std::move(terms));
      return record(std::move(requirement), offset);
    });
  }
  void
  whereRequirements(std::vector<source::Requirement> &requirements,
                    std::vector<std::vector<syntax::StaticTerm>> &metadata) {
    do {
      size_t offset = token().offset;
      auto subject = staticTerm();
      if (eat("==")) {
        auto right = staticTerm();
        source::Requirement r;
        r.predicate = "=";
        r.arguments = {termSpelling(subject), termSpelling(right)};
        requirements.push_back(record(std::move(r), offset));
        metadata.push_back({subject, right});
      } else if (token().is("(")) {
        if (!subject.members.empty())
          fail("source-syntax",
               "a predicate has a declared name, not a domain projection");
        source::Requirement r;
        r.predicate = subject.root.value;
        std::vector<syntax::StaticTerm> terms;
        r.arguments = list("(", ")", [&] {
          terms.push_back(staticTerm());
          return termSpelling(terms.back());
        });
        requirements.push_back(record(std::move(r), offset));
        metadata.push_back(std::move(terms));
      } else {
        expect(":");
        do {
          source::Requirement r;
          r.predicate = name();
          r.arguments = {termSpelling(subject)};
          requirements.push_back(record(std::move(r), offset));
          metadata.push_back({subject});
        } while (eat("+"));
      }
      if (requirements.size() > 32768)
        fail("source-limit", "requirements exceed 32768 entries");
      if (!eat(","))
        break;
      if (token().is("{") ||
          ((token().is("requires") || token().is("external") ||
            token().is("origin")) &&
           !nextToken().is(":") && !nextToken().is("::")))
        break;
    } while (!failed());
  }
  void function(syntax::Module &module, size_t start, bool signature = false) {
    syntax::Function result;
    result.name = name();
    result.generic = token().is("<");
    if (result.generic)
      result.parameters = staticParameters();
    result.arguments = arguments();
    expect("->");
    result.results = results();
    if (eat("where"))
      whereRequirements(result.requirements, result.requirementTerms);
    if (eat("requires")) {
      auto requirements = requirementList(&result.requirementTerms);
      result.requirements.insert(result.requirements.end(),
                                 requirements.begin(), requirements.end());
      if (result.requirements.size() > 32768)
        fail("source-limit", "requirements exceed 32768 entries");
    }
    if (eat("effects"))
      result.effects = names();
    if (explicitBindings && !result.generic)
      result.origin = source::LogicalOrigin{result.name, {}};
    if (eat("origin")) {
      result.explicitOrigin = true;
      source::LogicalOrigin origin;
      origin.definition = name();
      origin.arguments = pairs(false, true);
      result.origin = std::move(origin);
    }
    if (signature)
      expect(";");
    else if (eat("external"))
      expect(";");
    else {
      expect("{");
      result.body = body(true);
    }
    module.functions.push_back(record(std::move(result), start));
  }
  syntax::Protocol protocol(size_t start) {
    syntax::Protocol result;
    result.name = name();
    result.generic = token().is("<");
    if (result.generic)
      result.staticParameters = staticParameters();
    if (eat("where"))
      whereRequirements(result.requirements, result.requirementTerms);
    if (eat("requires")) {
      auto extra = requirementList(&result.requirementTerms);
      result.requirements.insert(result.requirements.end(), extra.begin(),
                                 extra.end());
    }
    expect("{");
    std::set<std::string> headers;
    while (!failed()) {
      if (token().kind != TokenKind::Name)
        break;
      StringRef key = token().spelling;
      if (key != "roles" && key != "parameters" && key != "inputs" &&
          key != "outputs" && key != "dependencies")
        break;
      if (!headers.insert(key.str()).second)
        fail("source-duplicate", "duplicate protocol clause '" + key + "'");
      advance();
      if (key == "roles")
        result.roles = names();
      else if (key == "parameters")
        result.parameters = names();
      else if (key == "inputs")
        result.arguments = ownedArguments();
      else if (key == "outputs")
        result.results = ownedResults();
      else
        result.dependencies = dependencies(result);
      expect(";");
    }
    if (!headers.count("roles"))
      fail("source-syntax", "protocol requires an explicit roles clause");
    if (eat("external")) {
      expect(";");
      expect("}");
    } else
      result.body = body(false);
    return record(std::move(result), start);
  }
  source::Instance instance(size_t start, syntax::Module &module) {
    source::Instance result;
    result.name = name();
    expect(":");
    auto protocol = staticTerm();
    result.protocol = termSpelling(protocol);
    module.instanceProtocolTerms.emplace(result.name, std::move(protocol));
    expect("{");
    std::set<std::string> headers;
    while (!failed() && !eat("}")) {
      auto key = keyword();
      if (!headers.insert(key).second)
        fail("source-duplicate", "duplicate instance clause '" + key + "'");
      if (key == "parameters") {
        auto &metadata = module.instanceParameterAtoms[result.name];
        result.parameters = list("(", ")", [&] {
          auto key = name();
          expect("=");
          source::ParameterBinding value;
          if (eat("ingress")) {
            expect("(");
            metadata.push_back(atom());
            source::FamilyIngress ingress;
            ingress.bound = metadata.back().value;
            expect(",");
            do {
              auto role = name();
              expect("=");
              auto function = name();
              if (quotedName)
                module.quotedSelectors.insert({result.name, key, role});
              auto arguments = names();
              ingress.selectors.push_back(
                  {role, function, std::move(arguments)});
            } while (eat(","));
            expect(")");
            value = std::move(ingress);
          } else {
            metadata.push_back(atom());
            value = metadata.back().value;
          }
          return std::make_pair(key, std::move(value));
        });
      } else if (key == "dependencies")
        result.dependencies = list("(", ")", [&] {
          auto alias = name();
          expect("=");
          auto target = name();
          if (quotedName)
            module.quotedInstanceDependencies.insert({result.name, alias});
          return std::make_pair(std::move(alias), std::move(target));
        });
      else if (key == "roles")
        result.roles = pairs();
      else
        fail("source-syntax", "expected parameters, dependencies, or roles");
      expect(";");
    }
    if (!headers.count("roles"))
      fail("source-syntax", "instance requires an explicit roles clause");
    return record(std::move(result), start);
  }
  syntax::LibraryTerm libraryTerm(unsigned depth = 0) {
    size_t start = token().offset;
    syntax::LibraryTerm result;
    if (depth > 64) {
      fail("library-source-limit", "static selection depth exceeds 64");
      return result;
    }
    result.root = atom();
    if (token().is("<")) {
      result.applied = true;
      result.arguments = list("<", ">", [&] { return libraryTerm(depth + 1); });
    }
    while (eat("::")) {
      result.members.push_back(name());
      if (result.members.size() > 64)
        fail("library-source-limit", "static member depth exceeds 64");
    }
    return record(std::move(result), start);
  }
  void libraryMembers(syntax::LibraryInterface &result, bool concrete) {
    expect("{");
    size_t count = 0;
    while (!failed() && !eat("}")) {
      size_t start = token().offset;
      auto tag = keyword();
      if (++count > 4096)
        fail("library-source-limit",
             "library declaration exceeds 4096 members");
      if (tag == "type") {
        syntax::LibraryTypeMember member;
        member.name = name();
        if (concrete) {
          expect("=");
          member.representation = type();
        } else {
          std::set<std::string> permissions;
          while (!failed() && !token().is(";")) {
            auto permission = keyword();
            if (!permissions.insert(permission).second)
              fail("library-source-permission", "duplicate permission");
            if (permission == "copy")
              member.copy = true;
            else if (permission == "drop")
              member.drop = true;
            else
              fail("library-source-permission", "expected copy or drop");
          }
        }
        expect(";");
        result.types.push_back(record(std::move(member), start));
      } else if (tag == "nat" || tag == "domain" || tag == "association") {
        syntax::LibraryStaticMember member;
        member.sort = tag;
        member.name = name();
        if (tag == "domain") {
          expect(":");
          member.domain = name();
        }
        if (eat("="))
          member.equation = libraryTerm();
        else if (concrete)
          fail("library-source-static", "component member needs an equation");
        expect(";");
        result.statics.push_back(record(std::move(member), start));
      } else if (tag == "facet") {
        if (concrete)
          fail("library-source-facet",
               "facet declarations belong to interfaces");
        syntax::LibraryFacet facet;
        if (eat("required"))
          facet.required = true;
        else if (eat("optional"))
          facet.required = false;
        else
          fail("library-source-facet",
               "facet requires required or optional status");
        facet.owner = name();
        facet.name = name();
        expect(";");
        result.facets.push_back(record(std::move(facet), start));
      } else if (tag == "local") {
        syntax::Module holder;
        function(holder, start, !concrete);
        result.functions.push_back(std::move(holder.functions.front()));
      } else
        fail("library-source-member",
             "expected type, nat, domain, association or local");
    }
  }
  syntax::LibraryIdentity libraryIdentity(size_t start) {
    syntax::LibraryIdentity identity;
    auto fields = pairs();
    std::set<std::string> seen;
    for (const auto &[key, value] : fields) {
      if (!seen.insert(key).second)
        fail("library-source-identity", "duplicate identity field");
      if (key == "namespace")
        identity.nameSpace = value;
      else if (key == "name")
        identity.name = value;
      else if (key == "version")
        identity.version = value;
      else if (key == "resolution")
        identity.resolution = value;
      else
        fail("library-source-identity", "unknown identity field");
    }
    if (seen.size() != 4 || identity.nameSpace.empty() ||
        identity.name.empty() || identity.version.empty() ||
        identity.resolution.empty())
      fail("library-source-identity",
           "library requires namespace, name, version and resolution");
    return record(std::move(identity), start);
  }
  void use(syntax::Module &module, bool exported, size_t start,
           source::Names prefix = {}, unsigned depth = 0) {
    if (depth > 64) {
      fail("source-depth", "import path exceeds 64 levels");
      return;
    }
    prefix.push_back(keyword());
    while (eat("::")) {
      if (eat("{")) {
        do {
          use(module, exported, start, prefix, depth + 1);
          if (eat("}"))
            return;
          expect(",");
        } while (!failed() && !eat("}"));
        return;
      }
      prefix.push_back(keyword());
      if (prefix.size() > 64) {
        fail("source-depth", "import path exceeds 64 levels");
        return;
      }
    }
    syntax::Use item;
    item.name = eat("as") ? keyword() : prefix.back();
    item.path = std::move(prefix);
    item.exported = exported;
    module.uses.push_back(record(std::move(item), start));
  }
  syntax::Module module(bool carrier = false) {
    syntax::Module result;
    result.carrier = carrier;
    explicitBindings = token().is("{");
    if (!explicitBindings)
      result.profile = name();
    expect("{");
    while (!failed() && !eat("}")) {
      size_t start = token().offset;
      syntax::Module declaration;
      size_t declarationCursor = cursor;
      bool exported = eat("pub");
      auto tag = keyword();
      // This closed list cannot allocate authored-project generated symbols;
      // it is what makes the carrier exception to reservedPrefix safe.
      if (carrier && (exported || (tag != "fn" && tag != "bind" &&
                                   tag != "configure" && tag != "protocol" &&
                                   tag != "instance" && tag != "entry"))) {
        fail("source-carrier-authoring",
             "carrier modules contain only common-carrier declarations; "
             "use an ordinary module for source authoring");
      } else if (tag == "library" && explicitBindings) {
        auto identity = libraryIdentity(start);
        expect(";");
        declaration.libraryIdentities.push_back(std::move(identity));
      } else if (tag == "mod" && explicitBindings) {
        syntax::ModuleDeclaration child;
        child.name = keyword();
        expect(";");
        declaration.modules.push_back(record(std::move(child), start));
      } else if (tag == "dependency" && explicitBindings) {
        syntax::LibraryDependency dependency;
        dependency.name = keyword();
        expect("=");
        expect("library");
        dependency.identity = libraryIdentity(start);
        expect(";");
        declaration.dependencies.push_back(
            record(std::move(dependency), start));
      } else if (tag == "use" && explicitBindings) {
        use(declaration, exported, start);
        expect(";");
      } else if (tag == "association" && explicitBindings) {
        syntax::LibraryAssociation association;
        association.name = name();
        expect("=");
        if (token().kind != TokenKind::String)
          fail("library-source-association",
               "captured association requires exact quoted subject bytes");
        association.captured = name();
        expect(";");
        if (association.captured.empty())
          fail("library-source-association",
               "captured subject must not be empty");
        declaration.libraryAssociations.push_back(
            record(std::move(association), start));
      } else if (tag == "interface" && explicitBindings) {
        syntax::LibraryInterface interface;
        interface.name = name();
        libraryMembers(interface, false);
        declaration.libraryInterfaces.push_back(
            record(std::move(interface), start));
      } else if (tag == "component" && explicitBindings) {
        syntax::LibraryComponent component;
        component.name = name();
        if (token().is("<"))
          component.parameters = staticParameters();
        expect(":");
        component.interface = name();
        component.quotedInterface = quotedName;
        libraryMembers(component, true);
        declaration.libraryComponents.push_back(
            record(std::move(component), start));
      } else if ((tag == "select" || tag == "seal") && explicitBindings) {
        syntax::LibrarySelection selection;
        selection.name = name();
        selection.sealed = tag == "seal";
        expect("=");
        selection.target = libraryTerm();
        expect(";");
        declaration.librarySelections.push_back(
            record(std::move(selection), start));
      } else if (tag == "link" && explicitBindings) {
        syntax::LibraryLink link;
        link.name = name();
        expect("=");
        link.client = name();
        link.quotedClient = quotedName;
        link.arguments = list("<", ">", [&] { return libraryTerm(); });
        expect(";");
        declaration.libraryLinks.push_back(record(std::move(link), start));
      } else if (tag == "const" && explicitBindings) {
        syntax::Constant constant;
        constant.name = keyword();
        expect(":");
        expect("index");
        expect("=");
        constant.expression = expression();
        expect(";");
        declaration.constants.push_back(record(std::move(constant), start));
      } else if (tag == "bind" && explicitBindings) {
        source::OperationBinding binding;
        binding.name = name();
        expect("=");
        binding.application.contract = path();
        binding.application.arguments = list("(", ")", [&] { return path(); });
        if (eat("using"))
          binding.application.implementation = name();
        expect(";");
        declaration.bindings.push_back(record(std::move(binding), start));
      } else if (tag == "relation" && explicitBindings) {
        syntax::RelationImport relation;
        relation.name = name();
        expect("=");
        relation.family = keyword();
        expect("(");
        if (token().kind != TokenKind::String)
          fail("source-syntax",
               "relation asset requires a quoted relative path");
        relation.path = name();
        expect(")");
        expect(";");
        declaration.imports.push_back(record(std::move(relation), start));
      } else if (tag == "derive" && explicitBindings) {
        source::RelationView view;
        view.name = name();
        expect("=");
        view.kind = keyword();
        expect("(");
        view.relation = name();
        if (quotedName)
          declaration.quotedRelations.insert(view.name);
        expect(",");
        view.staging = keyword();
        if (eat(",")) {
          auto height = atom();
          declaration.relationViewHeights[view.name] = height;
          if (height.kind == syntax::Atom::Kind::Number &&
              StringRef(height.value).getAsInteger(10, view.height))
            fail("relation-view-height", "expected a bounded trace height");
        }
        expect(")");
        expect(";");
        declaration.relationViews.push_back(record(std::move(view), start));
      } else if (tag == "configure" && explicitBindings) {
        source::Configuration configuration;
        configuration.name = name();
        expect("=");
        configuration.base = name();
        if (quotedName)
          declaration.quotedBases.insert(configuration.name);
        auto &terms = declaration.configurationTerms[configuration.name];
        configuration.arguments = list("(", ")", [&] {
          auto key = name();
          expect("=");
          terms.push_back(staticTerm());
          return std::make_pair(key, termSpelling(terms.back()));
        });
        if (eat("using"))
          configuration.implementations = pairs();
        expect(";");
        declaration.configurations.push_back(
            record(std::move(configuration), start));
      } else if (tag == "enum" && explicitBindings) {
        syntax::Enum enumeration;
        enumeration.name = name();
        if (token().is("<"))
          enumeration.parameters = staticParameters();
        enumeration.alternatives = list("{", "}", [&] {
          auto label = name();
          syntax::Type payload;
          payload.product = true;
          if (token().is("(")) {
            payload.arguments = list("(", ")", [&] { return type(); });
            if (payload.arguments.size() == 1) {
              auto single = std::move(payload.arguments.front());
              payload = std::move(single);
            }
          }
          return syntax::Parameter{label, std::move(payload)};
        });
        declaration.enums.push_back(record(std::move(enumeration), start));
      } else if (tag == "struct" && explicitBindings) {
        structure(declaration, start, false);
      } else if (tag == "checked" && explicitBindings) {
        expect("struct");
        structure(declaration, start, true);
      } else if (tag == "bundle" && explicitBindings) {
        syntax::Bundle bundle;
        bundle.name = name();
        bundle.parameters = names();
        expect("=");
        bundle.requirements = requirementList(&bundle.requirementTerms);
        expect(";");
        declaration.bundles.push_back(record(std::move(bundle), start));
      } else if (tag == "fn")
        function(declaration, start);
      else if (tag == "protocol")
        declaration.protocols.push_back(protocol(start));
      else if (tag == "instance")
        declaration.instances.push_back(instance(start, declaration));
      else if (tag == "entry") {
        source::Entry entry;
        entry.name = name();
        expect("=");
        entry.instance = name();
        if (quotedName)
          declaration.quotedInstances.insert(entry.name);
        if (eat("::")) {
          auto &selection = declaration.entryArguments[entry.name];
          selection.arguments = list("<", ">", [&] {
            auto parameter = name();
            expect("=");
            selection.terms.push_back(staticTerm());
            return std::make_pair(parameter,
                                  termSpelling(selection.terms.back()));
          });
        }
        expect(";");
        declaration.entries.push_back(record(std::move(entry), start));
      } else
        fail("source-syntax",
             "expected bind, bundle, struct, configure, fn, protocol, "
             "instance, or entry");
      if (failed() && recovering) {
        syntax::ParseDiagnostic error;
        error.location = source::Span{errorOffset, 0, file};
        error.code = errorCode;
        error.message = message;
        diagnostics.push_back(std::move(error));
        declaration = {};
        errorCode.clear();
        message.clear();
        // Scan from the declaration start, respecting nested braces. Stop
        // after its top-level semicolon or closing body brace.
        cursor = declarationCursor;
        unsigned braces = 0;
        while (token().kind != TokenKind::End) {
          if (token().is("}") && braces == 0)
            break;
          bool done = (token().is(";") && braces == 0) ||
                      (token().is("}") && braces == 1);
          if (token().is("{"))
            ++braces;
          if (token().is("}"))
            --braces;
          advance();
          if (done)
            break;
        }
        if (token().kind == TokenKind::End) {
          fail("source-syntax", "expected '}'");
          break;
        }
      }
      auto append = [](auto &target, auto &items) {
        target.insert(target.end(), std::make_move_iterator(items.begin()),
                      std::make_move_iterator(items.end()));
      };
      if (exported && tag != "use") {
        if (tag == "library" || tag == "dependency" || tag == "entry")
          fail("source-visibility", "this declaration cannot be exported");
        auto publish = [&](const auto &items) {
          for (const auto &item : items)
            result.exports.push_back(item.name);
        };
        publish(declaration.modules);
        publish(declaration.libraryAssociations);
        publish(declaration.libraryInterfaces);
        publish(declaration.libraryComponents);
        publish(declaration.libraryLinks);
        publish(declaration.librarySelections);
        publish(declaration.constants);
        publish(declaration.functions);
        publish(declaration.protocols);
        publish(declaration.instances);
        publish(declaration.bindings);
        publish(declaration.bundles);
        publish(declaration.structs);
        publish(declaration.enums);
        publish(declaration.imports);
        publish(declaration.relationViews);
        publish(declaration.configurations);
      }
      append(result.modules, declaration.modules);
      append(result.dependencies, declaration.dependencies);
      append(result.uses, declaration.uses);
      append(result.libraryIdentities, declaration.libraryIdentities);
      append(result.libraryAssociations, declaration.libraryAssociations);
      append(result.libraryInterfaces, declaration.libraryInterfaces);
      append(result.libraryComponents, declaration.libraryComponents);
      append(result.libraryLinks, declaration.libraryLinks);
      append(result.librarySelections, declaration.librarySelections);
      append(result.constants, declaration.constants);
      append(result.functions, declaration.functions);
      append(result.protocols, declaration.protocols);
      append(result.instances, declaration.instances);
      append(result.entries, declaration.entries);
      result.entryArguments.insert(declaration.entryArguments.begin(),
                                   declaration.entryArguments.end());
      append(result.bindings, declaration.bindings);
      append(result.bundles, declaration.bundles);
      append(result.structs, declaration.structs);
      append(result.enums, declaration.enums);
      append(result.imports, declaration.imports);
      append(result.relations, declaration.relations);
      append(result.relationViews, declaration.relationViews);
      append(result.configurations, declaration.configurations);
      result.instanceProtocolTerms.insert(
          declaration.instanceProtocolTerms.begin(),
          declaration.instanceProtocolTerms.end());
      result.instanceParameterAtoms.insert(
          declaration.instanceParameterAtoms.begin(),
          declaration.instanceParameterAtoms.end());
      result.configurationTerms.insert(declaration.configurationTerms.begin(),
                                       declaration.configurationTerms.end());
      result.relationViewHeights.insert(declaration.relationViewHeights.begin(),
                                        declaration.relationViewHeights.end());
      result.quotedBases.merge(declaration.quotedBases);
      result.quotedRelations.merge(declaration.quotedRelations);
      result.quotedInstances.merge(declaration.quotedInstances);
      result.quotedInstanceDependencies.merge(
          declaration.quotedInstanceDependencies);
      result.quotedSelectors.merge(declaration.quotedSelectors);
      for (size_t size :
           {result.libraryIdentities.size(), result.libraryAssociations.size(),
            result.libraryInterfaces.size(), result.libraryComponents.size(),
            result.libraryLinks.size(), result.librarySelections.size(),
            result.constants.size(), result.functions.size(),
            result.protocols.size(), result.bundles.size(),
            result.structs.size(), result.enums.size(), result.instances.size(),
            result.entries.size(), result.bindings.size(),
            result.configurations.size(), result.imports.size(),
            result.relationViews.size()})
        if (size > 32768)
          fail("source-limit", "section exceeds 32768 declarations");
    }
    return result;
  }
  source::Construction construction() {
    source::Construction result;
    result.entry = name();
    // Normalized identity is the default; exact identity is chosen explicitly
    // (docs/spec/profiles/compiler/local-algorithms.md).
    result.identity = source::Construction::Identity::Normalized;
    if (eat("identity")) {
      if (eat("exact"))
        result.identity = source::Construction::Identity::Exact;
      else
        expect("normalized");
    }
    expect("{");
    std::set<std::string> clauses;
    while (!failed() && !eat("}")) {
      size_t start = token().offset;
      auto key = keyword();
      if (key != "public" && !clauses.insert(key).second)
        fail("source-duplicate", "duplicate construction clause '" + key + "'");
      if (key == "producer")
        result.producer = name();
      else if (key == "validator")
        result.validator = name();
      else if (key == "suite")
        result.suite = name();
      else if (key == "accept")
        result.acceptance = number();
      else if (key == "random") {
        result.randomness = name();
        expect("at");
        result.draws = references();
      } else if (key == "public") {
        source::PublicBinding binding;
        binding.name = name();
        expect("=");
        binding.ports = references();
        expect(";");
        result.publicBindings.push_back(record(std::move(binding), start));
        if (result.publicBindings.size() > 32768)
          fail("source-limit", "public bindings exceed 32768 entries");
        continue;
      } else
        fail("source-syntax", "unknown construction clause");
      expect(";");
    }
    for (StringRef key : {"producer", "validator", "random", "accept", "suite"})
      if (!clauses.count(key.str()))
        fail("source-syntax", "missing construction clause '" + key + "'");
    return result;
  }
  source::Assignments references() {
    return list("(", ")", [&] {
      auto owner = path();
      return std::make_pair(std::move(owner), name());
    });
  }

public:
  Parser(StringRef text, StringRef filename, ArrayRef<Token> tokens,
         uint32_t file)
      : text(text), filename(filename), file(file), tokens(tokens) {
    skipComments();
  }
  syntax::ParseResult runRecoverable() {
    recovering = true;
    size_t start = token().offset;
    syntax::ParseResult out;
    if (eat("carrier")) {
      expect("module");
      if (!token().is("{"))
        fail("source-carrier-authoring", "carrier modules use explicit bindings");
      out.content = record(module(true), start);
    } else if (eat("module"))
      out.content = record(module(), start);
    else if (eat("construction"))
      out.content = record(construction(), start);
    else
      fail("source-syntax", "expected module or construction");
    if (!failed() && token().kind != TokenKind::End)
      fail("source-syntax", "unexpected text after document");
    if (failed()) {
      syntax::ParseDiagnostic error;
      error.location = source::Span{errorOffset, 0, file};
      error.code = errorCode;
      error.message = message;
      diagnostics.push_back(std::move(error));
    }
    out.diagnostics = std::move(diagnostics);
    return out;
  }
  Expected<syntax::Content> run() {
    auto out = runRecoverable();
    if (!out.complete()) {
      const auto &error = out.diagnostics.front();
      return diagnostic(text, filename, error.location->offset, error.code,
                        error.message);
    }
    return std::move(*out.content);
  }
};

} // namespace

syntax::ParseResult syntax::parseRecoverable(StringRef text, StringRef filename,
                                             uint32_t file) {
  auto tokens = lex(text, filename);
  if (!tokens) {
    ParseResult result;
    handleAllErrors(tokens.takeError(), [&](const SourceDiagnostic &d) {
      ParseDiagnostic error;
      error.code = d.code;
      error.message = d.message;
      error.location = d.location;
      error.location->file = file;
      result.diagnostics.push_back(std::move(error));
    });
    return result;
  }
  return Parser(text, filename, *tokens, file).runRecoverable();
}

Expected<syntax::Content> syntax::parse(StringRef text, StringRef filename,
                                        uint32_t file) {
  auto tokens = lex(text, filename);
  if (!tokens)
    return tokens.takeError();
  return Parser(text, filename, *tokens, file).run();
}

} // namespace zkc::frontend
