#include "Grammar.h"
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
  bool recovering = false;
  std::vector<syntax::ParseDiagnostic> diagnostics;
  std::set<std::string> explicitSites;
  std::vector<bool> anonymousSites;

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
    if (failed())
      return {};
    // A word or quoted spelling in an identifier position is a misspelled
    // identifier; punctuation there is ordinary malformed syntax.
    if (token().kind != TokenKind::Name &&
        token().kind != TokenKind::RawIdentifier &&
        token().kind != TokenKind::String) {
      fail("source-syntax", "expected an identifier");
      return {};
    }
    if (token().kind == TokenKind::String ||
        (token().kind == TokenKind::Name &&
         grammar::reserved(token().value()))) {
      fail("source-identifier",
           "expected an identifier (escape reserved words with r#)");
      return {};
    }
    auto result = token().value().str();
    advance();
    return result;
  }
  std::string label() {
    if (token().kind != TokenKind::String)
      return name();
    auto result = token().value().str();
    advance();
    return result;
  }
  std::string exact() {
    if (token().kind != TokenKind::String) {
      fail("source-string", "expected an exact quoted string");
      return {};
    }
    return label();
  }
  syntax::Atom atom() {
    syntax::Atom result;
    size_t start = token().offset;
    result.kind = token().kind == TokenKind::String ? syntax::Atom::Kind::String
                  : token().kind == TokenKind::Number
                      ? syntax::Atom::Kind::Number
                      : syntax::Atom::Kind::Name;
    result.value = token().kind == TokenKind::Number ? number() : label();
    return record(std::move(result), start);
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
  // A declaration path of decoded identifiers. With `turbofish`, a trailing
  // `::<` ends the path and is reported rather than read as a segment.
  syntax::Path path(bool *turbofish = nullptr) {
    size_t start = token().offset;
    syntax::Path result;
    if (turbofish)
      *turbofish = false;
    result.segments.push_back(name());
    while (eat("::")) {
      if (turbofish && token().is("<")) {
        *turbofish = true;
        break;
      }
      // The root is not a member; members share the type-path cap.
      if (result.segments.size() > 32768) {
        fail("source-limit", "path exceeds 32768 members");
        break;
      }
      result.segments.push_back(name());
    }
    return record(std::move(result), start);
  }
  syntax::Reference reference(bool *turbofish = nullptr) {
    syntax::Reference result;
    result.path = path(turbofish);
    result.location = result.path.location;
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
  syntax::StaticTerm staticTerm(unsigned depth = 0) {
    syntax::StaticTerm result;
    if (depth > 64) {
      fail("source-depth", "static term nesting exceeds 64");
      return result;
    }
    result.root = atom();
    if (token().is("<"))
      result.arguments = list("<", ">", [&] { return staticTerm(depth + 1); });
    while (eat("::")) {
      result.members.push_back(name());
      if (result.members.size() > 32768)
        fail("source-limit", "static path exceeds 32768 members");
    }
    if (token().is("<") && result.arguments.empty())
      result.arguments = list("<", ">", [&] { return staticTerm(depth + 1); });
    return result;
  }
  syntax::StaticTerms staticTerms() {
    return list("<", ">", [&] { return staticTerm(); });
  }
  syntax::StaticAssignments staticAssignments() {
    return list("<", ">", [&] {
      auto key = name();
      expect("=");
      return std::make_pair(std::move(key), staticTerm());
    });
  }
  std::vector<syntax::Atom> atoms() {
    return list("(", ")", [&] { return atom(); });
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
    result.kind = token().kind == TokenKind::String ? syntax::Atom::Kind::String
                  : token().kind == TokenKind::Number
                      ? syntax::Atom::Kind::Number
                      : syntax::Atom::Kind::Name;
    result.name = result.natural() ? number() : label();
    if (token().is("<"))
      result.arguments = list("<", ">", [&] { return type(depth + 1); });
    while (eat("::")) {
      result.members.push_back(name());
      if (result.members.size() > 32768)
        fail("source-limit", "type path exceeds 32768 members");
    }
    if (token().is("<") && result.arguments.empty())
      result.arguments = list("<", ">", [&] { return type(depth + 1); });
    return record(std::move(result), start);
  }
  // A reference-only slot: a value path with field, product or literal index
  // selections, parsed by the shared postfix grammar. It performs no
  // computation; each context's owner decides which roots it permits.
  syntax::Place place() {
    size_t start = token().offset;
    syntax::Expression root;
    root.reference = reference();
    auto value = postfix(record(std::move(root), start), 0);
    auto place = syntax::placeCandidate(value);
    if (!place || token().is("(")) {
      fail("source-reference",
           "this context requires a value reference without computation");
      return {};
    }
    return *place;
  }
  syntax::Places places() {
    return list("(", ")", [&] { return place(); });
  }
  source::Names names() {
    return list("(", ")", [&] { return name(); });
  }
  syntax::PlaceAssignments placePairs() {
    return list("(", ")", [&] {
      auto key = name();
      expect("=");
      return std::make_pair(std::move(key), place());
    });
  }
  // Identifier keys bound to identifiers, or to exact labels when `labels`.
  source::Assignments pairs(bool labels = false) {
    return list("(", ")", [&] {
      auto key = name();
      expect("=");
      auto value = labels ? label() : name();
      return std::make_pair(std::move(key), std::move(value));
    });
  }
  std::string site() {
    bool anonymous = !eat("[");
    anonymousSites.push_back(anonymous);
    if (anonymous)
      return {};
    auto result = label();
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
            !std::holds_alternative<syntax::Return>(instruction.value) &&
            !std::holds_alternative<syntax::Yield>(instruction.value)) {
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
  syntax::Places values() {
    if (token().is(";"))
      return {};
    return token().is("(") ? places() : syntax::Places{place()};
  }
  // Operators have a fixed table: unary minus binds tightest, then `*`, then
  // `+` and `-`; binary operators associate to the left.
  syntax::Expression expression(unsigned depth = 0, bool allowRecord = true) {
    return binary(depth, 0, allowRecord);
  }
  syntax::Expression binary(unsigned depth, unsigned level, bool allowRecord) {
    if (level == 2)
      return unary(depth, allowRecord);
    size_t start = token().offset;
    auto result = binary(depth, level + 1, allowRecord);
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
      operation.operands.push_back(binary(depth, level + 1, allowRecord));
      result = record(std::move(operation), start);
    }
    return result;
  }
  syntax::Expression unary(unsigned depth, bool allowRecord) {
    if (!token().is("-"))
      return primary(depth, allowRecord);
    size_t start = token().offset;
    if (depth > 64) {
      fail("source-depth", "expression nesting exceeds 64");
      return {};
    }
    syntax::Expression operation;
    operation.kind = syntax::Expression::Kind::Operator;
    operation.name = "-";
    advance();
    operation.operands.push_back(unary(depth + 1, allowRecord));
    return record(std::move(operation), start);
  }
  syntax::Expression primary(unsigned depth, bool allowRecord) {
    using Kind = syntax::Expression::Kind;
    size_t start = token().offset;
    syntax::Expression result;
    if (depth > 64) {
      fail("source-depth", "expression nesting exceeds 64");
      return result;
    }
    if (token().is("map") || token().is("fold")) {
      bool fold = eat("fold");
      if (!fold)
        expect("map");
      result.kind = fold ? Kind::Fold : Kind::Map;
      result.traversal = std::make_shared<syntax::LexicalTraversal>();
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
      result.traversal->body = body(true, depth + 1);
    } else if (token().is("(")) {
      advance();
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
      if (token().kind != TokenKind::Name &&
          token().kind != TokenKind::RawIdentifier &&
          token().kind != TokenKind::String) {
        fail("source-syntax", "expected an expression");
        return result;
      }
      bool trailing = false;
      result.reference = reference(&trailing);
      if (trailing)
        result.staticArguments = staticTerms();
      if (allowRecord && token().is("{")) {
        result.kind = Kind::Struct;
        result.operands = list("{", "}", [&] {
          size_t fieldStart = token().offset;
          auto field = name();
          result.fields.push_back(field);
          if (eat(":"))
            return expression(depth + 1);
          // Shorthand reads the lexical value with the field's name.
          syntax::Expression value;
          value.reference.path.segments = {field};
          value = record(std::move(value), fieldStart);
          value.reference.location = value.reference.path.location =
              value.location;
          return value;
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
        if (eat("attributes"))
          result.attributes = atoms();
      } else if (trailing)
        fail("source-expression",
             "static actuals require a call or constructor");
    }
    return postfix(record(std::move(result), start), depth);
  }
  syntax::Expression postfix(syntax::Expression result, unsigned depth) {
    using Kind = syntax::Expression::Kind;
    size_t start = result.location->offset;
    while (!failed() && (token().is("[") || token().is("."))) {
      if (++depth > 64) {
        fail("source-depth", "expression nesting exceeds 64");
        break;
      }
      syntax::Expression projected;
      projected.operands.push_back(std::move(result));
      if (eat("[")) {
        projected.kind = Kind::Get;
        projected.operands.push_back(expression(depth + 1));
        expect("]");
      } else {
        expect(".");
        if (token().kind == TokenKind::Number) {
          projected.kind = Kind::TupleField;
          projected.name = number();
        } else {
          projected.kind = Kind::Field;
          projected.name = name();
        }
        if (eat("(")) {
          if (projected.kind != Kind::Field || projected.name != "len")
            fail("source-receiver-call",
                 "only the collection query .len() is supported");
          expect(")");
          projected.kind = Kind::Length;
          projected.name.clear();
        }
      }
      result = record(std::move(projected), start);
    }
    return result;
  }
  syntax::Instruction localInstruction(unsigned depth) {
    size_t start = token().offset;
    syntax::Instruction result;
    if (eat("match")) {
      result.site = site();
      result.explicitSite = !anonymousSites.back();
      syntax::Match match;
      match.input = place();
      if (eat("capture")) {
        match.explicitCaptures = true;
        match.captures = places();
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
      branch.condition = expression(0, false);
      if (eat("capture")) {
        branch.explicitCaptures = true;
        branch.explicitRegion = true;
        branch.captures = places();
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
      loop.lower = expression(0, false);
      if (token().is("carry")) {
        syntax::ArrayTraversal traversal;
        traversal.element = loop.induction;
        auto input = syntax::placeCandidate(loop.lower);
        if (!input)
          fail("library-source-traversal", "traversal requires an array place");
        traversal.input = input.value_or(syntax::Place{});
        expect("carry");
        traversal.carried = placePairs();
        if (eat("capture")) {
          traversal.explicitCaptures = true;
          traversal.captures = places();
        }
        expect("->");
        traversal.outputs = names();
        expect("{");
        traversal.body = body(true, depth + 1);
        result.value = std::move(traversal);
        return record(std::move(result), start);
      }
      expect("..");
      loop.upper = expression(0, false);
      if (eat("carry")) {
        loop.explicitRegion = true;
        loop.carried = placePairs();
        if (eat("capture")) {
          loop.explicitCaptures = true;
          loop.captures = places();
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
      } else {
        binding.expression = expression();
        if (eat("=")) {
          auto place = syntax::placeCandidate(binding.expression);
          if (!place)
            fail("source-reference",
                 "assignment requires an existing scalar place");
          binding.assignment = place.value_or(syntax::Place{});
          binding.expression = expression();
        }
      }
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
        flatCall &= syntax::placeCandidate(operand, false).has_value();
      if (flatCall) {
        syntax::Call call;
        call.location = expr.location;
        if (isOperator)
          call.operatorSymbol = expr.name;
        else
          call.callee = expr.reference;
        call.staticArguments = expr.staticArguments;
        call.attributes = expr.attributes;
        call.argumentNames = expr.argumentNames;
        call.outputs = binding.outputs;
        call.destructure = binding.destructure;
        call.annotation = binding.annotation;
        for (const auto &operand : expr.operands)
          call.inputs.push_back(*syntax::placeCandidate(operand, false));
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
    bool turbofish = false;
    result.callee = reference(&turbofish);
    // path consumes the turbofish separator, but never accepts bare <...>.
    if (turbofish)
      result.staticArguments = staticTerms();
    result.inputs = places();
    if (eat("attributes"))
      result.attributes = atoms();
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
  std::vector<syntax::Dependency> dependencies() {
    return list("(", ")", [&] {
      size_t start = token().offset;
      syntax::Dependency result;
      result.name = name();
      expect(":");
      bool turbofish = false;
      result.protocol = reference(&turbofish);
      if (turbofish)
        result.arguments = staticAssignments();
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
        size_t portStart = token().offset;
        auto port = name();
        if (eat(":"))
          return std::make_pair(port, place());
        // Shorthand finishes the port from the lexical value of its name.
        syntax::Place value;
        value.root.path.segments = {port};
        value = record(std::move(value), portStart);
        value.root.location = value.root.path.location = value.location;
        return std::make_pair(port, std::move(value));
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
        result.value = syntax::Return{values()};
      else
        result.value = syntax::Yield{values()};
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
      syntax::Message message;
      message.schema = label();
      expect(":");
      message.sender = name();
      expect("(");
      message.input = place();
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
      call.inputs = places();
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
      // `stop reason;` or `stop Role reason;`: a role is an identifier and a
      // reason an exact label.
      if (!nextToken().is(";"))
        stop.role = name();
      stop.reason = label();
      result.value = std::move(stop);
    } else if (tag == "loop") {
      syntax::Loop loop;
      loop.count = atom();
      expect("carry");
      loop.carried = placePairs();
      if (eat("capture")) {
        loop.explicitCaptures = true;
        loop.captures = places();
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
      if (token().kind == TokenKind::End) {
        fail("source-syntax", "expected '}' before end of file");
        break;
      }
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
          parameter.bounds.push_back(reference());
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
      return list("(", ")", [&] { return reference(); });
    };
    if (eat("constructors")) {
      result.checked = true;
      result.constructors = constructors();
    }
    result.fields = list("{", "}", [&] {
      auto field = name();
      expect(":");
      return syntax::Parameter{std::move(field), type()};
    });
    if (checked) {
      if (!eat("constructors"))
        fail("source-syntax", "a checked struct names its constructors");
      result.constructors = constructors();
    }
    eat(";");
    module.structs.push_back(record(std::move(result), start));
  }
  // A requirement item: `Predicate(terms)`, or `term == term`. The leading
  // static term of a predicate item is its declaration path.
  syntax::Requirement requirement(syntax::StaticTerm subject, size_t offset) {
    syntax::Requirement result;
    if (eat("==")) {
      result.arguments = {std::move(subject), staticTerm()};
      return record(std::move(result), offset);
    }
    if (subject.root.kind != syntax::Atom::Kind::Name ||
        !subject.arguments.empty() || !token().is("(")) {
      fail("source-syntax",
           "a requirement is Predicate(terms) or term == term");
      return result;
    }
    syntax::Reference predicate;
    predicate.location = predicate.path.location = subject.root.location;
    predicate.path.segments.push_back(subject.root.value);
    llvm::append_range(predicate.path.segments, subject.members);
    result.predicate = std::move(predicate);
    result.arguments = list("(", ")", [&] { return staticTerm(); });
    return record(std::move(result), offset);
  }
  std::vector<syntax::Requirement> requirementList() {
    return list("(", ")", [&] {
      size_t offset = token().offset;
      return requirement(staticTerm(), offset);
    });
  }
  void whereRequirements(std::vector<syntax::Requirement> &requirements) {
    do {
      size_t offset = token().offset;
      auto subject = staticTerm();
      if (token().is("==") || token().is("("))
        requirements.push_back(requirement(std::move(subject), offset));
      else {
        expect(":");
        do {
          syntax::Requirement r;
          r.predicate = reference();
          r.arguments = {subject};
          requirements.push_back(record(std::move(r), offset));
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
      whereRequirements(result.requirements);
    if (eat("requires")) {
      llvm::append_range(result.requirements, requirementList());
      if (result.requirements.size() > 32768)
        fail("source-limit", "requirements exceed 32768 entries");
    }
    if (eat("effects"))
      result.effects = list(
          "(", ")", [&] { return token().is("local") ? keyword() : label(); });
    if (!result.generic)
      result.origin = source::LogicalOrigin{result.name, {}};
    if (eat("origin")) {
      result.explicitOrigin = true;
      source::LogicalOrigin origin;
      origin.definition = label();
      origin.arguments = pairs(true);
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
      whereRequirements(result.requirements);
    if (eat("requires"))
      llvm::append_range(result.requirements, requirementList());
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
        result.dependencies = dependencies();
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
  syntax::Instance instance(size_t start) {
    syntax::Instance result;
    result.name = name();
    expect(":");
    result.protocol = reference();
    expect("{");
    std::set<std::string> headers;
    while (!failed() && !eat("}")) {
      auto key = keyword();
      if (!headers.insert(key).second)
        fail("source-duplicate", "duplicate instance clause '" + key + "'");
      if (key == "parameters") {
        result.parameters = list("(", ")", [&] {
          auto key = name();
          expect("=");
          syntax::InstanceParameter value;
          if (eat("ingress")) {
            expect("(");
            value.value = atom();
            expect(",");
            value.ingress.emplace();
            do {
              syntax::IngressSelector selector;
              selector.role = name();
              expect("=");
              selector.function = reference();
              selector.arguments = names();
              value.ingress->push_back(std::move(selector));
            } while (eat(","));
            expect(")");
          } else
            value.value = atom();
          return std::make_pair(key, std::move(value));
        });
      } else if (key == "dependencies")
        result.dependencies = list("(", ")", [&] {
          auto alias = name();
          expect("=");
          return std::make_pair(std::move(alias), reference());
        });
      else if (key == "roles")
        result.roles = pairs(true);
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
        facet.owner = label();
        facet.name = label();
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
    auto fields = pairs(true);
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
    prefix.push_back(name());
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
      prefix.push_back(name());
      if (prefix.size() > 64) {
        fail("source-depth", "import path exceeds 64 levels");
        return;
      }
    }
    syntax::Use item;
    item.name = eat("as") ? name() : prefix.back();
    item.path = std::move(prefix);
    item.exported = exported;
    module.uses.push_back(record(std::move(item), start));
  }
  // Discard one failed declaration without stripping the next declaration's
  // prefixes. Prefix lookahead is used only on failure and stops at recovery
  // delimiters, so repeated unclosed attributes take linear work.
  void recoverDeclaration(size_t start) {
    size_t head = start;
    auto skipCommentsAtHead = [&] {
      while (tokens[head].kind == TokenKind::Comment)
        ++head;
    };
    for (;;) {
      skipCommentsAtHead();
      if (tokens[head].is("pub")) {
        ++head;
        continue;
      }
      if (!tokens[head].is("#"))
        break;
      ++head;
      skipCommentsAtHead();
      if (!tokens[head].is("["))
        break;
      unsigned depth = 0;
      do {
        if (tokens[head].is("["))
          ++depth;
        else if (tokens[head].is("]"))
          --depth;
        ++head;
      } while (depth && tokens[head].kind != TokenKind::End &&
               !tokens[head].is(";") && !tokens[head].is("{") &&
               !tokens[head].is("}"));
      if (depth)
        break;
    }
    // Contextual declaration words are legal names. Neither the failed
    // declaration's own keyword nor its name is a new synchronization point.
    if (tokens[head].kind == TokenKind::Name) {
      bool checked = tokens[head].is("checked");
      ++head;
      skipCommentsAtHead();
      if (checked && tokens[head].is("struct")) {
        ++head;
        skipCommentsAtHead();
      }
      if (tokens[head].kind == TokenKind::Name ||
          tokens[head].kind == TokenKind::RawIdentifier)
        ++head;
    }
    size_t resume = std::max(head, cursor);
    cursor = start;
    unsigned braces = 0, parentheses = 0, brackets = 0;
    while (token().kind != TokenKind::End) {
      if (token().is("}") && braces == 0) {
        advance();
        break;
      }
      if (cursor > start && cursor >= resume && braces == 0 &&
          parentheses == 0 && brackets == 0 &&
          (token().is("#") || (token().kind == TokenKind::Name &&
                               grammar::declarationStart(token().value()))))
        break;
      bool done =
          (token().is(";") && braces == 0) || (token().is("}") && braces == 1);
      if (token().is("("))
        ++parentheses;
      if (token().is(")") && parentheses)
        --parentheses;
      if (token().is("["))
        ++brackets;
      if (token().is("]") && brackets)
        --brackets;
      if (token().is("{"))
        ++braces;
      if (token().is("}"))
        --braces;
      advance();
      if (done)
        break;
    }
  }
  syntax::Module module() {
    syntax::Module result;
    while (!failed() && token().kind != TokenKind::End) {
      size_t start = token().offset;
      syntax::Module declaration;
      size_t declarationCursor = cursor;
      std::optional<std::string> operatorHook;
      while (eat("#")) {
        expect("[");
        if (!eat("operator"))
          fail("source-operator-attribute", "expected operator attribute");
        expect("(");
        auto hook = keyword();
        if (hook != "add" && hook != "sub" && hook != "mul" && hook != "neg")
          fail("source-operator-attribute", "unknown operator hook");
        expect(")");
        expect("]");
        if (operatorHook)
          fail("source-operator-attribute", "duplicate operator attribute");
        operatorHook = std::move(hook);
      }
      bool exported = eat("pub");
      auto tag = keyword();
      if (exported &&
          (tag == "library" || tag == "dependency" || tag == "entry"))
        fail("source-visibility", "this declaration cannot be exported");
      if (operatorHook && tag != "fn")
        fail("source-operator-attribute",
             "operator attributes require an ordinary source function");
      if (tag == "library") {
        auto identity = libraryIdentity(start);
        expect(";");
        declaration.libraryIdentities.push_back(std::move(identity));
      } else if (tag == "mod") {
        syntax::ModuleDeclaration child;
        child.name = name();
        expect(";");
        declaration.modules.push_back(record(std::move(child), start));
      } else if (tag == "dependency") {
        syntax::LibraryDependency dependency;
        dependency.name = name();
        expect("=");
        expect("library");
        dependency.identity = libraryIdentity(start);
        expect(";");
        declaration.dependencies.push_back(
            record(std::move(dependency), start));
      } else if (tag == "use") {
        use(declaration, exported, start);
        expect(";");
      } else if (tag == "association") {
        syntax::LibraryAssociation association;
        association.name = name();
        expect("=");
        if (token().kind != TokenKind::String)
          fail("library-source-association",
               "captured association requires exact quoted subject bytes");
        association.captured = exact();
        expect(";");
        if (association.captured.empty())
          fail("library-source-association",
               "captured subject must not be empty");
        declaration.libraryAssociations.push_back(
            record(std::move(association), start));
      } else if (tag == "interface") {
        syntax::LibraryInterface interface;
        interface.name = name();
        libraryMembers(interface, false);
        declaration.libraryInterfaces.push_back(
            record(std::move(interface), start));
      } else if (tag == "component") {
        syntax::LibraryComponent component;
        component.name = name();
        if (token().is("<"))
          component.parameters = staticParameters();
        expect(":");
        component.interface = reference();
        libraryMembers(component, true);
        declaration.libraryComponents.push_back(
            record(std::move(component), start));
      } else if ((tag == "select" || tag == "seal")) {
        syntax::LibrarySelection selection;
        selection.name = name();
        selection.sealed = tag == "seal";
        expect("=");
        selection.target = libraryTerm();
        expect(";");
        declaration.librarySelections.push_back(
            record(std::move(selection), start));
      } else if (tag == "link") {
        syntax::LibraryLink link;
        link.name = name();
        expect("=");
        link.client = reference();
        link.arguments = list("<", ">", [&] { return libraryTerm(); });
        expect(";");
        declaration.libraryLinks.push_back(record(std::move(link), start));
      } else if (tag == "const") {
        syntax::Constant constant;
        constant.name = name();
        expect(":");
        expect("index");
        expect("=");
        constant.expression = expression();
        expect(";");
        declaration.constants.push_back(record(std::move(constant), start));
      } else if (tag == "bind") {
        source::OperationBinding binding;
        binding.name = name();
        expect("=");
        binding.application.contract = exact();
        binding.application.arguments = list("(", ")", [&] { return exact(); });
        if (eat("using"))
          binding.application.implementation = label();
        expect(";");
        declaration.bindings.push_back(record(std::move(binding), start));
      } else if (tag == "relation") {
        syntax::RelationImport relation;
        relation.name = name();
        expect("=");
        relation.family = keyword();
        expect("(");
        if (token().kind != TokenKind::String)
          fail("source-syntax",
               "relation asset requires a quoted relative path");
        relation.path = exact();
        expect(")");
        expect(";");
        declaration.imports.push_back(record(std::move(relation), start));
      } else if (tag == "derive") {
        syntax::RelationView view;
        view.name = name();
        expect("=");
        view.kind = keyword();
        expect("(");
        view.relation = reference();
        expect(",");
        view.staging = keyword();
        if (eat(",")) {
          view.height = atom();
          uint32_t height;
          if (view.height->kind == syntax::Atom::Kind::Number &&
              StringRef(view.height->value).getAsInteger(10, height))
            fail("relation-view-height", "expected a bounded trace height");
        }
        expect(")");
        expect(";");
        declaration.relationViews.push_back(record(std::move(view), start));
      } else if (tag == "configure") {
        syntax::Configuration configuration;
        configuration.name = name();
        expect("=");
        configuration.base = reference();
        configuration.arguments = list("(", ")", [&] {
          auto key = name();
          expect("=");
          return std::make_pair(std::move(key), staticTerm());
        });
        // Implementation selections are exact installed identities.
        if (eat("using"))
          configuration.implementations = list("(", ")", [&] {
            auto site = label();
            expect("=");
            return std::make_pair(std::move(site), label());
          });
        expect(";");
        declaration.configurations.push_back(
            record(std::move(configuration), start));
      } else if (tag == "enum") {
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
      } else if (tag == "struct") {
        structure(declaration, start, false);
      } else if (tag == "checked") {
        expect("struct");
        structure(declaration, start, true);
      } else if (tag == "bundle") {
        syntax::Bundle bundle;
        bundle.name = name();
        bundle.parameters = names();
        expect("=");
        bundle.requirements = requirementList();
        expect(";");
        declaration.bundles.push_back(record(std::move(bundle), start));
      } else if (tag == "fn") {
        function(declaration, start);
        declaration.functions.back().operatorHook = std::move(operatorHook);
      } else if (tag == "protocol")
        declaration.protocols.push_back(protocol(start));
      else if (tag == "instance")
        declaration.instances.push_back(instance(start));
      else if (tag == "entry") {
        syntax::Entry entry;
        entry.name = name();
        expect("=");
        bool turbofish = false;
        entry.instance = reference(&turbofish);
        if (turbofish)
          entry.arguments = staticAssignments();
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
        recoverDeclaration(declarationCursor);
      }
      if (failed())
        break;
      auto append = [](auto &target, auto &items) {
        target.insert(target.end(), std::make_move_iterator(items.begin()),
                      std::make_move_iterator(items.end()));
      };
      if (exported && tag != "use") {
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
      append(result.bindings, declaration.bindings);
      append(result.bundles, declaration.bundles);
      append(result.structs, declaration.structs);
      append(result.enums, declaration.enums);
      append(result.imports, declaration.imports);
      append(result.relations, declaration.relations);
      append(result.relationViews, declaration.relationViews);
      append(result.configurations, declaration.configurations);
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
    result.entry = selector();
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
        result.producer = label();
      else if (key == "validator")
        result.validator = label();
      else if (key == "suite")
        result.suite = label();
      else if (key == "accept")
        result.acceptance = number();
      else if (key == "random") {
        result.randomness = label();
        expect("at");
        result.draws = references();
      } else if (key == "public") {
        source::PublicBinding binding;
        binding.name = label();
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
  // A construction selector is common descriptor data: an exact quoted key,
  // or a declaration path written as the descriptor's dotted key.
  std::string selector() {
    if (token().kind == TokenKind::String)
      return label();
    return llvm::join(path().segments, ".");
  }
  source::Assignments references() {
    return list("(", ")", [&] {
      auto owner = selector();
      return std::make_pair(std::move(owner), label());
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
    if (eat("carrier"))
      fail("source-carrier-authoring",
           "carrier text requires the common carrier reader");
    else if (eat("module"))
      fail("source-module-wrapper",
           "ordinary files contain declarations without a module wrapper");
    else if (eat("construction"))
      out.content = record(construction(), start);
    else
      out.content = record(module(), start);
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
