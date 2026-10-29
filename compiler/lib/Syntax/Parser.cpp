#include "Storage.h"
#include "zkc/Source/Names.h"
#include "llvm/ADT/ScopeExit.h"
#include <algorithm>
#include <set>

using namespace llvm;
namespace zkc::syntax::detail {
namespace {
enum class SuiteKind {
  Declarations,
  Statements,
  Contract,
  Requests,
  Fields,
  Variants,
  Scheme,
  Formula,
  Oracle,
  Cases
};
}
class Parser {
  std::shared_ptr<Storage> data;
  Work work;
  std::vector<uint32_t> significant;
  size_t cursor = 0;
  unsigned recursion = 0, angleDepth = 0;
  const Environment *environment;
  std::map<const Environment *,
           std::map<std::string, const NotationDescriptor *>>
      syntaxIndices;
  uint32_t environmentOwner = UINT32_MAX;

  const Token &token(unsigned look = 0) const {
    return data
        ->tokens[significant[std::min(cursor + look, significant.size() - 1)]];
  }
  uint32_t mark() const { return significant[cursor]; }
  StringRef text(unsigned look = 0) const {
    const auto &t = token(look);
    return data->revision.text().slice(t.begin, t.end);
  }
  bool at(StringRef value) const {
    return !token().synthetic() && text() == value;
  }
  bool at(TokenKind kind) const { return token().kind == kind; }
  bool end() const { return at(TokenKind::End) || work.stopped(); }
  bool boundary() const {
    return end() || at(TokenKind::LineEnd) || at(TokenKind::Dedent);
  }
  void advance() {
    if (cursor + 1 < significant.size()) {
      work.charge(1, token().begin);
      ++cursor;
    }
  }
  bool take(StringRef value) {
    if (!at(value))
      return false;
    advance();
    return true;
  }
  bool take(TokenKind kind) {
    if (!at(kind))
      return false;
    advance();
    return true;
  }
  void error(StringRef code, StringRef message) {
    work.error(code, message, token().begin, token().end);
  }
  NodeId make(Kind kind, uint32_t begin, ArrayRef<NodeId> children = {}) {
    if (!work.charge(1, token().begin) ||
        data->nodes.size() >= work.budget.nodes ||
        children.size() >
            work.budget.nodes -
                std::min<uint64_t>(data->children.size(), work.budget.nodes)) {
      work.exhaust(token().begin);
      return {0};
    }
    uint32_t height = 1;
    for (auto child : children)
      height = std::max(height, data->nodes[child.index].height + 1);
    if (height > work.budget.depth) {
      work.exhaust(token().begin);
      return {0};
    }
    NodeId id{uint32_t(data->nodes.size())};
    uint32_t last = cursor && significant[cursor - 1] >= begin
                        ? significant[cursor - 1] + 1
                        : begin;
    data->nodes.push_back({kind, begin, last, uint32_t(data->children.size()),
                           uint32_t(children.size()), height,
                           environmentOwner});
    data->children.insert(data->children.end(), children.begin(),
                          children.end());
    return id;
  }
  NodeId missing(StringRef expected) {
    error("syntax.expected", "expected " + expected.str());
    if (++work.insertions > work.budget.insertions)
      work.exhaust(token().begin);
    return make(Kind::Missing, mark());
  }
  bool expect(StringRef value) {
    if (take(value))
      return true;
    missing(value);
    return false;
  }
  NodeId name(bool qualified = true, bool dots = false) {
    auto begin = mark();
    if (!at(TokenKind::Word))
      return missing("name");
    advance();
    if (qualified) {
      while (at("::") || (dots && at("."))) {
        if (text(1) == "{")
          break;
        advance();
        if (!at(TokenKind::Word)) {
          missing("qualified name segment");
          break;
        }
        advance();
      }
    }
    return make(Kind::Name, begin);
  }
  void lineEnd() {
    if (cursor && token().kind != TokenKind::LineEnd &&
        data->tokens[significant[cursor - 1]].kind == TokenKind::Dedent)
      return;
    if (take(TokenKind::LineEnd) || at(TokenKind::Dedent) || end())
      return;
    error("syntax.line", "unexpected token after complete item");
    while (!boundary())
      advance();
    take(TokenKind::LineEnd);
  }
  NodeId recover() {
    auto begin = mark();
    unsigned nesting = 0;
    do {
      if (at(TokenKind::Indent))
        ++nesting;
      if (at(TokenKind::Dedent)) {
        if (!nesting)
          break;
        --nesting;
      }
      advance();
    } while (!end() && (nesting || !boundary()));
    take(TokenKind::LineEnd);
    return make(Kind::Error, begin);
  }
  bool enter() {
    if (++recursion > work.budget.depth) {
      work.exhaust(token().begin);
      return false;
    }
    return work.charge(1, token().begin);
  }
  const NotationDescriptor *notation(StringRef symbol,
                                     NotationDescriptor::Position position) {
    if (!work.charge(1, token().begin))
      return nullptr;
    auto index = syntaxIndices.find(environment);
    if (index == syntaxIndices.end())
      return nullptr;
    auto found = index->second.find(
        std::to_string(static_cast<unsigned>(position)) + ":" + symbol.str());
    return found == index->second.end() ? nullptr : found->second;
  }
  struct Operator {
    unsigned precedence;
    bool right, comparison;
  };
  std::optional<Operator> infix(StringRef op) {
    if (auto n = notation(op, NotationDescriptor::Position::Infix))
      return Operator{n->precedence,
                      n->association == NotationDescriptor::Association::Right,
                      n->association == NotationDescriptor::Association::None};
    if (op == "or" || op == "∨" || op == "||")
      return Operator{10, false, false};
    if (op == "and" || op == "∧" || op == "&&")
      return Operator{20, false, false};
    if (op == "==" || op == "!=" || op == "<=" || op == ">=" || op == "<" ||
        op == ">" || op == "∈")
      return Operator{50, false, true};
    if (op == "+" || op == "-" || op == "++")
      return Operator{65, false, false};
    if (op == "*" || op == "/" || op == "⋅" || op == "%")
      return Operator{70, false, false};
    if (op == "^")
      return Operator{72, true, false};
    return std::nullopt;
  }
  NodeId argument(bool parameter = false) {
    auto begin = mark();
    std::vector<NodeId> children;
    if (token(1).kind == TokenKind::Word &&
        (at("ghost") ||
         (parameter && (at("statement") || at("witness") || at("parameter")))))
      advance();
    children.push_back(expression());
    if (take(":"))
      children.push_back(expression());
    if (take("="))
      children.push_back(expression());
    return make(parameter ? Kind::Parameter : Kind::Argument, begin, children);
  }
  NodeId list(Kind kind, StringRef open, StringRef close,
              bool parameter = false) {
    auto begin = mark();
    expect(open);
    unsigned oldAngle = angleDepth;
    angleDepth = close == ">" ? angleDepth + 1 : 0;
    auto restore = scope_exit([&] { angleDepth = oldAngle; });
    std::vector<NodeId> children;
    while (!end() && !at(close) && !boundary()) {
      auto before = cursor;
      children.push_back(argument(parameter));
      if (take(",") || ((parameter || kind == Kind::Tuple) && take(";")))
        continue;
      if (cursor == before)
        advance();
      if (!at(close)) {
        missing("separator or closing delimiter");
        while (!end() && !at(close) && !at(",") && !at(";") && !boundary())
          advance();
        take(",");
        take(";");
      }
    }
    expect(close);
    return make(kind, begin, children);
  }
  NodeId role() {
    auto begin = mark();
    expect("@");
    std::vector<NodeId> children;
    if (at("(")) {
      children.push_back(list(Kind::Roles, "(", ")"));
    } else {
      children.push_back(name(false));
      if (take("->")) {
        children.push_back(name(false));
        while (at(",") && token(1).kind == TokenKind::Word && text(2) != ":") {
          advance();
          children.push_back(name(false));
        }
      }
    }
    return make(Kind::Roles, begin, children);
  }
  NodeId expression(unsigned minimum = 0) {
    auto begin = mark();
    if (!enter())
      return {0};
    auto leave = scope_exit([&] { --recursion; });
    NodeId left{0};
    auto prefix = notation(text(), NotationDescriptor::Position::Prefix);
    auto delimited = notation(text(), NotationDescriptor::Position::Delimited);
    auto reduction = notation(text(), NotationDescriptor::Position::Reduction);
    if (at("if") || at("match")) {
      bool matching = take("match");
      if (!matching)
        expect("if");
      std::vector<NodeId> parts{expression()};
      expect(":");
      parts.push_back(
          suite(matching ? SuiteKind::Cases : SuiteKind::Statements));
      if (!matching) {
        auto first = mark();
        expect("else");
        expect(":");
        parts.push_back(
            make(Kind::Else, first, {suite(SuiteKind::Statements)}));
      }
      left = make(matching ? Kind::Match : Kind::If, begin, parts);
    } else if (at("-") || at("!") || at("not") || at("¬") || prefix) {
      unsigned power = prefix ? prefix->precedence : 75;
      if (minimum > power)
        error("syntax.association",
              "a weaker prefix in a stronger operand requires parentheses");
      advance();
      left = make(Kind::Prefix, begin, {expression(power)});
    } else if (at("∀") || at("∃")) {
      advance();
      std::vector<NodeId> children{name(false)};
      expect(":");
      children.push_back(expression());
      expect(",");
      children.push_back(expression());
      left = make(Kind::Quantifier, begin, children);
    } else if (at("|") && token(1).kind == TokenKind::Word &&
               (text(2) == "," ||
                (text(2) == "|" && (token(3).kind == TokenKind::Word ||
                                    token(3).kind == TokenKind::Number ||
                                    text(3) == "(" || text(3) == "[")))) {
      advance();
      std::vector<NodeId> children{name(false)};
      while (take(","))
        children.push_back(name(false));
      expect("|");
      children.push_back(expression());
      left = make(Kind::Lambda, begin, children);
    } else if (take("|")) {
      auto value = expression();
      expect("|");
      left = make(Kind::Delimited, begin, {value});
    } else if (reduction) {
      auto descriptor = *reduction;
      advance();
      std::vector<NodeId> children;
      auto groupAhead = [&] {
        unsigned nesting = 0;
        for (unsigned i = 0; cursor + i < significant.size(); ++i) {
          if (!work.charge(1, token(i).begin))
            break;
          if (token(i).kind == TokenKind::LineEnd ||
              token(i).kind == TokenKind::End)
            break;
          if (text(i) == "(")
            ++nesting;
          if (text(i) == ")" && !--nesting)
            break;
          if (nesting == 1 && (text(i) == "in" || text(i) == "∈"))
            return true;
        }
        return false;
      };
      bool grouped = at("(") && groupAhead();
      do {
        if (grouped)
          expect("(");
        children.push_back(expression(100));
        if (!take("in"))
          expect("∈");
        children.push_back(expression());
        if (grouped)
          expect(")");
      } while (grouped && at("(") && groupAhead() && !end());
      if (take("with"))
        children.push_back(expression());
      expect(",");
      children.push_back(expression(descriptor.precedence));
      left = make(Kind::Reduction, begin, children);
    } else if (delimited) {
      auto descriptor = *delimited;
      advance();
      std::vector<NodeId> children;
      while (!end() && !boundary() && !at(descriptor.closing)) {
        auto before = cursor;
        children.push_back(argument());
        if (take(","))
          continue;
        if (cursor == before)
          advance();
        if (!at(descriptor.closing))
          break;
      }
      if (children.size() != descriptor.arity)
        error("syntax.notation",
              "delimited notation has the wrong number of holes");
      expect(descriptor.closing);
      left = make(Kind::Delimited, begin, children);
    } else if (at("(")) {
      left = list(Kind::Tuple, "(", ")");
      if (data->nodes[left.index].childCount == 1)
        data->nodes[left.index].kind = Kind::Group;
    } else if (at("[")) {
      left = list(Kind::Array, "[", "]");
    } else if (at(TokenKind::Number) || at(TokenKind::String) || at("true") ||
               at("false")) {
      advance();
      left = make(Kind::Literal, begin);
    } else if (take("?")) {
      left = make(Kind::Hole, begin);
    } else if (at(TokenKind::Word)) {
      left = name();
    } else {
      left = missing("expression");
      if (!boundary() && !at(")") && !at("]") && !at("}") && !at(">") &&
          !at(",") && !at(";") && !at(":"))
        advance();
      return left;
    }
    while (!end() && !boundary()) {
      if (at("(") && minimum <= 100) {
        auto args = list(Kind::Parameters, "(", ")");
        left = make(Kind::Call, begin, {left, args});
      } else if (at("<") &&
                 token().begin ==
                     data->tokens[data->nodes[left.index].lastToken - 1].end &&
                 (data->nodes[left.index].kind == Kind::Name ||
                  data->nodes[left.index].kind == Kind::StaticApply ||
                  data->nodes[left.index].kind == Kind::Projection) &&
                 minimum <= 100) {
        auto args = list(Kind::Parameters, "<", ">");
        left = make(Kind::StaticApply, begin, {left, args});
      } else if ((at(".") || at("::")) && minimum <= 100) {
        advance();
        auto memberBegin = mark();
        NodeId member;
        if (at(TokenKind::Number)) {
          advance();
          member = make(Kind::Literal, memberBegin);
        } else
          member = name(false);
        left = make(Kind::Projection, begin, {left, member});
      } else if (at("[") && minimum <= 100) {
        auto args = list(Kind::Parameters, "[", "]");
        left = make(Kind::Index, begin, {left, args});
      } else if (at("{") && minimum <= 100) {
        auto fields = list(Kind::Parameters, "{", "}");
        left = make(Kind::Record, begin, {left, fields});
      } else if (at("@") && minimum <= 80) {
        auto roles = role();
        left = make(Kind::RoleType, begin, {left, roles});
      } else if (auto postfix =
                     notation(text(), NotationDescriptor::Position::Postfix);
                 postfix && postfix->precedence >= minimum) {
        advance();
        left = make(Kind::Call, begin, {left});
      } else {
        if (angleDepth && at(">"))
          break;
        auto op = infix(text());
        if (!op || op->precedence < minimum)
          break;
        advance();
        auto right = expression(op->precedence + (op->right ? 0 : 1));
        for (auto operand : {left, right}) {
          const auto &node = data->nodes[operand.index];
          if (node.kind != Kind::Binary || node.childCount != 2)
            continue;
          auto child = data->children[node.firstChild];
          auto index = data->nodes[child.index].lastToken;
          while (index < node.lastToken && data->tokens[index].trivia())
            ++index;
          if (index >= node.lastToken)
            continue;
          auto t = data->tokens[index];
          auto inner = infix(data->revision.text().slice(t.begin, t.end));
          if (inner && inner->precedence == op->precedence &&
              (op->comparison || inner->comparison ||
               inner->right != op->right))
            error(op->comparison ? "syntax.comparison" : "syntax.association",
                  "equal-precedence mixed or nonassociative chains require "
                  "parentheses");
        }
        left = make(Kind::Binary, begin, {left, right});
      }
    }
    return left;
  }
  NodeId attribute() {
    auto begin = mark();
    expect("#");
    expect("[");
    std::vector<NodeId> children{name()};
    if (at("("))
      children.push_back(list(Kind::Parameters, "(", ")"));
    expect("]");
    lineEnd();
    return make(Kind::Attribute, begin, children);
  }
  NodeId suite(SuiteKind kind, bool opaque = false) {
    auto begin = mark();
    if (!take(TokenKind::LineEnd))
      missing("newline before suite");
    if (!take(TokenKind::Indent))
      return missing("indented nonempty suite");
    if (!enter())
      return {0};
    auto leave = scope_exit([&] { --recursion; });
    if (opaque && data->headersOnly) {
      unsigned depth = 1;
      while (!end() && depth) {
        if (at(TokenKind::Indent))
          ++depth;
        if (at(TokenKind::Dedent))
          --depth;
        advance();
      }
      return make(Kind::OpaqueBody, begin);
    }
    std::vector<NodeId> children;
    while (!end() && !at(TokenKind::Dedent)) {
      auto before = cursor;
      if (take(TokenKind::LineEnd))
        continue;
      if (at("#"))
        children.push_back(attribute());
      else if (kind == SuiteKind::Declarations)
        children.push_back(declaration());
      else if (kind == SuiteKind::Contract || kind == SuiteKind::Requests ||
               kind == SuiteKind::Scheme || kind == SuiteKind::Oracle)
        children.push_back(contract(kind));
      else if (kind == SuiteKind::Fields) {
        auto first = mark();
        take("pub");
        auto field = name(false);
        expect(":");
        auto type = expression();
        lineEnd();
        children.push_back(make(Kind::Field, first, {field, type}));
      } else if (kind == SuiteKind::Variants) {
        auto first = mark();
        std::vector<NodeId> parts{name(false)};
        if (at("("))
          parts.push_back(list(Kind::Parameters, "(", ")"));
        lineEnd();
        children.push_back(make(Kind::Variant, first, parts));
      } else if (kind == SuiteKind::Formula) {
        children.push_back(expression());
        lineEnd();
        if (children.size() > 1)
          error("syntax.formula",
                "a formula suite contains exactly one expression");
      } else if (kind == SuiteKind::Cases) {
        auto first = mark();
        expect("case");
        auto pattern = expression();
        expect(":");
        auto body = suite(SuiteKind::Statements);
        children.push_back(make(Kind::Case, first, {pattern, body}));
      } else
        children.push_back(statement());
      if (cursor == before && !end() && !at(TokenKind::Dedent))
        children.push_back(recover());
    }
    if (children.empty())
      missing("nonempty suite");
    take(TokenKind::Dedent);
    return make(Kind::Suite, begin, children);
  }
  NodeId contract(SuiteKind context) {
    auto begin = mark();
    Kind kind = Kind::Request;
    std::vector<NodeId> children;
    if (at("requires") || at("ensures") || at("target") || at("reduces") ||
        at("law")) {
      if (context == SuiteKind::Requests)
        error("syntax.spec", "an audit may submit requests but cannot redefine "
                             "its subject contract");
      auto keyword = text();
      kind = keyword == "requires"  ? Kind::Requires
             : keyword == "ensures" ? Kind::Ensures
             : keyword == "target"  ? Kind::Target
             : keyword == "reduces" ? Kind::Reduces
                                    : Kind::Law;
      advance();
      if (token().kind == TokenKind::Word && text(1) == ":") {
        children.push_back(name(false));
        expect(":");
      } else if (kind == Kind::Law) {
        children.push_back(name(false));
        expect(":");
      }
      if (at(TokenKind::LineEnd)) {
        children.push_back(suite(SuiteKind::Formula, true));
        return make(kind, begin, children);
      }
      children.push_back(expression());
      if (kind == Kind::Reduces) {
        expect("to");
        children.push_back(expression());
      }
    } else if (context == SuiteKind::Oracle && at("query")) {
      advance();
      children.push_back(list(Kind::Parameters, "(", ")", true));
      expect(":");
      children.push_back(suite(SuiteKind::Statements, true));
      return make(Kind::QueryBody, begin, children);
    } else if (context == SuiteKind::Scheme &&
               (at("construction") || at("prover") || at("verifier") ||
                at("public") || at("accept"))) {
      auto word = text();
      advance();
      if (word == "public")
        children.push_back(list(Kind::Parameters, "{", "}"));
      else
        children.push_back(expression());
      kind = Kind::Selection;
    } else {
      children.push_back(name(false));
      if (take("="))
        kind = Kind::GoalAlias;
      else
        expect(":");
      children.push_back(expression());
    }
    lineEnd();
    return make(kind, begin, children);
  }
  NodeId notationDeclaration(uint32_t begin) {
    auto form = text();
    advance();
    std::vector<NodeId> children;
    std::vector<std::string> holes;
    NotationDescriptor descriptor;
    bool explicitFixity = false;
    auto hole = [&] {
      auto value = text().str();
      children.push_back(name(false));
      if (std::find(holes.begin(), holes.end(), value) != holes.end())
        error("syntax.notation", "notation holes must be distinct");
      holes.push_back(std::move(value));
      if (holes.size() > 64)
        work.exhaust(token().begin);
    };
    if (form == "operator") {
      if (at("infixl") || at("infixr") || at("infix") || at("prefix") ||
          at("postfix")) {
        explicitFixity = true;
        using P = NotationDescriptor::Position;
        using A = NotationDescriptor::Association;
        descriptor.position = at("prefix")    ? P::Prefix
                              : at("postfix") ? P::Postfix
                                              : P::Infix;
        descriptor.association = at("infixl")   ? A::Left
                                 : at("infixr") ? A::Right
                                                : A::None;
        descriptor.arity = descriptor.position == P::Infix ? 2 : 1;
        children.push_back(name(false));
        expect("(");
        auto first = mark();
        unsigned precedence = 0;
        if (!at(TokenKind::Number) || text().getAsInteger(10, precedence) ||
            !precedence || precedence > 99)
          error("syntax.notation",
                "operator precedence must be from 1 through 99");
        if (!boundary())
          advance();
        children.push_back(make(Kind::Literal, first));
        descriptor.precedence = precedence;
        expect(")");
      }
    }
    if (form == "indexing") {
      hole();
      expect("[");
      hole();
      while (take(","))
        hole();
      expect("]");
    } else if (form == "notation") {
      auto scalar = source::decodeSourceScalar(text(), 0);
      auto close = scalar ? source::matchingSourceDelimiter(scalar->value)
                          : std::nullopt;
      if (!close)
        error("syntax.notation", "expected a paired Unicode delimiter");
      if (!boundary())
        advance();
      hole();
      while (take(","))
        hole();
      auto closing = source::decodeSourceScalar(text(), 0);
      if (!closing || !close || closing->value != *close)
        error("syntax.notation", "notation requires the matching closer");
      if (!boundary())
        advance();
    } else {
      descriptor.symbol = text().str();
      if (form == "reduction") {
        descriptor.position = NotationDescriptor::Position::Reduction;
        descriptor.precedence = 67;
        descriptor.arity = 2;
        explicitFixity = true;
      }
      auto scalar = source::decodeSourceScalar(text(), 0);
      bool custom =
          scalar && scalar->bytes == text().size() && scalar->value > 127 &&
          source::isMathematicalSymbol(scalar->value) && text() != "∑" &&
          text() != "∏" && text() != "∈" && text() != "∀" && text() != "∃";
      bool fixed = at("+") || at("-") || at("*") || at("==") || at("!") ||
                   at("&&") || at("||");
      if ((explicitFixity && !validNotationDescriptor(descriptor)) ||
          (!explicitFixity && !custom && !fixed))
        error("syntax.notation", "invalid operator symbol or fixed syntax");
      if (!boundary())
        advance();
    }
    expect("=");
    // Capture the exact callable target and optional static arguments. A
    // descriptor's shape never depends on the callable's eventual type.
    auto targetBegin = mark();
    auto target = name();
    if (at("<")) {
      auto args = list(Kind::Parameters, "<", ">");
      target = make(Kind::StaticApply, targetBegin, {target, args});
    }
    children.push_back(target);
    if (form == "reduction" && take(","))
      children.push_back(expression(100));
    if (!holes.empty()) {
      expect("(");
      for (size_t i = 0; i < holes.size(); ++i) {
        if (i)
          expect(",");
        if (!take(holes[i])) {
          error("syntax.notation",
                "notation must use every hole once in written order");
          if (!boundary())
            advance();
        }
      }
      expect(")");
    }
    lineEnd();
    return make(Kind::Notation, begin, children);
  }
  NodeId imports() {
    auto begin = mark();
    expect("{");
    std::vector<NodeId> children;
    if (at("}"))
      missing("nonempty import list");
    while (!end() && !at("}")) {
      auto first = mark();
      if ((at("operator") || at("reduction") || at("notation")) &&
          text(1) != "," && text(1) != "}" && text(1) != "::") {
        advance();
        if (at(TokenKind::Punctuation))
          advance();
        else
          missing("notation symbol");
        children.push_back(make(Kind::ImportSelector, first));
      } else if (at("indexing") && text(1) == "[") {
        advance();
        expect("[");
        expect("]");
        children.push_back(make(Kind::ImportSelector, first));
      } else
        children.push_back(name());
      if (!take(","))
        break;
    }
    expect("}");
    return make(Kind::Parameters, begin, children);
  }
  NodeId declaration() {
    auto begin = mark();
    auto oldEnv = environment;
    auto oldOwner = environmentOwner;
    auto supplied = data->environments.find(token().begin);
    if (supplied != data->environments.end()) {
      environment = &supplied->second;
      environmentOwner = supplied->first;
    }
    auto restore = scope_exit([&] {
      environment = oldEnv;
      environmentOwner = oldOwner;
    });
    if (at("#"))
      return attribute();
    bool visible = take("pub");
    auto keyword = text();
    if (at("operator") || at("notation") || at("indexing") || at("reduction"))
      return notationDeclaration(begin);
    if (keyword == "law")
      return contract(SuiteKind::Contract);
    Kind kind;
    SuiteKind bodyKind = SuiteKind::Statements;
    std::vector<NodeId> children;
    bool needsSuite = false;
    if (take("module")) {
      kind = Kind::Module;
      bodyKind = SuiteKind::Declarations;
    } else if (take("section")) {
      kind = Kind::Section;
      bodyKind = SuiteKind::Declarations;
      needsSuite = true;
    } else if (take("interface")) {
      kind = Kind::Interface;
      bodyKind = SuiteKind::Declarations;
      needsSuite = true;
    } else if (take("struct")) {
      kind = Kind::Struct;
      bodyKind = SuiteKind::Fields;
      needsSuite = true;
    } else if (take("enum")) {
      kind = Kind::Enum;
      bodyKind = SuiteKind::Variants;
      needsSuite = true;
    } else if (take("use")) {
      if (take("lean"))
        children.push_back(name(true, true));
      else
        children.push_back(name());
      if (take("::"))
        children.push_back(imports());
      if (take("as"))
        children.push_back(name(false));
      lineEnd();
      return make(Kind::Use, begin, children);
    } else if (take("spec")) {
      bool named = !at("for");
      if (named) {
        children.push_back(name(false));
        if (at("<"))
          children.push_back(list(Kind::StaticParameters, "<", ">", true));
      } else if (visible) {
        error("syntax.spec",
              "an owner specification has no visibility modifier");
      }
      expect("for");
      children.push_back(expression(80));
      if (take(":"))
        children.push_back(
            suite(named ? SuiteKind::Requests : SuiteKind::Contract, true));
      else
        lineEnd();
      return make(Kind::Spec, begin, children);
    } else if (take("scheme")) {
      children.push_back(name(false));
      expect("=");
      children.push_back(expression(80));
      expect(":");
      children.push_back(suite(SuiteKind::Scheme, true));
      return make(Kind::Scheme, begin, children);
    } else if (take("protocol"))
      kind = Kind::Protocol;
    else if (take("relation")) {
      kind = Kind::Relation;
      needsSuite = true;
    } else if (take("oracle")) {
      expect("def");
      kind = Kind::OracleDefinition;
      bodyKind = SuiteKind::Oracle;
      needsSuite = true;
    } else if (take("local") || take("ghost") || take("entry")) {
      expect("def");
      kind = Kind::Definition;
    } else if (take("def"))
      kind = Kind::Definition;
    else if (take("type"))
      kind = Kind::TypeAlias;
    else if (take("domain"))
      kind = Kind::Domain;
    else {
      error("syntax.declaration", "expected a declaration");
      return recover();
    }
    if (kind != Kind::Section)
      children.push_back(name(kind == Kind::Module));
    if (at("<"))
      children.push_back(list(Kind::StaticParameters, "<", ">", true));
    else if (kind == Kind::Section)
      children.push_back(missing("section parameters"));
    if (kind == Kind::Section && (at("roles") || at("effects") || at("where")))
      error("syntax.section", "section headers accept only static parameters");
    if (take("roles"))
      children.push_back(list(Kind::Roles, "(", ")"));
    if (kind == Kind::Protocol || kind == Kind::Definition ||
        kind == Kind::Relation || kind == Kind::OracleDefinition) {
      children.push_back(list(Kind::Parameters, "(", ")", true));
      if (take("->")) {
        auto first = mark();
        children.push_back(make(Kind::Result, first, {expression()}));
      }
    }
    if (kind == Kind::TypeAlias || kind == Kind::Domain) {
      if (take("=") || take(":"))
        children.push_back(expression());
      else
        children.push_back(missing("type definition or constraint"));
      lineEnd();
      return make(kind, begin, children);
    }
    if (kind == Kind::Module && at(":") &&
        token(1).kind != TokenKind::LineEnd) {
      advance();
      children.push_back(expression());
    }
    if (take("effects"))
      children.push_back(list(Kind::Effects, "(", ")"));
    if (take("where")) {
      auto first = mark();
      children.push_back(make(Kind::Where, first, {expression()}));
    }
    if (take(":")) {
      auto body = suite(bodyKind, bodyKind == SuiteKind::Statements ||
                                      bodyKind == SuiteKind::Oracle);
      children.push_back(body);
    } else {
      if (needsSuite)
        children.push_back(missing("declaration suite"));
      lineEnd();
    }
    auto id = make(kind, begin, children);
    return id;
  }
  NodeId action() {
    auto begin = mark();
    std::vector<NodeId> children;
    if (take("send")) {
      children.push_back(expression());
      if (take("from"))
        children.push_back(name(false));
      expect("to");
      children.push_back(name(false));
      while (take(","))
        children.push_back(name(false));
      return make(Kind::Send, begin, children);
    }
    if (take("query")) {
      children.push_back(expression());
      expect("at");
      children.push_back(expression());
      return make(Kind::Query, begin, children);
    }
    return expression();
  }
  NodeId statement() {
    auto begin = mark();
    std::vector<NodeId> children;
    Kind kind = Kind::ExpressionStatement;
    if (take("return")) {
      kind = Kind::Return;
      children.push_back(expression());
    } else if (at("guard") && token(1).kind != TokenKind::LineEnd &&
               text(1) != "::" && text(1) != "." && text(1) != "=" &&
               text(1) != ":=" && text(1) != "<-") {
      advance();
      kind = Kind::Guard;
      if (at("@"))
        children.push_back(role());
      children.push_back(expression());
    } else if (take("for")) {
      children.push_back(expression());
      expect("in");
      children.push_back(expression());
      expect("..");
      children.push_back(expression());
      if (take("roles"))
        children.push_back(list(Kind::Roles, "(", ")"));
      if (take("max"))
        children.push_back(expression());
      expect(":");
      children.push_back(suite(SuiteKind::Statements));
      return make(Kind::For, begin, children);
    } else if (take("if")) {
      children.push_back(expression());
      expect(":");
      children.push_back(suite(SuiteKind::Statements));
      if (take("else")) {
        auto first = mark();
        expect(":");
        children.push_back(
            make(Kind::Else, first, {suite(SuiteKind::Statements)}));
      }
      return make(Kind::If, begin, children);
    } else if (take("match")) {
      children.push_back(expression());
      expect(":");
      children.push_back(suite(SuiteKind::Cases));
      return make(Kind::Match, begin, children);
    } else {
      bool mutableBinding = take("mut");
      children.push_back(expression());
      if (take(":"))
        children.push_back(expression());
      if (take("=")) {
        kind = Kind::Binding;
        children.push_back(expression());
      } else if (take("<-")) {
        kind = Kind::ActionBinding;
        children.push_back(action());
      } else if (take(":=")) {
        kind = Kind::Update;
        children.push_back(expression());
      } else if (mutableBinding)
        children.push_back(missing("binding initializer"));
    }
    lineEnd();
    return make(kind, begin, children);
  }
  void validate(const Environment &env) {
    std::map<std::string, NotationDescriptor> keys;
    if (env.notation.size() > 4096) {
      work.exhaust(0);
      return;
    }
    for (const auto &n : env.notation) {
      if (!work.charge(n.symbol.size() + n.closing.size() + 1, token().begin))
        break;
      syntaxIndices[&env].try_emplace(n.key(), &n);
      if (!validNotationDescriptor(n))
        error("syntax.notation", "invalid bounded notation descriptor");
      using P = NotationDescriptor::Position;
      if (n.position == P::Infix || n.position == P::Postfix ||
          n.position == P::Prefix || n.position == P::Reduction) {
        auto other = n;
        other.position = n.position == P::Infix     ? P::Postfix
                         : n.position == P::Postfix ? P::Infix
                         : n.position == P::Prefix  ? P::Reduction
                                                    : P::Prefix;
        if (keys.count(other.key()))
          error("syntax.notation", "notation token has conflicting positions");
      }
      auto [it, inserted] = keys.emplace(n.key(), n);
      if (!inserted && it->second != n)
        error("syntax.notation", "conflicting notation descriptors");
    }
  }

public:
  Parser(source::Revision revision, source::SourceId id, bool headers,
         Environment env, Environments environments, Budget budget,
         source::Cancellation cancellation)
      : data(std::make_shared<Storage>(std::move(revision), id)),
        work(*data, budget, cancellation) {
    data->headersOnly = headers;
    data->defaultEnvironment = std::move(env);
    data->environments = std::move(environments);
    environment = &data->defaultEnvironment;
  }
  Snapshot run() {
    const Budget maximum;
    if (work.budget.bytes > maximum.bytes ||
        work.budget.tokens > maximum.tokens ||
        work.budget.tokenBytes > maximum.tokenBytes ||
        work.budget.identifierBytes > maximum.identifierBytes ||
        work.budget.nodes > maximum.nodes ||
        work.budget.depth > maximum.depth || work.budget.work > maximum.work ||
        work.budget.diagnostics > maximum.diagnostics ||
        work.budget.insertions > maximum.insertions)
      work.exhaust(0);
    lex(work);
    layout(work);
    for (uint32_t i = 0; i < data->tokens.size(); ++i)
      if (!data->tokens[i].trivia())
        significant.push_back(i);
    if (significant.empty())
      significant.push_back(0);
    // A fixed leaf is the bounded failure result, never an executable node.
    data->nodes.push_back({Kind::Error, 0, 0, 0, 0, 1, UINT32_MAX});
    validate(*environment);
    if (data->environments.size() > work.budget.nodes)
      work.exhaust(0);
    for (const auto &[_, env] : data->environments) {
      if (work.stopped())
        break;
      validate(env);
    }
    std::vector<NodeId> children;
    while (!end()) {
      auto before = cursor;
      if (take(TokenKind::LineEnd))
        continue;
      if (at(TokenKind::Indent) || at(TokenKind::Dedent)) {
        error("syntax.indent", "unexpected suite boundary");
        advance();
      } else
        children.push_back(declaration());
      if (cursor == before && !end())
        children.push_back(recover());
    }
    data->root = make(Kind::File, 0, children);
    data->nodes[data->root.index].firstToken = 0;
    data->nodes[data->root.index].lastToken = uint32_t(data->tokens.size() - 1);
    data->workUsed = work.budget.work - work.remaining;
    return Snapshot(data);
  }
};
} // namespace zkc::syntax::detail
namespace zkc::syntax {
Snapshot parseHeaders(source::Revision revision, source::SourceId id,
                      Budget budget, source::Cancellation cancellation) {
  return detail::Parser(std::move(revision), id, true, {}, {}, budget,
                        cancellation)
      .run();
}
Snapshot parseBodies(const Snapshot &headers, Environment environment,
                     Environments environments, Budget budget,
                     source::Cancellation cancellation) {
  return detail::Parser(headers.revision(), headers.sourceId(), false,
                        std::move(environment), std::move(environments), budget,
                        cancellation)
      .run();
}
Snapshot parse(source::Revision revision, Environment environment,
               Budget budget, source::Cancellation cancellation,
               source::SourceId id) {
  return detail::Parser(std::move(revision), id, false, std::move(environment),
                        {}, budget, cancellation)
      .run();
}
} // namespace zkc::syntax
