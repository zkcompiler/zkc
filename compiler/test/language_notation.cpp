#include "../lib/Language/Internal.h"
#include "support/NativeCases.h"
#include "zkc/Language/Names.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::language::detail;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
Expected<SyntaxModule> syntax(StringRef prefix, StringRef expression,
                              const Limits &limits = {}) {
  SourceBuffer source{"m",
                      "module m;" + prefix.str() +
                          "fn f(a:bool,b:bool,c:bool)->bool{return " +
                          expression.str() + ";}",
                      {}};
  Work work{limits};
  std::vector<Token> tokens;
  if (auto error = lex(source, {0}, work, tokens))
    return error;
  auto parsed = parse(source, {0}, tokens, work);
  if (!parsed)
    return parsed.takeError();
  auto environment = fixedNotationEnvironment({0});
  if (auto error = resolveNotationSyntax(parsed->operators, environment, work))
    return error;
  if (auto error = parseBodies(
          source, *parsed, tokens,
          std::make_shared<const NotationEnvironment>(std::move(environment)),
          work))
    return error;
  return std::move(*parsed);
}
std::string shape(const SyntaxDeclaration &decl, unsigned index) {
  const auto &expression = decl.expressions[index];
  if (expression.children.empty())
    return expression.text;
  std::string result =
      expression.notation ? expression.notation->symbol
      : expression.kind == Expression::Kind::Projection ? "." + expression.text
      : expression.kind == Expression::Kind::Not        ? "!"
                                                        : expression.text;
  result += "(";
  for (unsigned i = 0; i < expression.children.size(); ++i) {
    if (i)
      result += ",";
    result += shape(decl, expression.children[i]);
  }
  return result + ")";
}
void hasShape(StringRef declarations, StringRef expression,
              StringRef expected) {
  auto parsed = take(syntax(declarations, expression));
  const auto &decl = parsed.declarations.front();
  auto actual = shape(decl, decl.bodies.front().results.front().second);
  require(actual == expected, "unexpected parse: " + actual);
}
Expected<CheckedProject> checked(std::vector<SourceBuffer> sources,
                                 const Limits &limits = {}) {
  auto captureValue = capture(std::move(sources));
  if (!captureValue)
    return captureValue.takeError();
  return analyze(*captureValue, limits).checkedProject();
}
Expected<CheckedProject> checked(StringRef source, const Limits &limits = {}) {
  return checked({{"m", "module m;" + source.str(), {}}}, limits);
}
const Declaration &declaration(const CheckedProject &project, StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == name)
      return decl;
  throw std::runtime_error("missing declaration");
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("fixed ASCII expression structure", [&] {
    hasShape("", "a+b*c-a", "-(+(a,*(b,c)),a)");
    hasShape("", "!a&&b||c", "||(&&(!(a),b),c)");
    refuses(syntax("", "a==b==c"), "source.syntax");
    hasShape("", "(a==b)==c", "==(==(a,b),c)");
    for (StringRef expression : {"a⊜b==c", "a==b⊜c"})
      refuses(syntax("operator infix(50) ⊜=f;", expression),
              "source.notation-association");
  });
  cases.run("all infix associativities and grouping", [&] {
    hasShape("operator infixl(60) ⊕=f;operator infixl(70) ⊗=f;", "a⊕b⊗c",
             "⊕(a,⊗(b,c))");
    hasShape("operator infixl(60) ⊕=f;", "a⊕b⊕c", "⊕(⊕(a,b),c)");
    hasShape("operator infixr(60) ⊕=f;", "a⊕b⊕c", "⊕(a,⊕(b,c))");
    hasShape("operator infix(60) ⊕=f;", "a⊕(b⊕c)", "⊕(a,⊕(b,c))");
    refuses(syntax("operator infix(60) ⊕=f;", "a⊕b⊕c"),
            "source.notation-association");
    for (StringRef expression : {"a⊕b⊗c", "a⊗b⊕c"})
      refuses(syntax("operator infixl(60) ⊕=f;operator infixr(60) ⊗=f;",
                     expression),
              "source.notation-association");
    hasShape("operator infixl(60) ⊕=f;operator infixr(60) ⊗=f;", "(a⊕b)⊗c",
             "⊗(⊕(a,b),c)");
  });
  cases.run("prefix powers and position disambiguation", [&] {
    hasShape("operator prefix(75) ⊖=f;operator infixl(65) ⊖=f;", "⊖a⊖b",
             "⊖(⊖(a),b)");
    hasShape("operator prefix(60) ⊖=f;operator infixl(70) ⊗=f;", "⊖a⊗b",
             "⊖(⊗(a,b))");
    refuses(syntax("operator prefix(60) ⊖=f;operator infixl(70) ⊗=f;", "a⊗⊖b"),
            "source.notation-precedence");
    hasShape("operator prefix(60) ⊖=f;operator infixl(70) ⊗=f;", "a⊗(⊖b)",
             "⊗(a,⊖(b))");
    refuses(
        syntax("operator prefix(60) ⊖=f;operator infixl(70) ⊖=f;operator ⊖=f;",
               "a"),
        "source.notation-ambiguous");
  });
  cases.run("postfix and projection share the suffix loop", [&] {
    hasShape("operator postfix(80) ⊤=f;", "a⊤⊤", "⊤(⊤(a))");
    hasShape("operator postfix(80) ⊤=f;", "a⊤.0", ".0(⊤(a))");
    hasShape("operator postfix(80) ⊤=f;", "a.0⊤", "⊤(.0(a))");
    hasShape("operator postfix(60) ⊤=f;", "a*b⊤", "⊤(*(a,b))");
    refuses(syntax("operator postfix(60) ⊤=f;operator infixl(60) ⊤=f;", "a"),
            "source.notation-conflict");
  });
  cases.run("delimiter holes preserve shape and nesting", [&] {
    hasShape("notation ⟪ left,right ⟫=f(left,right);", "⟪a,⟪b,c⟫⟫",
             "⟪(a,⟪(b,c))");
    hasShape("notation ⟪ left,middle,right ⟫=f(left,middle,right);", "⟪a,b,c⟫",
             "⟪(a,b,c)");
    for (StringRef expression : {"⟪a⟫", "⟪a,b,c⟫", "⟪a,⟫", "⟪a,,b⟫", "⟪a,b⟩"})
      refuses(syntax("notation ⟪ left,right ⟫=f(left,right);", expression),
              "source.notation-delimiter");
    for (StringRef definition :
         {"notation ⟪ a,a ⟫=f(a,a);", "notation ⟪ a,b ⟫=f(b,a);",
          "notation ⟪ a,b ⟫=f(a,a);", "notation ⟪ a,b ⟩=f(a,b);"})
      refuses(syntax(definition, "a"), "source.notation");
  });
  cases.run("fixed grammar and binder reservations", [&] {
    for (StringRef definition :
         {"operator infixr(65) +=f;", "operator prefix(65) -=f;",
          "operator infixl(64) +=f;"})
      refuses(syntax(definition, "a"), "source.notation-conflict");
    for (StringRef definition :
         {"operator prefix(70) ∑=f;", "operator prefix(70) ∏=f;",
          "operator infixl(0) ⊕=f;", "operator infixl(100) ⊕=f;"})
      refuses(syntax(definition, "a"), "source.notation");
    refuses(syntax("", "a⊕b"), "source.notation-visibility");
    refuses(syntax("", "⟪a,b⟫"), "source.notation-visibility");
    refuses(syntax("operator ⊕=f;", "a"), "source.notation-visibility");
  });
  cases.run("body prefix resolves later explicit syntax", [&] {
    take(checked(R"(
      math fn plus(a:bool,b:bool)->bool{return a;}
      fn f(a:bool,b:bool)->bool {
        operator ⊕=plus;
        operator infixl(65) ⊕=plus;
        return a⊕b;
      }
    )"));
    refuses(
        checked(
            "fn f(a:bool)->bool{let b=a;operator infixl(65) ⊕=f;return b;}"),
        "source.operator");
    refuses(
        checked("fn f(a:bool)->bool{pub operator infixl(65) ⊕=f;return a;}"),
        "source.operator");
    take(checked(
        "fn notation(prefix:bool,infixl:bool)->bool{return prefix&&infixl;}"));
    take(checked(
        "fn f(operator:index,x:index)->index{operator+x;return operator+x;}"));
    take(checked(
        "use zkc::prelude::{operator +};fn f(a:index)->index{return a+1;}"));
  });
  cases.run("Unicode names and original byte spans", [&] {
    const std::string text =
        "module 数学;pub fn 函数(α:bool,β₂:bool)->bool{return α&&β₂;}";
    auto project = take(checked({{"数学", text, {}}}));
    require(project.capture().sources().front().text == text,
            "capture bytes changed");
    const auto &decl = declaration(project, "数学::函数");
    require(decl.inputs[1].name == "β₂", "subscript name changed");
    bool found = false;
    for (const auto &token : project.tokens({0}))
      if (StringRef(text).slice(token.span.begin, token.span.end) == "β₂") {
        require(token.span.end - token.span.begin == 5,
                "span is not UTF-8 bytes");
        found = true;
      }
    require(found, "Unicode token missing");
    require(take(encodeSymbol("m::α")) == "s1h6d2hceb1",
            "symbol encoding mismatch");
    take(checked("fn f(а:bool,a:bool)->bool{return а&&a;}"));
    refuses(checked("fn f(e\u0301:bool)->bool{return true;}"), "source.nfc");
    refuses(checked("fn f(a\u200d:bool)->bool{return true;}"),
            "source.unicode");
    refuses(checked("fn f(a:bool)->bool{return a\u202e;}"), "source.unicode");
    take(checked("// comment \u202e\nfn f(a:bool)->bool{return a;}"));
  });
  cases.run(
      "syntax resource limits include fixed descriptors and retained holes",
      [&] {
        Limits limits;
        limits.notationDescriptors = 6;
        refuses(checked("", limits), "source.limit");
        limits = Limits{};
        limits.notationHoles = 0;
        auto noHoles =
            take(checked("fn f(a:index,b:index)->index{return a+b;}", limits));
        require(noHoles.checkedNotationHoles() == 0,
                "ordinary operators consumed the delimiter-hole budget");
        limits.notationHoles = 1;
        take(syntax("notation ⟪ a ⟫=f(a);", "⟪a⟫", limits));
        limits.notationHoles = 2;
        refuses(syntax("notation ⟪ a,b,c ⟫=f(a,b,c);", "a", limits),
                "source.limit");
        limits = Limits{};
        limits.expressionDepth = 4;
        refuses(syntax("operator infixl(60) ⊕=f;", "a⊕a⊕a⊕a⊕a", limits),
                "source.limit");
        limits = Limits{};
        limits.notationDescriptors = 7;
        refuses(syntax("operator infixl(60) ⊕=f;", "a", limits),
                "source.limit");
      });
  const std::string library = R"(module v;
    pub math fn first(a:bool,b:bool)->bool{return a;}
    pub operator infixl(65) ⊕=first;
    pub notation ⟪ a,b ⟫=first(a,b);
  )";
  cases.run("imports and reexports supply one syntax environment", [&] {
    for (bool reverse : {false, true}) {
      std::vector<SourceBuffer> sources{
          {"v", library, {}},
          {"r", "module r;pub use v::{operator ⊕,notation ⟪};", {}},
          {"m",
           std::string("module m;") +
               (reverse ? "use r;use v;" : "use v;use r;") +
               "fn f(a:bool,b:bool)->bool{return ⟪a⊕b,b⟫;}",
           {}}};
      if (reverse)
        std::reverse(sources.begin(), sources.end());
      take(checked(std::move(sources)));
    }
    refuses(
        checked(
            {{"v", library, {}},
             {"m",
              "module m;use v::{first};fn f(a:bool,b:bool)->bool{return a⊕b;}",
              {}}}),
        "source.notation-visibility");
    refuses(checked({{"v", library, {}},
                     {"m", "module m;use v::{notation ⟩};", {}}}),
            "source.syntax");
  });
  cases.run("short exported syntax resolves at its definition module", [&] {
    take(checked(
        {{"v",
          R"(module v; pub math fn first(a:bool,b:bool)->bool{return a;}
        operator infixl(65) ⊕=first; pub operator ⊕=first;)",
          {}},
         {"m", "module m;use v;fn f(a:bool,b:bool)->bool{return a⊕b;}", {}}}));
  });
  cases.run("local target override cannot change syntax or fall back", [&] {
    refuses(checked({{"v", library, {}},
                     {"m",
                      R"(module m;use v;
      fn f(a:bool,b:bool)->bool{operator infixl(66) ⊕=v::first;return a⊕b;})",
                      {}}}),
            "source.notation-conflict");
    refuses(checked({{"v", library, {}},
                     {"m",
                      R"(module m;use v;
      fn numbers(a:index,b:index)->index=primitive("index.add");
      fn f(a:bool,b:bool)->bool{operator ⊕=numbers;return a⊕b;})",
                      {}}}),
            "source.operator");
  });
  return cases.result();
}
