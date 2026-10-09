#include "zkc/Compiler/Language.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <functional>
using namespace llvm;
using namespace zkc::language;
namespace {
void require(bool ok, const Twine &message) {
  if (!ok) {
    errs() << message << '\n';
    std::exit(1);
  }
}
template <class T> T must(Expected<T> result) {
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
const std::string prelude = R"(module m;
domain F=field("bls12-381.fr");
fn f(x:F)->F{return x;}
fn g(x:F,y:F)->F{return x+y;}
fn unit(x:F)->(){return ();}
fn yes(x:bool)->bool{return x;}
math fn zero(x:F)->F{return 0;}
math fn ignored(x:F,y:F)->F{let unused=x*y;return 0;}
math fn keep(x:F,y:F)->F{return x;}
math fn firstPair(x:F,y:F)->F{let packed=(x,y);return packed.0;}
math fn pair(x:F,y:F)->(F,F){return(x+y,x);}
)";
Expected<CheckedProject> analyzeText(StringRef body) {
  auto capture = must(
      zkc::language::capture({{"m", prelude + body.str(), "placement.zkc"}}));
  return analyze(capture).checkedProject();
}
void refuses(StringRef body, StringRef code) {
  auto result = analyzeText(body);
  require(!result, "unexpected acceptance: " + body);
  auto error = toString(result.takeError());
  require(StringRef(error).contains(code),
          "expected " + code + ": " + error + "\n" + body);
}
CheckedOriginal native(StringRef body) {
  auto original = must(
      prepareOriginal(must(closeEntry(must(analyzeText(body)), "m::Demo"))));
  for (bool simplify : {false, true})
    must(compileEntry(original, {simplify, false}));
  return original;
}
std::vector<unsigned> callOwners(const Body &body) {
  std::vector<unsigned> result;
  for (const auto &operation : body.operations)
    if (auto *call = std::get_if<HelperCall>(&operation.action);
        call && call->owner)
      result.push_back(*call->owner);
  return result;
}
void examples() {
  native("struct Ticket:Drop {} fn make()->Ticket{return Ticket{};}"
         "fn consumeTicket(x:Ticket)->bool{consume x;return true;}"
         "protocol Run roles(P,V)()->(r:bool@V){return consumeTicket(make());}"
         "entry Demo=Run;");
  refuses("struct Ticket:Drop {} fn make()->Ticket{return Ticket{};}"
          "protocol Run roles(P,V)()->(){let _=make();return ();}",
          "source.owner");
  native("interface Select{math fn selected(x:F,y:F)->F;}"
         "component First:Select{math fn selected(x:F,y:F)->F{return x;}}"
         "protocol Run<C:Select> roles(P,V)(s:F@(P,V),p:F@P)->(){"
         "let r=C::selected(f(s),p);return ();}entry Demo=Run<First>;");
  for (StringRef expression : {"f(p)", "f(f(p))", "f(s)+p", "g(f(s),p)",
                               "zero(g(f(s),p))", "zero(f(v))+f(p)"}) {
    auto original = native(
        "protocol Run roles(P,V)(p:F@P,v:F@V,s:F@(P,V))->(r:F@P){return " +
        expression.str() + ";}entry Demo=Run;");
    require(!callOwners(*original.entry().protocol().body).empty(),
            "ordinary call disappeared");
  }
  const std::string header =
      "protocol Run roles(P,V)(p:F@P,v:F@V,s:F@(P,V))->(){";
  for (StringRef expression :
       {"f(s)", "zero(f(s))", "ignored(f(s),p)", "zero(f(s)*p)",
        "zero(f(s)-f(s))", "zero(f(s)*0)"})
    refuses(header + "let r=" + expression.str() + ";return ();}",
            "source.owner");
  refuses(header + "let r@P=zero(f(s));return ();}", "source.owner");
  refuses(header + "let r=f(s);let actual=send P->V(r);return ();}",
          "source.owner");
  refuses(header + "let r@P={let x=f(s);x};return ();}", "source.owner");
  refuses(header + "let r=ignored(f(v),p);return ();}", "source.roles");
  refuses(header + "let r@V=f(p);return ();}", "source.roles");
  refuses(header + "let r@(P,V)=f(s);return ();}", "source.roles");
  refuses(header + "let mut x=s;x=f(p);return ();}", "source.roles");
  refuses(header + "let t=pair(s,p);let x@V=t.1;return ();}", "source.roles");
  refuses(header + "let r@V=firstPair(s,p);return ();}", "source.roles");
  refuses(header + "let r@P=firstPair(p,v);return ();}", "source.roles");
  // Selection fixes P from the returned product, then formation fails at V.
  refuses("math fn mixed(x:F,y:F,z:F)->F{let unused=x*z;return x*y;}" + header +
              "let r=mixed(f(s),p,v);return ();}",
          "source.roles");
  native(header + "let x@P=f(s);let r=ignored(x,p);let _@P=unit(s);return "
                  "();}entry Demo=Run;");
  native(header + "let r@P={let x=f(p);f(s)+x};return ();}entry Demo=Run;");
  auto mixed =
      native(header + "let r@P=zero(f(v))+f(s);return ();}entry Demo=Run;");
  require(callOwners(*mixed.entry().protocol().body) ==
              std::vector<unsigned>({1, 0}),
          "one statement lost its independently owned calls");
  auto nested = native(header + "let r@P=f(s)+{let y@V=f(s);zero(y)};"
                                "return ();}entry Demo=Run;");
  require(callOwners(*nested.entry().protocol().body) ==
              std::vector<unsigned>({0, 1}),
          "inner statement settlement changed a pending outer call");
  native("protocol Run roles(P,V)(s:F@(P,V))->(r:F@V){let r=send "
         "P->V(g(f(s),f(s)));return r;}entry Demo=Run;");
  native("protocol Pair roles(P,V)(p:F@P,v:F@V)->(p:F@P,v:F@V){return(p,v);}"
         "protocol Run "
         "roles(P,V)(s:F@(P,V))->(p:F@P,v:F@V){let(a,b)=Pair(f(s),f(s));return("
         "p=a,v=b);}entry Demo=Run;");
  refuses("protocol Pair roles(P,V)(p:F@P,v:F@V)->(p:F@P,v:F@V){return(p,v);}" +
              header + "let r=Pair(p,v);return ();}",
          "source.binding");
  auto outputs = native("protocol Run "
                        "roles(P,V)(s:F@(P,V))->(p:F@P,v:F@V){return(v=f(s),p="
                        "f(s));}entry Demo=Run;");
  require(callOwners(*outputs.entry().protocol().body) ==
              std::vector<unsigned>({1, 0}),
          "return order or independent port demand changed");
  native("protocol Run roles(P,V)(s:F@(P,V),n:index@P)->(r:F@P){let mut x@P=s;"
         "for _ in 0..n roles(P) max 4{x=f(x);}return x;}entry Demo=Run;");
  refuses("protocol Run roles(P,V)(n:index@P,s:F@V)->(){for _ in 0..n roles(P) "
          "max 4{let x=f(s);}return ();}",
          "source.roles");
  native("protocol Run roles(P)(n:index@P,x:F@P)->(){"
         "for _ in 0..n roles(P) max 4{unit(x)}return ();}entry Demo=Run;");
  native("protocol Run roles(P,V)(n:index@(P,V),x:F@P)->(){"
         "for _ in 0..n roles(P,V) max 4{unit(x)}return ();}entry Demo=Run;");
  refuses("protocol Run roles(P,V)(n:index@(P,V),x:F@(P,V))->(){"
          "for _ in 0..n roles(P,V) max 4{unit(x)}return ();}",
          "source.owner");
  native("protocol Run roles(P)(n:index@P)->(){"
         "for _ in 0..n roles(P) max 4{}return ();}entry Demo=Run;");
  native("fn count(n:index)->index{return n;}"
         "protocol Run roles(P,V)(n:index@(P,V))->(){"
         "for _ in 0..count(n) roles(P) max 4{}return ();}entry Demo=Run;");
  refuses("fn count(n:index)->index{return n;}"
          "protocol Run roles(P,V)(n:index@(P,V))->(){"
          "for _ in 0..count(n) roles(P,V) max 4{}return ();}",
          "source.roles");
  native("protocol Run roles(P,V)(s:F@(P,V),go:bool@V)->(r:F@V)completes{"
         "let ()=finish_if @V(yes(go))(r=f(s));return f(s);}entry Demo=Run;");
  native("fn check(go:bool)->bool{require go;return go;}"
         "protocol Run roles(P,V)(go:bool@V)->(r:bool@V){require "
         "yes(go);return check(go);}entry Demo=Run;");
  refuses(
      "protocol Run roles(P,V)(go:bool@(P,V))->(){require yes(go);return ();}",
      "source.owner");
  refuses("protocol Run roles(P)(go:bool@P)->(){guard @P go;return ();}",
          "source.syntax");
  refuses("fn bad(go:bool)->(){require @P go;return ();}", "source.roles");
  refuses("protocol Run roles(P)()->(){require @;return ();}", "source.name");
  // Suffixes cannot alter the committed owner; a direct return demand can.
  auto a = native(header + "let x=f(p);return ();}entry Demo=Run;");
  auto b = native(
      header + "let x=f(p);let actual=send P->V(x);return ();}entry Demo=Run;");
  require(callOwners(*a.entry().protocol().body) ==
              callOwners(*b.entry().protocol().body),
          "a later statement changed an earlier owner");
}

// Independent finite oracle over generated source expression trees. It
// evaluates candidate assignments using bitset set semantics, never the
// production constraint representation. K and F are deliberately separate.
struct Expr {
  enum Kind { A, B, Call, BinaryCall, Product, Zero, Ignored, FirstPair } kind;
  std::vector<Expr> children;
};
std::string source(const Expr &e) {
  if (e.kind == Expr::A)
    return "a";
  if (e.kind == Expr::B)
    return "b";
  if (e.kind == Expr::Call)
    return "f(" + source(e.children[0]) + ")";
  if (e.kind == Expr::Zero)
    return "zero(" + source(e.children[0]) + ")";
  auto a = source(e.children[0]), b = source(e.children[1]);
  if (e.kind == Expr::Product)
    return "(" + a + "*" + b + ")";
  return std::string(e.kind == Expr::BinaryCall ? "g"
                     : e.kind == Expr::Ignored  ? "ignored"
                                                : "firstPair") +
         "(" + a + "," + b + ")";
}
unsigned count(const Expr &e) {
  unsigned n = e.kind == Expr::Call || e.kind == Expr::BinaryCall;
  for (const auto &child : e.children)
    n += count(child);
  return n;
}
unsigned evaluate(const Expr &e, unsigned a, unsigned b,
                  ArrayRef<unsigned> owners, unsigned &cursor, bool &selection,
                  bool &formation) {
  if (e.kind == Expr::A)
    return a;
  if (e.kind == Expr::B)
    return b;
  std::vector<unsigned> arguments;
  for (const auto &child : e.children)
    arguments.push_back(
        evaluate(child, a, b, owners, cursor, selection, formation));
  if (e.kind == Expr::Call || e.kind == Expr::BinaryCall) {
    unsigned owned = 1u << owners[cursor++];
    for (auto argument : arguments)
      selection &= (argument & owned) != 0;
    return owned;
  }
  if (e.kind == Expr::Zero)
    return 7;
  unsigned intersection = arguments[0] & arguments[1];
  formation &= intersection != 0;
  return e.kind == Expr::Ignored ? 7 : intersection;
}
std::string roles(unsigned mask) {
  std::string result = "@(";
  for (unsigned i = 0; i < 3; ++i)
    if (mask & (1u << i)) {
      if (result.size() > 2)
        result += ',';
      result += std::string(1, char('P' + i));
    }
  return result + ")";
}
void oracle() {
  const Expr a{Expr::A, {}}, b{Expr::B, {}}, fa{Expr::Call, {a}},
      fb{Expr::Call, {b}};
  std::vector<Expr> cases{fa,
                          {Expr::Product, {fa, b}},
                          {Expr::Zero, {fa}},
                          {Expr::Ignored, {fa, b}},
                          {Expr::FirstPair, {fa, b}},
                          {Expr::Zero, {{Expr::Product, {fa, b}}}},
                          {Expr::BinaryCall, {fa, b}},
                          {Expr::Zero, {{Expr::BinaryCall, {fa, b}}}},
                          {Expr::Product, {fa, fb}},
                          {Expr::BinaryCall, {fa, fb}},
                          {Expr::Product, {{Expr::Zero, {fa}}, fb}},
                          {Expr::Call, {{Expr::Ignored, {fa, b}}}}};
  unsigned tested = 0, formationOnly = 0;
  for (const auto &expression : cases)
    for (unsigned aMask = 1; aMask < 8; ++aMask)
      for (unsigned bMask = 1; bMask < 8; ++bMask)
        for (unsigned demand : {0u, 1u, 2u, 3u, 4u}) {
          std::vector<std::vector<unsigned>> solutions;
          std::vector<bool> formed;
          std::vector<unsigned> assignment(count(expression));
          std::function<void(unsigned)> enumerate = [&](unsigned i) {
            if (i < assignment.size()) {
              for (unsigned role = 0; role < 3; ++role) {
                assignment[i] = role;
                enumerate(i + 1);
              }
              return;
            }
            bool k = true, f = true;
            unsigned cursor = 0;
            unsigned result =
                evaluate(expression, aMask, bMask, assignment, cursor, k, f);
            k &= result != 0 && (result & demand) == demand;
            if (k) {
              solutions.push_back(assignment);
              formed.push_back(f);
            }
          };
          enumerate(0);
          if (solutions.size() > 1 && llvm::count(formed, true) == 1)
            ++formationOnly;
          auto text = "protocol Run roles(P,Q,R)(a:F" + roles(aMask) + ",b:F" +
                      roles(bMask) + ")->(){let result" +
                      (demand ? roles(demand) : "") + "=" + source(expression) +
                      ";return ();}";
          auto checked = analyzeText(text);
          bool accepted = solutions.size() == 1 && formed.front();
          require(bool(checked) == accepted,
                  "oracle admission differs: " + text);
          if (checked) {
            const Declaration *protocol = nullptr;
            for (const auto &decl : checked->declarations())
              if (decl.name == "Run")
                protocol = &decl;
            require(protocol &&
                        callOwners(*protocol->body) == solutions.front(),
                    "oracle selected owners differ: " + text);
          } else {
            auto diagnostic = toString(checked.takeError());
            auto expected =
                solutions.size() > 1 ? "source.owner" : "source.roles";
            require(StringRef(diagnostic).contains(expected),
                    "oracle diagnostic differs: " + diagnostic + "\n" + text);
          }
          ++tested;
        }
  require(formationOnly > 0, "oracle omitted ambiguous K with unique K-and-F");
  outs() << tested << " source constraint cases; " << formationOnly
         << " distinguish selection from formation\n";
}
} // namespace
int main() {
  examples();
  oracle();
}
