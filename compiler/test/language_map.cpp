#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Language/Project.h"
#include <string>

using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
constexpr StringLiteral prelude = R"(module m;
domain Fr = field("koala-bear");
domain Ext = field("koala-bear.ext8-binomial3");
type Vector<F: Field> = builtin("vector", F);
math fn square<F: Field>(x: F) -> F { return x * x; }
math fn affine<F: Field>(low: F, high: F, r: F) -> F {
  return low + (high - low) * r;
}
math fn residual<F: Field>(a: F, b: F, unused: F, s: F) -> F {
  return (s + 1) * (square(a) - b) + s;
}
)";
constexpr StringLiteral program = R"(
fn fold<F: Field>(low: Vector<F>, high: Vector<F>, r: F) -> Vector<F> {
  return map affine(each low, each high, r);
}
math fn lerp<F: Field>(a: F, b: F, r: F) -> F { return a * r + b; }
fn combine(a: Vector<Fr>, b: Vector<Fr>, c: Vector<Fr>, s: Fr) -> Vector<Fr> {
  let shifted = map lerp(each a, each b, s);
  return map residual<Fr>(each shifted, each b, each c, s);
}
fn repeat(a: Vector<Fr>, s: Fr, n: index) -> Vector<Fr> {
  let mut acc = a;
  for _ in 0..n {
    acc = map affine<_>(each acc, each a, s);
  }
  return acc;
}
protocol Demo roles(P)(a: Vector<Fr> @P, b: Vector<Fr> @P, c: Vector<Fr> @P,
                       s: Fr @P, n: index @P)
    -> (folded: Vector<Fr> @P, combined: Vector<Fr> @P,
        repeated: Vector<Fr> @P) {
  let folded = fold(a, b, s);
  let combined = combine(a, b, c, s);
  let repeated = repeat(a, s, n);
  return (folded = folded, combined = combined, repeated = repeated);
}
entry Run = Demo;
)";
Expected<CheckedProject> check(StringRef body) {
  auto captured = capture({{"m", (prelude + body).str(), "map.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
Expected<CheckedOriginal> original(StringRef body) {
  auto checked = check(body);
  if (!checked)
    return checked.takeError();
  auto closed = closeEntry(*checked, "m::Run");
  if (!closed)
    return closed.takeError();
  return prepareOriginal(*closed);
}
unsigned occurrences(StringRef text, StringRef needle) {
  unsigned result = 0;
  for (auto at = text.find(needle); at != StringRef::npos;
       at = text.find(needle, at + needle.size()))
    ++result;
  return result;
}
} // namespace

int main() {
  Cases cases;
  cases.run("generic inference, helper calls and local wrappers", [] {
    auto checked = take(original(program));
    auto bytes = checked.bytes();
    // fold and repeat share one helper instance and row mask.
    require(occurrences(bytes, "\"algebra.map_realize\"") == 3,
            "expected one declaration per helper instance and row mask");
    require(bytes.contains("rowwise = array<i1: true, true, false>") &&
                bytes.contains("rowwise = array<i1: true, true, true, false>"),
            "row masks differ from the written each markers");
    require(occurrences(bytes, "\"local.apply\"") == 4,
            "map calls are not ordered");
    require(!bytes.contains("vector_add") && !bytes.contains("vector_mul"),
            "original contains realized vector arithmetic");
    take(compileEntry(checked));
    take(compileEntry(checked, {false, false}));
  });
  cases.run("compilation is deterministic", [] {
    auto first = take(original(program));
    auto second = take(original(program));
    require(first.bytes() == second.bytes(), "original bytes differ");
    require(take(compileEntry(first)).bytes() ==
                take(compileEntry(second)).bytes(),
            "artifact bytes differ");
  });
  cases.run("emitted original is compared with source", [] {
    auto checked = take(original(program));
    auto closed = take(closeEntry(take(check(program)), "m::Run"));
    auto admit = [&](const std::string &text, StringRef code) {
      refuses(admitOriginal(closed, text, checked.interfaceJson()), code);
    };
    auto edit = [&](StringRef from, StringRef to) {
      auto text = checked.bytes().str();
      auto at = text.find(from.str());
      require(at != std::string::npos, "missing original edit: " + from);
      text.replace(at, from.size(), to.str());
      return text;
    };
    // Formation refuses a mask that disagrees with the declared signature.
    admit(edit("rowwise = array<i1: true, true, false>",
               "rowwise = array<i1: true, true, true>"),
          "algebra-map-signature");
    // Only local.apply may name a preparation-time declaration.
    admit(edit("\"local.apply\"", "\"local.call\""), "interactive-symbol-kind");
    // Two well-formed maps share a signature; exchanging their helpers is a
    // different formula and must not correspond to the source.
    SmallVector<StringRef> lines;
    checked.bytes().split(lines, '\n');
    SmallVector<StringRef> helpers;
    for (auto line : lines)
      if (line.contains("\"algebra.map_realize\"") &&
          line.contains("rowwise = array<i1: true, true, false>")) {
        auto helper = line.substr(line.find("helper = @"));
        helpers.push_back(helper.substr(0, helper.find(',')));
      }
    require(helpers.size() == 2 && helpers[0] != helpers[1],
            "expected two same-shaped maps");
    auto text = checked.bytes().str();
    auto first = text.find(helpers[0].str()),
         second = text.find(helpers[1].str());
    text.replace(second, helpers[1].size(), helpers[0].str());
    text.replace(first, helpers[0].size(), helpers[1].str());
    admit(text, "source.correspondence");
  });

  auto refusal = [&](StringRef label, StringRef body, StringRef code) {
    cases.run(label, [&] { refuses(check(body), code); });
  };
  refusal("missing each on a vector argument",
          "fn f(a: Vector<Fr>, b: Vector<Fr>, s: Fr) -> Vector<Fr> {\n"
          "  return map affine(each a, b, s);\n}\n",
          "source.map");
  refusal("each on a scalar argument",
          "fn f(a: Vector<Fr>, b: Vector<Fr>, s: Fr) -> Vector<Fr> {\n"
          "  return map affine(each a, each b, each s);\n}\n",
          "source.map");
  refusal("no each argument",
          "fn f(a: Fr, b: Fr, s: Fr) -> Vector<Fr> {\n"
          "  return map affine(a, b, s);\n}\n",
          "source.map");
  refusal("argument count",
          "fn f(a: Vector<Fr>, s: Fr) -> Vector<Fr> {\n"
          "  return map affine(each a, s);\n}\n",
          "source.map");
  refusal("ordered helper",
          "fn g(x: Fr) -> Fr { return x; }\n"
          "fn f(a: Vector<Fr>) -> Vector<Fr> { return map g(each a); }\n",
          "source.map");
  refusal("interface member requires a defined helper",
          "interface Step<F: Field> { math fn apply(x: F) -> F; }\n"
          "component One<F: Field>: Step<F> {\n"
          "  math fn apply(x: F) -> F { return x + 1; }\n}\n"
          "fn f<C: Step<Fr>>(a: Vector<Fr>) -> Vector<Fr> {\n"
          "  return map C::apply(each a);\n}\n",
          "source.map");
  refusal("mixed fields",
          "math fn mix(x: Fr, y: Ext) -> Fr { return x; }\n"
          "fn f(a: Vector<Fr>, e: Ext) -> Vector<Fr> {\n"
          "  return map mix(each a, e);\n}\n",
          "source.map");
  refusal("non-field result",
          "math fn test(x: Fr) -> bool { return x == x; }\n"
          "fn f(a: Vector<Fr>) -> Vector<Fr> {\n"
          "  let tested = map test(each a);\n  return a;\n}\n",
          "source.map");
  refusal("map in a protocol body",
          "protocol P roles(A)(a: Vector<Fr> @A) -> (r: Vector<Fr> @A) {\n"
          "  let r = map square(each a);\n  return (r = r);\n}\n",
          "source.mode");
  refusal("map in a math fn",
          "math fn h(a: Vector<Fr>) -> Vector<Fr> {\n"
          "  return map square(each a);\n}\n",
          "source.mode");
  refusal("index scalar argument",
          "fn f(a: Vector<Fr>, b: Vector<Fr>, n: index) -> Vector<Fr> {\n"
          "  return map affine(each a, each b, n);\n}\n",
          "source.map");
  refusal("boolean scalar argument",
          "fn f(a: Vector<Fr>, b: Vector<Fr>, go: bool) -> Vector<Fr> {\n"
          "  return map affine(each a, each b, go);\n}\n",
          "source.map");
  // A scalar of another field is an ordinary type conflict of the inferred F.
  refusal("scalar of another field",
          "fn f(a: Vector<Fr>, b: Vector<Fr>, e: Ext) -> Vector<Fr> {\n"
          "  return map affine(each a, each b, e);\n}\n",
          "source.type");
  refusal("vector of another field",
          "fn f(a: Vector<Fr>, b: Vector<Ext>, s: Fr) -> Vector<Fr> {\n"
          "  return map affine<Fr>(each a, each b, s);\n}\n",
          "source.type");
  refusal("unbound map argument",
          "fn f(a: Vector<Fr>) -> Vector<Fr> {\n"
          "  return map affine(each a, each missing, a);\n}\n",
          "source.name");
  refusal("map is reserved", "fn f(map: Fr) -> Fr { return map; }\n",
          "source.name");
  refusal("each is reserved", "fn each(x: Fr) -> Fr { return x; }\n",
          "source.name");
  refusal("each outside map",
          "fn f(a: Vector<Fr>) -> Vector<Fr> { return each a; }\n",
          "source.name");
  cases.run("unsupported scalar operation in a mapped helper", [] {
    refuses(original("math fn bad<F: Field>(x: F, y: F) -> F {\n"
                     "  let unused = x == y;\n  return x;\n}\n"
                     "fn f(a: Vector<Fr>, b: Vector<Fr>) -> Vector<Fr> {\n"
                     "  return map bad(each a, each b);\n}\n"
                     "protocol Demo roles(P)(a: Vector<Fr> @P, b: Vector<Fr> "
                     "@P) -> (r: Vector<Fr> @P) {\n"
                     "  let r = f(a, b);\n  return (r = r);\n}\n"
                     "entry Run = Demo;\n"),
            "algebra-map-formula");
  });
  return cases.result();
}
