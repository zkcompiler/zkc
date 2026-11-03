#include "support/NativeCases.h"
#include "zkc/Language/Project.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(StringRef source) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured =
      capture({{"m", source.str(), "record-inference.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
const Body &body(const CheckedProject &project) {
  auto found = llvm::find_if(project.declarations(), [](const auto &decl) {
    return decl.qualifiedName == "m::Run";
  });
  require(found != project.declarations().end() && found->body,
          "missing checked body");
  return *found->body;
}
const ProductPlacement &product(const Value &value) {
  require(value.placement &&
              std::holds_alternative<ProductPlacement>(value.placement->value),
          "missing product placement");
  return std::get<ProductPlacement>(value.placement->value);
}
void constructedMap(const CheckedProject &project, ArrayRef<unsigned> mapping) {
  const auto &checked = body(project);
  bool found = false;
  for (const auto &operation : checked.operations)
    if (std::holds_alternative<Construct>(operation.action)) {
      const auto &value = checked.values[operation.results.front().index];
      if (value.type.domain == "m::Wrap") {
        found = true;
        require(ArrayRef(product(value).arguments) == mapping,
                "constructor inferred the wrong ordered telescope");
      }
    }
  require(found, "missing checked constructor");
}
const char *placedAlias = "type Split roles(P, V) = (index @P, index @V)\n";
const char *leaf = R"(struct Leaf roles(A, B):
    pub first: index @A
    pub second: index @B
)";
const char *oracle = R"(domain F = field("bls12-381.fr")
type K = builtin("oracle.table", F, 16)
type O = builtin("oracle", K)
)";
void captures(const CheckedProject &project,
              ArrayRef<std::vector<unsigned>> components) {
  const auto &checked = body(project);
  const ProtocolRepeat *repeat = nullptr;
  for (const auto &operation : checked.operations)
    if (auto *candidate = std::get_if<ProtocolRepeat>(&operation.action))
      repeat = candidate;
  require(repeat && repeat->captures.size() == components.size(),
          "missing exact repeated captures");
  for (unsigned i = 0; i < components.size(); ++i) {
    const auto &outer = checked.values[repeat->captures[i].index];
    const auto &inner = repeat->region->values[i + 1];
    require(outer.components == components[i] &&
                inner.components == components[i] &&
                inner.placement == outer.placement &&
                inner.oracleHolder == outer.oracleHolder,
            "capture changed projected components or placed identity");
  }
}
} // namespace
int main() {
  Cases cases;
  for (StringRef nested : {"[Split; 0]", "[Split; 2]", "(index, Split)",
                           "[(Split,); 0]", "([Split; 1], index)"}) {
    cases.run("ordinary field rejects " + nested, [&] {
      refuses(check(std::string(placedAlias) +
                    "struct Hidden:\n    pub value: " + nested.str() + "\n"),
              "source.oracle-aggregate");
    });
    cases.run("enum payload rejects " + nested, [&] {
      refuses(check(std::string(placedAlias) + "enum Hidden:\n    Some(" +
                    nested.str() + ")\n"),
              "source.oracle-aggregate");
    });
    cases.run("ordinary generic rejects " + nested, [&] {
      refuses(
          check(std::string(placedAlias) +
                "struct Box<T: Type>:\n    pub value: T\ntype Hidden = Box<" +
                nested.str() + ">\n"),
          "source.oracle-aggregate");
    });
  }
  cases.run("ordinary collection rejects nested alias", [] {
    refuses(check(std::string(placedAlias) +
                  "type Hidden = builtin(\"sequence\", [Split; 0])\n"),
            "source.oracle-aggregate");
  });
  cases.run("associated representation rejects nested alias", [] {
    refuses(check(std::string(placedAlias) +
                  "interface Carrier:\n    type Item: Type\nmodule Concrete: "
                  "Carrier:\n    type Item = [Split; 0]\n"),
            "source.oracle-aggregate");
  });
  cases.run("outer component annotation cannot erase placed alias", [] {
    refuses(check(std::string(placedAlias) +
                  "protocol Run roles(P, V)(s: (Split @P,)) -> bool @P:\n"
                  "    return true\n"),
            "source.placement");
  });
  cases.run(
      "ordinary aliases still nest through empty storage and generics", [] {
        take(check(
            "type Pair = (index, index)\nstruct Box<T: Type>:\n    pub "
            "value: T\nstruct Ordinary:\n    pub empty: [Pair; 0]\n    pub "
            "values: Box<[(Pair,); 2]>\n"));
      });
  for (StringRef binding : {"result = ", "result: Wrap roles(V, P) = "})
    cases.run("placed tuple constructor field " + binding, [&] {
      auto project = take(
          check("struct Wrap roles(A, B):\n    pub pair: (index @A, index @B)\n"
                "protocol Run roles(P, V)(pair: (index @V, index @P)) -> Wrap "
                "roles(V, P):\n    " +
                binding.str() + "Wrap {pair: pair}\n    return result\n"));
      constructedMap(project, {1, 0});
    });
  cases.run("deferred field schema preserves numeric type context", [] {
    auto project = take(
        check("struct Wrap roles(A, B):\n    pub pair: (index @A, index @B)\n"
              "    pub marker: index @A\nprotocol Run roles(P, V)(x: index @P, "
              "y: index @V) -> Wrap roles(P, V):\n"
              "    result = Wrap {pair: (x, y), marker: 7}\n"
              "    return result\n"));
    constructedMap(project, {0, 1});
  });
  cases.run("nested structural constructor retains actual field evidence", [] {
    auto project = take(check(
        "struct Wrap roles(A, B):\n    pub pairs: [(index @A, index @B); 2]\n"
        "protocol Run roles(P, V)(pair: (index @V, index @P)) -> Wrap "
        "roles(V, P):\n    result = Wrap {pairs: [pair, pair]}\n"
        "    return result\n"));
    constructedMap(project, {1, 0});
  });
  cases.run("constructor preserves ordinary generic helper inference", [] {
    auto project = take(check(
        "def keep<T: Type>(x: T) -> T:\n    return x\n"
        "struct Wrap<T: Type> roles(A, B):\n    pub pair: (T @A, T @B)\n"
        "protocol Run roles(P, V)(pair: (index @V, index @P)) -> Wrap<index> "
        "roles(V, P):\n    result = Wrap<index> "
        "{pair: (keep(pair.0), keep(pair.1))}\n    return result\n"));
    constructedMap(project, {1, 0});
    require(
        body(project).values[body(project).results[0].index].type.arguments ==
            std::vector<Type>{Type(Type::Kind::Index)},
        "placement inference changed the ordinary static argument");
  });
  cases.run("ordinary helper still rejects placed tuple", [] {
    refuses(
        check("def keep(s: (index, index)) -> (index, index):\n    return s\n"
              "protocol Run roles(P, V)(s: (index @P, index @V)) -> bool @P:\n"
              "    result = keep(s)\n    return true\n"),
        "source.placement");
  });
  cases.run("deferred constructor field cannot bypass ordinary helper", [] {
    refuses(
        check("def keep(s: (index, index)) -> (index, index):\n    return s\n"
              "struct Wrap roles(A, B):\n    pub pair: (index @A, index @B)\n"
              "protocol Run roles(P, V)(s: (index @P, index @V)) -> Wrap "
              "roles(P, V):\n    result = Wrap {pair: keep(s)}\n"
              "    return result\n"),
        "source.placement");
  });
  for (StringRef extent : {"0", "2"})
    cases.run("reversed nominal map through array extent " + extent, [&] {
      auto project = take(check(
          std::string(leaf) +
          "struct Wrap roles(A, B):\n    pub items: [Leaf "
          "roles(A, B); " +
          extent.str() + "]\nprotocol Run roles(P, V)(xs: [Leaf roles(V, P); " +
          extent.str() +
          "]) -> Wrap roles(V, P):\n"
          "    result = Wrap {items: xs}\n    return result\n"));
      constructedMap(project, {1, 0});
    });
  cases.run("reversed nominal map through tuple", [] {
    auto project = take(check(
        std::string(leaf) +
        "struct Wrap roles(A, B):\n    pub items: (Leaf roles(A, B), index "
        "@A)\n"
        "protocol Run roles(P, V)(xs: (Leaf roles(V, P), index @V)) -> Wrap "
        "roles(V, P):\n    result = Wrap {items: xs}\n    return result\n"));
    constructedMap(project, {1, 0});
  });
  cases.run("nominal phantom telescope remains ordered", [] {
    auto project = take(check(
        "struct Empty roles(A, B):\nstruct Wrap roles(A, B):\n"
        "    pub items: [Empty roles(A, B); 0]\n"
        "protocol Run roles(P, V)(xs: [Empty roles(V, P); 0]) -> Wrap "
        "roles(V, P):\n    result = Wrap {items: xs}\n    return result\n"));
    constructedMap(project, {1, 0});
  });
  cases.run("inconsistent structural equations refuse", [] {
    refuses(
        check(std::string(leaf) +
              "struct Wrap roles(A, B):\n    pub left: [Leaf roles(A, B); 0]\n"
              "    pub right: (Leaf roles(A, B),)\nprotocol Run roles(P, V)("
              "xs: [Leaf roles(V, P); 0], ys: (Leaf roles(P, V),)) -> bool "
              "@P:\n    result = Wrap {left: xs, right: ys}\n"
              "    return true\n"),
        "source.placement-inference");
  });
  cases.run("receiver sets solve with a separate distinguishing equation", [] {
    auto project = take(check(
        std::string(oracle) +
        "struct Wrap roles(H, A, B):\n    pub word: (O @H -> (A, B), index "
        "@A)\n"
        "protocol Run roles(P, V, W)(xs: (O @P -> (V, W), index @W)) -> Wrap "
        "roles(P, W, V):\n    result = Wrap {word: xs}\n    return result\n"));
    constructedMap(project, {0, 2, 1});
  });
  cases.run("undistinguished receiver permutation stays ambiguous", [] {
    refuses(
        check(
            std::string(oracle) +
            "struct Wrap roles(H, A, B):\n    pub words: [O @H -> (A, B); 0]\n"
            "protocol Run roles(P, V, W)(xs: [O @P -> (V, W); 0]) -> bool "
            "@P:\n    result = Wrap {words: xs}\n    return true\n"),
        "source.placement-inference");
  });
  cases.run("structural data sets solve from leaf equations", [] {
    auto project = take(check(
        "struct Wrap roles(A, B):\n    pub pair: (index @(A, B), index @A)\n"
        "protocol Run roles(P, V)(xs: (index @(P, V), index @V)) -> Wrap "
        "roles(V, P):\n    result = Wrap {pair: xs}\n    return result\n"));
    constructedMap(project, {1, 0});
  });
  cases.run("undistinguished data component permutation stays ambiguous", [] {
    refuses(
        check("struct Wrap roles(A, B):\n    pub items: [index @(A, B); 0]\n"
              "protocol Run roles(P, V)(xs: [index @(P, V); 0]) -> bool @P:\n"
              "    result = Wrap {items: xs}\n    return true\n"),
        "source.placement-inference");
  });
  for (StringRef count : {"0", "1"})
    cases.run("direct field capture with trip count " + count, [&] {
      auto project = take(check(std::string(leaf) +
                                "protocol Run roles(P, V)(s: Leaf roles(P, "
                                "V)) -> index @P:\n    for i in 0.." +
                                count.str() +
                                " roles(P, V):\n        observed = s.first\n"
                                "    return s.first\n"));
      captures(project, {{0}});
    });
  cases.run("nested field captures retain separate role components", [] {
    auto project = take(
        check(std::string(leaf) +
              "struct Wrap roles(A, B):\n    pub inner: Leaf roles(B, A)\n"
              "protocol Run roles(P, V)(s: Wrap roles(P, V)) -> index @V:\n"
              "    for i in 0..1 roles(P, V):\n        first = s.inner.first\n"
              "        second = s.inner.second\n    return s.inner.first\n"));
    captures(project, {{1}, {0}});
  });
  cases.run("two holder record captures each exact oracle family", [] {
    auto project = take(check(
        std::string(oracle) +
        "struct Sources roles(A, B, V):\n    pub left: O @A -> V\n"
        "    pub right: O @B -> V\nprotocol Run roles(P, Q, V)(s: Sources "
        "roles(P, Q, V)) -> O @P -> V:\n    for i in 0..1 roles(P, Q, V):\n"
        "        left = s.left\n        right = s.right\n    return s.left\n"));
    captures(project, {{0, 2}, {1, 2}});
  });
  cases.run("shared ordinary field capture selects only loop components", [] {
    auto project = take(
        check("struct State roles(A, B, C):\n    pub count: index @(A, B)\n"
              "    pub other: index @C\nprotocol Run roles(P, Q, V)(s: State "
              "roles(P, Q, V)) -> index @P:\n    for i in 0..1 roles(P, V):\n"
              "        seen = s.count\n    return s.count\n"));
    captures(project, {{0}});
  });
  cases.run("capture outside the loop roster refuses", [] {
    refuses(check(std::string(leaf) +
                  "protocol Run roles(P, V)(s: Leaf roles(P, V)) -> index @P:\n"
                  "    for i in 0..1 roles(P):\n        observed = s.second\n"
                  "    return s.first\n"),
            "source.roles");
  });
  cases.run("capture cannot gain a sibling field's availability", [] {
    refuses(check(std::string(leaf) +
                  "protocol Run roles(P, V)(s: Leaf roles(P, V)) -> index @P:\n"
                  "    for i in 0..1 roles(P, V):\n"
                  "        observed: index @V = s.first\n"
                  "    return s.first\n"),
            "source.roles");
  });
  cases.run("capture cannot fabricate missing oracle participants", [] {
    refuses(
        check(std::string(oracle) +
              "struct State roles(A, B, V):\n    pub word: O @A -> V\n"
              "    pub other: index @B\nprotocol Run roles(P, Q, V)(s: State "
              "roles(P, Q, V)) -> O @P -> V:\n    for i in 0..1 roles(P, Q):\n"
              "        word = s.word\n    return s.word\n"),
        "source.oracle-role");
  });
  return cases.result();
}
