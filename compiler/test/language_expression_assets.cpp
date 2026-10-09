#include "support/NativeCases.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Language/Project.h"
#include "zkc/Support/Json.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
AssetBuffer product(StringRef name = "product",
                    StringRef field = "koala-bear") {
  using namespace zkc::ring;
  auto arena = take(
      Expression::create({{field.str()}, {field.str()}},
                         {Node::slot(0), Node::slot(1), Node::mul(0, 1)}, {2}));
  return {name.str(), "ring-json", zkc::printJson(arena.encode()), "/missing"};
}
std::string source(StringRef field = "koala-bear",
                   StringRef reference = "asset product",
                   StringRef width = "asset(\"product\", \"inputs\")",
                   StringRef degree = "asset(\"product\", \"degree\")") {
  return (Twine(R"(module sample;
    domain F = field(")") +
          field + R"(");
    type Vector<T: Field> = builtin("vector", T);
    fn evaluate<T: Field>(v: Vector<T>) -> Vector<T> {
      return kernel<T>("ring.point", v; )" +
          reference + R"();
    }
    protocol Run<W: nat, D: nat> roles(E)(v: Vector<F>@E)->(r:Vector<F>@E) {
      local E let r = evaluate(v);
      return (r=r);
    }
    entry Demo = Run<)" +
          width + "," + degree + ">;")
      .str();
}
Expected<ClosedEntry> close(StringRef text, std::vector<AssetBuffer> assets,
                            const Limits &limits = {}) {
  auto captured = capture({{"sample", text.str(), {}}}, std::move(assets), {});
  if (!captured)
    return captured.takeError();
  auto checked = analyze(*captured, limits).checkedProject();
  if (!checked)
    return checked.takeError();
  return closeEntry(*checked, "sample::Demo", limits);
}
std::string replace(std::string text, StringRef before, StringRef after) {
  auto pos = text.find(before.str());
  require(pos != std::string::npos, "test substitution missing");
  text.replace(pos, before.size(), after.str());
  return text;
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("named expression and derived facts survive closure", [] {
    auto selected = take(close(source(), {product(), product("unused")}));
    require(selected.assets().size() == 1,
            "evaluator closure is not deduplicated");
    require(selected.assets()[0].ring(), "ring contents were lost");
    require(
        selected.protocol().staticArguments[0].dimension.closedValue() == 2 &&
            selected.protocol().staticArguments[1].dimension.closedValue() == 2,
        "derived input count or unit degree differs");
    auto weighted = take(close(source("koala-bear", "asset product",
                                      "asset(\"product\",\"outputs\")",
                                      "asset(\"product\",\"degree\",0,3)"),
                               {product()}));
    require(
        weighted.protocol().staticArguments[0].dimension.closedValue() == 1 &&
            weighted.protocol().staticArguments[1].dimension.closedValue() == 3,
        "weighted degree or output count differs");
  });
  cases.run("a base expression admits an extension carrier", [] {
    auto derived = replace(source(), "domain F = field(\"koala-bear\")",
                           "type F = asset(\"product\",\"input-field\",0)");
    take(close(derived, {product()}));
    take(close(source("koala-bear.ext8-binomial3"), {product()}));
    refuses(close(source(), {product("product", "koala-bear.ext8-binomial3")}),
            "source.asset-carrier");
    refuses(close(source("bls12-381.fr"), {product()}), "source.asset-carrier");
  });
  cases.run("named and literal references require captured contents", [] {
    refuses(close(source(), {}), "source.asset-reference");
    refuses(close(source("koala-bear", "asset absent"), {product()}),
            "source.asset-reference");
    std::string digest = take(Asset::read(product())).identity().str();
    take(close(source("koala-bear", "\"" + digest + "\""), {product()}));
    auto missing = source("koala-bear", "\"" + std::string(64, '0') + "\"");
    refuses(close(missing, {product()}), "source.asset-reference");
  });
  cases.run("unreachable definitions do not demand evaluator contents", [] {
    auto text = source("koala-bear", "\"" + std::string(64, '0') + "\"");
    text = replace(text, "local E let r = evaluate(v);", "let r = v;");
    require(take(close(text, {product()})).assets().empty(),
            "unused evaluator retained");
  });
  cases.run("both branches are checked before selecting runtime inputs", [] {
    auto text = source("koala-bear", "\"" + std::string(64, '0') + "\"");
    text = replace(text, "return kernel<T>(\"ring.point\", v;",
                   "return if true capture(v) { yield v; } else { yield "
                   "kernel<T>(\"ring.point\", v;");
    text = replace(text, "\");\n    }", "\"); };\n    }");
    refuses(close(text, {product()}), "source.asset-reference");
  });
  cases.run("static properties reject unknown and ill-shaped queries", [] {
    for (StringRef query :
         {"asset(\"absent\",\"inputs\")", "asset(\"product\",\"unknown\")",
          "asset(\"product\",\"inputs\",0)", "asset(\"product\",\"degree\",1)",
          "asset(\"product\",\"input-field\",2)",
          "asset(\"product\",\"output-field\")",
          "asset(\"product\",\"degree\",1048577,0)",
          "asset(\"product\",\"degree\",F,0)"})
      refuses(close(source("koala-bear", "asset product", query), {product()}),
              "source.asset-property");
  });
  cases.run("malformed unused ring contents cannot enter a checked project",
            [] {
              auto asset = product();
              asset.bytes = "[]";
              refuses(close(source(), {asset}), "source.asset");
            });
  cases.run("property work is bounded", [] {
    Limits limits;
    limits.work = 10;
    refuses(close(source(), {product()}, limits), "source.limit");
  });
  return cases.result();
}
