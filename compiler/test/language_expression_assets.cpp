#include "support/NativeCases.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Language/Project.h"
#include "zkc/Relation/Bundle.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/MemoryBuffer.h"
#include <functional>
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
using zkc::ring::Node;
AssetBuffer arena(StringRef name, std::vector<std::string> fields,
                  std::vector<Node> nodes, std::vector<uint32_t> outputs) {
  std::vector<zkc::ring::Input> inputs;
  for (auto &field : fields)
    inputs.push_back({std::move(field)});
  auto value = take(zkc::ring::Expression::create(
      std::move(inputs), std::move(nodes), std::move(outputs)));
  return {name.str(), "ring-json", zkc::printJson(value.encode()), "/missing"};
}
/// x*y: two inputs, one output of degree two.
AssetBuffer product(StringRef name = "product",
                    StringRef field = "koala-bear") {
  return arena(name, {field.str(), field.str()},
               {Node::slot(0), Node::slot(1), Node::mul(0, 1)}, {2});
}
/// x*y*z: three inputs, one output of degree three.
AssetBuffer cubic(StringRef name = "product") {
  return arena(name, {"koala-bear", "koala-bear", "koala-bear"},
               {Node::slot(0), Node::slot(1), Node::slot(2), Node::mul(0, 1),
                Node::mul(3, 2)},
               {4});
}
/// x*y and x+y: two outputs.
AssetBuffer twoOutputs(StringRef name = "product") {
  return arena(name, {"koala-bear", "koala-bear"},
               {Node::slot(0), Node::slot(1), Node::mul(0, 1), Node::add(0, 1)},
               {2, 3});
}
/// The constant one: no inputs, one output of degree zero.
AssetBuffer constant(StringRef name = "product") {
  return arena(name, {}, {Node::literal("koala-bear", "1")}, {0});
}
/// x squared twenty-one times: degree 2^21, above the arena degree limit, so
/// its unit degree fact is saturated.
AssetBuffer saturated(StringRef name = "product") {
  std::vector<Node> nodes{Node::slot(0)};
  for (unsigned i = 0; i < 21; ++i)
    nodes.push_back(Node::mul(i, i));
  return arena(name, {"koala-bear"}, std::move(nodes), {21});
}
/// One cyclic witness column whose single assertion is the cell itself.
AssetBuffer bundle(StringRef name = "recurrence") {
  using namespace zkc::relation;
  BundleTable table{"main",
                    false,
                    {BundleHeightAuthority::Fixed, 2, 2, false},
                    BundleReadModel::Cyclic,
                    {{"w", BundleAuthority::Witness, "koala-bear", 1}},
                    take(zkc::ring::Expression::create({{"koala-bear"}},
                                                       {Node::slot(0)}, {0})),
                    {BundleInput::read(0, 0, 0)},
                    {{0, {}}},
                    {}};
  std::vector<BundleTable> tables;
  tables.push_back(std::move(table));
  auto value = take(Bundle::create({}, {}, std::move(tables)));
  return {name.str(), "relation-bundle-json", zkc::printJson(value.encode()),
          "/missing"};
}
/// A generic consumer: the width, the degree bound and the kernel parameter
/// all come from the arena term, never from the author.
const char *const prelude = R"(module sample;
domain F = field("koala-bear");
domain Product = ring(asset product);
type Vector<T: Field> = builtin("vector", T);
fn evaluate<T: Field, A: Ring>(v: Vector<T>) -> Vector<T> {
  return kernel<T>("ring.point", v; A);
}
fn has_length<T: Field, N: nat>(v: Vector<T>) -> bool {
  return kernel<T>("vector.length", v) == index<N>();
}
fn shape<T: Field, A: Ring>(v: Vector<T>) -> bool
    where 1 <= A::Inputs, 1 <= A::Outputs, A::Outputs <= 1 {
  let wide = has_length<T, A::Inputs>(v);
  let r = evaluate<T, A>(v);
  let bounded = has_length<T, A::Degree + 1>(r);
  return wide == bounded;
}
)";
std::string
source(StringRef body = "", StringRef entry = "Run<Product>",
       StringRef protocolBound =
           "where 1 <= A::Inputs, 1 <= A::Outputs, A::Outputs <= 1") {
  return (Twine(prelude) + body +
          "protocol Run<A: Ring> roles(E)(v: Vector<F>@E)->(ok: bool@E) " +
          protocolBound + " {\n  let ok @E = shape<F,A>(v);\n" +
          "  return (ok=ok);\n}\nentry Demo = " + entry + ";\n")
      .str();
}
Expected<CheckedProject> check(StringRef text, std::vector<AssetBuffer> assets,
                               const Limits &limits = {}) {
  auto captured = capture({{"sample", text.str(), {}}}, std::move(assets), {});
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
Expected<ClosedEntry> close(StringRef text, std::vector<AssetBuffer> assets,
                            const Limits &limits = {},
                            StringRef entry = "sample::Demo") {
  auto checked = check(text, std::move(assets), limits);
  if (!checked)
    return checked.takeError();
  return closeEntry(*checked, entry, limits);
}
std::string rewrite(std::string text, StringRef before, StringRef after) {
  auto pos = text.find(before.str());
  require(pos != std::string::npos, "test substitution missing");
  text.replace(pos, before.size(), after.str());
  return text;
}
/// Every closed `index.constant` parameter, in body order.
std::vector<std::string> indexConstants(const ClosedEntry &entry) {
  std::vector<std::string> result;
  std::function<void(const Body &)> visit = [&](const Body &body) {
    for (const auto &op : body.operations) {
      if (const auto *primitive = std::get_if<LocalPrimitive>(&op.action)) {
        if (primitive->contract == "index.constant")
          result.push_back(primitive->parameters.front());
      } else if (const auto *control = std::get_if<LocalControl>(&op.action)) {
        for (const auto &region : control->regions)
          visit(*region);
      } else if (const auto *repeat = std::get_if<ProtocolRepeat>(&op.action))
        visit(*repeat->region);
    }
  };
  for (const auto &decl : entry.declarations())
    if (decl.body && decl.origin)
      visit(*decl.body);
  return result;
}
/// The closed ring kernels and their written identities.
std::vector<std::pair<std::string, std::string>>
ringReferences(const ClosedEntry &entry) {
  std::vector<std::pair<std::string, std::string>> result;
  for (const auto &decl : entry.declarations())
    if (decl.body && decl.origin)
      for (const auto &op : decl.body->operations)
        if (const auto *primitive = std::get_if<LocalPrimitive>(&op.action))
          for (const auto &reference : primitive->assetReferences) {
            require(reference.term.kind == Type::Kind::Asset &&
                        !reference.term.symbolic &&
                        reference.term.domain ==
                            primitive->parameters[reference.position],
                    "closed asset reference and parameter disagree");
            result.emplace_back(primitive->contract, reference.term.domain);
          }
  return result;
}
std::string file(const char *path) {
  auto buffer = MemoryBuffer::getFile(path);
  require(bool(buffer), Twine("fixture missing: ") + path);
  return (*buffer)->getBuffer().str();
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("the same generic consumer derives width and degree per arena", [] {
    auto quadratic = take(close(source(), {product()}));
    require(indexConstants(quadratic) == std::vector<std::string>({"2", "3"}),
            "x*y did not derive width 2 and degree bound 3");
    auto identity = take(Asset::read(product())).identity().str();
    require(ringReferences(quadratic) ==
                std::vector<std::pair<std::string, std::string>>(
                    {{"ring.point", identity}}),
            "kernel parameter is not the arena identity");
    require(quadratic.assets().size() == 1 &&
                quadratic.assets()[0].identity() == identity &&
                quadratic.assets()[0].ring(),
            "closed arena was not retained");
    auto three = take(close(source(), {cubic()}));
    require(indexConstants(three) == std::vector<std::string>({"3", "4"}),
            "x*y*z did not derive width 3 and degree bound 4");
    require(three.protocol().symbol != quadratic.protocol().symbol,
            "arena identity is not part of the instance key");
  });
  cases.run("asset domains require the named captured asset and its kind", [] {
    refuses(check(source(), {}), "source.asset-reference");
    refuses(
        check(rewrite(source(), "ring(asset product)", "ring(asset absent)"),
              {product()}),
        "source.asset-reference");
    refuses(
        check(rewrite(source(), "ring(asset product)", "bundle(asset product)"),
              {product()}),
        "source.asset-reference");
    refuses(check(rewrite(source(), "ring(asset product)",
                          "ring(asset recurrence)"),
                  {product(), bundle()}),
            "source.asset-reference");
    refuses(
        check(rewrite(source(), "ring(asset product)", "field(asset product)"),
              {product()}),
        "source.syntax");
    auto twice = source("domain Again = ring(asset product);\n"
                        "protocol Other roles(E)(v: Vector<F>@E)->(ok: bool@E)"
                        " { let ok @E = shape<F,Again>(v);"
                        " return (ok=ok); }\nentry Second = Other;\n");
    auto first = take(close(twice, {product()}));
    auto second = take(close(twice, {product()}, {}, "sample::Second"));
    require(indexConstants(first) == indexConstants(second) &&
                ringReferences(first) == ringReferences(second),
            "two domains over one captured asset differ");
  });
  cases.run("the field carrier is checked only once the entry closes", [] {
    auto extension = product("product", "koala-bear.ext8-binomial3");
    take(check(source(), {extension}));
    refuses(close(source(), {extension}), "source.asset-carrier");
    refuses(close(rewrite(source(), "field(\"koala-bear\")",
                          "field(\"bls12-381.fr\")"),
                  {product()}),
            "source.asset-carrier");
    take(close(rewrite(source(), "field(\"koala-bear\")",
                       "field(\"koala-bear.ext8-binomial3\")"),
               {product()}));
    auto branches = rewrite(source(), "return kernel<T>(\"ring.point\", v; A);",
                            "return if true { v } else {"
                            " kernel<T>(\"ring.point\", v; A) };");
    refuses(close(branches, {extension}), "source.asset-carrier");
  });
  cases.run("projections are the derived facts of the asset sort", [] {
    refuses(check(rewrite(source(), "A::Inputs", "A::Columns"), {product()}),
            "source.asset-projection");
    refuses(check(source("", "Run<Product>", "where 1 <= Product::Columns"),
                  {product()}),
            "source.asset-projection");
    refuses(
        check(source("", "Run<Product>", "where 1 <= Product::Inputs::Bits"),
              {product()}),
        "source.type");
    auto bundled =
        source("domain Recurrence = bundle(asset recurrence);\n"
               "fn tables<B: Bundle>() -> index {"
               " return index<B::Tables>(); }\n"
               "fn fixed() -> index {"
               " return index<Recurrence::Tables +"
               " Recurrence::Publics + Recurrence::Channels>(); }\n");
    refuses(check(bundled, {product(), bundle()}), "source.asset-projection");
    auto closedBundle = rewrite(bundled, "index<B::Tables>()", "index<1>()");
    auto entry = take(close(closedBundle, {product(), bundle()}));
    require(indexConstants(entry) == std::vector<std::string>({"2", "3"}),
            "closed bundle facts changed the ring consumer");
    refuses(check(rewrite(closedBundle, "Recurrence::Publics",
                          "Recurrence::Degree"),
                  {product(), bundle()}),
            "source.asset-projection");
    refuses(check(rewrite(source(), "A::Degree + 1", "pow2(A::Degree)"),
                  {product()}),
            "source.natural");
  });
  cases.run("a saturated degree refuses only when it is requested", [] {
    refuses(close(source(), {saturated()}), "source.asset-projection");
    refuses(check(source("", "Run<Product>", "where 1 <= Product::Degree"),
                  {saturated()}),
            "source.asset-projection");
    auto widthOnly = rewrite(source(), "A::Degree + 1", "A::Outputs");
    require(indexConstants(take(close(widthOnly, {saturated()}))) ==
                std::vector<std::string>({"1"}),
            "unrequested degree fact changed the closed body");
  });
  cases.run("body-only static expressions close with explicit overflow", [] {
    auto wide =
        rewrite(source(), "A::Degree + 1", "A::Degree * 18446744073709551615");
    take(check(wide, {product()}));
    refuses(close(wide, {product()}), "source.natural");
  });
  cases.run("no static argument is inferred through a projection", [] {
    auto inferred =
        source("fn count<A: Ring>(x: [bool; A::Inputs]) -> bool {"
               " return true; }\n"
               "fn use_count(x: bool) -> bool { return count([x, x]); }\n");
    refuses(check(inferred, {product()}), "source.inference");
    auto explicitly =
        rewrite(inferred, "count([x, x])", "count<Product>([x, x])");
    take(check(explicitly, {product()}));
  });
  cases.run("asset terms never form runtime values", [] {
    for (auto [before, after, code] :
         std::vector<std::tuple<StringRef, StringRef, StringRef>>{
             {"(v: Vector<F>@E)", "(v: Product@E)", "source.type"},
             {"(v: Vector<F>@E)", "(v: (Product, bool)@E)", "source.type"},
             {"(v: Vector<F>@E)", "(v: [Product; 2]@E)", "source.type"},
             {"(v: Vector<F>@E)", "(v: Vector<Product>@E)", "source.generic"},
             {"(v: Vector<F>@E)", "(v: builtin(\"vector\", Product)@E)",
              "source.builtin"},
             {"where 1 <= A::Inputs, 1 <= A::Outputs, A::Outputs <= 1 {\n  "
              "let",
              "where Copy(A) {\n  let", "source.permission"},
             {"protocol Run<A: Ring>", "protocol Run<A: Ring + Copy>",
              "source.permission"},
             {"fn has_length", "struct Holder { x: Product }\nfn has_length",
              "source.type"},
             {"fn has_length",
              "interface Shaped { type A: Ring; }\nfn has_length",
              "source.type"}})
      refuses(check(rewrite(source(), before, after), {product()}), code);
  });
  cases.run("aliases, components and entries specialize on the asset", [] {
    auto aliased =
        source("type Row<A: Ring> = [bool; A::Inputs];\n"
               "fn second(x: Row<Product>) -> bool { return x[1]; }\n"
               "protocol Rows roles(E)(x: Row<Product>@E)->(ok: bool@E)"
               " { let ok @E = second(x); return (ok=ok); }\n"
               "entry Alias = Rows;\n");
    auto rows = take(close(aliased, {product()}, {}, "sample::Alias"));
    require(rows.protocol().inputs[0].type.kind == Type::Kind::Array &&
                rows.protocol().inputs[0].type.dimension.closedValue() == 2,
            "alias did not close its projected length");
    auto component = source(
        "interface Eval<T: Field> { fn eval(v: Vector<T>) -> Vector<T>; }\n"
        "component Fixed<T: Field, A: Ring>: Eval<T> {\n"
        "  fn eval(v: Vector<T>) -> Vector<T> {"
        " return kernel<T>(\"ring.point\", v; A); }\n}\n"
        "fn through<T: Field, E: Eval<T>>(v: Vector<T>) -> Vector<T> {"
        " return E::eval(v); }\n"
        "protocol Dispatch roles(E)(v: Vector<F>@E)->(r: Vector<F>@E)"
        " { let r @E = through<F, Fixed<F, Product>>(v);"
        " return (r=r); }\nentry Selected = Dispatch;\n");
    auto dispatched =
        take(close(component, {product()}, {}, "sample::Selected"));
    require(ringReferences(dispatched).size() == 1 &&
                dispatched.assets().size() == 1,
            "component member did not close its asset parameter");
    auto generic = source("domain Cube = ring(asset cube);\n"
                          "entry Other = Run<Cube>;\n");
    auto first = take(close(generic, {product(), cubic("cube")}));
    auto other =
        take(close(generic, {product(), cubic("cube")}, {}, "sample::Other"));
    require(first.protocol().symbol != other.protocol().symbol &&
                indexConstants(other) == std::vector<std::string>({"3", "4"}),
            "entries over different arenas share an instance");
  });
  cases.run("kernel asset parameters are terms of the accepted sort", [] {
    auto digest = take(Asset::read(product())).identity().str();
    for (std::string parameter :
         {"\"" + digest + "\"", "\"" + std::string(64, '0') + "\"",
          std::string(), std::string("Recurrence"), std::string("F"),
          std::string("A, A"), std::string("\"0\", A")}) {
      auto text = rewrite(
          source("domain Recurrence = bundle(asset recurrence);\n"),
          "kernel<T>(\"ring.point\", v; A)",
          "kernel<T>(\"ring.point\", v" +
              (parameter.empty() ? std::string() : "; " + parameter) + ")");
      refuses(check(text, {product(), bundle()}), "source.asset-reference");
    }
    refuses(check(source("fn len<T: Field, A: Ring>(v: Vector<T>) -> index {"
                         " return kernel<T>(\"vector.length\", v; A); }\n"),
                  {product()}),
            "source.asset-reference");
    refuses(check(rewrite(source(), "kernel<T>(\"vector.length\", v)",
                          "kernel<T>(\"vector.length\", v; Product)"),
                  {product()}),
            "source.asset-reference");
  });
  cases.run(
      "projected bounds are inferred or checked against an explicit contract",
      [] {
        take(check(source("", "Run<Product>", ""), {product()}));
        refuses(close(source("", "Run<Product>", ""), {constant()}),
                "source.bound");
        refuses(check(source("", "Run<Product>", "where ()"), {product()}),
                "source.bound");
        refuses(check(source("", "Run<Product>",
                             "where 1 <= A::Outputs, A::Outputs <= 1"),
                      {product()}),
                "source.bound");
        take(check(
            source("", "Run<Product>",
                   "where 1 <= A::Outputs, A::Outputs <= 1, 2 <= A::Inputs"),
            {product()}));
        refuses(close(source(), {twoOutputs()}), "source.bound");
        refuses(close(source(), {constant()}), "source.bound");
      });
  cases.run("the Sumcheck library rejects arenas outside its premise", [] {
    auto library = file(ZKC_SUMCHECK_LIBRARY);
    auto client = file(ZKC_EXPRESSION_SUMCHECK_PROJECT "/main.zkc");
    auto compile = [&](AssetBuffer asset) -> Expected<ClosedEntry> {
      auto captured = capture({{"example", client, "main.zkc"},
                               {"expression_sumcheck", library, "library.zkc"}},
                              {std::move(asset)}, {});
      if (!captured)
        return captured.takeError();
      auto checked = analyze(*captured).checkedProject();
      if (!checked)
        return checked.takeError();
      return closeEntry(*checked, "example::Proof");
    };
    AssetBuffer shipped{
        "product", "ring-json",
        file(ZKC_EXPRESSION_SUMCHECK_PROJECT "/product.ring.json"),
        "product.ring.json"};
    require(indexConstants(take(compile(shipped))) ==
                std::vector<std::string>({"2", "3", "2"}),
            "shipped arena did not derive width 2 and degree bound 3");
    require(indexConstants(take(compile(cubic()))) ==
                std::vector<std::string>({"3", "4", "3"}),
            "cubic arena did not derive width 3 and degree bound 4");
    refuses(compile(twoOutputs()), "source.bound");
    refuses(compile(constant()), "source.bound");
    take(compile(product("product", "koala-bear.ext8-binomial3")));
    refuses(compile(product("product", "bls12-381.fr")),
            "source.asset-carrier");
  });
  cases.run("unreachable definitions retain no assets", [] {
    auto text =
        rewrite(source("fn trivial<T: Field>(v: Vector<T>) -> bool {"
                       " return has_length<T, 1>(v); }\n"),
                "let ok @E = shape<F,A>(v);", "let ok @E = trivial<F>(v);");
    require(take(close(text, {product()})).assets().empty(),
            "unused evaluator retained");
  });
  cases.run("malformed unused ring contents cannot enter a checked project",
            [] {
              auto asset = product();
              asset.bytes = "[]";
              refuses(check(source(), {asset}), "source.asset");
            });
  cases.run("projection work is bounded", [] {
    Limits limits;
    limits.work = 10;
    refuses(close(source(), {product()}, limits), "source.limit");
  });
  return cases.result();
}
