// The closed source body, not the emitted text, decides which arena a kernel
// evaluates: the digest written into the original MLIR must be the identity of
// the captured asset the checked body closed over.
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/LanguagePackage.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Language.h"
#include "llvm/Support/JSON.h"
using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
AssetBuffer product() {
  using namespace zkc::ring;
  auto arena = take(
      Expression::create({{"koala-bear"}, {"koala-bear"}},
                         {Node::slot(0), Node::slot(1), Node::mul(0, 1)}, {2}));
  return {"product", "ring-json", zkc::printJson(arena.encode()), "/missing"};
}
const char *const source = R"(module sample;
domain F = field("koala-bear");
domain Product = ring(asset product);
type Vector<T: Field> = builtin("vector", T);
fn evaluate<T: Field, A: Ring>(v: Vector<T>) -> Vector<T> {
  return kernel<T>("ring.point", v; A);
}
protocol Run<A: Ring> roles(E)(v: Vector<F>@E)->(r: Vector<F>@E) {
  let r @E = evaluate<F,A>(v);
  return (r=r);
}
run Demo = Run<Product>;
)";
} // namespace
int main() {
  zkc::test::Cases cases;
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto checked = [] {
    auto captured =
        take(capture({{"sample", source, "sample.zkc"}}, {product()}, {}));
    auto project = take(analyze(captured).checkedProject());
    return take(prepareOriginal(take(closeEntry(project, "sample::Demo"))));
  };
  cases.run(
      "a changed digest in the original MLIR is not the checked source", [&] {
        auto original = checked();
        auto identity = take(Asset::read(product())).identity().str();
        require(StringRef(original.bytes()).contains(identity),
                "original MLIR does not carry the arena identity");
        auto module =
            mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
        require(bool(module), "invalid mathematical original");
        take(compareOriginal(original.entry(), *module));
        unsigned changed = 0;
        module->walk([&](mlir::Operation *op) {
          auto parameters = op->getAttrOfType<mlir::ArrayAttr>("parameters");
          if (!parameters || parameters.size() != 1)
            return;
          auto value = dyn_cast<mlir::StringAttr>(parameters[0]);
          if (!value || value.getValue() != identity)
            return;
          std::string other = identity;
          other[0] = other[0] == '0' ? '1' : '0';
          op->setAttr("parameters",
                      mlir::ArrayAttr::get(
                          &context, {mlir::StringAttr::get(&context, other)}));
          ++changed;
        });
        require(changed == 1, "expected exactly one ring kernel");
        require(succeeded(mlir::verify(*module)),
                "digest mutation is ill-formed");
        refuses(compareOriginal(original.entry(), *module),
                "source.correspondence");
      });
  cases.run("the package carries the arena the closed body names", [&] {
    auto compiled = take(compileEntry(checked()));
    auto package = take(packageEntry(compiled));
    auto value = take(json::parse(package.bytes()));
    auto *assets = value.getAsObject()->getArray("assets");
    require(assets && assets->size() == 1, "package asset count differs");
    auto *entry = (*assets)[0].getAsArray();
    require(
        entry && entry->size() == 2 &&
            (*entry)[0].getAsString() ==
                take(Asset::read(product())).identity() &&
            take(json::parse(*(*entry)[1].getAsString())) ==
                take(zkc::ring::readExpressionText(product().bytes)).encode(),
        "packaged arena differs from the captured asset");
  });
  return cases.result();
}
