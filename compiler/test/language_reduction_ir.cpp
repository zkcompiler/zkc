#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Translation/Language.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
const std::string source = R"(module m;
domain Fr=field("koala-bear");
domain Ext=field("koala-bear.ext8-binomial3");
type Vector<F:Field>=builtin("vector",F);
fn sum<F:Field>(xs:Vector<F>)->F=primitive("vector.sum");
reduction ∑=sum;
math fn square<F:Field>(x:F)->F{return x*x;}
fn f<F:Field>(xs:Vector<F>,ys:Vector<F>,a:F,b:F)->F{
  return ∑[(x,_) in zip(xs,ys)]{let shifted=x+b;square(shifted)+a};
}
protocol Demo roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P,a:Fr@P,b:Fr@P,
                      ext:Vector<Ext>@P,c:Ext@P,d:Ext@P)->(r:Fr@P,s:Ext@P){
  return(r=f(xs,ys,a,b),s=f(ext,ext,c,d));
}
run Run=Demo;
)";
ClosedEntry close(StringRef text = source) {
  auto input = take(capture({{"m", text.str(), "reduction-ir.zkc"}}));
  return take(closeEntry(take(analyze(input).checkedProject()), "m::Run"));
}
} // namespace
int main() {
  Cases cases;
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run(
      "generated generic helpers close at two independent scalar fields", [&] {
        auto entry = close();
        auto original = take(prepareOriginal(entry));
        require(original.bytes().contains("algebra.map_realize"),
                "map was not retained");
        take(compileEntry(original));
        take(compileEntry(original, {false, false}));
        auto bytes = take(emitOriginal(entry, context));
        auto parsed = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
        require(bool(parsed), "emission did not parse");
        take(compareOriginal(entry, *parsed));
      });
  for (const auto &mutation :
       {"capture-order", "row-order", "scalar-operand", "mask", "map-site",
        "reducer-site", "reducer-operand", "helper-target"})
    cases.run(Twine("source/native comparison rejects ") + mutation, [&] {
      auto entry = close();
      auto bytes = take(emitOriginal(entry, context));
      auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
      require(bool(module), "emission did not parse");
      mlir::Operation *map = nullptr, *sum = nullptr, *formula = nullptr,
                      *recipe = nullptr;
      module->walk([&](mlir::Operation *op) {
        auto name = op->getName().getStringRef();
        if (name == "local.apply" && !map)
          map = op;
        if (name == "algebra.exec.vector_sum" && !sum)
          sum = op;
        if (name == "algebra.field_multiply" && !formula)
          formula = op;
        if (name == "algebra.map_realize" && !recipe)
          recipe = op;
      });
      require(map && sum && formula && recipe, "missing reduction structure");
      StringRef change = mutation;
      if (change == "capture-order" || change == "row-order") {
        unsigned left = change == "row-order" ? 0 : 2;
        auto operand = map->getOperand(left);
        map->setOperand(left, map->getOperand(left + 1));
        map->setOperand(left + 1, operand);
      } else if (change == "scalar-operand") {
        // Change the scalar operation while retaining its operands and types.
        mlir::OperationState state(formula->getLoc(), "algebra.field_add");
        state.addTypes(formula->getResultTypes());
        state.addOperands(formula->getOperands());
        auto changed = mlir::Operation::create(state);
        formula->getBlock()->getOperations().insert(formula->getIterator(),
                                                    changed);
        formula->getResult(0).replaceAllUsesWith(changed->getResult(0));
        formula->erase();
      } else if (change == "mask") {
        recipe->setAttr("rowwise", mlir::DenseBoolArrayAttr::get(
                                       &context, {true, false, false, false}));
      } else if (change == "map-site")
        map->setAttr("site", mlir::StringAttr::get(&context, "s999"));
      else if (change == "reducer-site")
        sum->setAttr("site", mlir::StringAttr::get(&context, "s999"));
      else if (change == "reducer-operand")
        sum->setOperand(0, map->getOperand(0));
      else if (change == "helper-target")
        recipe->setAttr("helper",
                        mlir::FlatSymbolRefAttr::get(&context, "missing"));
      auto result = compareOriginal(entry, *module);
      require(!result, "mutated original accepted");
      auto error = toString(result.takeError());
      require(error.find("source.correspondence") != std::string::npos ||
                  error.find("target.admission") != std::string::npos,
              "unexpected mutation failure: " + error);
    });
  cases.run("custom stopping reducer stays an ordinary local call", [&] {
    auto entry = close(
        R"(module m;domain Fr=field("koala-bear");type Vector<F:Field>=builtin("vector",F);
      fn custom(xs:Vector<Fr>)->Fr{stop "reject";}
      fn f(xs:Vector<Fr>)->Fr{return reduce custom[x in xs]{x};}
      protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return(r=f(xs));}run Run=Demo;)");
    auto original = take(prepareOriginal(entry));
    require(original.bytes().contains("local.stop") &&
                original.bytes().contains("algebra.map_realize"),
            "custom stop was replaced");
    take(compileEntry(original));
  });
  cases.run("binders in local branches and loops preserve lexical captures", [&] {
    auto entry = close(
        R"(module m;domain Fr=field("koala-bear");type Vector<F:Field>=builtin("vector",F);
      fn sum<F:Field>(xs:Vector<F>)->F=primitive("vector.sum");
      fn f(xs:Vector<Fr>,a:Fr,b:bool,n:index)->Fr{
        let mut acc=a;
        for _ in 0..n {acc=acc+reduce sum[x in xs]{x*a};}
        return if b {reduce sum[x in xs]{x+a}} else {acc};
      }
      protocol Demo roles(P)(xs:Vector<Fr>@P,a:Fr@P,b:bool@P,n:index@P)->(r:Fr@P){return(r=f(xs,a,b,n));}run Run=Demo;)");
    take(compileEntry(take(prepareOriginal(entry))));
  });
  return cases.result();
}
