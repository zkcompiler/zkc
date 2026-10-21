#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
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
domain fn zip<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:domain<A>,b:domain<B>)->domain<(A,B)>=domain("zip");
fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold");
fn sum<I:Type+Copy+Drop,F:Field>(rows:domain<I>,term:fn(item:I)->F effects(stop) where item_from(item, rows))->F effects(stop){return fold(rows,0,fn(state, item)=>state+term(item));}
reduction ∑=sum;
math fn square<F:Field>(x:F)->F{return x*x;}
fn f<F:Field>(xs:Vector<F>,ys:Vector<F>,a:F,b:F)->F{
  return ∑ (x,_) in zip(xs,ys),{let shifted=x+b;square(shifted)+a};
}
protocol Demo roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P,a:Fr@P,b:Fr@P,
                      ext:Vector<Ext>@P,c:Ext@P,d:Ext@P)->(r:Fr@P,s:Ext@P){
  return(r=f(xs,ys,a,b),s=f(ext,ext,c,d));
}
entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
)";
ClosedEntry close(StringRef text = source) {
  auto input = take(capture({{"m", text.str(), "reduction-ir.zkc"}}));
  return take(zkc::test::closeProtocolDeployment(
      take(analyze(input).checkedProject()), "m::Run"));
}
} // namespace
int main() {
  Cases cases;
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run(
      "generic finite binders close at two independent scalar fields", [&] {
        auto entry = close();
        auto original = take(prepareOriginal(entry));
        require(original.bytes().contains("data.domain_zip"),
                "strict domain was not retained");
        take(compileEntry(original));
        take(compileEntry(original, {false, false}));
        auto bytes = take(emitOriginal(entry, context));
        auto parsed = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
        require(bool(parsed), "emission did not parse");
        take(compareOriginal(entry, *parsed));
      });
  for (const auto &mutation : {"domain-order", "capture-order",
                               "scalar-operand", "call-site", "helper-target"})
    cases.run(Twine("source/native comparison rejects ") + mutation, [&] {
      auto entry = close();
      auto bytes = take(emitOriginal(entry, context));
      auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
      require(bool(module), "emission did not parse");
      bool changed = false;
      module->walk([&](mlir::Operation *op) {
        if (changed)
          return;
        auto name = op->getName().getStringRef();
        StringRef change = mutation;
        if (change == "domain-order" && name == "data.domain_zip") {
          auto value = op->getOperand(0);
          op->setOperand(0, op->getOperand(1));
          op->setOperand(1, value);
          changed = true;
        } else if (change == "capture-order" && name == "local.apply" &&
                   op->getNumOperands() == 4) {
          auto value = op->getOperand(2);
          op->setOperand(2, op->getOperand(3));
          op->setOperand(3, value);
          changed = true;
        } else if (change == "scalar-operand" &&
                   name == "algebra.field_multiply") {
          mlir::OperationState state(op->getLoc(), "algebra.field_add");
          state.addTypes(op->getResultTypes());
          state.addOperands(op->getOperands());
          auto replacement = mlir::Operation::create(state);
          op->getBlock()->getOperations().insert(op->getIterator(),
                                                 replacement);
          op->getResult(0).replaceAllUsesWith(replacement->getResult(0));
          op->erase();
          changed = true;
        } else if (change == "call-site" && name == "local.apply") {
          op->setAttr("site", mlir::StringAttr::get(&context, "s999"));
          changed = true;
        } else if (change == "helper-target" && name == "local.apply") {
          op->setAttr("callee",
                      mlir::FlatSymbolRefAttr::get(&context, "missing"));
          changed = true;
        }
      });
      require(changed, "missing finite mutation target");
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
      fn collect<I:Type+Copy+Drop,F:Field>(rows:domain<I>,term:fn(item:I)->F effects(stop) where item_from(item, rows))->Vector<F> effects(stop)=finite("local.collect.vector");
      fn f(xs:Vector<Fr>)->Fr{let terms=collect(xs,fn(x)=>x);return custom(terms);}
      protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return(r=f(xs));}entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); })");
    auto original = take(prepareOriginal(entry));
    require(original.bytes().contains("local.stop") &&
                original.bytes().contains("local.finite_collect"),
            "custom stop was replaced");
    take(compileEntry(original));
  });
  cases.run("binders in local branches and loops preserve lexical captures", [&] {
    auto entry = close(
        R"(module m;domain Fr=field("koala-bear");type Vector<F:Field>=builtin("vector",F);
      domain fn zip<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:domain<A>,b:domain<B>)->domain<(A,B)>=domain("zip");
fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold");
fn sum<I:Type+Copy+Drop,F:Field>(rows:domain<I>,term:fn(item:I)->F effects(stop) where item_from(item, rows))->F effects(stop){return fold(rows,0,fn(state, item)=>state+term(item));}
      reduction ∑=sum;
      fn f(xs:Vector<Fr>,a:Fr,b:bool,n:index)->Fr{
        let mut acc=a;
        for _ in 0..n {acc=acc+(∑ x in xs,x*a);}
        return if b {∑ x in xs,(x+a)} else {acc};
      }
      protocol Demo roles(P)(xs:Vector<Fr>@P,a:Fr@P,b:bool@P,n:index@P)->(r:Fr@P){return(r=f(xs,a,b,n));}entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); })");
    take(compileEntry(take(prepareOriginal(entry))));
  });
  return cases.result();
}
