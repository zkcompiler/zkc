#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "support/SourceProject.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Translation/Language.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
ClosedEntry example() {
  auto captured = take(capture(sourceProject(ZKC_SOURCE_PROJECT)));
  return take(zkc::test::closeProtocolDeployment(
      take(analyze(captured).checkedProject()), "example::Demo"));
}
} // namespace
int main() {
  Cases cases;
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run("module example emits closure-free ordinary helpers", [&] {
    auto entry = example();
    auto original = take(prepareOriginal(entry));
    require(original.bytes().contains("protocol.local_call") &&
                original.bytes().contains("runtime.site"),
            "ordinary call boundaries missing");
    require(!original.bytes().contains("scoped.invoke") &&
                !original.bytes().contains("closure"),
            "runtime closure emitted");
    take(compileEntry(original));
    take(compileEntry(original, {false, false}));
    auto bytes = take(emitOriginal(entry, context));
    auto parsed = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
    require(bool(parsed), "original did not parse");
    take(compareOriginal(entry, *parsed));
  });
  cases.run("native same-typed capture swap refuses source comparison", [&] {
    auto entry = example();
    auto bytes = take(emitOriginal(entry, context));
    auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
    require(bool(module), "original did not parse");
    bool changed = false;
    module->walk([&](mlir::Operation *op) {
      if (changed || op->getName().getStringRef() != "func.call" ||
          !op->hasAttr("runtime.site"))
        return;
      for (unsigned i = 1; i < op->getNumOperands(); ++i)
        for (unsigned j = i + 1; j < op->getNumOperands(); ++j)
          if (op->getOperand(i) != op->getOperand(j) &&
              op->getOperand(i).getType() == op->getOperand(j).getType()) {
            auto value = op->getOperand(i);
            op->setOperand(i, op->getOperand(j));
            op->setOperand(j, value);
            changed = true;
            return;
          }
    });
    require(changed, "no comparable captures");
    refuses(compareOriginal(entry, *module), "source.correspondence");
  });
  cases.run(
      "closed domain and callback environments compile through nested loops",
      [&] {
        auto captured = take(capture({{"sample", R"(module sample;
domain Fr=field("koala-bear");
type Vector<F:Field>=builtin("vector",F);
domain fn elements<F:Field>(xs:Vector<F>)->domain<F>=domain("elements");
fn ignore(rows:domain<Fr>,fallback:Fr)->Fr{return fallback;}
fn iterate(x:Fr,n:index,rows:domain<Fr>,body:fn(Fr)->Fr effects(stop))->Fr effects(stop){
 let mut state=x;for _ in 0..n {state=ignore(rows,body(state));}return state;
}
fn outer(xs:Vector<Fr>,x:Fr,n:index)->Fr effects(stop){
 let rows=elements(xs);return iterate(x,n,rows,fn(y)=>ignore(rows,y+x));
}
protocol Run roles(P)(xs:Vector<Fr>@P,x:Fr@P,n:index@P)->(r:Fr@P){return outer(xs,x,n);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
)",
                                       "domains.zkc"}}));
        auto entry = take(zkc::test::closeProtocolDeployment(
            take(analyze(captured).checkedProject()), "sample::Demo"));
        auto original = take(prepareOriginal(entry));
        require(original.bytes().contains("exec.range"),
                "loop was erased from original IR");
        take(compileEntry(original));
        take(compileEntry(original, {false, false}));
      });
  for (bool mathematical : {false, true})
    cases.run(
        mathematical ? "total finite fold source pipeline"
                     : "ordered finite fold source pipeline",
        [&] {
          std::string mode = mathematical ? "math " : "";
          std::string effects = mathematical ? "" : " effects(stop)";
          auto captured = take(capture(
              {{"sample",
                std::string(R"(module sample;
domain Fr=field("koala-bear");
type Vector<F:Field>=builtin("vector",F);
domain fn elements<F:Field>(xs:Vector<F>)->domain<F>=domain("elements");
)") + mode +
                    "fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:"
                    "domain<I>,initial:S,step:" +
                    mode + "fn(S,item:I)->S" + effects +
                    " where item_from(item, rows))->S" + effects +
                    "=finite(\"" + (mathematical ? "math.fold" : "local.fold") +
                    R"(");
protocol Run roles(P)(xs:Vector<Fr>@P,x:Fr@P,offset:Fr@P)->(r:Fr@P){return fold(elements(xs),x,fn(state, item)=>state+item+offset);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
)",
                "fold.zkc"}}));
          auto entry = take(zkc::test::closeProtocolDeployment(
              take(analyze(captured).checkedProject()), "sample::Demo"));
          auto original = take(prepareOriginal(entry));
          require(original.bytes().contains("data.domain_elements") &&
                      original.bytes().contains(
                          mathematical ? "data.finite_fold" : "exec.fold"),
                  "finite structure missing from source original");
          take(compileEntry(original));
          take(compileEntry(original, {false, false}));
        });
  cases.run("packed sequence collection source pipeline", [&] {
    auto captured = take(capture({{"sample", R"(module sample;
domain Fr=field("koala-bear");
type Sequence<T:Type+Copy+Drop>=builtin("sequence",T);
struct Row {pub value:Fr,pub enabled:bool}
domain fn elements<T:Type+Copy+Drop>(xs:Sequence<T>)->domain<T>=domain("elements");
fn collect<I:Type+Copy+Drop,B:Type+Copy+Drop>(rows:domain<I>,body:fn(item:I)->B effects(stop) where item_from(item, rows))->Sequence<B> effects(stop)=finite("local.collect.sequence");
protocol Run roles(P)(xs:Sequence<Row>@P)->(r:Sequence<Row>@P){return collect(elements(xs),fn(row)=>row);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
)",
                                   "collect.zkc"}}));
    auto entry = take(zkc::test::closeProtocolDeployment(
        take(analyze(captured).checkedProject()), "sample::Demo"));
    auto original = take(prepareOriginal(entry));
    require(original.bytes().contains("exec.collect") &&
                original.bytes().contains("exec.match"),
            "packed sequence item adapter missing");
    take(compileEntry(original));
    take(compileEntry(original, {false, false}));
  });
  for (bool mathematical : {false, true})
    for (unsigned count : {0u, 1u, 3u})
      cases.run(
          "fixed array finite pipeline " + std::to_string(mathematical) + "/" +
              std::to_string(count),
          [&] {
            std::string mode = mathematical ? "math " : "";
            std::string effects = mathematical ? "" : " effects(stop)";
            auto captured = take(capture(
                {{"sample",
                  std::string(R"(module sample;
domain Fr=field("koala-bear");
struct Row {pub a:Fr,pub b:Fr}
domain fn array<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<T>=domain("source_array");
)") + mode +
                      "fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:"
                      "domain<I>,initial:S,step:" +
                      mode + "fn(S,item:I)->S" + effects +
                      " where item_from(item, rows))->S" + effects +
                      "=finite(\"" +
                      (mathematical ? "math.fold" : "local.fold") + R"(");
protocol Run roles(P)(xs:[Row;)" +
                      std::to_string(count) +
                      R"(]@P,shift:Fr@P)->(r:Fr@P){return fold(array(xs),0,fn(state, row)=>state+row.a+row.b+shift);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
)",
                  "array.zkc"}}));
            auto entry = take(zkc::test::closeProtocolDeployment(
                take(analyze(captured).checkedProject()), "sample::Demo"));
            auto original = take(prepareOriginal(entry));
            require(original.bytes().contains("data.sequence_empty"),
                    "source array adapter missing");
            take(compileEntry(original));
            take(compileEntry(original, {false, false}));
            auto bytes = take(emitOriginal(entry, context));
            auto module =
                mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
            require(bool(module), "array original did not parse");
            take(compareOriginal(entry, *module));
            if (!mathematical && count == 3) {
              for (unsigned mutation = 0; mutation < 4; ++mutation) {
                auto altered =
                    mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
                bool changed = false;
                altered->walk([&](mlir::Operation *op) {
                  if (changed)
                    return;
                  auto name = op->getName().getStringRef();
                  if (name == "exec.compute") {
                    auto callee =
                        op->getAttrOfType<mlir::FlatSymbolRefAttr>("callee");
                    if (!callee || !callee.getValue().contains("_array_"))
                      return;
                    if (mutation == 0)
                      op->setAttr("callee", mlir::FlatSymbolRefAttr::get(
                                                &context, "wrong_array"));
                    else if (mutation == 1)
                      op->setAttr(
                          "callee",
                          mlir::FlatSymbolRefAttr::get(
                              &context,
                              op->getParentOp()
                                  ->getAttrOfType<mlir::StringAttr>("sym_name")
                                  .getValue()));
                    else if (mutation == 2)
                      op->setAttr("site", mlir::StringAttr::get(
                                              &context, "wrong_array_site"));
                    else {
                      auto first = op->getOperand(1);
                      op->setOperand(1, op->getOperand(3));
                      op->setOperand(3, first);
                    }
                    changed = true;
                  }
                });
                require(changed, "array computation mutation target missing");
                auto refused = compareOriginal(entry, *altered);
                require(!refused, "corrupted array adapter accepted");
                auto diagnostic = toString(refused.takeError());
                require(diagnostic.find("source.correspondence") !=
                                std::string::npos ||
                            diagnostic.find("target.admission") !=
                                std::string::npos,
                        "unexpected array adapter refusal");
              }
            }
            if (count) {
              bool changed = false;
              module->walk([&](mlir::Operation *op) {
                if (!changed && op->getName().getStringRef() == "data.make" &&
                    op->getNumOperands() == 2) {
                  auto first = op->getOperand(0);
                  op->setOperand(0, op->getOperand(1));
                  op->setOperand(1, first);
                  changed = true;
                }
              });
              require(changed, "array mutation target missing");
              refuses(compareOriginal(entry, *module), "source.correspondence");
            }
          });
  for (
      const std::string &work : {
          R"(math fn work(xs:Vector<Fr>)->Fr{return total(indices(xs),0,fn(state, i)=>state+at(xs,i));}
protocol Run roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return work(xs);})",
          R"(math fn inner(xs:Vector<Fr>,ys:Vector<Fr>)->Fr where equal_extent(xs,ys){return total(indices(xs),0,fn(state, i)=>state+at(ys,i));}
math fn work(xs:Vector<Fr>)->Fr{return inner(xs,xs);}
protocol Run roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return work(xs);})",
          R"(struct Row {pub value:Fr,pub enabled:bool}
domain fn positions(xs:Sequence<Row>)->domain<index>=domain("indices");
math fn get(xs:Sequence<Row>,i:index)->Row where in_bounds(i,xs){return intrinsic<Sequence<Row>>("container.at",xs,i);}
math fn work(xs:Sequence<Row>)->Fr{return total(positions(xs),0,fn(state, i)=>{let row=get(xs,i);state+row.value});}
protocol Run roles(P)(xs:Sequence<Row>@P)->(r:Fr@P){return work(xs);})",
          R"(domain fn coords(xs:Matrix<Fr>)->domain<(index,index)>=domain("matrix.coordinates.row_major");
math fn work(xs:Matrix<Fr>)->Fr{return total(coords(xs),0,fn(state, (i,j))=>state+intrinsic<Matrix<Fr>>("matrix.at",xs,i,j));}
protocol Run roles(P)(xs:Matrix<Fr>@P)->(r:Fr@P){return work(xs);})"})
    cases.run("total bounds compile " + work.substr(0, 70), [&] {
      auto captured = take(capture({{"sample", std::string(R"(module sample;
domain Fr=field("koala-bear");
type Vector<F:Field>=builtin("vector",F);
type Matrix<F:Field>=builtin("matrix",F);
type Sequence<T:Type+Copy+Drop>=builtin("sequence",T);
domain fn indices(xs:Vector<Fr>)->domain<index>=domain("indices");
math fn at(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return intrinsic<Vector<Fr>>("container.at",xs,i);}
math fn total<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item, rows))->S=finite("math.fold");
)") + work + "entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }",
                                     "bounds.zkc"}}));
      auto entry = take(zkc::test::closeProtocolDeployment(
          take(analyze(captured).checkedProject()), "sample::Demo"));
      auto original = take(prepareOriginal(entry));
      require(original.bytes().contains("data.preconditions"),
              "missing native data requirements");
      take(compileEntry(original));
      take(compileEntry(original, {false, false}));
      auto module =
          mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
      require(bool(module), "bound original did not parse");
      bool changed = false;
      module->walk([&](mlir::Operation *op) {
        if (!changed && op->hasAttr("data.preconditions")) {
          op->removeAttr("data.preconditions");
          changed = true;
        }
      });
      require(changed, "missing bound mutation target");
      auto comparison = compareOriginal(entry, *module);
      require(!comparison, "removed native bound accepted");
      consumeError(comparison.takeError());
    });
  cases.run("fixed array extents survive total zip and collection", [&] {
    auto captured = take(capture({{"sample", R"(module sample;
domain Fr=field("bls12-381.fr");
type Array<F:Field,N:nat>=builtin("field_array",F,N);
domain fn array<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<T>=domain("source_array");
domain fn zip<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:domain<A>,b:domain<B>)->domain<(A,B)>=domain("zip");
math fn collect<I:Type+Copy+Drop,N:nat>(rows:domain<I>,body:math fn(item:I)->Fr where item_from(item, rows))->Array<Fr,N>=finite("math.collect.field_array");
math fn work(xs:[Fr;2],ys:[Fr;2])->Array<Fr,2>{return collect(zip(array(xs),array(ys)),fn((x,y))=>x+y);}
protocol Run roles(P)(xs:[Fr;2]@P,ys:[Fr;2]@P)->(r:Array<Fr,2>@P){return work(xs,ys);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
)",
                                   "fixed.zkc"}}));
    auto entry = take(zkc::test::closeProtocolDeployment(
        take(analyze(captured).checkedProject()), "sample::Demo"));
    auto original = take(prepareOriginal(entry));
    take(compileEntry(original));
    take(compileEntry(original, {false, false}));
  });
  cases.run("total index expressions and range filters", [&] {
    auto captured = take(capture({{"sample", R"(module sample;
domain Fr=field("koala-bear");
domain fn range(lower:index,upper:index)->domain<index>=domain("range");
math fn filtered<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,keep:math fn(item:I)->bool where item_from(item, rows),step:math fn(S,item:I)->S where item_from(item, rows))->S=finite("math.fold_where");
math fn threshold<N:nat>()->index{return index<N>();}
math fn work(n:index)->(Fr,bool,index){
 let result:Fr=filtered(range(0,n),0,fn(i)=>intrinsic("index.less",i,threshold<2>()),fn(state, item)=>state+1);
 return(result,intrinsic("index.equal",n,2),18446744073709551615);
}
protocol Run roles(P)(n:index@P)->(r:(Fr,bool,index)@P){return work(n);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
)",
                                   "indices.zkc"}}));
    auto entry = take(zkc::test::closeProtocolDeployment(
        take(analyze(captured).checkedProject()), "sample::Demo"));
    auto original = take(prepareOriginal(entry));
    require(original.bytes().contains("data.index_less") &&
                original.bytes().contains("data.index_equal"),
            "total index identities missing");
    take(compileEntry(original));
    take(compileEntry(original, {false, false}));
    auto bytes = take(emitOriginal(entry, context));
    auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
    require(bool(module), "total index original did not parse");
    bool changed = false;
    module->walk([&](mlir::Operation *op) {
      if (!changed && op->getName().getStringRef() == "data.index") {
        op->setAttr("value", mlir::IntegerAttr::get(
                                 mlir::IntegerType::get(
                                     &context, 64, mlir::IntegerType::Unsigned),
                                 3));
        changed = true;
      }
    });
    require(changed, "index mutation target missing");
    refuses(compareOriginal(entry, *module), "source.correspondence");
  });
  for (unsigned mutation = 0; mutation < 3; ++mutation)
    cases.run(
        "finite native adapter corruption " + std::to_string(mutation), [&] {
          auto captured = take(capture({{"sample", R"(module sample;
domain Fr=field("koala-bear");
type Vector<F:Field>=builtin("vector",F);
domain fn elements<F:Field>(xs:Vector<F>)->domain<F>=domain("elements");
domain fn choose<F:Field>(left:Vector<F>,right:Vector<F>)->domain<F>{let a=elements(left);let b=elements(right);return a;}
fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold");
protocol Run roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P,offset:Fr@P)->(r:Fr@P){return fold(choose(xs,ys),0,fn(state, item)=>state*10+item+offset);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
)",
                                         "mutation.zkc"}}));
          auto entry = take(zkc::test::closeProtocolDeployment(
              take(analyze(captured).checkedProject()), "sample::Demo"));
          auto bytes = take(emitOriginal(entry, context));
          auto module =
              mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
          require(bool(module), "finite original did not parse");
          take(compareOriginal(entry, *module));
          bool changed = false;
          mlir::Operation *extra = nullptr;
          module->walk([&](mlir::Operation *op) {
            if (changed)
              return;
            if (mutation == 0 && op->getName().getStringRef() == "func.call" &&
                op->getAttrOfType<mlir::StringAttr>("runtime.site") ==
                    mlir::StringAttr::get(&context, "body")) {
              auto value = op->getOperand(1);
              op->setOperand(1, op->getOperand(2));
              op->setOperand(2, value);
              changed = true;
            } else if (mutation == 1 &&
                       op->getName().getStringRef() == "data.domain_yield") {
              op->setOperand(0, op->getPrevNode()->getResult(0));
              changed = true;
            } else if (mutation == 2 &&
                       op->getName().getStringRef() == "data.domain") {
              extra = op;
              changed = true;
            }
          });
          if (extra) {
            auto *copy = extra->clone();
            copy->setAttr("sym_name",
                          mlir::StringAttr::get(&context, "finite_unused"));
            extra->getBlock()->push_back(copy);
          }
          require(changed, "no finite native mutation target");
          refuses(compareOriginal(entry, *module), "source.correspondence");
        });
  return cases.result();
}
