#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Translation/Language.h"
#include <fstream>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
std::string read(const std::string &path) {
  std::ifstream input(path);
  require(bool(input), "cannot read fixture " + path);
  return std::string(std::istreambuf_iterator<char>(input), {});
}
ClosedEntry example() {
  std::string root = ZKC_SCOPED_ROOT;
  auto captured = take(
      capture({{"example",
                read(root + "/examples/projects/scoped-computations/main.zkc"),
                "main.zkc"},
               {"zkc::computation",
                read(root + "/libraries/zkc/computation.zkc"), "scoped.zkc"},
               {"zkc::vector", read(root + "/libraries/zkc/vector.zkc"),
                "vector.zkc"}}));
  return take(
      closeEntry(take(analyze(captured).checkedProject()), "example::Demo"));
}
} // namespace
int main() {
  Cases cases;
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run("component example emits closure-free ordinary helpers", [&] {
    auto entry = example();
    auto original = take(prepareOriginal(entry));
    require(original.bytes().contains("protocol.local_call") &&
                original.bytes().contains("local.apply"),
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
      if (changed || op->getName().getStringRef() != "local.apply")
        return;
      for (unsigned i = 0; i < op->getNumOperands(); ++i)
        for (unsigned j = i + 1; j < op->getNumOperands(); ++j)
          if (op->getOperand(i).getType() == op->getOperand(j).getType()) {
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
domain fn elements<F:Field>(xs:Vector<F>)->scoped domain<F>=domain("elements");
fn ignore(rows:scoped domain<Fr>,fallback:Fr)->Fr{return fallback;}
fn iterate(x:Fr,n:index,rows:scoped domain<Fr>,body:scoped fn(Fr)->Fr !{stop})->Fr !{stop}{
 let mut state=x;for _ in 0..n {state=ignore(rows,body(state));}return state;
}
fn outer(xs:Vector<Fr>,x:Fr,n:index)->Fr !{stop}{
 let rows=elements(xs);return iterate(x,n,rows,fun y=>ignore(rows,y+x));
}
protocol Run roles(P)(xs:Vector<Fr>@P,x:Fr@P,n:index@P)->(r:Fr@P){return outer(xs,x,n);}run Demo=Run;
)",
                                       "domains.zkc"}}));
        auto entry = take(closeEntry(take(analyze(captured).checkedProject()),
                                     "sample::Demo"));
        auto original = take(prepareOriginal(entry));
        require(original.bytes().contains("local.for"),
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
          std::string effects = mathematical ? "" : " !{stop}";
          auto captured = take(capture(
              {{"sample",
                std::string(R"(module sample;
domain Fr=field("koala-bear");
type Vector<F:Field>=builtin("vector",F);
domain fn elements<F:Field>(xs:Vector<F>)->scoped domain<F>=domain("elements");
)") + mode +
                    "fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:scoped "
                    "domain<I>,initial:S,step:scoped " +
                    mode + "fn(S,I)->S" + effects + " on(rows))->S" + effects +
                    "=finite(\"" + (mathematical ? "math.fold" : "local.fold") +
                    R"(");
protocol Run roles(P)(xs:Vector<Fr>@P,x:Fr@P,offset:Fr@P)->(r:Fr@P){return fold(elements(xs),x,fun state item=>state+item+offset);}run Demo=Run;
)",
                "fold.zkc"}}));
          auto entry = take(closeEntry(take(analyze(captured).checkedProject()),
                                       "sample::Demo"));
          auto original = take(prepareOriginal(entry));
          require(original.bytes().contains("data.domain_elements") &&
                      original.bytes().contains(mathematical
                                                    ? "algebra.finite_fold"
                                                    : "local.finite_fold"),
                  "finite structure missing from source original");
          take(compileEntry(original));
          take(compileEntry(original, {false, false}));
        });
  cases.run("packed sequence collection source pipeline", [&] {
    auto captured = take(capture({{"sample", R"(module sample;
domain Fr=field("koala-bear");
type Sequence<T:Type+Copy+Drop>=builtin("sequence",T);
struct Row {pub value:Fr,pub enabled:bool}
domain fn elements<T:Type+Copy+Drop>(xs:Sequence<T>)->scoped domain<T>=domain("elements");
fn collect<I:Type+Copy+Drop,B:Type+Copy+Drop>(rows:scoped domain<I>,body:scoped fn(I)->B !{stop} on(rows))->Sequence<B> !{stop}=finite("local.collect.sequence");
protocol Run roles(P)(xs:Sequence<Row>@P)->(r:Sequence<Row>@P){return collect(elements(xs),fun row=>row);}run Demo=Run;
)",
                                   "collect.zkc"}}));
    auto entry = take(
        closeEntry(take(analyze(captured).checkedProject()), "sample::Demo"));
    auto original = take(prepareOriginal(entry));
    require(original.bytes().contains("local.finite_collect") &&
                original.bytes().contains("local.match"),
            "packed sequence item adapter missing");
    take(compileEntry(original));
    take(compileEntry(original, {false, false}));
  });
  for (unsigned mutation = 0; mutation < 3; ++mutation)
    cases.run(
        "finite native adapter corruption " + std::to_string(mutation), [&] {
          auto captured = take(capture({{"sample", R"(module sample;
domain Fr=field("koala-bear");
type Vector<F:Field>=builtin("vector",F);
domain fn elements<F:Field>(xs:Vector<F>)->scoped domain<F>=domain("elements");
domain fn choose<F:Field>(left:Vector<F>,right:Vector<F>)->scoped domain<F>{let a=elements(left);let b=elements(right);return a;}
fn fold<I:Type+Copy+Drop,S:Type>(rows:scoped domain<I>,initial:S,step:scoped fn(S,I)->S !{stop} on(rows))->S !{stop}=finite("local.fold");
protocol Run roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P,offset:Fr@P)->(r:Fr@P){return fold(choose(xs,ys),0,fun state item=>state*10+item+offset);}run Demo=Run;
)",
                                         "mutation.zkc"}}));
          auto entry = take(closeEntry(take(analyze(captured).checkedProject()),
                                       "sample::Demo"));
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
            if (mutation == 0 &&
                op->getName().getStringRef() == "local.apply" &&
                op->getAttrOfType<mlir::StringAttr>("site").getValue() ==
                    "body") {
              auto value = op->getOperand(0);
              op->setOperand(0, op->getOperand(1));
              op->setOperand(1, value);
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
