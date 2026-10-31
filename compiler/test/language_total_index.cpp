#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/ProtocolDeployment.h"
#include "support/SourceProject.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Translation/Language.h"

using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
constexpr StringLiteral subject = R"(
module total_index;
use zkc::indices as indices;
math fn words(a:index,b:index)->index {
  let sum = indices::wrapping_add(a,b);
  let difference = indices::wrapping_sub(sum,b);
  let bits = indices::bit_and(difference,a);
  let shifted = indices::logical_shift_right(bits,b);
  return indices::bit_and(bits,shifted);
}
protocol Run roles(P)(a:index@P,b:index@P)->(out:index@P) {
  return(out=words(a,b));
}
entry fn Demo(inputs:Run::Inputs) { return Run::run(inputs); }
)";
constexpr StringLiteral operations[] = {
    "data.index_wrapping_add", "data.index_wrapping_subtract",
    "data.index_bit_and", "data.index_logical_shift_right"};

Expected<CheckedProject> check(StringRef text) {
  auto captured =
      capture({{"m", ("module m;" + text).str(), "total-index.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
} // namespace

int main() {
  Cases cases;
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run(
      "public library emits and exports exact total word mathematics", [&] {
        auto sources = sourceProject(ZKC_SOURCE_PROJECT);
        sources.push_back({"total_index", subject.str(), "total-index.zkc"});
        auto project =
            take(analyze(take(capture(std::move(sources)))).checkedProject());
        auto entry =
            take(closeProtocolDeployment(project, "total_index::Demo"));
        auto original = take(prepareOriginal(entry));
        auto module =
            mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
        require(bool(module), "total index source failed native formation");
        take(compareOriginal(entry, *module));
        auto exported = take(protocol::exportStructuredSource(
            original.bytes(), entry.protocol().symbol, context));
        for (StringRef name : operations)
          require(original.bytes().contains(name), "source lost " + name);
        for (StringRef name : {"index.wrapping_add", "index.wrapping_sub",
                               "index.bit_and", "index.logical_shift_right"})
          require(StringRef(exported.bytes).contains(name),
                  "mathematical export lost " + name);
        take(compileEntry(original));
        take(compileEntry(original, {false, false}));

        for (StringRef name : operations) {
          auto candidate = mlir::parseSourceString<mlir::ModuleOp>(
              original.bytes(), &context);
          bool changed = false;
          candidate->walk([&](mlir::Operation *op) {
            if (!changed && op->getName().getStringRef() == name) {
              require(op->getNumOperands() == 2 &&
                          op->getOperand(0) != op->getOperand(1),
                      "source mutation would not change an operand");
              op->setOperand(1, op->getOperand(0));
              changed = true;
            }
          });
          require(changed && succeeded(mlir::verify(*candidate)),
                  "word operand mutation lost native formation");
          refuses(compareOriginal(entry, *candidate), "source.correspondence");
        }
        auto candidate =
            mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
        bool changed = false;
        candidate->walk([&](data::IndexWrappingAddOp add) {
          if (changed)
            return;
          mlir::OpBuilder builder(add);
          mlir::OperationState state(add.getLoc(),
                                     "data.index_wrapping_subtract");
          state.addOperands(add->getOperands());
          state.addTypes(add->getResultTypes());
          auto *other = builder.create(state);
          add->replaceAllUsesWith(other->getResults());
          add.erase();
          changed = true;
        });
        require(changed && succeeded(mlir::verify(*candidate)),
                "identity mutation lost native formation");
        refuses(compareOriginal(entry, *candidate), "source.correspondence");
      });
  cases.run("intrinsic and primitive signatures preserve index results", [&] {
    take(check(R"(
math fn sum(a:index,b:index)->index=primitive("index.wrapping_add");
math fn difference(a:index,b:index)->index=primitive("index.wrapping_sub");
math fn bits(a:index,b:index)->index=primitive("index.bit_and");
math fn shift(a:index,b:index)->index=primitive("index.logical_shift_right");
math fn direct(a:index,b:index)->index{return intrinsic("index.wrapping_add",a,b);}
)"));
    refuses(
        check(
            R"(math fn bad(a:index,b:index)->bool=primitive("index.wrapping_add");)"),
        "source.primitive");
    refuses(
        check(
            R"(math fn bad(a:bool,b:index)->index=primitive("index.bit_and");)"),
        "source.primitive");
    refuses(
        check(
            R"(math fn bad(a:index,b:index)->index{return intrinsic<1>("index.wrapping_add",a,b);})"),
        "source.intrinsic");
  });
  cases.run(
      "checked arithmetic remains inadmissible as total mathematics", [&] {
        for (StringRef name :
             {"index.add", "index.sub", "index.div", "index.mod"})
          refuses(check(("math fn bad(a:index,b:index)->index=primitive(\"" +
                         name + "\");")
                            .str()),
                  "source.primitive");
        refuses(check(R"(
fn checked(a:index,b:index)->index=primitive("index.add");
math fn hidden(a:index,b:index)->index{return checked(a,b);}
)"),
                "source.mode");
      });
  return cases.result();
}
