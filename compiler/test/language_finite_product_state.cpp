#include "mlir/IR/Verifier.h"
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
const std::string prelude = R"(module sample;
domain F=field("koala-bear");
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,
 step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
)";
Expected<CheckedProject> check(StringRef source) {
  auto captured =
      capture({{"sample", prelude + source.str(), "finite-product-state.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
const std::string deployment = R"(
protocol Run roles(P)(x:F@P,n:index@P)->(r:F@P){return compute(x,n);}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
)";

CheckedOriginal prepare(const CheckedProject &project) {
  return take(
      prepareOriginal(take(closeProtocolDeployment(project, "sample::Demo"))));
}

void pipeline(const CheckedOriginal &original, mlir::MLIRContext &context) {
  auto module =
      mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
  require(bool(module) && mlir::succeeded(mlir::verify(*module)),
          "finite product original failed native formation");
  take(compareOriginal(original.entry(), *module));
  unsigned folds = 0;
  module->walk([&](mlir::Operation *op) {
    if (op->getName().getStringRef() != "algebra.finite_fold")
      return;
    ++folds;
    require(op->getNumResults() == 3 &&
                op->getResult(0).getType() == op->getResult(1).getType() &&
                op->getResult(2).getType().isUnsignedInteger(64),
            "finite state must flatten to two fields and one unsigned word");
  });
  require(folds != 0, "product state lost its finite computation");
  take(compileEntry(original));
  take(compileEntry(original, {false, false}));
}
} // namespace
int main() {
  Cases cases;
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  for (StringRef arguments : {"", "<index,(T,T,index)>"})
    cases.run("generic product state with fold arguments " + arguments, [&] {
      auto project = take(check((R"(
math fn compute<T:Field>(x:T,n:index)->T {
 let initial:(T,T,index)=(x,x*x,n);
 let state=fold)" + arguments + R"((range(0,64),initial,
   fn((a,b,k),_) => (a*b,b*b,k));
 return state.0;
}
)" + deployment)
                                    .str()));
      pipeline(prepare(project), context);
    });
  cases.run("concrete product state with named callback parameter", [&] {
    auto project = take(check(R"(
math fn compute(x:F,n:index)->F {
 let state=fold(range(0,64),(x,x*x,n),
   fn(s,_) => (s.0*s.1,s.1*s.1,s.2));
 return state.0;
}
)" + deployment));
    pipeline(prepare(project), context);
  });
  cases.run("nested product state through a higher order Math helper", [&] {
    auto project = take(check(R"(
math fn forward<S:Type+Copy+Drop>(rows:domain<index>,initial:S,
 step:math fn(S,item:index)->S where item_from(item,rows))->S {
 return fold(rows,initial,step);
}
math fn pair<S:Type+Copy+Drop>(rows:domain<index>,initial:S,
 step:math fn(S,item:index)->S where item_from(item,rows))->(bool,S) {
 return (true,forward(rows,initial,step));
}
math fn compute<T:Field>(x:T,n:index)->T {
 let initial:((T,()),(T,index))=((x,()),(x*x,n));
 let state=pair(range(0,64),initial,
   fn(((a,()),(b,k)),_) => ((a*b,()),(b*b,k)));
 return state.1.0.0;
}
)" + deployment));
    pipeline(prepare(project), context);
  });
  cases.run("empty product fold preserves a typed initial state", [&] {
    auto project = take(check(R"(
math fn compute<T:Field>(x:T,n:index)->T {
 let initial:(T,T,index)=(x,x*x,n);
 let state=fold(range(0,0),initial,fn((a,b,k),_) => (a*b,b*b,k));
 return state.0;
}
)" + deployment));
    pipeline(prepare(project), context);
  });
  cases.run("product projection through different generic instantiations", [&] {
    auto project = take(check(R"(
math fn identity<S:Type+Copy+Drop>(value:S)->S{return value;}
math fn compute<T:Field>(x:T,n:index)->T {
 let first=identity((x,n));
 let second=identity((true,x*x));
 let state=fold(range(0,64),(first.0,second.1,n),
   fn((a,b,k),_) => (a*b,b*b,k));
 return state.0;
}
)" + deployment));
    pipeline(prepare(project), context);
  });
  cases.run("same typed product state permutation refuses correspondence", [&] {
    auto project = take(check(R"(
math fn compute<T:Field>(x:T,n:index)->T {
 let initial:(T,T,index)=(x,x*x,n);
 let state=fold(range(0,64),initial,fn((a,b,k),_) => (a*b,b*b,k));
 return state.0;
}
)" + deployment));
    auto original = prepare(project);
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
    require(bool(module), "product original did not parse");
    bool changed = false;
    module->walk([&](mlir::Operation *op) {
      if (changed || op->getName().getStringRef() != "func.return" ||
          op->getNumOperands() != 3 ||
          op->getOperand(0).getType() != op->getOperand(1).getType() ||
          op->getOperand(0) == op->getOperand(1))
        return;
      auto first = op->getOperand(0);
      op->setOperand(0, op->getOperand(1));
      op->setOperand(1, first);
      changed = true;
    });
    require(changed && mlir::succeeded(mlir::verify(*module)),
            "product mutation must retain valid native types");
    refuses(compareOriginal(original.entry(), *module),
            "source.correspondence");
  });
  cases.run("product callback cannot change the state type", [&] {
    refuses(check(R"(
math fn compute<T:Field>(x:T,n:index)->T {
 let state=fold(range(0,64),(x,x,n),fn((a,b,k),_) => (a,b,true));
 return state.0;
}
)" + deployment),
            "source.type");
  });
  cases.run("product projection still checks actual field bounds", [&] {
    refuses(check(R"(
math fn compute<T:Field>(x:T,n:index)->T {
 let state=fold(range(0,64),(x,x,n),fn((a,b,k),_) => (a,b,k));
 return state.3;
}
)" + deployment),
            "source.field");
  });
  cases.run("scalar fold result still refuses product projection", [&] {
    refuses(check(R"(
math fn compute<T:Field>(x:T,n:index)->T {
 let state=fold(range(0,64),x,fn(a,_) => a);
 return state.0;
}
)" + deployment),
            "source.type");
  });
  cases.run("product state does not authorize unrelated container access", [&] {
    refuses(check(R"(
type Vector<T:Field>=builtin("vector",T);
math fn at(xs:Vector<F>,i:index)->F where in_bounds(i,xs){
 return intrinsic<Vector<F>>("container.at",xs,i);
}
math fn compute(xs:Vector<F>,x:F,n:index)->F {
 let state=fold(range(0,64),(x,x,n),fn((a,b,k),i) => (at(xs,i),b,k));
 return state.0;
}
)"),
            "source.data-bound");
  });
  cases.run("product fold result cannot borrow initial state bounds", [&] {
    refuses(check(R"(
type Vector<T:Field>=builtin("vector",T);
math fn at(xs:Vector<F>,i:index)->F where in_bounds(i,xs){
 return intrinsic<Vector<F>>("container.at",xs,i);
}
math fn compute(xs:Vector<F>,ys:Vector<F>,i:index)->F where in_bounds(i,xs) {
 let initial:(Vector<F>,F,index)=(xs,0,i);
 let state=fold(range(0,1),initial,fn((v,a,k),_) => (ys,a,k));
 return at(state.0,i);
}
)"),
            "source.data-bound");
  });
  cases.run("product state retains the Math Copy requirement", [&] {
    refuses(check(R"(
#[affine] struct Ticket {value:F}
fn compute(x:Ticket,n:index)->Ticket {
 return fold(range(0,64),(x,n),fn((a,k),_) => (a,k)).0;
}
)"),
            "source.permission");
  });
  for (StringRef field : {"koala-bear", "koala-bear.ext4-binomial3"})
    cases.run("total word power with public Math wrappers over " + field, [&] {
      auto sources = sourceProject(ZKC_SOURCE_PROJECT);
      sources.push_back({"sample",
                         (R"(module sample;
use zkc::finite_math as total;
use zkc::finite_domain as finite_domain;
use zkc::scalar as scalar;
use zkc::indices as indices;
math fn power_word<T:Field>(base:T,exponent:index)->T {
 let initial:(T,T,index)=(1,base,exponent);
 let state=total::fold(finite_domain::range(0,64),initial,
   fn((result,factor,remaining),_) =>
     (scalar::select(indices::bit_and(remaining,1)==1,result*factor,result),
      factor*factor,indices::logical_shift_right(remaining,1)));
 return state.0;
}
domain F=field(")" + field +
                          R"(");
protocol Run roles(P)(base:F@P,n:index@P)->(r:F@P){return power_word(base,n);}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
)")
                             .str(),
                         "finite-product-power.zkc"});
      auto project =
          take(analyze(take(capture(std::move(sources)))).checkedProject());
      auto original = prepare(project);
      require(original.bytes().contains("data.index_bit_and") &&
                  original.bytes().contains("data.index_logical_shift_right") &&
                  original.bytes().contains("arith.select"),
              "power lost its total word and selection operations");
      pipeline(original, context);
    });
  for (StringRef field : {"koala-bear", "koala-bear.ext4-binomial3"})
    cases.run(
        "FRI power compiles its finite product state over " + field, [&] {
          auto sources = sourceProject(ZKC_SOURCE_PROJECT);
          sources.push_back({"sample",
                             (R"(module sample;
use fri as fri;
domain F=field(")" + field + R"(");
protocol Run roles(P)(base:F@P,n:index@P)->(r:F@P){return fri::power_word(base,n);}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
)")
                                 .str(),
                             "fri-power.zkc"});
          auto project =
              take(analyze(take(capture(std::move(sources)))).checkedProject());
          pipeline(prepare(project), context);
        });
  return cases.result();
}
