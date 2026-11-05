#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Analysis/MathematicalFacts.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Translation/Language.h"

using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
const std::string prelude = R"(module sample;
domain F=field("koala-bear");
type Vector=builtin("vector",F);
domain fn indices(xs:Vector)->domain<index>=domain("indices");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn at(xs:Vector,i:index)->F where in_bounds(i,xs){return intrinsic<Vector>("container.at",xs,i);}
)";
const std::string deployment = R"(
protocol Run roles(P)(xs:Vector@P,x:F@P)->(r:bool@P){return work(xs,x);}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
)";
Expected<CheckedProject> check(StringRef source) {
  auto captured =
      capture({{"sample", prelude + source.str(), "index-fact-transport.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
CheckedOriginal original(StringRef source) {
  auto project = take(check(source));
  if (auto error = checkScopedElaboration(project))
    throw std::runtime_error(toString(std::move(error)));
  auto closed = take(closeProtocolDeployment(project, "sample::Demo"));
  if (auto error = checkScopedSpecialization(closed))
    throw std::runtime_error(toString(std::move(error)));
  return take(prepareOriginal(closed));
}
std::string computation(StringRef body) {
  return R"(
math fn choose(acc:bool,xs:Vector,i:index,x:F)->bool where in_bounds(i,xs){
)" + body.str() +
         R"(
}
math fn work(xs:Vector,x:F)->bool{return fold(indices(xs),true,fn(acc,item)=>choose(acc,xs,item,x));}
)" + deployment;
}
} // namespace
int main() {
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  for (StringRef body :
       {"return if acc {at(xs,i)==x}else{false};",
        "return if acc {at(xs,i)==x}else{at(xs,i)==x};",
        "return if acc {if acc "
        "{at(xs,i)==x}else{at(xs,i)==x}}else{at(xs,i)==x};",
        "return if acc "
        "{intrinsic<Vector>(\"container.at\",xs,i)==x}else{false};",
        "let pair=((xs,i),(i,xs));let alias=pair.0.0;return if acc "
        "{at(alias,pair.1.0)==x}else{at(pair.1.1,pair.0.1)==x};"})
    cases.run("whole-item premise reaches selected Math: " + body, [&] {
      auto input = original(computation(body));
      require(input.bytes().contains("data.branch"),
              "selected Math became eager");
      auto module =
          mlir::parseSourceString<mlir::ModuleOp>(input.bytes(), &context);
      require(bool(module) && succeeded(mlir::verify(*module)),
              "original is not well-typed");
      take(compareOriginal(input.entry(), *module));
      for (bool simplify : {false, true})
        take(compileEntry(input, {simplify, false}));
    });
  cases.run("selected Boolean finite callback keeps its item origin", [&] {
    auto input = original(R"(
math fn work(xs:Vector,x:F)->bool {
 return fold(indices(xs),true,fn(acc,item)=>acc&&(at(xs,item)==x));
}
)" + deployment);
    require(input.bytes().contains("data.branch") &&
                input.bytes().contains("data.finite_fold"),
            "finite selected client lost its control or domain");
    for (bool simplify : {false, true})
      take(compileEntry(input, {simplify, false}));
  });
  for (StringRef body : {"return if acc {at(other,i)==x}else{false};",
                         "return if acc {at(xs,j)==x}else{false};",
                         "return if acc {at(xs,i)==x}else{false};"})
    cases.run("source refuses missing or mismatched selected premise: " + body,
              [&] {
                std::string declaration = "math fn "
                                          "choose(acc:bool,xs:Vector,other:"
                                          "Vector,i:index,j:index,x:F)->bool";
                if (!body.contains("at(xs,i)"))
                  declaration += " where in_bounds(i,xs)";
                refuses(check(declaration + "{" + body.str() + "}"),
                        "source.data-bound");
              });
  const auto mutationSource = R"(
math fn choose(acc:bool,xs:Vector,other:Vector,i:index,j:index,x:F)->bool where in_bounds(i,xs){
 let pair=((xs,i),(other,j));
 return if acc {at(pair.0.0,pair.0.1)==x}else{at(pair.0.0,pair.0.1)==x};
}
math fn work(xs:Vector,x:F)->bool {
 return fold(indices(xs),true,fn(acc,item)=>choose(acc,xs,xs,item,item,x));
}
)" + deployment;
  for (StringRef mutation : {"container", "index", "premise", "yield"})
    cases.run("actual source-emitted native mutation: " + mutation, [&] {
      auto input = original(mutationSource);
      auto module =
          mlir::parseSourceString<mlir::ModuleOp>(input.bytes(), &context);
      require(bool(module), "original did not parse");
      mlir::func::FuncOp function;
      data::BranchOp branch;
      module->walk([&](mlir::func::FuncOp op) {
        if (op.getNumArguments() == 6 && op->hasAttr("data.preconditions")) {
          data::BranchOp selected;
          op.walk([&](data::BranchOp candidate) { selected = candidate; });
          if (selected) {
            function = op;
            branch = selected;
          }
        }
      });
      require(bool(function) && bool(branch),
              "missing selected helper and actual captures");
      if (mutation == "premise")
        function->removeAttr("data.preconditions");
      else if (mutation == "yield") {
        auto &arm = branch.getArms()[1].front();
        mlir::OpBuilder builder(&arm.back());
        auto flag =
            mlir::arith::ConstantIntOp::create(builder, branch.getLoc(), 0, 1);
        arm.back().setOperand(0, flag);
      } else {
        // Actual helper formals are flattened in source order. Replace only
        // the captured xs or i with its distinct equal-typed source formal.
        unsigned from = mutation == "container" ? 1 : 3;
        unsigned to = mutation == "container" ? 2 : 4;
        bool changed = false;
        for (mlir::OpOperand &operand : branch->getOpOperands())
          if (operand.get() == function.getArgument(from)) {
            operand.set(function.getArgument(to));
            changed = true;
          }
        require(changed, "mutation changed no actual capture");
      }
      require(succeeded(mlir::verify(*module)),
              "mutation is not native well-typed IR");
      if (mutation == "yield") {
        require(succeeded(admitStage(*module)),
                "yield mutation did not reach source comparison");
      } else {
        SmallVector<std::string> codes;
        mlir::ScopedDiagnosticHandler capture(
            &context, [&](mlir::Diagnostic &diagnostic) {
              for (const auto &refusal : diagnostics::refusals(diagnostic))
                codes.push_back(refusal.code);
              return mlir::success();
            });
        require(failed(admitStage(*module)) &&
                    llvm::is_contained(codes, "finite-bound"),
                "changed actual subject borrowed the original premise");
      }
      mlir::ScopedDiagnosticHandler capture(
          &context, [](mlir::Diagnostic &) { return mlir::success(); });
      refuses(compareOriginal(input.entry(), *module),
              mutation == "yield" ? "source.correspondence"
                                  : "target.admission");
    });

  for (bool container : {false, true})
    cases.run(
        container ? "checked source cannot swap equal-typed container captures"
                  : "checked source cannot swap equal-typed index captures",
        [&] {
          auto project = take(check(R"(
math fn choose(acc:bool,xs:Vector,other:Vector,i:index,j:index,x:F)->bool where in_bounds(i,xs){
 return if acc {at(xs,i)==x}else{false};
}
)"));
          const auto &declarations = project.declarations();
          auto declaration = llvm::find_if(declarations, [](const auto &decl) {
            return decl.name == "choose" && decl.body;
          });
          require(declaration != declarations.end(),
                  "missing checked source helper");
          auto &body = const_cast<Body &>(*declaration->body);
          unsigned from = container ? 1 : 3, to = container ? 2 : 4;
          require(body.values[from].type == body.values[to].type,
                  "source mutation is not equal-typed");
          bool changed = false;
          for (auto &op : body.operations)
            if (auto *projection = std::get_if<Projection>(&op.action);
                projection && projection->input.index == from) {
              projection->input = ValueId{to};
              changed = true;
            }
          require(changed, "source mutation changed no actual capture");
          auto error = checkScopedElaboration(project);
          require(bool(error),
                  "rewritten checked source passed authored replay");
          auto message = toString(std::move(error));
          require(StringRef(message).contains("source.data-bound"), message);
        });

  cases.run("record field projections retain exact captures in both arms", [&] {
    auto input = original(R"(
struct Selection {xs:Vector,i:index}
math fn choose(acc:bool,xs:Vector,i:index,x:F)->bool where in_bounds(i,xs){
 let pair=Selection{xs:xs,i:i};
 return if acc {at(pair.xs,pair.i)==x}else{at(pair.xs,pair.i)==x};
}
math fn work(xs:Vector,x:F)->bool{return fold(indices(xs),true,fn(acc,item)=>choose(acc,xs,item,x));}
)" + deployment);
    for (bool simplify : {false, true})
      take(compileEntry(input, {simplify, false}));
  });

  cases.run("source-emitted captured word expressions preserve depth", [&] {
    auto input = original(R"(
math fn mask(a:index,b:index)->index=primitive("index.bit_and");
math fn choose(c:bool,i:index)->index {
 let word=mask(i,7);
 return if c {word}else{word};
}
protocol Run roles(P)(c:bool@P,i:index@P)->(r:index@P){return choose(c,i);}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
)");
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(input.bytes(), &context);
    require(bool(module) && succeeded(mlir::verify(*module)) &&
                succeeded(admitStage(*module)),
            "source word original failed native admission");
    take(compareOriginal(input.entry(), *module));
    MathematicalFactAnalysis analysis(*module);
    unsigned checked = 0;
    module->walk([&](data::BranchOp branch) {
      for (mlir::Region &arm : branch.getArms()) {
        auto argument = mlir::dyn_cast<mlir::BlockArgument>(
            arm.front().back().getOperand(0));
        require(bool(argument), "source did not capture the constructed word");
        for (unsigned depth : {254u, 255u}) {
          uint64_t remaining = 65536;
          facts::Work work(remaining);
          auto range = analysis.wordRange(argument, work, depth);
          if (depth == 254) {
            require(range.status == facts::Status::Proven && range.value &&
                        range.value->minimum == 0 &&
                        range.value->maximum == 7 && !work.exhausted(),
                    "source-emitted word range changed");
          } else {
            require(range.status == facts::Status::Capacity && !range.value &&
                        work.exhausted() && remaining > 65000,
                    "source-emitted word overflow did not preserve capacity");
          }
        }
        ++checked;
      }
    });
    require(checked == 2, "missing actual captured word in both source arms");
    for (bool simplify : {false, true})
      take(compileEntry(input, {simplify, false}));
  });

  cases.run(
      "source-emitted captured collect retains constructor cardinality", [&] {
        auto input = original(R"(
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
math fn mapped<I:Type+Copy+Drop>(rows:domain<I>,body:math fn(item:I)->F where item_from(item,rows))->Vector=finite("math.collect.vector");
math fn choose(c:bool,x:F)->F {
 let xs=mapped(range(0,1),fn(_)=>x);
 return if c {at(xs,0)}else{at(xs,0)};
}
protocol Run roles(P)(c:bool@P,x:F@P)->(r:F@P){return choose(c,x);}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
)");
        auto module =
            mlir::parseSourceString<mlir::ModuleOp>(input.bytes(), &context);
        require(bool(module) && succeeded(mlir::verify(*module)) &&
                    succeeded(admitStage(*module)),
                "source collect original failed native admission");
        take(compareOriginal(input.entry(), *module));
        MathematicalFactAnalysis analysis(*module);
        unsigned checked = 0;
        module->walk([&](data::BranchOp branch) {
          for (mlir::Region &arm : branch.getArms())
            for (auto value : arm.front().getArguments()) {
              if (!mlir::isa<data::FieldVectorType>(value.getType()))
                continue;
              uint64_t remaining = 65536;
              facts::Work work(remaining);
              auto count = analysis.cardinality(value, 0, work);
              require(
                  count.value &&
                      count.value->precision == facts::Precision::Exact &&
                      count.value->value == 1,
                  "actual source constructor lost its count through a capture");
              for (unsigned depth : {252u, 253u}) {
                remaining = 65536;
                facts::Work limited(remaining);
                auto result = analysis.cardinality(value, 0, limited, depth);
                require(result.status == (depth == 252
                                              ? facts::Status::Proven
                                              : facts::Status::Capacity) &&
                            bool(result.value) == (depth == 252) &&
                            limited.exhausted() == (depth == 253),
                        "source constructor continuation reset depth");
                if (result.value)
                  require(result.value->precision == facts::Precision::Exact &&
                              result.value->value == 1,
                          "source constructor boundary changed its count");
              }
              ++checked;
            }
        });
        require(checked == 2,
                "missing captured source constructors in both arms");
        for (bool simplify : {false, true})
          take(compileEntry(input, {simplify, false}));
      });
  return cases.result();
}
