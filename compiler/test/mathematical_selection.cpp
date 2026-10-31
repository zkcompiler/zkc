#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/ProtocolDeployment.h"
#include "support/SourceProject.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Interfaces/Mathematical.h"
#include "zkc/Language/Diagnostics.h"
#include "zkc/Translation/Language.h"

using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
constexpr StringLiteral subject = R"(
module mathematical_selection;
use zkc::scalar as scalar;
use zkc::indices as indices;
domain Fr = field("koala-bear");
math fn choose(c:bool,d:bool,a:Fr,b:Fr)->Fr {
  return scalar::select(c,a*b,a+b);
}
math fn direct(c:bool,a:Fr,b:Fr)->Fr {
  return intrinsic<Fr>("field.select",c,a,b);
}
fn local(c:bool,a:Fr,b:Fr)->Fr effects() {
  return scalar::select(c,a,b);
}
protocol Run roles(P)(c:bool@P,d:bool@P,a:Fr@P,b:Fr@P)
 ->(chosen:Fr@P,direct:Fr@P,local:Fr@P,word:index@P) {
  return(chosen=choose(c,d,a,b),direct=direct(c,a,b),local=local(c,a,b),word=indices::select(c,1,2));
}
entry fn Demo(inputs:Run::Inputs) { return Run::run(inputs); }
)";

Expected<CheckedProject> check(StringRef text) {
  auto captured =
      capture({{"m", ("module m;domain Fr=field(\"koala-bear\");" + text).str(),
                "mathematical-selection.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}

const Declaration &named(const CheckedProject &project, StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.name == name && decl.body)
      return decl;
  throw std::runtime_error("missing declaration: " + name.str());
}

void dependencies(const Declaration &decl, ArrayRef<unsigned> expected) {
  const auto &body = *decl.body;
  require(body.mode == Body::Mode::Math && body.results.size() == 1,
          "selection lost its mathematical body");
  require(ArrayRef(body.values[body.results.front().index].components) ==
              expected,
          "selection omitted an operand dependency");
  require(llvm::any_of(body.formationRequirements,
                       [&](const auto &requirement) {
                         return ArrayRef(requirement) == expected;
                       }),
          "selection omitted whole operand formation");
}
} // namespace

int main() {
  Cases cases;
  cases.run("catalog enrolls only the exact total field selection", [] {
    const auto *intrinsic = mathematicalIntrinsic("field.select");
    require(intrinsic && intrinsic->identity == MathematicalIdentity::Select &&
                intrinsic->domain == MathematicalIntrinsic::Domain::Field &&
                intrinsic->naturals == 0 && !intrinsic->domainPoints &&
                !intrinsic->scalar,
            "field selection catalog signature differs");
    require(
        llvm::none_of(protocol::executableOperationContracts(),
                      [](const auto &op) { return op.name == "field.select"; }),
        "selection unexpectedly enrolled a runtime operation");
  });
  cases.run("index selection has one total catalog identity", [] {
    const auto *intrinsic = mathematicalIntrinsic("index.select");
    require(intrinsic && intrinsic->identity == MathematicalIdentity::Select &&
                intrinsic->domain == MathematicalIntrinsic::Domain::Index &&
                intrinsic->naturals == 0 && !intrinsic->domainPoints &&
                !intrinsic->scalar,
            "index selection signature differs");
    auto project = take(check(R"(
math fn select(c:bool,a:index,b:index)->index=primitive("index.select");
math fn direct(c:bool,a:index,b:index)->index {
  return intrinsic("index.select",c,a,b);
}
)"));
    dependencies(named(project, "select"), {0, 1, 2});
    dependencies(named(project, "direct"), {0, 1, 2});
  });
  for (StringRef statics : {"<1>", "<Fr>"})
    cases.run("index selection refuses static roots: " + statics, [=] {
      refuses(
          check(
              ("math fn bad(c:bool,a:index,b:index)->index {return intrinsic" +
               statics + "(\"index.select\",c,a,b);}")
                  .str()),
          "source.intrinsic");
    });
  for (StringRef ports : {"a,b", "c,a,b,a"})
    cases.run("index selection refuses operand count: " + ports, [=] {
      refuses(check(("math fn bad(c:bool,a:index,b:index)->index {return "
                     "intrinsic(\"index.select\"," +
                     ports + ");}")
                        .str()),
              "source.intrinsic");
    });
  cases.run("index selection refuses a nonboolean condition", [] {
    refuses(check(R"(
math fn bad(c:index,a:index,b:index)->index {
 return intrinsic("index.select",c,a,b);
}
)"),
            "source.type");
  });
  cases.run("generic and closed primitive and intrinsic signatures", [] {
    take(check(R"(
math fn select<F:Field>(c:bool,a:F,b:F)->F=primitive("field.select");
math fn closed(c:bool,a:Fr,b:Fr)->Fr=primitive("field.select");
math fn direct<F:Field>(c:bool,a:F,b:F)->F {
  return intrinsic<F>("field.select",c,a,b);
}
math fn concrete(c:bool,a:Fr,b:Fr)->Fr {
  return intrinsic<Fr>("field.select",c,a,b);
}
)"));
  });
  cases.run("constant conditions and equal arms retain whole dependencies", [] {
    auto project = take(check(R"(
math fn select<F:Field>(c:bool,a:F,b:F)->F=primitive("field.select");
math fn direct(c:bool,a:Fr,b:Fr)->Fr {
  return intrinsic<Fr>("field.select",c,a,b);
}
math fn constant(a:Fr,b:Fr)->Fr {
  return intrinsic<Fr>("field.select",false,a*b,b);
}
math fn equal(c:bool,a:Fr)->Fr {
  return intrinsic<Fr>("field.select",c,a,a);
}
)"));
    dependencies(named(project, "select"), {0, 1, 2});
    dependencies(named(project, "direct"), {0, 1, 2});
    dependencies(named(project, "constant"), {0, 1});
    dependencies(named(project, "equal"), {0, 1});
    const auto &primitive = named(project, "select");
    const auto *selection =
        std::get_if<MathValue>(&primitive.body->operations.front().action);
    require(selection && selection->staticArguments.size() == 1 &&
                selection->staticArguments.front() ==
                    primitive.outputs.front().type,
            "selection lost its exact static field root");
  });
  for (StringRef statics : {"", "<1>", "<bool>", "<Fr,1>", "<Fr,Fr>"})
    cases.run("malformed selection statics refuse: " + statics, [=] {
      refuses(check(("math fn bad(c:bool,a:Fr,b:Fr)->Fr {return intrinsic" +
                     statics + "(\"field.select\",c,a,b);}")
                        .str()),
              "source.intrinsic");
    });
  cases.run("literal parameters refuse", [] {
    refuses(check(R"(
math fn bad(c:bool,a:Fr,b:Fr)->Fr {
  return intrinsic<Fr>("field.select",c,a,b;"1");
}
)"),
            "source.intrinsic");
  });
  for (StringRef ports : {"a,b", "c,a,b,a"})
    cases.run("selection operand arity refuses: " + ports, [=] {
      refuses(check(("math fn bad(c:bool,a:Fr,b:Fr)->Fr {return "
                     "intrinsic<Fr>(\"field.select\"," +
                     ports + ");}")
                        .str()),
              "source.intrinsic");
    });
  for (
      StringRef source :
      {R"(math fn bad(c:Fr,a:Fr,b:Fr)->Fr=primitive("field.select");)",
       R"(math fn bad(c:bool,a:Fr,b:Fr)->bool=primitive("field.select");)",
       R"(math fn bad<F:Field,G:Field>(c:bool,a:F,b:G)->F=primitive("field.select");)",
       R"(math fn bad<F:Field,G:Field>(c:bool,a:F,b:F)->G=primitive("field.select");)",
       R"(math fn bad(c:bool,a:Fr)->Fr=primitive("field.select");)"})
    cases.run("malformed primitive ports refuse: " + source, [=] {
      // A non-Field result also fails the inferred static root signature.
      refuses(check(source), source.contains("->bool") ? "source.intrinsic"
                                                       : "source.primitive");
    });
  for (
      StringRef source :
      {R"(math fn bad(c:index,a:Fr,b:Fr)->Fr{return intrinsic<Fr>("field.select",c,a,b);})",
       R"(math fn bad<F:Field,G:Field>(c:bool,a:F,b:G)->F{return intrinsic<F>("field.select",c,a,b);})",
       R"(math fn bad<F:Field,G:Field>(c:bool,a:F,b:F)->G{return intrinsic<F>("field.select",c,a,b);})",
       R"(domain Other=field("baby-bear"); math fn bad(c:bool,a:Fr,b:Other)->Fr{return intrinsic<Fr>("field.select",c,a,b);})"})
    cases.run("nonbool or mismatched field operand refuses: " + source,
              [=] { refuses(check(source), "source.type"); });
  cases.run("empty effect Local alternative stays outside mathematics", [] {
    const StringLiteral local = R"(
fn alternative(a:Fr)->Fr effects() { return a; }
)";
    auto project = take(check(local));
    const auto &body = *named(project, "alternative").body;
    require(body.mode == Body::Mode::Local && !body.effects.fixed.mayStop &&
                !body.effects.fixed.opaque && body.effects.dependencies.empty(),
            "test alternative must be Local with empty effects");
    refuses(check(local.str() + R"(
math fn bad(a:Fr,b:Fr)->Fr {
  return intrinsic<Fr>("field.select",false,alternative(a),b);
}
)"),
            "source.mode");
  });
  cases.run("empty effect Local conditional helper stays Local", [] {
    const StringLiteral local = R"(
fn select(c:bool,a:Fr,b:Fr)->Fr effects() {
  return if c { a } else { b };
}
)";
    take(check(local));
    refuses(check(local.str() + R"(
math fn bad(c:bool,a:Fr,b:Fr)->Fr { return select(c,a,b); }
)"),
            "source.mode");
    refuses(check(R"(fn bad(c:bool,a:Fr,b:Fr)->Fr=primitive("field.select");)"),
            "source.primitive");
  });
  for (StringRef arguments : {"false,at(xs,i),0", "true,0,at(xs,i)"})
    cases.run("unselected alternative retains formation: " + arguments, [=] {
      refuses(check((R"(
type Vector<F:Field>=builtin("vector",F);
math fn at(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs) {
  return intrinsic<Vector<Fr>>("container.at",xs,i);
}
math fn bad(xs:Vector<Fr>,i:index)->Fr {
  return intrinsic<Fr>("field.select",)" +
                     arguments + ");}")
                        .str()),
              "source.data-bound");
    });
  cases.run("mathematical selection does not admit mathematical if", [] {
    refuses(check(R"(
math fn bad(c:bool,a:Fr,b:Fr)->Fr {
  return if c { a } else { b };
}
)"),
            "source.mode");
    refuses(check(R"(
fn bad(c:bool,a:Fr,b:Fr)->Fr {
  return intrinsic<Fr>("field.select",c,a,b);
}
)"),
            "source.mode");
  });

  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run("public scalar wrapper emits upstream selection and realizes", [&] {
    auto sources = sourceProject(ZKC_SOURCE_PROJECT);
    sources.push_back({"mathematical_selection", subject.str(),
                       "mathematical-selection.zkc"});
    auto captured = take(capture(std::move(sources)));
    auto analysis = analyze(captured);
    require(analysis.diagnostics().empty(),
            formatDiagnostics(analysis.diagnostics(), analysis.sources()));
    auto project = take(analysis.checkedProject());
    require(llvm::any_of(
                named(project, "local").body->operations,
                [&](const auto &operation) {
                  const auto *call = std::get_if<HelperCall>(&operation.action);
                  return call &&
                         project.declarations()[call->callee.index].kind ==
                             Declaration::Kind::Math;
                }),
            "Local selection must retain its mathematical helper call");
    auto entry =
        take(closeProtocolDeployment(project, "mathematical_selection::Demo"));
    auto original = take(prepareOriginal(entry));
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
    require(bool(module) && succeeded(mlir::verify(*module)),
            "field selection source failed native formation");
    take(compareOriginal(entry, *module));
    unsigned selects = 0;
    module->walk([&](mlir::arith::SelectOp select) {
      ++selects;
      auto interface =
          mlir::cast<MathematicalOpInterface>(select.getOperation());
      require(interface.getMathematicalIdentity() ==
                      MathematicalIdentity::Select &&
                  interface.getOperandDependencies(0) ==
                      SmallVector<unsigned>({0, 1, 2}),
              "native selection omitted whole dependencies");
      require(select->getNumRegions() == 0,
              "source selection became conditional execution");
    });
    require(selects >= 3 &&
                original.bytes().contains("algebra.field_multiply") &&
                original.bytes().contains("algebra.field_add"),
            "selection lost eager operand formation or a caller mode");
    for (unsigned mutation = 0; mutation < 5; ++mutation) {
      cases.run(
          "independent selection comparison mutation " + Twine(mutation), [&] {
            auto candidate = mlir::parseSourceString<mlir::ModuleOp>(
                original.bytes(), &context);
            bool changed = false;
            candidate->walk([&](mlir::arith::SelectOp select) {
              auto function = select->getParentOfType<mlir::func::FuncOp>();
              if (changed || !function || function.getNumArguments() != 4)
                return;
              require(function.getArgument(1).getType().isSignlessInteger(1) &&
                          select.getTrueValue() != select.getFalseValue(),
                      "source mutation would not change selection");
              if (mutation == 0)
                select->setOperand(0, function.getArgument(1));
              else if (mutation == 1)
                select->setOperand(1, select.getFalseValue());
              else if (mutation == 2)
                select->setOperand(2, select.getTrueValue());
              else if (mutation == 3) {
                auto yes = select.getTrueValue();
                select->setOperand(1, select.getFalseValue());
                select->setOperand(2, yes);
              } else
                select->setAttr("unexpected", mlir::UnitAttr::get(&context));
              changed = true;
            });
            require(changed && succeeded(mlir::verify(*candidate)),
                    "selection mutation lost native formation");
            refuses(compareOriginal(entry, *candidate),
                    mutation == 4 ? "target.admission"
                                  : "source.correspondence");
          });
    }
    for (bool simplify : {false, true})
      cases.run("selection computation recipe, simplify=" + Twine(simplify),
                [&] { take(compileEntry(original, {simplify, false})); });
  });
  return cases.result();
}
