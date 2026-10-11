#include "../lib/Transforms/LaneRealization.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/Semantics.h"
#include "zkc/Transforms/Finite.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/Support/raw_ostream.h"
#include <fstream>
#include <sstream>
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
const char *source = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = tensor<?x!F>
module { "protocol.module"() ({
 "local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : () -> ()
 "data.domain"() ({
 ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V) -> !data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>) -> ()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 local.func private @step(%state:!F,%item:!F,%xs:!V) -> !F attributes {logical_origin=["step",[]]} {
   %next = "algebra.exec.field_add"(%state,%item) {binding=@add,parameters=[],site="add"} : (!F,!F)->!F
   local.return %next : !F
 }
 "local.finite_fold"() {sym_name="fold",function_type=(!V,!F)->!F,domain=@items,step=@step} : ()->()
 local.func @work(%xs:!V,%init:!F) -> !F attributes {logical_origin=["work",[]]} {
   %r = local.apply @fold(%xs,%init) {site="fold"} : (!V,!F)->!F
   local.return %r : !F
 }
 "protocol.func"() ({
 ^entry(%xs:!V,%init:!F):
   %r = "protocol.local_call"(%xs,%init) {callee=@work,role="P",site="work"} : (!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
std::string replace(std::string text, StringRef old, StringRef next) {
  auto pos = text.find(old.str());
  require(pos != std::string::npos, "missing fixture edit");
  text.replace(pos, old.size(), next.str());
  return text;
}
} // namespace
std::string fixture(StringRef name) {
  std::ifstream stream(std::string(ZKC_FINITE_FIXTURES) + "/" + name.str() +
                       ".mlir");
  require(bool(stream), "missing finite fixture");
  std::ostringstream text;
  text << stream.rdbuf();
  return text.str();
}
std::string linearCollect(unsigned additions, bool subtract = false) {
  auto text = fixture("collect");
  auto begin = text.find("   %y =");
  auto end = text.find("\n }", begin);
  require(begin != std::string::npos && end != std::string::npos,
          "missing collect helper body");
  std::string body, previous = "%x";
  for (unsigned i = 0; i < additions; ++i) {
    auto next = "%v" + std::to_string(i);
    body += "   " + next + " = \"algebra.exec." +
            (subtract ? "field_subtract\"(%x," + previous
                      : "field_add\"(" + previous + ",%x") +
            ") {binding=@mul,parameters=[],site=\"step" + std::to_string(i) +
            "\"} : (!F,!F)->!F\n";
    previous = next;
  }
  body += "   local.return " + previous + " : !F";
  text.replace(begin, end - begin, body);
  return replace(text, "contract=\"field.mul\"",
                 subtract ? "contract=\"field.sub\""
                          : "contract=\"field.add\"");
}
void refusesIR(StringRef text, MLIRContext &context, StringRef code) {
  SmallVector<std::string> codes;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
    for (auto &refusal : diagnostics::refusals(diagnostic))
      codes.push_back(refusal.code);
    return success();
  });
  require(!parseSourceString<ModuleOp>(text, &context),
          "invalid IR was admitted");
  require(llvm::is_contained(codes, code.str()),
          "missing refusal identifier " + code);
}
void pipeline(ModuleOp module, bool optimize = true) {
  PassManager pm(module.getContext());
  pm.addPass(protocol::createProjectProtocolPass(optimize, {optimize, false}));
  pm.addPass(protocol::createEliminatePolynomialsPass());
  pm.addPass(protocol::createLowerMathPass({optimize, false}));
  pm.addPass(protocol::createSelectPhysicalPass());
  require(succeeded(pm.run(module)), "finite pipeline failed");
}
int main(int argc, char **argv) {
  bool checkedAccess = argc == 2 && StringRef(argv[1]) == "--checked-access";
  require(argc == 1 || checkedAccess, "expected optional --checked-access");
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  auto original = parseSourceString<ModuleOp>(source, &context);
  require(bool(original), "finite source refused");
  cases.run("lane outcomes distinguish decline from construction failure", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("collect"), &context);
    require(bool(module), "collect was refused");
    SymbolTable symbols(&module->getBody()->front());
    auto helper = symbols.lookup<local::FuncOp>("square");
    auto vector = helper.getArgument(1);
    llvm::DenseMap<Value, mathematical::LaneInput> inputs;
    inputs[helper.getArgument(0)] = {vector, true};
    inputs[vector] = {vector, false};
    unsigned emitted = 0;
    auto emit = [&](StringRef, ValueRange, Type, ArrayRef<std::string>) {
      ++emitted;
      return Value();
    };
    uint64_t remaining = 0;
    auto declined = take(mathematical::realizeLanes(helper.getBody().front(),
                                                    inputs, vector.getType(),
                                                    {}, &remaining, emit));
    require(declined.status == mathematical::LaneRealizationStatus::Capacity &&
                declined.reason == "mathematical-lane-work" && !emitted,
            "optional capacity emitted part of a candidate");
    remaining = 1000;
    auto work = symbols.lookup<local::FuncOp>("work");
    llvm::DenseMap<Value, mathematical::LaneInput> noInputs;
    auto unsupported = take(
        mathematical::realizeLanes(work.getBody().front(), noInputs,
                                   vector.getType(), {}, &remaining, emit));
    require(unsupported.status ==
                    mathematical::LaneRealizationStatus::Unsupported &&
                unsupported.reason == "mathematical-lane-unsupported" &&
                !emitted,
            "unsupported formula emitted part of a candidate");
    remaining = 1000;
    refuses(mathematical::realizeLanes(helper.getBody().front(), inputs,
                                       vector.getType(), {}, &remaining, emit),
            "mathematical-lane-realization");
    require(emitted == 1, "construction failure did not come from the emitter");
  });
  for (unsigned additions : {1023u, 1024u})
    cases.run("optional lane depth " + std::to_string(additions), [&] {
      auto text = linearCollect(additions);
      for (bool prepare : {false, true}) {
        auto module = parseSourceString<ModuleOp>(text, &context);
        require(bool(module), "valid linear collect was refused");
        if (prepare) {
          PassManager pm(&context);
          pm.addPass(protocol::createPrepareProtocolPass());
          require(succeeded(pm.run(*module)), "prepare lost ordered fallback");
        } else
          require(succeeded(finite::realizeLocals(*module)),
                  "optional Ring capacity rejected ordered collect");
        bool loop = false, lanes = false;
        module->walk([&](Operation *op) {
          loop |= isa<local::LocalForOp>(op);
          lanes |= op->getName().getStringRef() == "algebra.exec.vector_add";
        });
        require(loop == (additions == 1024) && lanes == !loop,
                "depth boundary did not select bulk or clean fallback");
      }
    });
  for (unsigned subtractions : {511u, 512u})
    cases.run(
        "right-nested subtraction depth " + std::to_string(subtractions), [&] {
          auto module = parseSourceString<ModuleOp>(
              linearCollect(subtractions, true), &context);
          require(bool(module), "valid subtraction collection was refused");
          require(succeeded(finite::realizeLocals(*module)),
                  "subtraction depth rejected ordered fallback");
          bool loop = false, lanes = false;
          module->walk([&](Operation *op) {
            loop |= isa<local::LocalForOp>(op);
            lanes |= op->getName().getStringRef() == "algebra.exec.vector_sub";
          });
          require(loop == (subtractions == 512) && lanes == !loop,
                  "subtraction's extra negation depth lost clean fallback");
        });
  cases.run("lane work is shared across definitions", [&] {
    auto text = fixture("collect");
    auto begin = text.find(" \"local.finite_collect\"");
    auto end = text.find('\n', begin);
    require(begin != std::string::npos && end != std::string::npos,
            "missing collect declaration");
    auto second = replace(text.substr(begin, end - begin),
                          "sym_name=\"collect\"", "sym_name=\"second\"");
    text.insert(end, "\n" + second);
    for (uint64_t allowance : {0u, 64u}) {
      auto module = parseSourceString<ModuleOp>(text, &context);
      require(bool(module), "two collects were refused");
      mathematical::RealizationWork work;
      work.lanes = allowance;
      require(succeeded(finite::realizeLocals(*module, {}, &work)),
              "lane exhaustion refused an ordered implementation");
      unsigned loops = 0, lanes = 0;
      module->walk([&](Operation *op) {
        loops += isa<local::LocalForOp>(op);
        lanes += op->getName().getStringRef() == "algebra.exec.vector_mul";
      });
      require(loops == (allowance ? 1u : 2u) && lanes == 2 - loops,
              "lane budget was reset or a declined candidate emitted payload");
      require(work.lanes == 0, "lane work was not charged to the caller");
    }
  });
  cases.run("bound queries share the enclosing work budget", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("total-state"), &context);
    require(bool(module), "total-state source refused");
    bool checked = false;
    module->walk([&](data::BoundedAtOp access) {
      uint64_t remaining = 65536;
      require(finite::provesBound(access.getOperand(1), access.getOperand(0), 0,
                                  remaining),
              "known bound was lost");
      auto consumed = 65536 - remaining;
      require(consumed > 0, "bound query did not charge its enclosing budget");
      remaining = consumed;
      require(finite::provesBound(access.getOperand(1), access.getOperand(0), 0,
                                  remaining) &&
                  remaining == 0,
              "bound query charged inconsistently");
      require(!finite::provesBound(access.getOperand(1), access.getOperand(0),
                                   0, remaining),
              "exhausted bound query acquired a fresh budget");
      remaining = 1;
      require(finite::provesEqualExtent(access.getOperand(0), 0,
                                        access.getOperand(0), 0, remaining) &&
                  remaining == 0,
              "extent evidence did not consume shared work");
      require(!finite::provesEqualExtent(access.getOperand(0), 0,
                                         access.getOperand(0), 0, remaining),
              "exhausted extent query acquired a fresh budget");
      checked = true;
    });
    require(checked, "missing source bound access");
  });
  for (bool optimize : {false, true})
    cases.run(optimize ? "native sum" : "generic fold", [&] {
      OwningOpRef<ModuleOp> candidate(cast<ModuleOp>((*original)->clone()));
      require(succeeded(finite::realizeLocals(*candidate, {optimize, false})),
              "finite realization failed");
      require(succeeded(finite::verifyRealizations(*original, *candidate)),
              "independent correspondence failed");
      bool found = false;
      candidate->walk([&](Operation *op) {
        if (optimize &&
            op->getName().getStringRef() == "algebra.exec.vector_sum")
          found = true;
        if (!optimize && isa<local::LocalForOp>(op))
          found = true;
      });
      require(found, "required realization missing");
      candidate->walk([&](local::ReturnOp ret) {
        auto function = ret->getParentOfType<local::FuncOp>();
        if (function.getSymName() == "fold")
          ret->setOperand(0, function.getArgument(1));
      });
      require(failed(finite::verifyRealizations(*original, *candidate)),
              "mutated result accepted");
    });
  for (bool optimize : {false, true})
    cases.run(optimize ? "optimized pipeline" : "fallback pipeline", [&] {
      OwningOpRef<ModuleOp> candidate(cast<ModuleOp>((*original)->clone()));
      PassManager pm(&context);
      pm.addPass(
          protocol::createProjectProtocolPass(optimize, {optimize, false}));
      pm.addPass(protocol::createEliminatePolynomialsPass());
      pm.addPass(protocol::createLowerMathPass({optimize, false}));
      pm.addPass(protocol::createSelectPhysicalPass());
      require(succeeded(pm.run(*candidate)), "finite pipeline failed");
    });
  for (bool simplify : {false, true})
    for (bool bulk : {false, true})
      cases.run(
          std::string("finite policy independent of simplify ") +
              (simplify ? "on/" : "off/") + (bulk ? "bulk" : "loop"),
          [&] {
            for (bool fuse : {false, true}) {
              MathematicalSelectionPolicy policy{bulk, fuse};
              OwningOpRef<ModuleOp> candidate(
                  cast<ModuleOp>((*original)->clone()));
              PassManager prepare(&context);
              prepare.addPass(
                  protocol::createPrepareProtocolPass(simplify, policy));
              require(succeeded(prepare.run(*candidate)),
                      "policy preparation failed");
              bool sum = false, loop = false;
              candidate->walk([&](Operation *op) {
                sum |=
                    op->getName().getStringRef() == "algebra.exec.vector_sum";
                loop |= isa<local::LocalForOp>(op);
              });
              require(sum == bulk && loop == !bulk,
                      "finite selection followed simplify or fusion");
              OwningOpRef<ModuleOp> projected(
                  cast<ModuleOp>((*candidate)->clone()));
              PassManager project(&context);
              project.addPass(
                  protocol::createProjectProtocolPass(simplify, policy));
              require(succeeded(project.run(*projected)),
                      "policy projection failed");
              require(succeeded(mathematical::verifyAuthoredLocalsPreserved(
                          &candidate->getBody()->front(),
                          &projected->getBody()->front())),
                      "projection changed accepted Local algorithms");
              auto total = parseSourceString<ModuleOp>(fixture("total-collect"),
                                                       &context);
              require(bool(total), "total fixture refused");
              PassManager demand(&context);
              demand.addPass(
                  protocol::createProjectProtocolPass(simplify, policy));
              demand.addPass(protocol::createLowerMathPass(policy));
              require(succeeded(demand.run(*total)),
                      "total demand policy failed");
              bool totalLoop = false;
              total->walk([&](local::LocalForOp) { totalLoop = true; });
              require(totalLoop == !bulk,
                      "total demand ignored finite family policy");
            }
          });
  cases.run("default preparation selects bulk without generic simplify", [&] {
    auto candidate = mathematical::rewriteLocalAlgorithms(*original);
    require(bool(candidate), "checked Local preparation failed");
    bool sum = false, originalFinite = false;
    candidate->walk([&](Operation *op) {
      sum |= op->getName().getStringRef() == "algebra.exec.vector_sum";
    });
    original->walk(
        [&](Operation *op) { originalFinite |= finite::isDeclaration(op); });
    require(sum && originalFinite,
            "default preparation changed source or omitted bulk selection");
  });
  cases.run("descriptor arbitrary expression refused", [&] {
    auto invalid = replace(
        source, "   %d =",
        "   %bad = \"data.index\"() {value=\"0\"} : () -> ui64\n   %d =");
    require(!parseSourceString<ModuleOp>(invalid, &context),
            "descriptor evaluated arbitrary expression");
  });
  cases.run("same helper name changed body refused", [&] {
    OwningOpRef<ModuleOp> candidate(cast<ModuleOp>((*original)->clone()));
    require(succeeded(finite::realizeLocals(*candidate)),
            "finite realization failed");
    candidate->walk([&](local::FuncOp function) {
      if (function.getSymName() == "step")
        function.getBody().front().back().setOperand(0,
                                                     function.getArgument(0));
    });
    require(failed(finite::verifyRealizations(*original, *candidate)),
            "stale helper accepted");
  });
  for (StringRef name : {"dot",
                         "collect",
                         "total-state",
                         "unit-state",
                         "affine",
                         "filter",
                         "predicate-stop",
                         "independent",
                         "dependent",
                         "stopping-branches",
                         "mixed-sequence",
                         "order",
                         "nested-total",
                         "total-collect",
                         "product",
                         "aliased-predicate",
                         "msm",
                         "materialized",
                         "match",
                         "dot-large",
                         "realized-total",
                         "fixed-collect",
                         "total-predicate",
                         "eager",
                         "coordinates-row",
                         "coordinates-column",
                         "total-zip",
                         "dead-domain",
                         "affine-successor"}) {
    for (bool optimize : {false, true})
      cases.run(name + (optimize ? " optimized" : " fallback"), [&] {
        auto module = parseSourceString<ModuleOp>(fixture(name), &context);
        require(bool(module), "finite fixture refused");
        pipeline(*module, optimize);
      });
  }
  for (StringRef name : {"matrix-row", "matrix-column"})
    cases.run(name + " optimized", [&] {
      auto module = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(module), "matrix fixture refused");
      pipeline(*module);
    });
  cases.run("finite repeated state fixed point and conservative cloning", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("total-state"), &context);
    require(bool(module), "total fixture refused");
    Operation *fold = nullptr;
    module->walk([&](algebra::FiniteFoldOp op) { fold = op; });
    finite::Summary summary;
    require(succeeded(finite::summarize(fold, summary)), "summary failed");
    require(summary.results.size() == 2 && summary.results[0].test(0) &&
                summary.results[0].test(1) && summary.results[0].test(2),
            "state dependence did not reach a fixed point");
    auto dependencies = mathematical::operandDependencies(fold, 0);
    require(succeeded(dependencies) && dependencies->size() == 3,
            "whole operation cloning was narrowed");
  });
  cases.run("empty native state retains total formation", [&] {
    auto text = replace(fixture("total-state"),
                        "@step(%a:!F,%b:!F,%i:ui64,%xs:!V) -> (!F,!F)",
                        "@step(%i:ui64,%xs:!V)");
    text =
        replace(text, "#data.index_bound<2,3,0>", "#data.index_bound<0,1,0>");
    text = replace(text, "func.return %b,%v : !F,!F", "func.return");
    text = replace(
        text,
        "%r:2 = \"algebra.finite_fold\"(%xs,%a,%b) {domain=@items,step=@step} "
        ": (!V,!F,!F)->(!F,!F)",
        "\"algebra.finite_fold\"(%xs) {domain=@items,step=@step} : (!V)->()");
    text = replace(text, "\"protocol.return\"(%r#0,%r#1)",
                   "\"protocol.return\"(%a,%b)");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "Unit state total fold refused");
    Operation *fold = nullptr;
    module->walk([&](algebra::FiniteFoldOp op) { fold = op; });
    finite::Summary summary;
    require(succeeded(finite::summarize(fold, summary)) &&
                summary.results.empty() &&
                llvm::any_of(summary.formation,
                             [](const auto &bits) { return bits.test(0); }),
            "Unit state erased formation obligations");
    pipeline(*module);
    refusesIR(
        replace(text, "#data.index_bound<0,1,0>", "#data.index_bound<1,0,0>"),
        context, "finite-bound");
  });
  cases.run("affine state swapping refused", [&] {
    refusesIR(
        replace(fixture("affine"), "local.return %a,%b", "local.return %b,%a"),
        context, "mathematical-formation");
  });
  cases.run("unknown bound boolean refused", [&] {
    refusesIR(replace(fixture("total-state"),
                      "(%xs,%i) :", "(%xs,%i) {in_bounds=true} :"),
              context, "finite-bound");
  });
  cases.run("unproved index refused", [&] {
    refusesIR(replace(fixture("total-state"),
                      "data.preconditions=[#data.index_bound<2,3,0>]",
                      "data.preconditions=[]"),
              context, "finite-bound");
  });
  cases.run("wrong helper container refused", [&] {
    auto wrong = replace(fixture("total-state"), "%i:ui64,%xs:!V)",
                         "%i:ui64,%xs:!V,%ys:!V)");
    wrong = replace(wrong, "(%xs,%i) :", "(%ys,%i) :");
    wrong = replace(wrong, "(%xs,%a,%b) {domain", "(%xs,%a,%b,%xs) {domain");
    wrong = replace(wrong, "(!V,!F,!F)->(!F,!F)\n   ",
                    "(!V,!F,!F,!V)->(!F,!F)\n   ");
    refusesIR(wrong, context, "finite-bound");
  });
  cases.run("domain indices can bound a proven captured container", [&] {
    auto text = replace(fixture("total-state"), "%i:ui64,%xs:!V)",
                        "%i:ui64,%xs:!V,%ys:!V)");
    text =
        replace(text, "#data.index_bound<2,3,0>", "#data.index_bound<2,4,0>");
    text = replace(text, "(%xs,%i) :", "(%ys,%i) :");
    text = replace(text, "(%xs,%a,%b) {domain", "(%xs,%a,%b,%xs) {domain");
    text = replace(text, "(!V,!F,!F)->(!F,!F)\n   ",
                   "(!V,!F,!F,!V)->(!F,!F)\n   ");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "exact captured-container bound refused");
    pipeline(*module);
    auto wrong = replace(text, "^entry(%xs:!V,%a:!F,%b:!F)",
                         "^entry(%xs:!V,%a:!F,%b:!F,%other:!V)");
    wrong =
        replace(wrong, "(%xs,%a,%b,%xs) {domain", "(%xs,%a,%b,%other) {domain");
    wrong = replace(wrong, "sym_name=\"main\",function_type=(!V,!F,!F)",
                    "sym_name=\"main\",function_type=(!V,!F,!F,!V)");
    wrong = replace(wrong, "input_roles=[[\"P\"],[\"P\"],[\"P\"]]",
                    "input_roles=[[\"P\"],[\"P\"],[\"P\"],[\"P\"]]");
    refusesIR(wrong, context, "finite-bound");
  });
  cases.run("dead helper polynomial observation refused", [&] {
    auto wrong =
        replace(fixture("total-state"), "   func.return",
                R"mlir(   %array = tensor.from_elements %a,%b : tensor<2x!F>
   %poly = "poly.from_coefficients"(%array) : (tensor<2x!F>)->!poly.polynomial<"bls12-381.fr",1>
   %bad = "poly.coefficients"(%poly) : (!poly.polynomial<"bls12-381.fr",1>)->tensor<1x!F>
   func.return)mlir");
    refusesIR(wrong, context, "polynomial-formation");
  });
  for (bool fits : {false, true})
    cases.run(
        fits ? "substituted polynomial observation fits"
             : "dead substituted polynomial observation refused",
        [&] {
          std::string width = fits ? "2" : "1";
          auto text = replace(
              fixture("total-state"), " func.func private @step",
              " func.func private "
              "@observe(%p:!poly.polynomial<\"bls12-381.fr\",1>)->tensor<" +
                  width +
                  "x!F> {\n"
                  "   %v = \"poly.coefficients\"(%p) : "
                  "(!poly.polynomial<\"bls12-381.fr\",1>)->tensor<" +
                  width +
                  "x!F>\n"
                  "   func.return %v : tensor<" +
                  width + "x!F>\n }\n func.func private @step");
          text =
              replace(text, "   func.return %b,%v",
                      "   %array = tensor.from_elements %a,%b : tensor<2x!F>\n"
                      "   %poly = \"poly.from_coefficients\"(%array) : "
                      "(tensor<2x!F>)->!poly.polynomial<\"bls12-381.fr\",1>\n"
                      "   %dead = func.call @observe(%poly) : "
                      "(!poly.polynomial<\"bls12-381.fr\",1>)->tensor<" +
                          width +
                          "x!F>\n"
                          "   func.return %b,%v");
          if (fits) {
            auto module = parseSourceString<ModuleOp>(text, &context);
            require(bool(module),
                    "generic polynomial helper was prematurely refused");
            pipeline(*module);
          } else
            refusesIR(text, context, "polynomial-formation");
        });
  cases.run("domain argument must have native encoding", [&] {
    auto text = replace(source, " \"local.binding\"()", R"mlir(
 "data.domain"() ({
 ^entry(%p:!poly.polynomial<"bls12-381.fr",1>,%lo:ui64,%hi:ui64):
   %d = "data.domain_range"(%lo,%hi) : (ui64,ui64)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="bad_domain",sym_visibility="private",function_type=(!poly.polynomial<"bls12-381.fr",1>,ui64,ui64)->!data.domain<ui64>} : ()->()
 "local.binding"())mlir");
    refusesIR(text, context, "finite-domain");
  });
  for (StringRef name : {"dot", "collect"})
    cases.run(name + " actual kernel operand mutation", [&] {
      auto before = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(before), "fixture refused");
      OwningOpRef<ModuleOp> after(cast<ModuleOp>((*before)->clone()));
      require(succeeded(finite::realizeLocals(*after)), "realization failed");
      bool changed = false;
      after->walk([&](Operation *op) {
        if (op->getName().getStringRef() == "algebra.exec.vector_dot") {
          op->setOperand(1, op->getOperand(0));
          changed = true;
        } else if (name == "collect" &&
                   op->getName().getStringRef() == "algebra.exec.vector_mul") {
          auto function = op->getParentOfType<local::FuncOp>();
          function.getBody().front().back().setOperand(0,
                                                       function.getArgument(0));
          changed = true;
        }
      });
      require(changed, "native realization missing");
      require(failed(finite::verifyRealizations(*before, *after)),
              "changed native candidate accepted");
    });
  for (StringRef name : {"dot", "filter"})
    cases.run(name + " removed ignored shape guard", [&] {
      auto before = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(before), "fixture refused");
      OwningOpRef<ModuleOp> after(cast<ModuleOp>((*before)->clone()));
      require(succeeded(finite::realizeLocals(*after)), "realization failed");
      Operation *last = nullptr;
      after->walk([&](Operation *op) {
        if (op->getName().getStringRef() == "local.exec.require")
          last = op;
      });
      if (!last)
        after->walk([&](Operation *op) {
          auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
          auto binding =
              ref ? dyn_cast_or_null<local::OperationBindingOp>(
                        SymbolTable::lookupNearestSymbolFrom(op, ref))
                  : local::OperationBindingOp();
          if (binding && binding.getContract() == "control.require")
            last = op;
        });
      require(last, "shape guard missing");
      last->erase();
      require(failed(finite::verifyRealizations(*before, *after)),
              "removed ignored guard accepted");
    });
  cases.run("actual predicate arms exchanged", [&] {
    auto before = parseSourceString<ModuleOp>(fixture("filter"), &context);
    OwningOpRef<ModuleOp> after(cast<ModuleOp>((*before)->clone()));
    require(succeeded(finite::realizeLocals(*after, {false, false})),
            "realization failed");
    local::LocalIfOp branch;
    after->walk([&](local::LocalIfOp op) { branch = op; });
    require(bool(branch), "predicate branch missing");
    Region temporary;
    temporary.takeBody(branch->getRegion(0));
    branch->getRegion(0).takeBody(branch->getRegion(1));
    branch->getRegion(1).takeBody(temporary);
    require(failed(finite::verifyRealizations(*before, *after)),
            "predicate arms exchanged");
  });
  cases.run("finite local static reference cycle", [&] {
    auto text = replace(
        source,
        "%next = \"algebra.exec.field_add\"(%state,%item) "
        "{binding=@add,parameters=[],site=\"add\"} : (!F,!F)->!F",
        "%next = local.apply @fold(%xs,%state) {site=\"recur\"} : (!V,!F)->!F");
    refusesIR(text, context, "finite-cycle");
  });
  cases.run("nested total static reference cycle", [&] {
    refusesIR(replace(fixture("nested-total"), "step=@inside", "step=@outside"),
              context, "finite-cycle");
  });
  cases.run("total helper body same symbol changed", [&] {
    auto before =
        parseSourceString<ModuleOp>(fixture("nested-total"), &context);
    auto after = parseSourceString<ModuleOp>(replace(fixture("nested-total"),
                                                     "algebra.field_add",
                                                     "algebra.field_multiply"),
                                             &context);
    require(before && after, "fixture refused");
    require(failed(mathematical::verifyProtocolPreparationPreserved(
                &before->getBody()->front(), &after->getBody()->front())),
            "changed total referenced helper accepted");
  });
  cases.run("successor sequence does not inherit bound", [&] {
    auto helper = R"mlir(
 func.func private @successor(%i:ui64,%xs:!data.sequence<i1>,%flag:i1)->i1 attributes {data.preconditions=[#data.index_bound<0,1,0>]} {
   %ys = "data.sequence_append"(%xs,%flag) : (!data.sequence<i1>,i1)->!data.sequence<i1>
   %x = "data.bounded_at"(%ys,%i) : (!data.sequence<i1>,ui64)->i1
   func.return %x : i1
 }
)mlir";
    refusesIR(replace(source, " \"local.binding\"()",
                      std::string(helper) + " \"local.binding\"()"),
              context, "finite-bound");
  });
  cases.run("shifted index does not inherit bound", [&] {
    auto text = replace(fixture("total-state"), "   %v =",
                        R"mlir(   %one = "data.index"() {value="1"} : ()->ui64
   %isSmall = "data.index_less"(%i,%one) : (ui64,ui64)->i1
   %shifted = arith.select %isSmall,%one,%i : ui64
   %v =)mlir");
    text = replace(text, "(%xs,%i) :", "(%xs,%shifted) :");
    refusesIR(text, context, "finite-bound");
  });
  cases.run("exact helper forwarding retains bound", [&] {
    auto text = replace(
        fixture("total-state"), " func.func private @step",
        R"mlir( func.func private @identity(%i:ui64)->ui64 { func.return %i : ui64 }
 func.func private @step)mlir");
    text = replace(
        text, "   %v =",
        "   %forwarded = func.call @identity(%i) : (ui64)->ui64\n   %v =");
    text = replace(text, "(%xs,%i) :", "(%xs,%forwarded) :");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "forwarded bound refused");
    pipeline(*module);
  });
  cases.run("unknown total zip extent refused", [&] {
    auto text = replace(fixture("total-zip"), "^entry(%xs:!V,%factor:!F)",
                        "^entry(%xs:!V,%ys:!V,%factor:!F)");
    text = replace(text, "finite_collect\"(%xs,%xs,%factor)",
                   "finite_collect\"(%xs,%ys,%factor)");
    text = replace(text, "function_type=(!V,!F)->!V",
                   "function_type=(!V,!V,!F)->!V");
    text = replace(text, "input_roles=[[\"P\"],[\"P\"]]",
                   "input_roles=[[\"P\"],[\"P\"],[\"P\"]]");
    refusesIR(text, context, "finite-bound");
  });
  cases.run("forwarding evidence reuses a shared helper graph", [&] {
    std::string helpers;
    for (unsigned level = 0; level < 9; ++level) {
      helpers += " func.func private @forward_" + std::to_string(level) +
                 "(%x:ui64)->ui64 {\n";
      std::string value = "%x";
      if (level < 8)
        for (unsigned call = 0; call < 63; ++call) {
          auto next = "%v" + std::to_string(call);
          helpers += "  " + next + " = func.call @forward_" +
                     std::to_string(level + 1) + "(" + value +
                     ") : (ui64)->ui64\n";
          value = next;
        }
      helpers += "  func.return " + value + " : ui64\n }\n";
    }
    auto text = replace(fixture("total-state"), " func.func private @step",
                        helpers + " func.func private @step");
    text = replace(
        text, "   %v =",
        "   %forward = func.call @forward_0(%i) : (ui64)->ui64\n   %v =");
    text = replace(text, "(%xs,%i) :", "(%xs,%forward) :");
    // Exercise the evidence query itself. Whole-unit expanded analysis has a
    // separate operation budget and intentionally rejects this helper graph.
    ParserConfig config(&context, false);
    auto module = parseSourceString<ModuleOp>(text, config);
    require(bool(module), "forwarding graph did not parse");
    bool checked = false;
    module->walk([&](data::BoundedAtOp access) {
      require(
          finite::provesBound(access->getOperand(1), access->getOperand(0), 0),
          "shared forwarding evidence exhausted work");
      checked = true;
    });
    require(checked, "missing forwarding access");
    refusesIR(text, context, "mathematical-analysis-limit");
  });
  cases.run("fixed Sequence extent is checked through ordinary returns", [&] {
    std::string helpers = R"mlir(
 func.func private @make()->!data.sequence<i1> {
   %s = "data.sequence_empty"() : ()->!data.sequence<i1>
   %b = arith.constant true
   %t = "data.sequence_append"(%s,%b) : (!data.sequence<i1>,i1)->!data.sequence<i1>
   func.return %t : !data.sequence<i1>
 }
 func.func private @relay()->!data.sequence<i1> {
   %s = func.call @make() : ()->!data.sequence<i1>
   func.return %s : !data.sequence<i1>
 }
 func.func private @read()->i1 {
   %s = func.call @relay() : ()->!data.sequence<i1>
   %i = "data.index"() {value="0"} : ()->ui64
   %b = "data.bounded_at"(%s,%i) : (!data.sequence<i1>,ui64)->i1
   func.return %b : i1
 }
)mlir";
    auto text = replace(source, " \"local.binding\"()",
                        helpers + " \"local.binding\"()");
    require(bool(parseSourceString<ModuleOp>(text, &context)),
            "returned constructor extent refused");
    refusesIR(replace(text, "func.return %t :", "func.return %s :"), context,
              "finite-bound");
    auto unknown =
        replace(text, "@read()->i1", "@read(%unknown:!data.sequence<i1>)->i1");
    unknown = replace(unknown, "(%s,%i) :", "(%unknown,%i) :");
    refusesIR(unknown, context, "finite-bound");
  });
  cases.run("actual total multi-result candidate exchanged", [&] {
    auto before = parseSourceString<ModuleOp>(fixture("total-state"), &context);
    require(bool(before), "fixture refused");
    PassManager project(&context);
    project.addPass(protocol::createProjectProtocolPass());
    require(succeeded(project.run(*before)), "projection failed");
    OwningOpRef<ModuleOp> after(cast<ModuleOp>((*before)->clone()));
    PassManager lower(&context);
    lower.addPass(protocol::createLowerMathPass({false, false}));
    require(succeeded(lower.run(*after)), "lowering failed");
    bool changed = false;
    after->walk([&](local::ReturnOp op) {
      if (op.getNumOperands() == 2) {
        Value first = op.getOperand(0);
        op->setOperand(0, op.getOperand(1));
        op->setOperand(1, first);
        changed = true;
      }
    });
    require(changed, "multi-result calculation missing");
    require(failed(mathematical::verifyProjectionPreserved(*before, *after)),
            "exchanged total results accepted");
  });
  for (StringRef name : {"matrix-row", "matrix-column", "msm", "product"})
    cases.run(name + " native operand mutation", [&] {
      auto before = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(before), "fixture refused");
      OwningOpRef<ModuleOp> after(cast<ModuleOp>((*before)->clone()));
      require(succeeded(finite::realizeLocals(*after)), "realization failed");
      bool changed = false;
      after->walk([&](local::FuncOp function) {
        if (function.getSymName() != "fold")
          return;
        auto &body = function.getBody().front();
        body.back().setOperand(
            0, function.getArgument(function.getNumArguments() - 1));
        changed = true;
      });
      require(changed, "native result missing");
      require(failed(finite::verifyRealizations(*before, *after)),
              "changed native result accepted");
    });
  if (checkedAccess) {
    bool installed = !protocol::boundOperationName("matrix.get").empty() &&
                     !protocol::boundOperationName("field_array.get").empty();
    cases.run("checked access prerequisites installed", [&] {
      require(installed, "matrix.get and field_array.get must be integrated");
    });
    if (installed) {
      for (StringRef name :
           {"fixed-elements", "matrix-row", "matrix-column", "matrix-values",
            "total-matrix-values", "bilinear"})
        for (bool optimize : {false, true})
          cases.run(name +
                        (optimize ? " optimized access" : " fallback access"),
                    [&] {
                      auto module =
                          parseSourceString<ModuleOp>(fixture(name), &context);
                      require(bool(module), "access fixture refused");
                      pipeline(*module, optimize);
                    });
      cases.run("actual bilinear operand mutation", [&] {
        auto before =
            parseSourceString<ModuleOp>(fixture("bilinear"), &context);
        require(bool(before), "bilinear source refused");
        OwningOpRef<ModuleOp> after(cast<ModuleOp>((*before)->clone()));
        require(succeeded(finite::realizeLocals(*after)),
                "bilinear realization failed");
        bool changed = false;
        after->walk([&](Operation *op) {
          if (op->getName().getStringRef() == "algebra.exec.matrix_bilinear") {
            op->setOperand(2, op->getOperand(1));
            changed = true;
          }
        });
        require(changed, "bilinear native kernel missing");
        require(failed(finite::verifyRealizations(*before, *after)),
                "wrong bilinear vector accepted");
      });
    }
  }
  return cases.result();
}
