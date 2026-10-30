#include "../lib/Target/PhysicalPlan.h"
#include "../lib/Transforms/Computation/Support.h"
#include "../lib/Transforms/HelperNormalization.h"
#include "../lib/Transforms/MathematicalPreservation.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Computation.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace sc = zkc::test::scopedComputation;
namespace sf = zkc::test::scopedFinite;
namespace {
std::string fixture(StringRef directory, StringRef name) {
  auto bytes =
      llvm::MemoryBuffer::getFile((directory + "/" + name + ".mlir").str());
  require(bool(bytes), "fixture unavailable");
  return (*bytes)->getBuffer().str();
}
std::string insert(StringRef original, StringRef declarations) {
  auto text = original.str();
  auto at = text.find(" func.func private @polynomial");
  require(at != std::string::npos, "fixture insertion unavailable");
  text.insert(at, declarations.str());
  return text;
}
protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
OwningOpRef<ModuleOp> copy(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}
void computationFixture(ModuleOp module, StringRef helper, StringRef caller) {
  auto function = SymbolTable(unit(module)).lookup<func::FuncOp>(helper);
  require(bool(function), "missing computation helper");
  sc::computation(function, caller);
  require(succeeded(verify(module)), "scoped computation fixture refused");
}
OwningOpRef<ModuleOp> prepare(ModuleOp source,
                              MathematicalSelectionPolicy policy = {}) {
  auto logical = copy(source);
  PassManager pipeline(source.getContext());
  pipeline.addPass(protocol::createProjectProtocolPass(false, policy));
  pipeline.addPass(protocol::createLowerMathPass(policy));
  require(succeeded(pipeline.run(*logical)), "logical computation refused");
  return logical;
}
OwningOpRef<ModuleOp> select(ModuleOp logical,
                             MathematicalSelectionPolicy policy = {}) {
  target::PhysicalPlanOptions options;
  options.numericalPolicy = policy;
  auto proposal = take(target::proposePhysical(
      logical, target::installedCandidates(), {}, options));
  auto checked = take(target::validatePhysical(logical, proposal));
  auto selected = take(checked.cloneSelectedSubject(logical));
  require(succeeded(mathematical::verifyNumericalLowering(logical, *selected,
                                                          policy)),
          "independent numerical comparison refused");
  return selected;
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto base = fixture(ZKC_MATH_FIXTURES, "helper-realization");

  const char *nested = R"(
 func.func private @difference(%a:!F,%b:!F)->(!F,!F) {
   %d = algebra.field_subtract %a,%b : (!F,!F)->!F
   func.return %d,%a : !F,!F
 }
 func.func private @nested(%a:!F,%b:!F)->(!F,!F) {
   %r:2 = func.call @difference(%b,%a) : (!F,!F)->(!F,!F)
   %s:2 = func.call @difference(%a,%b) : (!F,!F)->(!F,!F)
   func.return %r#0,%s#1 : !F,!F
 }
 func.func private @expanded(%a:!F,%b:!F)->(!F,!F) {
   %r = algebra.field_subtract %b,%a : (!F,!F)->!F
   %s = algebra.field_subtract %a,%b : (!F,!F)->!F
   func.return %r,%a : !F,!F
 }
 )";
  cases.run("comparison capacity has its own diagnostic", [&] {
    auto source = parseSourceString<ModuleOp>(insert(base, nested), &context);
    require(bool(source), "ordinary nested program refused");
    SymbolTable symbols(unit(*source));
    auto helper = symbols.lookup<func::FuncOp>("nested");
    auto expanded = symbols.lookup<func::FuncOp>("expanded");
    std::string before, after;
    llvm::raw_string_ostream(before) << *source;
    bool named = false;
    ScopedDiagnosticHandler handler(&context, [&](Diagnostic &d) {
      named |= d.str().find("mathematical-helper-limit") != std::string::npos;
      return success();
    });
    mathematical::HelperNormalizationChecker bounded(unit(*source), 1);
    require(failed(bounded.check(helper, expanded.front())) && named,
            "comparison capacity was reported as a semantic mismatch");
    llvm::raw_string_ostream(after) << *source;
    require(before == after, "failed comparison changed its subjects");
    mathematical::HelperNormalizationChecker complete(unit(*source));
    require(succeeded(complete.check(helper, expanded.front())),
            "capacity refusal changed later independent checking");
  });
  cases.run("independent substitution preserves positional calls and tuples",
            [&] {
              auto source =
                  parseSourceString<ModuleOp>(insert(base, nested), &context);
              require(bool(source), "ordinary nested program refused");
              SymbolTable symbols(unit(*source));
              auto helper = symbols.lookup<func::FuncOp>("nested");
              auto expanded = symbols.lookup<func::FuncOp>("expanded");
              mathematical::HelperNormalizationChecker checker(unit(*source));
              require(succeeded(checker.check(helper, expanded.front())),
                      "independent handwritten substitution refused");
              expanded.front().back().setOperand(1, expanded.getArgument(1));
              require(succeeded(verify(*source)),
                      "tuple mutation is not ordinary math");
              bool named = false;
              ScopedDiagnosticHandler handler(&context, [&](Diagnostic &d) {
                named |= d.str().find("mathematical-helper-correspondence") !=
                         std::string::npos;
                return success();
              });
              require(failed(checker.check(helper, expanded.front())) && named,
                      "changed second result escaped substitution comparison");
            });
  cases.run("same-type argument permutation changes subtraction", [&] {
    auto source = parseSourceString<ModuleOp>(insert(base, nested), &context);
    require(bool(source), "ordinary nested program refused");
    SymbolTable symbols(unit(*source));
    auto helper = symbols.lookup<func::FuncOp>("nested");
    auto expanded = symbols.lookup<func::FuncOp>("expanded");
    expanded.front().front().setOperands(expanded.getArguments());
    require(succeeded(verify(*source)), "permutation is not ordinary math");
    ScopedDiagnosticHandler handler(&context,
                                    [](Diagnostic &) { return success(); });
    mathematical::HelperNormalizationChecker checker(unit(*source));
    require(failed(checker.check(helper, expanded.front())),
            "same-type permutation escaped substitution comparison");
  });
  cases.run(
      "unexpanded candidates do not substitute for checked proposals", [&] {
        auto source =
            parseSourceString<ModuleOp>(insert(base, nested), &context);
        require(bool(source), "ordinary nested program refused");
        SymbolTable symbols(unit(*source));
        auto helper = symbols.lookup<func::FuncOp>("nested");
        bool named = false;
        ScopedDiagnosticHandler handler(&context, [&](Diagnostic &d) {
          named |= d.str().find("mathematical-helper-correspondence") !=
                   std::string::npos;
          return success();
        });
        mathematical::HelperNormalizationChecker checker(unit(*source));
        require(failed(checker.check(helper, helper.front())) && named,
                "an unexpanded call was accepted as a normalization proposal");
      });
  cases.run("checked proposals are explicit cached and source preserving", [&] {
    auto source = parseSourceString<ModuleOp>(insert(base, nested), &context);
    require(bool(source), "ordinary nested program refused");
    SymbolTable symbols(unit(*source));
    auto helper = symbols.lookup<func::FuncOp>("nested");
    std::string before, after;
    llvm::raw_string_ostream(before) << *source;
    mathematical::CheckedHelperNormalizations proposals(unit(*source));
    require(!proposals.lookup(helper),
            "lookup manufactured an unchecked proposal");
    require(succeeded(proposals.prepare(helper)),
            "normalization proposal failed");
    auto normalized = proposals.lookup(helper);
    require(normalized && normalized.front().getOps<func::CallOp>().empty(),
            "checked proposal retained an unexpanded call");
    require(succeeded(proposals.prepare(helper)) &&
                proposals.lookup(helper) == normalized,
            "an already checked helper was regenerated");
    llvm::raw_string_ostream(after) << *source;
    require(before == after, "proposal preparation changed its original");
  });
  cases.run("explicit packed projection folding is independently checked", [&] {
    auto source = parseSourceString<ModuleOp>(insert(base, R"(
 func.func private @projection(%a:!F,%b:!F)->!F {
   %pack = "algebra.array_from_elements"(%a,%b) : (!F,!F)->!A
   %value = "algebra.array_at"(%pack) {index=1:i64} : (!A)->!F
   func.return %value : !F
 }
 )"),
                                              &context);
    require(bool(source), "packed helper refused");
    auto helper = SymbolTable(unit(*source)).lookup<func::FuncOp>("projection");
    mathematical::CheckedHelperNormalizations proposals(unit(*source));
    require(succeeded(proposals.prepare(helper)),
            "packed helper realization could not be checked");
    auto prepared = proposals.lookup(helper);
    require(bool(prepared), "missing checked helper");
    OwningOpRef<func::FuncOp> folded(cast<func::FuncOp>(prepared->clone()));
    uint64_t work = 100000;
    require(
        succeeded(mathematical::foldArrayProjections(folded->front(), work)),
        "projection folding failed");
    auto normalized = *folded;
    require(normalized.front().getOperations().size() == 1 &&
                normalized.front().back().getOperand(0) ==
                    normalized.getArgument(1),
            "packed projection was not folded to its selected value");
    normalized.front().back().setOperand(0, normalized.getArgument(0));
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    mathematical::HelperNormalizationChecker checker(unit(*source));
    require(failed(checker.check(helper, normalized.front())),
            "changed packed result escaped normalization comparison");
  });
  cases.run("static dimension meaning is checked before recipe lowering", [&] {
    auto source = parseSourceString<ModuleOp>(insert(base, R"(
 func.func private @dimension(%v:!algebra.field_array<"bls12-381.fr", 4>)->ui64 {
   %n = "data.dim"(%v) {axis=0:i64} : (!algebra.field_array<"bls12-381.fr", 4>)->ui64
   func.return %n : ui64
 }
 func.func private @constant(%v:!algebra.field_array<"bls12-381.fr", 4>)->ui64 {
   %n = "data.index"() {value=4 : ui64} : ()->ui64
   func.return %n : ui64
 }
 )"),
                                              &context);
    require(bool(source), "ordinary dimension program refused");
    SymbolTable symbols(unit(*source));
    auto helper = symbols.lookup<func::FuncOp>("dimension");
    auto expanded = symbols.lookup<func::FuncOp>("constant");
    mathematical::HelperNormalizationChecker checker(unit(*source));
    require(succeeded(checker.check(helper, expanded.front())),
            "correct static dimension refused");
    expanded.front().front().setAttr(
        "value", IntegerAttr::get(
                     IntegerType::get(&context, 64, IntegerType::Unsigned), 3));
    require(succeeded(verify(*source)),
            "dimension mutation is not ordinary math");
    ScopedDiagnosticHandler handler(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(checker.check(helper, expanded.front())),
            "incorrect static dimension escaped independent comparison");
  });
  cases.run("outer correspondence checks the full realized tuple", [&] {
    auto source = parseSourceString<ModuleOp>(insert(base, nested), &context);
    require(bool(source), "ordinary nested program refused");
    computationFixture(*source, "nested", "tuple");
    auto logical = prepare(*source);
    auto candidate = select(*logical);
    auto returned = sc::returned(sf::function(*candidate, "tuple"));
    returned->setOperand(1, returned->getOperand(0));
    require(succeeded(verify(*candidate)), "tuple mutation is not executable");
    ScopedDiagnosticHandler handler(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(mathematical::verifyNumericalLowering(*logical, *candidate)),
            "outer correspondence ignored the second result");
  });
  cases.run("raw dependency bodies are frozen with their scoped caller", [&] {
    auto source = parseSourceString<ModuleOp>(insert(base, nested), &context);
    require(bool(source), "raw closure source refused");
    computationFixture(*source, "nested", "tuple");
    auto helper = SymbolTable(unit(*source)).lookup<func::FuncOp>("nested");
    uint64_t remaining = 1000000;
    auto closure = computation::closeComputation(helper, remaining);
    require(bool(closure) && succeeded(computation::verifyComputationClosure(
                                 unit(*source), helper, *closure)),
            "closing computation changed the original dependency bodies");
    auto dependency = SymbolTable(*closure).lookup<func::FuncOp>("difference");
    require(bool(dependency), "formation normalized away the raw dependency");
    auto &subtract = dependency.front().front();
    subtract.setOperand(1, subtract.getOperand(0));
    require(succeeded(verify(*closure)),
            "same-typed dependency mutation lost formation");
    ScopedDiagnosticHandler expected(&context,
                                     [](Diagnostic &) { return success(); });
    require(failed(computation::verifyComputationClosure(unit(*source), helper,
                                                         *closure)),
            "closure comparison ignored a changed dependency");
    auto candidate = copy(*source);
    auto changed =
        SymbolTable(unit(*candidate)).lookup<func::FuncOp>("difference");
    changed.front().front().setOperand(1, changed.getArgument(0));
    require(succeeded(verify(*candidate)),
            "source dependency mutation lost formation");
    require(
        failed(mathematical::verifyAuthoredLocalsPreserved(unit(*source),
                                                           unit(*candidate))),
        "scoped caller preservation failed to freeze its numerical closure");
  });
  cases.run("bounded indices retain their argument assignment", [&] {
    auto source = parseSourceString<ModuleOp>(insert(base, R"(
 func.func private @access(%xs:!algebra.field_vector<"bls12-381.fr">,%i:ui64,%j:ui64)->!F
 attributes {data.preconditions=[#data.index_bound<1,0,0>,#data.index_bound<2,0,0>]} {
   %v = "data.bounded_at"(%xs,%i) : (!algebra.field_vector<"bls12-381.fr">,ui64)->!F
   func.return %v : !F
 }
 func.func private @other(%xs:!algebra.field_vector<"bls12-381.fr">,%i:ui64,%j:ui64)->!F
 attributes {data.preconditions=[#data.index_bound<1,0,0>,#data.index_bound<2,0,0>]} {
   %v = "data.bounded_at"(%xs,%j) : (!algebra.field_vector<"bls12-381.fr">,ui64)->!F
   func.return %v : !F
 }
 )"),
                                              &context);
    require(bool(source), "ordinary bounded accesses refused");
    SymbolTable symbols(unit(*source));
    mathematical::HelperNormalizationChecker checker(unit(*source));
    auto helper = symbols.lookup<func::FuncOp>("access");
    require(succeeded(checker.check(helper, helper.front())),
            "identical bounded access refused");
    ScopedDiagnosticHandler handler(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(checker.check(
                helper, symbols.lookup<func::FuncOp>("other").front())),
            "different admitted index accepted");
  });
  cases.run(
      "sequences group operations and Boolean selection stay supported", [&] {
        auto source = parseSourceString<ModuleOp>(insert(base, R"(
 func.func private @mixed(%a:!F,%b:!F,%g:!algebra.group<"bls12-381.g1">,%c:i1)->(!F,!algebra.group<"bls12-381.g1">,ui64) {
   %v = arith.select %c,%a,%b : !F
   %p = algebra.group_scale %g,%v : (!algebra.group<"bls12-381.g1">,!F)->!algebra.group<"bls12-381.g1">
   %empty = "data.sequence_empty"() : ()->!data.sequence<!F>
   %one = "data.sequence_append"(%empty,%a) : (!data.sequence<!F>,!F)->!data.sequence<!F>
   %two = "data.sequence_append"(%one,%b) : (!data.sequence<!F>,!F)->!data.sequence<!F>
   %n = "data.sequence_length"(%two) : (!data.sequence<!F>)->ui64
   func.return %v,%p,%n : !F,!algebra.group<"bls12-381.g1">,ui64
 }
 )"),
                                                  &context);
        require(bool(source), "ordinary mixed helper refused");
        computationFixture(*source, "mixed", "mixed_exec");
        auto logical = prepare(*source);
        auto candidate = select(*logical);
        auto function = sf::function(*candidate, "mixed_exec");
        auto application = sf::application(function, "curve.scale");
        application.setSite("changed_site");
        require(succeeded(verify(*candidate)),
                "site mutation is not executable");
        ScopedDiagnosticHandler handler(&context,
                                        [](Diagnostic &) { return success(); });
        require(
            failed(mathematical::verifyNumericalLowering(*logical, *candidate)),
            "changed computation occurrence accepted");
      });

  cases.run("independent polynomial observation against handwritten arithmetic",
            [&] {
              auto source = parseSourceString<ModuleOp>(insert(base, R"(
 func.func private @expanded(%a:!F,%b:!F,%x:!F)->!F {
   %bx = algebra.field_multiply %b,%x : (!F,!F)->!F
   %p = algebra.field_add %bx,%a : (!F,!F)->!F
   %r = algebra.field_multiply %p,%p : (!F,!F)->!F
   func.return %r : !F
 }
 )"),
                                                        &context);
              require(bool(source), "ordinary polynomial program refused");
              SymbolTable symbols(unit(*source));
              auto helper = symbols.lookup<func::FuncOp>("polynomial");
              auto expanded = symbols.lookup<func::FuncOp>("expanded");
              mathematical::HelperNormalizationChecker checker(unit(*source));
              require(succeeded(checker.check(helper, expanded.front())),
                      "independent polynomial meaning differs");
              expanded.front().front().setOperand(1, expanded.getArgument(0));
              require(succeeded(verify(*source)),
                      "point mutation is not ordinary math");
              ScopedDiagnosticHandler handler(
                  &context, [](Diagnostic &) { return success(); });
              require(failed(checker.check(helper, expanded.front())),
                      "changed evaluation point escaped comparison");
            });

  const char *polynomials = R"(
 func.func private @observe(%p:!P)->!A {
   %c = "poly.coefficients"(%p) : (!P)->!A
   func.return %c : !A
 }
 func.func private @tables(%a:!F,%b:!F,%x:!F)->(!A,!A,!F) {
   %v = "algebra.array_from_elements"(%a,%b) : (!F,!F)-> !A
   %p = "poly.interpolate"(%v) {points=[#algebra.literal<!algebra.field<"bls12-381.fr">, 0 : ui255>,#algebra.literal<!algebra.field<"bls12-381.fr">, 1 : ui255>]} : (!A)->!P
   %c = func.call @observe(%p) : (!P)->!A
   %d = "poly.evaluate_domain"(%p) {points=[#algebra.literal<!algebra.field<"bls12-381.fr">, 2 : ui255>,#algebra.literal<!algebra.field<"bls12-381.fr">, 3 : ui255>]} : (!P)->!A
   %unused = func.call @observe(%p) : (!P)->!A
   %m = "poly.mle"(%v) : (!A)->!P
   %f = "poly.fix"(%m,%x) : (!P,!F)->!poly.polynomial<"bls12-381.fr",0>
   %r = "poly.evaluate"(%f) : (!poly.polynomial<"bls12-381.fr",0>)->!F
   func.return %c,%d,%r : !A,!A,!F
 }
 func.func private @sum(%a:!F,%b:!F,%x:!F)->(!A,!A,ui64) {
   %v = "algebra.array_from_elements"(%a,%b,%b,%a) : (!F,!F,!F,!F)-> !algebra.field_array<"bls12-381.fr", 4>
   %m = "poly.mle"(%v) : (!algebra.field_array<"bls12-381.fr", 4>)->!poly.polynomial<"bls12-381.fr",2>
   %s = "poly.sum_suffix"(%m) {count=1:i64} : (!poly.polynomial<"bls12-381.fr",2>)->!P
   %c = "poly.coefficients"(%s) : (!P)->!A
   %t = "poly.fix_table"(%v,%x) : (!algebra.field_array<"bls12-381.fr", 4>,!F)->!A
   %n = "data.dim"(%v) {axis=0:i64} : (!algebra.field_array<"bls12-381.fr", 4>)->ui64
   func.return %c,%t,%n : !A,!A,ui64
 }
 )";
  cases.run(
      "interpolation tables fixing suffix sums and dead valid observations",
      [&] {
        auto source =
            parseSourceString<ModuleOp>(insert(base, polynomials), &context);
        require(bool(source), "ordinary polynomial family refused");
        computationFixture(*source, "tables", "tables_exec");
        computationFixture(*source, "sum", "sum_exec");
        auto logical = prepare(*source);
        unsigned rawPolynomialOperations = 0;
        logical->walk([&](Operation *operation) {
          rawPolynomialOperations +=
              operation->getName().getStringRef().starts_with("poly.");
        });
        require(
            rawPolynomialOperations,
            "source preparation normalized away raw polynomial mathematics");
        auto candidate = select(*logical);
        auto function = sf::function(*candidate, "sum_exec");
        auto dimension = sc::returned(function)->getOperand(2);
        exec::ApplyOp constant;
        for (auto op : sf::applications(function, "index.constant"))
          if (sc::payload(op).front() == dimension)
            constant = op;
        require(constant && constant.getParameters() ==
                                ArrayAttr::get(
                                    &context,
                                    {IntegerAttr::get(
                                        IntegerType::get(&context, 64,
                                                         IntegerType::Unsigned),
                                        4)}),
                "missing returned static dimension");
        constant.setParametersAttr(ArrayAttr::get(
            &context,
            {IntegerAttr::get(
                IntegerType::get(&context, 64, IntegerType::Unsigned), 3)}));
        require(succeeded(verify(*candidate)),
                "dimension mutation is not executable");
        ScopedDiagnosticHandler handler(&context,
                                        [](Diagnostic &) { return success(); });
        require(
            failed(mathematical::verifyNumericalLowering(*logical, *candidate)),
            "changed static dimension escaped correspondence");
      });
  cases.run("ordered finite helper checks original polynomial meaning", [&] {
    auto text = fixture(ZKC_FINITE_FIXTURES, "total-state");
    auto returned = text.find("   func.return %b,%v");
    require(returned != std::string::npos,
            "finite polynomial insertion unavailable");
    text.replace(returned, std::string("   func.return %b,%v").size(), R"(
   %coeffs = "algebra.array_from_elements"(%a,%b) : (!F,!F)-> !algebra.field_array<"bls12-381.fr", 2>
   %p = "poly.from_coefficients"(%coeffs) : (!algebra.field_array<"bls12-381.fr", 2>)->!poly.polynomial<"bls12-381.fr",1>
   %y = "poly.evaluate"(%p,%v) : (!poly.polynomial<"bls12-381.fr",1>,!F)->!F
   func.return %b,%y)");
    auto source = parseSourceString<ModuleOp>(text, &context);
    require(bool(source), "ordinary finite polynomial program refused");
    MathematicalSelectionPolicy policy;
    policy.finiteBulk = false;
    PassManager preparation(&context);
    preparation.addPass(protocol::createProjectProtocolPass(false, policy));
    require(succeeded(preparation.run(*source)), "finite preparation failed");
    auto candidate = copy(*source);
    PassManager lowering(&context);
    lowering.addPass(protocol::createLowerMathPass(policy));
    require(succeeded(lowering.run(*candidate)),
            "finite polynomial lowering failed");
    require(succeeded(mathematical::verifyMathLowering(unit(*source),
                                                       unit(*candidate))),
            "original finite polynomial recipe refused");
    auto logical = copy(*candidate);
    candidate = select(*logical, policy);
    auto product = sf::application(*candidate, "field.mul");
    product.getInputsMutable()[1].set(product.getInputs()[0]);
    require(succeeded(verify(*candidate)), "finite mutation is not executable");
    ScopedDiagnosticHandler handler(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(mathematical::verifyNumericalLowering(*logical, *candidate,
                                                         policy)),
            "changed finite polynomial computation escaped correspondence");
  });
  cases.run(
      "admitted shared helper expansion retains its operation capacity", [&] {
        std::string declarations = "func.func private @leaf(%x:!F)->!F {\n";
        for (unsigned i = 0; i < 250; ++i)
          declarations += "%v" + std::to_string(i) +
                          " = algebra.field_add %x,%x : (!F,!F)->!F\n";
        declarations +=
            "func.return %x:!F }\nfunc.func private @many(%x:!F)->!F {\n";
        for (unsigned i = 0; i < 195; ++i)
          declarations +=
              "%v" + std::to_string(i) + " = func.call @leaf(%x):(!F)->!F\n";
        declarations += "func.return %x:!F }\n";
        auto source =
            parseSourceString<ModuleOp>(insert(base, declarations), &context);
        require(bool(source), "ordinary shared helper program refused");
        computationFixture(*source, "many", "one");
        computationFixture(*source, "many", "two");
        auto logical = prepare(*source);
        auto selected = select(*logical);
        require(sf::function(*selected, "one") &&
                    sf::function(*selected, "two"),
                "shared helper occurrence disappeared");
      });
  cases.run("helper comparisons share one cumulative work budget", [&] {
    std::string declarations = "func.func private @budgeted(%x:!F)->!F {\n";
    for (unsigned i = 0; i < 250; ++i)
      declarations += "%v" + std::to_string(i) +
                      " = algebra.field_add %x,%x : (!F,!F)->!F\n";
    declarations += "func.return %x:!F }\n";
    auto source =
        parseSourceString<ModuleOp>(insert(base, declarations), &context);
    require(bool(source), "ordinary comparison-budget fixture refused");
    SymbolTable symbols(unit(*source));
    auto helper = symbols.lookup<func::FuncOp>("budgeted");
    mathematical::HelperNormalizationChecker checker(unit(*source));
    bool named = false, exhausted = false;
    ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
      named |= diagnostic.str().find("mathematical-helper-limit") !=
               std::string::npos;
      return success();
    });
    require(succeeded(checker.check(helper, helper.front())),
            "first bounded comparison refused");
    for (unsigned i = 0; i < 2048 && !exhausted; ++i)
      exhausted = failed(checker.check(helper, helper.front()));
    require(exhausted && named,
            "helper comparison reset its cumulative budget");
    require(failed(checker.check(helper, helper.front())),
            "exhausted comparison budget reset");
  });
  for (bool bulk : {false, true})
    for (StringRef name : {"total-state", "realized-total", "nested-total",
                           "total-predicate", "total-collect", "total-zip"})
      cases.run(("admitted finite computation " + name +
                 (bulk ? " bulk" : " ordered"))
                    .str(),
                [&] {
                  auto source = parseSourceString<ModuleOp>(
                      fixture(ZKC_FINITE_FIXTURES, name), &context);
                  require(bool(source), "ordinary finite program refused");
                  PassManager pipeline(&context);
                  MathematicalSelectionPolicy policy;
                  policy.finiteBulk = bulk;
                  pipeline.addPass(
                      protocol::createProjectProtocolPass(false, policy));
                  pipeline.addPass(protocol::createLowerMathPass(policy));
                  pipeline.addPass(
                      computation::createRealizeComputationsPass());
                  require(succeeded(pipeline.run(*source)),
                          "finite helper realization failed");
                });
  return cases.result();
}
