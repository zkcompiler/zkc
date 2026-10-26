#include "../lib/Target/PhysicalPlan.h"
#include "../lib/Transforms/MathematicalSupport.h"
#include "mlir/Parser/Parser.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "support/ScopedFixture.h"
#include "zkc/Dialect/Registry.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace sf = zkc::test::scopedFinite;
namespace sc = zkc::test::scopedComputation;
namespace {
const std::string declarations = R"mlir(
"runtime.binding"() {sym_name="sum",contract="vector.sum",arguments=["koala-bear"],implementation=""} : ()->()
"data.domain"() ({^entry(%a:!V,%b:!V,%c:!V):
%as = "data.domain_elements"(%a) : (!V)->!data.domain<!F>
%bs = "data.domain_elements"(%b) : (!V)->!data.domain<!F>
%cs = "data.domain_elements"(%c) : (!V)->!data.domain<!F>
%zip = "data.domain_zip"(%as,%bs,%cs) : (!data.domain<!F>,!data.domain<!F>,!data.domain<!F>)->!data.domain<!F,!F,!F>
"data.domain_yield"(%zip) : (!data.domain<!F,!F,!F>)->()
}) {sym_name="rows",sym_visibility="private",function_type=(!V,!V,!V)->!data.domain<!F,!F,!F>} : ()->()
func.func private @product(%a:!F,%b:!F,%unused:!F,%s:!F)->!F {
%dead = algebra.field_add %s,%s : (!F,!F)->!F
%p = algebra.field_multiply %a,%b : (!F,!F)->!F
return %p : !F
}
func.func private @row(%scope:!runtime.scope,%a:!F,%b:!F,%c:!F,%xs:!V,%ys:!V,%zs:!V,%s:!F)->!exec.outcome<(!F)> attributes {no_inline,runtime.origin=["row",[]]} {
%attempt = "exec.compute"(%scope,%a,%b,%c,%s) {callee=@product,site="product"} : (!runtime.scope,!F,!F,!F,!F)->!exec.outcome<(!F)>
"exec.dispatch"(%attempt)[^ok,^failed] : (!exec.outcome<(!F)>)->()
^ok(%p:!F):
%result = "exec.returned"(%p) : (!F)->!exec.outcome<(!F)>
func.return %result : !exec.outcome<(!F)>
^failed(%stop:!exec.stop):
%failure = "exec.failed"(%stop) : (!exec.stop)->!exec.outcome<(!F)>
func.return %failure : !exec.outcome<(!F)>
}
)mlir";
std::string fixture() {
  return "!F = !algebra.field<\"koala-bear\">\n!V = "
         "!algebra.field_vector<\"koala-bear\">\n" +
         scopedFixture(declarations, "%a:!V,%b:!V,%c:!V,%s:!F", "%a,%b,%c,%s",
                       "!V,!V,!V,!F", "!F",
                       R"mlir(
%attempt = "exec.collect"(%scope,%a,%b,%c,%s) {domain=@rows,body=@row,site="map"} : (!runtime.scope,!V,!V,!V,!F)->!exec.outcome<(!V)>
"exec.dispatch"(%attempt)[^mapped,^failed] : (!exec.outcome<(!V)>)->()
^mapped(%v:!V):
)mlir" + scopedApply("sum", "sum", "%v", "!V", "%r", "!F") +
                           scopedReturn("%r", "!F"),
                       4);
}
LogicalResult compare(ModuleOp source, ModuleOp candidate,
                      MathematicalSelectionPolicy policy = {true, true, false},
                      const llvm::DenseSet<Operation *> *fixed = nullptr) {
  mathematical::RealizationWork work;
  return protocol::verifyScopedFinitePreparation(source, candidate, work,
                                                 policy, nullptr, fixed);
}
OwningOpRef<ModuleOp>
prepare(ModuleOp source,
        MathematicalSelectionPolicy policy = {true, true, false},
        mathematical::RealizationWork *work = nullptr,
        const llvm::DenseSet<Operation *> *fixed = nullptr,
        const mathematical::MathematicalRecipes &recipes =
            mathematical::mathematicalRecipes()) {
  mathematical::RealizationWork local;
  uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
  std::optional<CapacityCause> capacity;
  return protocol::prepareScopedFinite(source, work ? *work : local, copy,
                                       bytes, capacity, policy, fixed, nullptr,
                                       nullptr, recipes);
}
class Providers final : public target::CandidateCatalog {
public:
  unsigned withheld = 0;
  llvm::Expected<std::vector<std::string>> implementations(
      const protocol::BindingApplication &application) const override {
    if ((withheld >= 1 && application.contract == "vector.dot") ||
        (withheld >= 2 && application.contract == "numerical.sum") ||
        (withheld >= 3 && application.contract == "numerical.map") ||
        (withheld >= 4 && application.contract == "vector.mul"))
      return std::vector<std::string>{};
    return target::installedCandidates().implementations(application);
  }
  std::vector<protocol::BindingApplication>
  conversions(const protocol::BoundType &from,
              const protocol::BoundType &to) const override {
    return target::installedCandidates().conversions(from, to);
  }
};
} // namespace
int main(int argc, char **argv) {
  if (argc == 2 && StringRef(argv[1]) == "--emit") {
    llvm::outs() << fixture();
    return 0;
  }
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry, MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  Cases cases;
  auto parse = [&](StringRef text) {
    auto result = parseSourceString<ModuleOp>(text, &context);
    require(bool(result), "source fixture refused");
    return result;
  };
  auto source = parse(fixture());
  auto candidate = prepare(*source);
  require(bool(candidate), "collection/sum preparation failed");
  for (bool bulk : {false, true})
    for (bool fusion : {false, true})
      cases.run("independent policies bulk=" + std::to_string(bulk) +
                    " fusion=" + std::to_string(fusion),
                [&] {
                  MathematicalSelectionPolicy policy{bulk, fusion, false};
                  auto actual = prepare(*source, policy);
                  require(bool(actual) &&
                              succeeded(compare(*source, *actual, policy)),
                          "independent policy correspondence failed");
                  auto function = sf::function(*actual, "Work");
                  require(sf::applications(function, "vector.dot").size() ==
                              unsigned(fusion),
                          "fusion did not follow its independent policy");
                  require(sf::hasLoop(function) == (!bulk && !fusion),
                          "fusion enabled unrelated bulk lowering");
                });
  cases.run("unused row shape guards precede the original sum site", [&] {
    auto function = sf::function(*candidate, "Work");
    auto lengths = sf::applications(function, "vector.length");
    auto guards = sf::applications(function, "control.require");
    auto dot = sf::application(function, "vector.dot");
    require(lengths.size() == 3 && guards.size() == 2 &&
                lengths[2].getInputs()[0] == function.getArgument(3) &&
                dot.getInputs()[0] == function.getArgument(1) &&
                dot.getInputs()[1] == function.getArgument(2) &&
                dot.getSite() == "sum",
            "row inventory, contraction ports or sum origin changed");
    require(succeeded(compare(*source, *candidate)),
            "original correspondence failed");
  });
  auto mutation = [&](StringRef name,
                      llvm::function_ref<void(ModuleOp)> mutate) {
    cases.run(name, [&] {
      auto actual = sf::clone(*candidate);
      mutate(*actual);
      require(succeeded(verify(*actual)), "mutation must remain admitted");
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      require(failed(compare(*source, *actual)),
              "independent reader accepted mutation");
    });
  };
  mutation("same-type dot input substitution", [&](ModuleOp m) {
    auto dot = sf::application(sf::function(m, "Work"), "vector.dot");
    dot->setOperand(2, dot.getInputs()[0]);
  });
  mutation("ignored row substitution", [&](ModuleOp m) {
    auto function = sf::function(m, "Work");
    sf::applications(function, "vector.length")[2]->setOperand(
        1, function.getArgument(1));
  });
  mutation("drop a shape guard", [&](ModuleOp m) {
    sc::omit(sf::application(sf::function(m, "Work"), "control.require"));
  });
  mutation("replace second guard with first", [&](ModuleOp m) {
    auto guards = sf::applications(sf::function(m, "Work"), "control.require");
    guards[1]->setOperand(1, guards[0].getInputs()[0]);
  });
  mutation("change reduction occurrence", [&](ModuleOp m) {
    sf::application(sf::function(m, "Work"), "vector.dot").setSite("forged");
  });
  mutation("change guard occurrence", [&](ModuleOp m) {
    sf::application(sf::function(m, "Work"), "control.require")
        .setSite("forged");
  });
  mutation("change returned scalar", [&](ModuleOp m) {
    auto function = sf::function(m, "Work");
    sc::returned(function)->setOperand(0, function.getArgument(4));
  });
  cases.run("synchronized helper change cannot justify old candidate", [&] {
    auto before = sf::clone(*source), after = sf::clone(*candidate);
    for (ModuleOp m : {*before, *after}) {
      auto helper = sf::function(m, "product");
      helper.front().back().setOperand(0, helper.getArgument(0));
    }
    require(succeeded(verify(*before)) && succeeded(verify(*after)),
            "source mutation malformed");
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    require(failed(compare(*before, *after)),
            "checker trusted producer's equation");
  });
  cases.run("explicitly fixed native sum retains its application", [&] {
    auto binding = SymbolTable(&source->getBody()->front())
                       .lookup<runtime::BindingOp>("sum");
    llvm::DenseSet<Operation *> fixed{binding};
    auto actual = prepare(*source, {true, true, false}, nullptr, &fixed);
    require(bool(actual) && succeeded(compare(*source, *actual,
                                              {true, true, false}, &fixed)),
            "fixed sum refused");
    require(
        sf::applications(sf::function(*actual, "Work"), "vector.dot").empty() &&
            sf::applications(sf::function(*actual, "Work"), "vector.sum")
                    .size() == 1,
        "fixed sum was replaced");
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    require(failed(compare(*source, *candidate, {true, true, false}, &fixed)),
            "reader ignored explicit sum request");
  });
  cases.run(
      "withheld contraction recipe preserves the ordinary collection", [&] {
        const auto &installed = mathematical::mathematicalRecipes();
        auto *dot = installed.reduction(
            MathematicalIdentity::FieldAdd, MathematicalIdentity::FieldMultiply,
            mathematical::ReductionForm::Contraction);
        require(dot, "missing installed dot recipe");
        SmallVector<mathematical::ReductionRecipe> reductions;
        for (const auto &recipe : installed.reductions)
          if (&recipe != dot)
            reductions.push_back(recipe);
        mathematical::MathematicalRecipes recipes{installed.lanes, reductions};
        auto actual =
            prepare(*source, {true, true, false}, nullptr, nullptr, recipes);
        require(bool(actual) && succeeded(compare(*source, *actual)),
                "withheld recipe fallback failed");
        require(sf::applications(sf::function(*actual, "Work"), "vector.dot")
                    .empty(),
                "withheld recipe emitted");
        require(sf::applications(sf::function(*actual, "Work"), "numerical.sum")
                        .size() == 1,
                "missing summed-expression alternative");
      });
  for (bool bulk : {false, true})
    for (unsigned exhausted : {0u, 1u, 2u})
      cases.run("bounded fallback bulk=" + std::to_string(bulk) +
                    " account=" + std::to_string(exhausted),
                [&] {
                  mathematical::RealizationWork work;
                  if (exhausted == 0)
                    work.matching.structural = 0;
                  if (exhausted == 1)
                    work.optionalFiniteChecking = 0;
                  if (exhausted == 2)
                    work.discardedRecipeCopy = 0;
                  auto actual = prepare(*source, {bulk, true, false}, &work);
                  require(bool(actual),
                          "optional exhaustion prevented ordered endpoint");
                  require(sf::hasLoop(sf::function(*actual, "Work")) &&
                              succeeded(compare(*source, *actual,
                                                {bulk, true, false})),
                          "optional exhaustion lost checked ordered execution");
                });
  for (bool bulk : {false, true})
    cases.run("general summed formula bulk=" + std::to_string(bulk), [&] {
      auto text = replaceText(fixture(), "return %p : !F", "return %dead : !F");
      auto before = parse(text);
      auto after = prepare(*before, {bulk, true, false});
      require(bool(after) &&
                  succeeded(compare(*before, *after, {bulk, true, false})),
              "general formula fusion failed correspondence");
      auto function = sf::function(*after, "Work");
      auto sums = sf::applications(function, "numerical.sum");
      require(sums.size() == 1 && sums[0].getSite() == "sum" &&
                  !sf::hasLoop(function),
              "scalar capture formula did not use summed expression");
    });
  for (unsigned variant : {0u, 1u, 2u})
    cases.run("ineligible consumer=" + std::to_string(variant), [&] {
      auto text = fixture();
      if (variant == 0)
        text = replaceText(text, "contract=\"vector.sum\"",
                           "contract=\"vector.product\"");
      if (variant == 1)
        text = replaceText(
            text, scopedReturn("%r", "!F"),
            scopedApply("sum", "again", "%v", "!V", "%other", "!F") +
                scopedReturn("%r", "!F"));
      if (variant == 2) {
        text = replaceText(text, "func.func private @product",
                           "\"runtime.binding\"() "
                           "{sym_name=\"length\",contract=\"vector.length\","
                           "arguments=[\"koala-bear\"],implementation=\"\"} : "
                           "()->()\nfunc.func private @product");
        text = replaceText(
            text, "%sum_attempt =",
            scopedApply("length", "intervening", "%a", "!V", "%n", "ui64") +
                "%sum_attempt =");
      }
      auto before = parse(text), after = prepare(*before);
      require(bool(after) && succeeded(compare(*before, *after)),
              "ineligible consumer fallback failed");
      auto function = sf::function(*after, "Work");
      require(sf::applications(function, "vector.dot").empty() &&
                  sf::applications(function, "numerical.sum").empty(),
              "custom, escaped or nonadjacent consumer acquired fusion");
    });
  for (bool bulk : {false, true})
    for (unsigned withheld = 0; withheld <= 4; ++withheld)
      cases.run("physical retry bulk=" + std::to_string(bulk) +
                    " withheld=" + std::to_string(withheld),
                [&] {
                  auto module = take(executableFixture(fixture(), context));
                  Providers providers;
                  providers.withheld = withheld;
                  mathematical::RealizationWork work;
                  target::PhysicalPlanOptions options;
                  options.numericalWork = &work;
                  options.numericalPolicy = {bulk, true, false};
                  auto proposal = take(
                      target::proposePhysical(*module, providers, {}, options));
                  auto checked = take(
                      target::validatePhysical(*module, proposal, providers));
                  auto actual = take(checked.cloneSelectedSubject(*module));
                  auto function = sf::function(*actual, "Work");
                  StringRef expected = withheld == 0           ? "vector.dot"
                                       : withheld == 1         ? "numerical.sum"
                                       : withheld == 2 && bulk ? "numerical.map"
                                       : withheld == 3 && bulk ? "vector.mul"
                                                               : "vector.sum";
                  require(sf::applications(function, expected).size() == 1,
                          "wrong surviving numerical alternative");
                  require(sf::hasLoop(function) ==
                              (withheld >= 4 || (!bulk && withheld >= 2)),
                          "retry lost the required ordered endpoint");
                  if (withheld)
                    require(work.discardedRecipeCopy < 1000000,
                            "failed alternatives refunded construction work");
                });
  cases.run("missing lane recipes cannot enable unrequested map lowering", [&] {
    const auto &installed = mathematical::mathematicalRecipes();
    mathematical::MathematicalRecipes recipes{{}, installed.reductions};
    auto after =
        prepare(*source, {false, true, false}, nullptr, nullptr, recipes);
    require(bool(after) &&
                succeeded(compare(*source, *after, {false, true, false})),
            "missing recipe fallback correspondence failed");
    require(
        sf::hasLoop(sf::function(*after, "Work")),
        "fusion policy enabled an ordinary map without finite-bulk permission");
  });
  cases.run("fixed callback application cannot be hidden by fusion", [&] {
    auto text = replaceText(
        fixture(), "func.func private @product",
        "\"runtime.binding\"() "
        "{sym_name=\"multiply\",contract=\"field.mul\",arguments=[\"koala-"
        "bear\"],implementation=\"\"} : ()->()\nfunc.func private @product");
    text = replaceText(
        text,
        "\"exec.compute\"(%scope,%a,%b,%c,%s) "
        "{callee=@product,site=\"product\"} : (!runtime.scope,!F,!F,!F,!F)",
        "\"exec.apply\"(%scope,%a,%b) "
        "{binding=@multiply,parameters=[],site=\"product\"} : "
        "(!runtime.scope,!F,!F)");
    auto before = parse(text), unrestricted = prepare(*before);
    require(
        bool(unrestricted) &&
            sf::applications(sf::function(*unrestricted, "Work"), "vector.dot")
                    .size() == 1,
        "unfixed callback product did not select the contraction");
    auto binding = SymbolTable(&before->getBody()->front())
                       .lookup<runtime::BindingOp>("multiply");
    llvm::DenseSet<Operation *> fixed{binding};
    auto after = prepare(*before, {true, true, false}, nullptr, &fixed);
    require(
        bool(after) &&
            succeeded(compare(*before, *after, {true, true, false}, &fixed)) &&
            sf::hasLoop(sf::function(*after, "Work")),
        "fixed callback lost ordered execution");
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    require(
        failed(compare(*before, *unrestricted, {true, true, false}, &fixed)),
        "independent reader ignored the callback implementation request");
  });
  return cases.result();
}
