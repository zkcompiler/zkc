#include "../lib/Transforms/ComputationSelection.h"
#include "../lib/Transforms/RecipeRealizations.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Finite.h"
#include "zkc/Transforms/NestedContractions.h"
#include <fstream>
#include <sstream>
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
std::string fixture(StringRef name) {
  std::ifstream input(std::string(ZKC_FINITE_FIXTURES) + "/" + name.str() +
                      ".mlir");
  require(bool(input), "missing finite fixture");
  std::ostringstream text;
  text << input.rdbuf();
  return text.str();
}
finite::Computation computation(ModuleOp module) {
  Operation *found = nullptr;
  module.walk([&](Operation *op) {
    if (finite::isComputation(op))
      found = op;
  });
  require(found, "missing computation");
  finite::Computation result;
  require(succeeded(finite::describe(found, result)), "invalid computation");
  return result;
}
OwningOpRef<ModuleOp> clone(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}
bool equivalent(ModuleOp left, ModuleOp right) {
  return OperationEquivalence::isEquivalentTo(
      left, right, OperationEquivalence::IgnoreLocations);
}
bool hasKernel(ModuleOp module, StringRef contract) {
  bool found = false;
  module.walk([&](Operation *op) {
    found |=
        op->getName().getStringRef() == protocol::boundOperationName(contract);
  });
  return found;
}
bool hasStatefulLoop(ModuleOp module, StringRef name) {
  bool found = false;
  module.walk([&](local::FuncOp function) {
    if (function.getSymName() == name)
      function.walk([&](local::LocalForOp loop) {
        // Product cardinality admission retains empty, zero-trip bound checks
        // even in a bulk realization. Only payload iteration carries state.
        found |= loop->getNumResults() != 0;
      });
  });
  return found;
}
llvm::SmallVector<mathematical::MatrixContractionRecipe>
withoutMatrixForm(mathematical::MatrixContractionForm form) {
  llvm::SmallVector<mathematical::MatrixContractionRecipe> result;
  for (const auto &recipe :
       mathematical::mathematicalRecipes().matrixContractions)
    if (recipe.form != form)
      result.push_back(recipe);
  return result;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  using namespace mathematical;
  const MathematicalRecipes absent{{}, {}};
  cases.run("two-member inventory has no implicit matrix recipes", [&] {
    const auto &installed = mathematicalRecipes();
    const MathematicalRecipes original{installed.lanes, installed.reductions};
    require(original.matrixContractions.empty() &&
                original.lane(MathematicalIdentity::FieldAdd) &&
                original.reduction(MathematicalIdentity::FieldAdd,
                                   MathematicalIdentity::FieldMultiply,
                                   ReductionForm::Contraction),
            "two-member inventory silently installed additional recipes");
    require(installed.matrixContractions.size() == 3,
            "installed matrix inventory is incomplete");
  });
  cases.run("bilinear withheld recipe retains checked ordered fallback", [&] {
    auto source = parseSourceString<ModuleOp>(fixture("bilinear"), &context);
    require(bool(source) && succeeded(verify(*source)),
            "bilinear fixture refused");
    auto c = computation(*source);
    const auto &installed = mathematicalRecipes();
    auto matrices = withoutMatrixForm(MatrixContractionForm::Bilinear);
    const MathematicalRecipes withheld{installed.lanes, installed.reductions,
                                       matrices};
    auto selected = selectComputation(c, {});
    auto missing = selectComputation(c, {}, withheld);
    require(selected.kind == RealizationKind::Bilinear && selected.matrix &&
                selected.outcome == SelectionOutcome::Selected &&
                selected.matrix->target == "matrix.bilinear" &&
                selected.matrix->seedCombiner == "field.add" &&
                missing.kind == RealizationKind::Ordered && !missing.matrix &&
                missing.outcome == SelectionOutcome::MissingRecipe &&
                missing.equations.bilinear &&
                missing.equations.bilinear->matrix ==
                    selected.equations.bilinear->matrix &&
                missing.equations.bilinear->left ==
                    selected.equations.bilinear->left &&
                missing.equations.bilinear->right ==
                    selected.equations.bilinear->right,
            "missing bilinear recipe changed recognition or selected a target");
    auto present = clone(*source), fallback = clone(*source);
    auto defaultInventory = clone(*source);
    require(
        succeeded(finite::realizeLocals(*present, {}, nullptr, installed)) &&
            succeeded(finite::realizeLocals(*defaultInventory)),
        "installed bilinear recipe realization failed");
    require(equivalent(*present, *defaultInventory),
            "explicit installed inventory changed default bilinear output");
    require(succeeded(finite::verifyRealizations(*source, *present)),
            "installed bilinear recipe failed independent correspondence");
    require(hasKernel(*present, "matrix.bilinear") &&
                !hasStatefulLoop(*present, "fold"),
            "installed bilinear recipe did not replace payload iteration");
    require(
        succeeded(finite::realizeLocals(*fallback, {}, nullptr, withheld)) &&
            succeeded(verify(*fallback)) &&
            succeeded(finite::verifyRealizations(*source, *fallback)) &&
            hasStatefulLoop(*fallback, "fold") &&
            !hasKernel(*fallback, "matrix.bilinear"),
        "withheld bilinear recipe failed independently checked ordered path");
  });
  for (bool columns : {false, true})
    cases.run(
        columns ? "withheld column matvec recipe"
                : "withheld row matvec recipe",
        [&] {
          auto text = fixture("nested-matrix");
          if (columns)
            for (auto [before, after] :
                 {std::pair{"domain_matrix_row", "domain_matrix_column"},
                  {"axis=0:i64", "axis=1:i64"}}) {
              auto position = text.find(before);
              require(position != std::string::npos,
                      "column fixture edit missing");
              text.replace(position, StringRef(before).size(), after);
            }
          auto source = parseSourceString<ModuleOp>(text, &context);
          require(bool(source) && succeeded(verify(*source)),
                  "matvec fixture refused");
          auto view = finite::analyzeComputation(computation(*source));
          require(bool(view), "nested structural view missing");
          auto form = columns ? MatrixContractionForm::Columns
                              : MatrixContractionForm::Rows;
          const auto &installed = mathematicalRecipes();
          auto matrices = withoutMatrixForm(form);
          const MathematicalRecipes withheld{installed.lanes,
                                             installed.reductions, matrices};
          auto selected = selectNestedContraction(*view);
          auto missing = selectNestedContraction(*view, withheld);
          StringRef target =
              columns ? "matrix.transpose_mul_vector" : "matrix.mul_vector";
          require(
              selected.recipe && selected.recipe->target == target &&
                  selected.outcome == SelectionOutcome::Selected &&
                  selected.recipe->seedCombiner == "vector.add" &&
                  selected.equation && missing.equation && !missing.recipe &&
                  missing.outcome == SelectionOutcome::MissingRecipe &&
                  missing.equation->axis == unsigned(columns) &&
                  missing.equation->matrix == selected.equation->matrix &&
                  missing.equation->vector == selected.equation->vector &&
                  missing.equation->seed.input ==
                      selected.equation->seed.input &&
                  missing.equation->seed.constant ==
                      selected.equation->seed.constant,
              "withheld matvec recipe changed equation or selected a target");
          auto present = clone(*source), fallback = clone(*source);
          auto defaultInventory = clone(*source);
          require(succeeded(nested::rewriteFiniteCollections(*present, {},
                                                             installed)) &&
                      succeeded(nested::rewriteFiniteCollections(
                          *defaultInventory)) &&
                      equivalent(*present, *defaultInventory) &&
                      succeeded(
                          nested::verifyFiniteCollections(*source, *present)) &&
                      hasKernel(*present, target),
                  "installed matvec recipe changed default output or "
                  "correspondence");
          require(
              succeeded(
                  nested::rewriteFiniteCollections(*fallback, {}, withheld)) &&
                  equivalent(*source, *fallback) &&
                  succeeded(
                      nested::verifyFiniteCollections(*source, *fallback)),
              "withheld matvec recipe failed independent identity checking");
          auto beforeFinite = clone(*fallback);
          require(succeeded(finite::realizeLocals(*fallback, {}, nullptr,
                                                  withheld)) &&
                      succeeded(verify(*fallback)) &&
                      succeeded(finite::verifyRealizations(*beforeFinite,
                                                           *fallback)) &&
                      hasStatefulLoop(*fallback, "all_rows") &&
                      !hasKernel(*fallback, "matrix.mul_vector") &&
                      !hasKernel(*fallback, "matrix.transpose_mul_vector"),
                  "withheld matvec recipe failed independently checked ordered "
                  "path");
        });
  for (auto [name, target] : {std::pair{"sum", "vector.sum"},
                              {"product", "vector.product"},
                              {"dot", "vector.dot"},
                              {"msm-direct", "curve.msm"},
                              {"matrix-row", "matrix.row_dot"},
                              {"matrix-column", "matrix.column_dot"}})
    cases.run(name, [&, name = name, target = target] {
      auto module = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(module), "fixture refused");
      auto c = computation(*module);
      auto selected = selectComputation(c, {});
      require(selected.kind == RealizationKind::Reduction &&
                  selected.reduction &&
                  selected.reduction->recipe->target == target,
              "native reduction recipe not selected");
      auto withheld = selectComputation(c, {}, absent);
      require(withheld.kind == RealizationKind::Ordered &&
                  withheld.outcome == SelectionOutcome::MissingRecipe &&
                  !withheld.reduction && withheld.view &&
                  withheld.equations.reduction &&
                  withheld.equations.reduction->combine ==
                      selected.equations.reduction->combine &&
                  withheld.equations.reduction->inputs ==
                      selected.equations.reduction->inputs,
              "withheld recipe erased mathematical recognition or invented a "
              "target");
      if (StringRef(name) == "msm-direct")
        require(selected.equations.reduction->inputs ==
                        SmallVector<unsigned>({0, 1}) &&
                    selected.reduction->inputs ==
                        SmallVector<unsigned>({1, 0}) &&
                    selected.reduction->staticSourceInput == 0,
                "group/scalar semantic roles confused with native MSM order");
      if (StringRef(name).starts_with("matrix-")) {
        auto *term = selected.equations.reduction->term.getDefiningOp();
        Value left = term->getOperand(0), right = term->getOperand(1);
        term->setOperands({right, left});
        selected = selectComputation(c, {});
        require(selected.kind == RealizationKind::Reduction &&
                    selected.equations.reduction->inputs ==
                        SmallVector<unsigned>({1, 0}) &&
                    selected.equations.reduction->matrixOperand == 1 &&
                    selected.reduction->inputs ==
                        SmallVector<unsigned>({0, 1}) &&
                    selected.reduction->selectedIndex == 3 &&
                    selected.reduction->staticSourceInput == 0,
                "matrix semantic role or selected native mapping changed");
      }
    });
  cases.run("disabled selection preserves recipe-free equations", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("dot"), &context);
    auto c = computation(*module);
    auto disabled = selectComputation(c, {false, false}, absent);
    require(disabled.view && disabled.equations.reduction &&
                disabled.outcome == SelectionOutcome::PolicyDisabled &&
                disabled.kind == RealizationKind::Ordered &&
                !disabled.reduction &&
                disabled.equations.reduction->witness.yielded ==
                    disabled.view->result &&
                disabled.equations.reduction->witness.seed.formal ==
                    disabled.view->seeds[0].formal,
            "selection policy erased source equation or exact witness");
  });
  cases.run("lane recognition with withheld recipes", [&] {
    auto module =
        parseSourceString<ModuleOp>(fixture("total-collect"), &context);
    require(bool(module), "collect refused");
    auto c = computation(*module);
    auto present = selectComputation(c, {});
    auto withheld = selectComputation(c, {}, absent);
    require(present.kind == RealizationKind::Elementwise &&
                present.outcome == SelectionOutcome::Selected &&
                withheld.outcome == SelectionOutcome::MissingRecipe &&
                withheld.kind == RealizationKind::Ordered && withheld.view &&
                withheld.equations.elementwise &&
                withheld.view->result == present.view->result,
            "withheld lane recipe changed semantic formula recognition");
  });
  cases.run("pinned meaning is recognized and retained", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("sum"), &context);
    require(bool(module), "sum refused");
    auto c = computation(*module);
    auto &operation = c.helper->getRegion(0).front().front();
    auto binding = operation.getAttrOfType<FlatSymbolRefAttr>("binding");
    auto declaration =
        SymbolTable::lookupNearestSymbolFrom<local::OperationBindingOp>(
            &operation, binding);
    require(bool(declaration), "missing scalar binding");
    declaration.setImplementation("arkworks/field.add");
    require(succeeded(verify(*module)),
            "pinned scalar binding is not admitted");
    auto selected = selectComputation(c, {});
    require(selected.view && selected.equations.reduction &&
                selected.outcome == SelectionOutcome::ReplacementRestricted &&
                !canReplacePayload(*selected.view) &&
                selected.kind == RealizationKind::Ordered &&
                finite::semantics(&operation) &&
                !finite::replaceable(&operation),
            "explicit implementation erased meaning or permitted replacement");
    OwningOpRef<ModuleOp> candidate(cast<ModuleOp>((*module)->clone()));
    require(succeeded(finite::realizeLocals(*candidate)) &&
                succeeded(finite::verifyRealizations(*module, *candidate)),
            "pinned ordered fallback failed independent checking");
    bool retained = false;
    candidate->walk([&](local::OperationBindingOp op) {
      retained |= op.getContract() == "field.add" &&
                  op.getImplementation() == "arkworks/field.add";
    });
    require(retained, "pinned implementation disappeared");
    // An unavailable pin is still mathematically identifiable, but ordinary
    // binding admission rejects it. Analysis is not physical admission.
    declaration.setImplementation("withheld/field.add");
    require(finite::semantics(&operation) && !finite::replaceable(&operation),
            "unavailable provider erased meaning");
    auto physical = protocol::operationBinding(&operation);
    require(!physical, "unknown physical implementation gained admission");
    llvm::consumeError(physical.takeError());
  });
  cases.run(
      "nested equation recognition preserves implementation constraints", [&] {
        auto module =
            parseSourceString<ModuleOp>(fixture("nested-matrix"), &context);
        auto c = computation(*module);
        auto view = finite::analyzeComputation(c);
        require(view && matchNestedContraction(*view) &&
                    canReplaceNestedContraction(*view),
                "nested equation missing");
        Operation *add = view->nested[0].payload.back();
        auto declaration =
            SymbolTable::lookupNearestSymbolFrom<local::OperationBindingOp>(
                add, add->getAttrOfType<FlatSymbolRefAttr>("binding"));
        declaration.setImplementation("arkworks/field.add");
        require(succeeded(verify(*module)), "nested pin is not admitted");
        view = finite::analyzeComputation(c);
        require(view && matchNestedContraction(*view) &&
                    !canReplaceNestedContraction(*view),
                "nested pin erased the equation or permitted replacement");
        auto selected = selectNestedContraction(*view);
        require(selected.equation && !selected.recipe &&
                    selected.outcome == SelectionOutcome::ReplacementRestricted,
                "nested pin did not explain its selection restriction");
      });
  cases.run("indexed group access retains ordered fallback", [&] {
    auto source = fixture("msm-direct");
    auto replace = [&](StringRef before, StringRef after) {
      auto position = source.find(before.str());
      require(position != std::string::npos,
              "indexed group fixture edit missing");
      source.replace(position, before.size(), after.str());
    };
    replace("module { \"protocol.module\"() ({",
            R"mlir(module { "protocol.module"() ({
 "local.binding"() {sym_name="get",contract="curve.get",arguments=["bls12-381.g1"],implementation=""} : ()->()
)mlir");
    replace(
        R"mlir(%p = "data.domain_elements"(%points) : (!GS)->!data.domain<!G>)mlir",
        R"mlir(%p = "data.domain_indices"(%points) {axis=0:i64} : (!GS)->!data.domain<ui64>)mlir");
    replace(
        R"mlir(%d = "data.domain_zip"(%p,%s) : (!data.domain<!G>,!data.domain<!F>)->!data.domain<!G,!F>)mlir",
        R"mlir(%d = "data.domain_zip"(%p,%s) : (!data.domain<ui64>,!data.domain<!F>)->!data.domain<ui64,!F>)mlir");
    replace("data.domain_yield\"(%d) : (!data.domain<!G,!F>)",
            "data.domain_yield\"(%d) : (!data.domain<ui64,!F>)");
    replace("function_type=(!GS,!V)->!data.domain<!G,!F>",
            "function_type=(!GS,!V)->!data.domain<ui64,!F>");
    replace("%state:!G,%point:!G,%scalar:!F",
            "%state:!G,%index:ui64,%scalar:!F");
    replace(
        R"mlir(   %term = "algebra.exec.group_scale")mlir",
        R"mlir(   %point = "algebra.exec.group_get"(%points,%index) {binding=@get,parameters=[],site="get"} : (!GS,ui64)->!G
   %term = "algebra.exec.group_scale")mlir");
    auto module = parseSourceString<ModuleOp>(source, &context);
    require(bool(module) && succeeded(verify(*module)),
            "indexed group control not admitted");
    auto selected = selectComputation(computation(*module), {});
    require(selected.view && !selected.equations.reduction &&
                selected.outcome == SelectionOutcome::UnsupportedEquation &&
                selected.kind == RealizationKind::Ordered,
            "indexed group access acquired an unsupported bulk equation");
    OwningOpRef<ModuleOp> candidate(cast<ModuleOp>((*module)->clone()));
    require(succeeded(finite::realizeLocals(*candidate)) &&
                succeeded(finite::verifyRealizations(*module, *candidate)),
            "indexed group fallback failed independent correspondence");
    bool loop = false, lookup = false;
    candidate->walk([&](Operation *op) {
      loop |= isa<local::LocalForOp>(op);
      lookup |= op->getName().getStringRef() == "algebra.exec.group_get";
    });
    require(loop && lookup,
            "indexed group fallback lost ordered iteration or group lookup");
  });
  cases.run(
      "recognized group sum has no direct recipe and executes fallback", [&] {
        auto module =
            parseSourceString<ModuleOp>(fixture("msm-direct"), &context);
        require(bool(module), "group fixture refused");
        auto c = computation(*module);
        auto &body = c.helper->getRegion(0).front();
        auto &scale = body.front();
        scale.getResult(0).replaceAllUsesWith(scale.getOperand(0));
        scale.erase();
        require(succeeded(verify(*module)), "group sum control not admitted");
        auto selected = selectComputation(c, {});
        require(selected.view && selected.equations.reduction &&
                    selected.equations.reduction->combine ==
                        MathematicalIdentity::GroupAdd &&
                    !selected.equations.reduction->termIdentity &&
                    selected.kind == RealizationKind::Ordered &&
                    !selected.reduction,
                "group sum was not recognized independently of missing direct "
                "recipe");
        OwningOpRef<ModuleOp> candidate(cast<ModuleOp>((*module)->clone()));
        require(succeeded(finite::realizeLocals(*candidate)) &&
                    succeeded(finite::verifyRealizations(*module, *candidate)),
                "missing-recipe ordered fallback failed independent checking");
        bool loop = false;
        candidate->walk([&](local::LocalForOp) { loop = true; });
        require(loop,
                "missing direct group recipe did not retain an ordered loop");
      });
  return cases.result();
}
