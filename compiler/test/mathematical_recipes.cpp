#include "../lib/Transforms/ComputationSelection.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Finite.h"
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
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  using namespace mathematical;
  const MathematicalRecipes absent{{}, {}};
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
                  !withheld.reduction && withheld.view &&
                  withheld.view->reduction &&
                  withheld.view->reduction->combine ==
                      selected.view->reduction->combine &&
                  withheld.view->reduction->inputs ==
                      selected.view->reduction->inputs,
              "withheld recipe erased mathematical recognition or invented a "
              "target");
      if (StringRef(name) == "msm-direct")
        require(
            selected.view->reduction->inputs == SmallVector<unsigned>({0, 1}) &&
                selected.reduction->inputs == SmallVector<unsigned>({1, 0}) &&
                selected.reduction->staticSourceInput == 0,
            "group/scalar semantic roles confused with native MSM order");
      if (StringRef(name).starts_with("matrix-")) {
        auto *term = selected.view->reduction->term.getDefiningOp();
        Value left = term->getOperand(0), right = term->getOperand(1);
        term->setOperands({right, left});
        selected = selectComputation(c, {});
        require(selected.kind == RealizationKind::Reduction &&
                    selected.view->reduction->inputs ==
                        SmallVector<unsigned>({1, 0}) &&
                    selected.view->reduction->matrixOperand == 1 &&
                    selected.reduction->inputs ==
                        SmallVector<unsigned>({0, 1}) &&
                    selected.reduction->selectedIndex == 3 &&
                    selected.reduction->staticSourceInput == 0,
                "matrix semantic role or selected native mapping changed");
      }
    });
  cases.run("lane recognition with withheld recipes", [&] {
    auto module =
        parseSourceString<ModuleOp>(fixture("total-collect"), &context);
    require(bool(module), "collect refused");
    auto c = computation(*module);
    auto present = selectComputation(c, {});
    auto withheld = selectComputation(c, {}, absent);
    require(present.kind == RealizationKind::Elementwise &&
                withheld.kind == RealizationKind::Ordered && withheld.view &&
                withheld.view->elementwise &&
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
    require(selected.view && selected.view->reduction &&
                !selected.view->replaceable &&
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
    require(selected.view && !selected.view->reduction &&
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
        require(selected.view && selected.view->reduction &&
                    selected.view->reduction->combine ==
                        MathematicalIdentity::GroupAdd &&
                    !selected.view->reduction->termIdentity &&
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
