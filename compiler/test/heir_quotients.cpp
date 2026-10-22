#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/Parser/Parser.h"
#include "support/KernelRecipes.h"
#include "zkc/Dialect/Registry.h"
#include "llvm/Support/raw_ostream.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using zkc::test::require;
namespace {
Operation *first(Operation *owner, StringRef name) {
  Operation *found = nullptr;
  owner->walk([&](Operation *op) {
    if (!found && op->getName().getStringRef() == name)
      found = op;
  });
  require(found, "missing mutation target");
  return found;
}
unsigned occurrences(Operation *owner, StringRef name) {
  unsigned result = 0;
  owner->walk(
      [&](Operation *op) { result += op->getName().getStringRef() == name; });
  return result;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto module = parseSourceString<ModuleOp>(R"mlir(
    !R = !algebra.quotient<17,4>
    !I = !algebra.indices
    module { func.func private @compute(%a:!I,%b:!I,%x:!I)->(!I,!I,!I,!I) {
      %pa = algebra.quotient_project %a : (!I)->!R
      %pb = algebra.quotient_project %b : (!I)->!R
      %px = algebra.quotient_project %x : (!I)->!R
      %ax = algebra.quotient_multiply %pa,%px : (!R,!R)->!R
      %bx = algebra.quotient_multiply %pb,%px : (!R,!R)->!R
      %sum = algebra.quotient_add %ax,%bx : (!R,!R)->!R
      %diff = algebra.quotient_subtract %ax,%bx : (!R,!R)->!R
      %s = algebra.quotient_coefficients %sum : (!R)->!I
      %d = algebra.quotient_coefficients %diff : (!R)->!I
      %v = algebra.quotient_coefficients %px : (!R)->!I
      return %s,%d,%v,%s : !I,!I,!I,!I
    } })mlir",
                                            &context);
  require(bool(module), "source did not parse");
  auto unit = zkc::test::kernelRecipeSource(*module, "compute", "entry");
  auto snapshot =
      OwningOpRef<kernel::ModuleOp>(cast<kernel::ModuleOp>(unit->clone()));
  mathematical::RealizationWork work;
  auto candidate = zkc::test::realizeKernelEntry(*unit, "quotient", {}, work);
  zkc::test::Cases cases;
  cases.run("shared transforms, ordered and aliased outputs", [&] {
    require(bool(candidate), "HEIR candidate construction failed");
    require(
        succeeded(kernel::verifyEntryRecipes(*unit, *candidate, "quotient")),
        "HEIR native reader failed");
    require(occurrences(*candidate, "algebra.exec.quotient_ntt") == 3,
            "shared input transform was not reused");
    require(occurrences(*candidate, "algebra.exec.quotient_intt") == 2,
            "compound output placement differs");
    require(occurrences(*candidate, "algebra.exec.quotient_multiply") == 0,
            "compound product did not use evaluation multiplication");
    require(OperationEquivalence::isEquivalentTo(
                *unit, *snapshot, OperationEquivalence::IgnoreLocations),
            "retained quotient source changed");
    require(work.quotientPlacements == 15 &&
                work.quotientConstruction < 100000 &&
                work.quotientInspection < 1000000,
            "optional planning work was not charged");
  });
  for (StringRef mutation :
       {"modulus", "degree", "root", "inverse", "basis", "operand", "return",
        "binding", "implementation", "parameters", "site", "output-position",
        "unprojected"})
    cases.run(mutation, [&] {
      require(bool(candidate), "missing candidate");
      auto changed = OwningOpRef<ModuleOp>(cast<ModuleOp>(candidate->clone()));
      OpBuilder builder(&context);
      auto *project = first(*changed, "algebra.exec.quotient_project");
      auto *forward = first(*changed, "algebra.exec.quotient_ntt");
      auto *inverse = first(*changed, "algebra.exec.quotient_intt");
      auto *product = first(*changed, "algebra.exec.quotient_pointwise");
      if (mutation == "modulus" || mutation == "degree") {
        auto *literal =
            project->getOperand(mutation == "modulus" ? 1 : 2).getDefiningOp();
        literal->setAttr(
            "parameters",
            builder.getStrArrayAttr({mutation == "modulus" ? "97" : "8"}));
      } else if (mutation == "root") {
        forward->getOperand(2).getDefiningOp()->setAttr(
            "parameters", builder.getStrArrayAttr({"1"}));
      } else if (mutation == "inverse") {
        inverse->setOperand(2, forward->getOperand(2));
      } else if (mutation == "basis") {
        builder.setInsertionPoint(forward);
        auto *root = builder.clone(*forward->getOperand(2).getDefiningOp());
        auto old =
            forward->getOperand(2).getDefiningOp()->getAttrOfType<ArrayAttr>(
                "parameters");
        auto value = std::stoull(cast<StringAttr>(old[0]).getValue().str());
        root->setAttr("parameters",
                      builder.getStrArrayAttr({std::to_string(17 - value)}));
        root->setAttr("site", builder.getStringAttr(
                                  zkc::test::kernelRecipeSite("quotient", 0) +
                                  "_recipe_quotient_changed_basis"));
        forward->setOperand(2, root->getResult(0));
      } else if (mutation == "operand") {
        product->setOperand(0, product->getOperand(1));
      } else if (mutation == "unprojected") {
        forward->setOperand(0, project->getOperand(0));
      } else if (mutation == "return") {
        auto *returned = first(*changed, "local.return");
        returned->setOperand(0, returned->getOperand(1));
      } else if (mutation == "site") {
        forward->setAttr("site", builder.getStringAttr("another_occurrence"));
      } else if (mutation == "output-position") {
        auto *returned = first(*changed, "local.return");
        auto *output = returned->getOperand(0).getDefiningOp();
        output->setAttr("site", builder.getStringAttr(
                                    zkc::test::kernelRecipeSite("quotient", 0) +
                                    "_recipe_quotient_outputs_1_3"));
      } else if (mutation == "parameters") {
        forward->setAttr("parameters", builder.getStrArrayAttr({"1"}));
      } else {
        auto owner = zkc::test::kernelRecipeOutput(*changed);
        auto binding = SymbolTable(owner).lookup<local::OperationBindingOp>(
            product->getAttrOfType<FlatSymbolRefAttr>("binding").getValue());
        if (mutation == "binding")
          binding.setContract("quotient.multiply");
        else
          binding.setImplementation("native/quotient.pointwise");
      }
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      require(failed(kernel::verifyEntryRecipes(*unit, *changed, "quotient")),
              "mutated HEIR execution accepted");
    });
  for (StringRef limit :
       {"placements", "inspection", "construction", "site-bytes"})
    cases.run(limit, [&] {
      mathematical::RealizationWork limited;
      if (limit == "placements")
        limited.quotientPlacements = 0;
      if (limit == "inspection")
        limited.quotientInspection = 1;
      if (limit == "construction")
        limited.quotientConstruction = 0;
      if (limit == "site-bytes")
        limited.quotientSiteBytes = 0;
      auto fallback =
          zkc::test::realizeKernelEntry(*unit, "quotient", {}, limited);
      require(bool(fallback),
              "optional HEIR refusal lost coefficient fallback");
      require(occurrences(*fallback, "algebra.exec.quotient_ntt") == 0 &&
                  occurrences(*fallback, "algebra.exec.quotient_multiply") == 2,
              "coefficient fallback changed");
    });
  cases.run("caller input aliases share the same mathematical assignment", [&] {
    require(bool(candidate), "missing candidate");
    auto changed = OwningOpRef<ModuleOp>(cast<ModuleOp>(candidate->clone()));
    auto owner = zkc::test::kernelRecipeOutput(*changed);
    auto target = SymbolTable(owner).lookup<local::FuncOp>("entry");
    target.getArgument(0).replaceAllUsesWith(target.getArgument(1));
    SmallVector<Value> arguments{target.getArgument(1), target.getArgument(1),
                                 target.getArgument(2)};
    auto source = SymbolTable(*unit).lookup<func::FuncOp>("entry");
    auto *cursor = &target.getBody().front().front();
    uint64_t remaining = 1000000, bytes = 16 * 1024 * 1024;
    finite::VerificationResult outcome{finite::VerificationStatus::Mismatch,
                                       {}};
    auto outputs =
        kernel::verifyKernelRecipes(source, owner, "quotient", arguments,
                                    cursor, remaining, bytes, {}, {}, outcome);
    require(succeeded(outputs) && isa<local::ReturnOp>(cursor) &&
                cursor->getOperands() == ValueRange(*outputs),
            "aliased actual arguments rejected");
  });
  for (auto profile :
       {std::tuple{12289, 512, 1}, std::tuple{8380417, 256, 4}}) {
    const int q = std::get<0>(profile), n = std::get<1>(profile),
              rows = std::get<2>(profile);
    cases.run("module product " + std::to_string(q), [&] {
      const unsigned columns = 4, captures = rows * columns + columns;
      std::string text;
      raw_string_ostream stream(text);
      stream
          << "!R = !algebra.quotient<" << q << "," << n
          << ">\n!I = !algebra.indices\nmodule { func.func private @compute(";
      for (unsigned i = 0; i < captures; ++i)
        stream << (i ? "," : "") << "%a" << i << ":!I";
      stream << ")->(";
      for (int i = 0; i < rows; ++i)
        stream << (i ? "," : "") << "!I";
      stream << "){\n";
      for (unsigned i = 0; i < captures; ++i)
        stream << "%p" << i << " = algebra.quotient_project %a" << i
               << " : (!I)->!R\n";
      for (int i = 0; i < rows; ++i) {
        std::string sum;
        for (unsigned j = 0; j < columns; ++j) {
          auto term = "m" + std::to_string(i * columns + j);
          stream << "%" << term << " = algebra.quotient_multiply %p"
                 << i * columns + j << ",%p" << rows * columns + j
                 << " : (!R,!R)->!R\n";
          if (j) {
            auto next = "s" + std::to_string(i * columns + j);
            stream << "%" << next << " = algebra.quotient_add %" << sum << ",%"
                   << term << " : (!R,!R)->!R\n";
            sum = next;
          } else
            sum = term;
        }
        stream << "%o" << i << " = algebra.quotient_coefficients %" << sum
               << " : (!R)->!I\n";
      }
      stream << "return ";
      for (int i = 0; i < rows; ++i)
        stream << (i ? "," : "") << "%o" << i;
      stream << " : ";
      for (int i = 0; i < rows; ++i)
        stream << (i ? "," : "") << "!I";
      stream << "} }";
      auto workload = parseSourceString<ModuleOp>(text, &context);
      require(bool(workload), "module source did not parse");
      auto input = zkc::test::kernelRecipeSource(*workload, "compute", "entry");
      mathematical::RealizationWork moduleWork;
      auto realized =
          zkc::test::realizeKernelEntry(*input, "module", {}, moduleWork);
      require(bool(realized), "module placement failed");
      require(
          succeeded(kernel::verifyEntryRecipes(*input, *realized, "module")),
          "module candidate did not match retained source");
      require(occurrences(*realized, "algebra.exec.quotient_ntt") == captures &&
                  occurrences(*realized, "algebra.exec.quotient_intt") ==
                      unsigned(rows) &&
                  occurrences(*realized, "algebra.exec.quotient_multiply") == 0,
              "module did not retain the globally shared transform schedule");
    });
  }
  return cases.result();
}
