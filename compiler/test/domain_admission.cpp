#include "mlir/IR/Verifier.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Transforms/Passes.h"
#include "support/NativeCases.h"
#include "support/ScopedFinite.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/IR.h"
#include <fstream>
#include <sstream>
#include <vector>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;

namespace {
// Both equal-looking element descriptors are live in the returned zip. The
// other constructors are unused, but their admission still belongs to the body.
const char *constructors = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
!M = !data.field_matrix<"bls12-381.fr">
module { "protocol.module"() ({
  "data.domain"() ({
  ^entry(%xs: !V, %matrix: !M, %lower: ui64, %upper: ui64, %selector: ui64):
    %elements = "data.domain_elements"(%xs) : (!V) -> !data.domain<!F>
    %same = "data.domain_elements"(%xs) : (!V) -> !data.domain<!F>
    %indices = "data.domain_indices"(%xs) {axis = 0 : i64} : (!V) -> !data.domain<ui64>
    %range = "data.domain_range"(%lower, %upper) : (ui64, ui64) -> !data.domain<ui64>
    %row = "data.domain_matrix_row"(%matrix, %selector) : (!M, ui64) -> !data.domain<!F>
    %column = "data.domain_matrix_column"(%matrix, %selector) : (!M, ui64) -> !data.domain<!F>
    %rows = "data.domain_matrix_coordinates"(%matrix) {order = "row_major"} : (!M) -> !data.domain<ui64, ui64>
    %columns = "data.domain_matrix_coordinates"(%matrix) {order = "column_major"} : (!M) -> !data.domain<ui64, ui64>
    %product = "data.domain_product"(%indices, %range) : (!data.domain<ui64>, !data.domain<ui64>) -> !data.domain<ui64, ui64>
    %unused = "data.domain_zip"(%row, %column) : (!data.domain<!F>, !data.domain<!F>) -> !data.domain<!F, !F>
    %result = "data.domain_zip"(%elements, %same) : (!data.domain<!F>, !data.domain<!F>) -> !data.domain<!F, !F>
    "data.domain_yield"(%result) : (!data.domain<!F, !F>) -> ()
  }) {sym_name = "items", sym_visibility = "private", function_type = (!V, !M, ui64, ui64, ui64) -> !data.domain<!F, !F>} : () -> ()
  "protocol.func"() ({
    "protocol.return"() : () -> ()
  }) {sym_name = "main", function_type = () -> (), roles = ["P"], input_roles = [], output_roles = []} : () -> ()
}) {profile = #protocol.profile<protocol>} : () -> () }
)mlir";

std::string fixture(StringRef name) {
  std::ifstream input(std::string(ZKC_FINITE_FIXTURES) + "/" + name.str() +
                      ".mlir");
  require(bool(input), "missing finite fixture " + name);
  std::ostringstream text;
  text << input.rdbuf();
  return text.str();
}

std::vector<std::string> domains(ModuleOp module) {
  std::vector<std::string> result;
  module.walk([&](data::DomainOp domain) {
    std::string text;
    llvm::raw_string_ostream stream(text);
    domain->print(stream, OpPrintingFlags().useLocalScope());
    result.push_back(std::move(text));
  });
  require(!result.empty(), "fixture has no domains");
  return result;
}

void simplify(ModuleOp module, StringRef pipeline) {
  PassManager manager(module.getContext());
  if (pipeline == "canonicalize")
    manager.addPass(createCanonicalizerPass());
  else if (pipeline == "cse")
    manager.addPass(createCSEPass());
  else {
    // Exercise both orders, including another DCE round after CSE.
    manager.addPass(createCanonicalizerPass());
    manager.addPass(createCSEPass());
    manager.addPass(createCanonicalizerPass());
  }
  require(succeeded(manager.run(module)), "generic simplification failed");
  require(succeeded(zkc::admitStage(module)),
          "simplified module was not admitted");
}

void preservesDomains(StringRef source, MLIRContext &context,
                      StringRef pipeline, bool realize) {
  auto original = parseSourceString<ModuleOp>(source, &context);
  require(bool(original), "domain fixture was not admitted");
  auto expected = domains(*original);
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>((*original)->clone()));
  simplify(*candidate, pipeline);
  // Compare complete declarations, not just constructor counts: operands,
  // attributes, order, unused intermediates and the returned root all matter.
  require(domains(*candidate) == expected,
          "generic simplification changed ordered domain admission");
  if (realize) {
    auto prepared = scopedFinite::prepare(*candidate);
    require(succeeded(scopedFinite::compare(*original, *prepared)),
            "realization lost original admission or nested entry conditions");
  }
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("bounded reads do not promise context-free speculation", [&] {
    auto module = parseSourceString<ModuleOp>(R"mlir(
!F = !algebra.field<"koala-bear">
!V = !data.field_vector<"koala-bear">
!M = !data.field_matrix<"koala-bear">
module {
  func.func @read(%xs: !V, %matrix: !M, %i: ui64, %j: ui64) -> (!F, !F) {
    %x = "data.bounded_at"(%xs, %i) : (!V, ui64) -> !F
    %y = "data.bounded_matrix_at"(%matrix, %i, %j) : (!M, ui64, ui64) -> !F
    return %x, %y : !F, !F
  }
})mlir",
                                              &context);
    require(bool(module), "local bound-read structure did not form");
    unsigned reads = 0;
    module->walk([&](Operation *op) {
      if (!isa<data::BoundedAtOp, data::BoundedMatrixAtOp>(op))
        return;
      ++reads;
      require(isMemoryEffectFree(op) && !isSpeculatable(op),
              "bounded read promises speculation without its bound premise");
    });
    require(reads == 2, "missing bounded-read coverage");
  });
  cases.run("constructor effects and speculation", [&] {
    auto module = parseSourceString<ModuleOp>(constructors, &context);
    require(bool(module), "constructor fixture was not admitted");
    module->walk([&](data::DomainOp domain) {
      for (auto &op : domain.getBody().front().without_terminator()) {
        require(!isMemoryEffectFree(&op),
                op.getName().getStringRef() + " permits erasing admission");
        require(!wouldOpBeTriviallyDead(&op),
                op.getName().getStringRef() + " permits unused admission DCE");
        require(!isSpeculatable(&op),
                op.getName().getStringRef() + " permits speculative admission");
      }
    });
  });
  for (StringRef pipeline : {"canonicalize", "cse", "canonicalize-cse"}) {
    cases.run("all constructors and live duplicates / " + pipeline, [&] {
      preservesDomains(constructors, context, pipeline, false);
    });
    for (StringRef name :
         {"dead-domain", "independent", "dependent", "order", "matrix-row",
          "matrix-column", "coordinates-row", "coordinates-column"})
      cases.run(name + " admission and realization / " + pipeline, [&] {
        preservesDomains(fixture(name), context, pipeline, true);
      });
    for (StringRef name : {"total-zip", "nested-total"})
      cases.run(name + " mathematical domains / " + pipeline, [&] {
        preservesDomains(fixture(name), context, pipeline, false);
      });
  }
  cases.run("total field expressions still simplify", [&] {
    auto module = parseSourceString<ModuleOp>(R"mlir(
!F = !algebra.field<"bls12-381.fr">
module {
  func.func @sum(%x: !F, %y: !F) -> !F {
    %first = algebra.field_add %x, %y : (!F, !F) -> !F
    %unused = algebra.field_multiply %x, %y : (!F, !F) -> !F
    %second = algebra.field_add %x, %y : (!F, !F) -> !F
    %result = algebra.field_add %first, %second : (!F, !F) -> !F
    func.return %result : !F
  }
}
)mlir",
                                              &context);
    require(bool(module), "total field fixture was not admitted");
    simplify(*module, "canonicalize-cse");
    unsigned additions = 0, products = 0;
    module->walk([&](algebra::FieldAddOp op) {
      ++additions;
      require(isPure(op), "total field addition lost its purity contract");
    });
    module->walk([&](algebra::FieldMultiplyOp) { ++products; });
    require(additions == 2 && products == 0,
            "generic CSE/DCE did not simplify total field expressions");
  });
  return cases.result();
}
