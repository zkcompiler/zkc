#include "mlir/Dialect/Linalg/IR/Linalg.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/StructuredComputation.h"
#include "zkc/Dialect/Registry.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::mathematical;
using namespace zkc::test;
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  // A handwritten packet, linked only against IR, with no producer available.
  auto packet = parseSourceString<ModuleOp>(R"mlir(
!F = !algebra.field<"koala-bear">
!T = tensor<?x!F>
module {
 func.func @map(%xs: !T, %scale: !F) -> !T {
  %zero = arith.constant 0 : index
  %size = tensor.dim %xs, %zero : !T
  %empty = tensor.empty(%size) : !T
  %r = linalg.generic {indexing_maps = [affine_map<(d0)->(d0)>, affine_map<(d0)->()>, affine_map<(d0)->(d0)>], iterator_types = ["parallel"]}
      ins(%xs, %scale : !T, !F) outs(%empty : !T) {
    ^bb0(%x: !F, %s: !F, %unused: !F):
     %v = "algebra.field_multiply"(%x, %s) : (!F, !F)->!F
     linalg.yield %v : !F
  } -> !T
  return %r : !T
 }
})mlir",
                                            &context);
  require(bool(packet), "handwritten packet parsing");
  cases.run("independent scalar interpretation and source correspondence", [&] {
    auto actual = readStructuredComputation(*packet);
    require(bool(actual) && actual->rowwise.size() == 2 && actual->rowwise[0] &&
                !actual->rowwise[1] && actual->result == StructuredResult::Map,
            "actual ports were not interpreted");
    require(succeeded(verifyStructuredComputation(actual->scalar->front(),
                                                  actual->rowwise,
                                                  actual->result, *packet)),
            "scalar correspondence");
    require(actual->scalar->front().getOperations().size() == 2,
            "reader did not extract the actual multiplication");
  });
  cases.run("absent and empty packets refuse without dereferencing", [&] {
    require(!readStructuredComputation({}), "absent packet admitted");
    auto empty = ModuleOp::create(UnknownLoc::get(&context));
    OwningOpRef<ModuleOp> owned(empty);
    require(!readStructuredComputation(empty), "empty packet admitted");
    auto actual = readStructuredComputation(*packet);
    require(failed(verifyStructuredComputation(
                actual->scalar->front(), actual->rowwise, actual->result, {})),
            "absent correspondence admitted");
  });
  cases.run("mutation requires a new admission", [&] {
    auto actual = readStructuredComputation(*packet);
    OwningOpRef<ModuleOp> changed(cast<ModuleOp>((*packet)->clone()));
    changed->getOperation()->setAttr("unchecked", UnitAttr::get(&context));
    require(!readStructuredComputation(*changed),
            "unknown module metadata admitted");
    std::string diagnostic;
    ScopedDiagnosticHandler handler(&context, [&](Diagnostic &d) {
      diagnostic += d.str();
      return success();
    });
    require(failed(verifyStructuredComputation(actual->scalar->front(),
                                               actual->rowwise, actual->result,
                                               *changed)) &&
                diagnostic.find("structured-computation") != std::string::npos,
            "correspondence reused stale admission");
  });
  cases.run("source row roles remain exact", [&] {
    auto actual = readStructuredComputation(*packet);
    const bool swapped[] = {false, true};
    ScopedDiagnosticHandler handler(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(verifyStructuredComputation(actual->scalar->front(), swapped,
                                               actual->result, *packet)),
            "row/broadcast swap admitted");
  });
  return cases.result();
}
