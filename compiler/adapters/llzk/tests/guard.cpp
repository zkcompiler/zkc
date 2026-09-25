// Fault injection at the final admission boundary: model a normalization pass
// leaving/introducing a constraint operation that its R1CS successor would
// drop.
#include "../Adapter.h"
#include "llzk/Dialect/InitDialects.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/Parser/Parser.h"
#include "llvm/ADT/StringRef.h"
#include <stdexcept>
using namespace mlir;
using namespace llvm;

int main() {
  DialectRegistry registry;
  llzk::registerAllDialects(registry);
  MLIRContext context(registry, MLIRContext::Threading::DISABLED);
  const char *text = R"mlir(
module attributes {llzk.lang, llzk.main = !struct.type<@Main>} {
  struct.def @Main {
    struct.member @out : !felt.type<"bn254"> {llzk.pub, signal}
    function.def @compute(%a: !felt.type<"bn254">) -> !struct.type<@Main> {
      %self = struct.new : !struct.type<@Main>
      function.return %self : !struct.type<@Main>
    }
    function.def @constrain(%self: !struct.type<@Main>, %a: !felt.type<"bn254">) {
      %out = struct.readm %self[@out] : !struct.type<@Main>, !felt.type<"bn254">
      constrain.eq %out, %a : !felt.type<"bn254">
      %b = bool.cmp eq(%out, %a) : !felt.type<"bn254">, !felt.type<"bn254">
      bool.assert %b
      function.return
    }
  }
})mlir";
  auto module = parseSourceString<ModuleOp>(text, &context);
  if (!module)
    return 1;
  // This check intentionally bypasses sourceGuard, simulating an operation
  // introduced after that guard. The final scalar checker must still refuse.
  try {
    zkc::llzk_adapter::validateScalarModule(*module);
  } catch (const std::runtime_error &e) {
    return StringRef(e.what()).starts_with("llzk-scalar-operation:") ? 0 : 1;
  }
  return 1;
}
