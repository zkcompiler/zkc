#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Interfaces/Mathematical.h"
#include "llvm/Support/raw_ostream.h"

using namespace mlir;
using namespace zkc;

namespace {
template <unsigned Kind>
struct MalformedModel final
    : MathematicalOpInterface::ExternalModel<MalformedModel<Kind>,
                                             arith::AndIOp> {
  std::optional<MathematicalIdentity>
  getMathematicalIdentity(Operation *) const {
    return MathematicalIdentity::BooleanAnd;
  }
  llvm::SmallVector<unsigned> getOperandDependencies(Operation *,
                                                     unsigned) const {
    if constexpr (Kind == 0)
      return {0, 5};
    if constexpr (Kind == 1)
      return {0, 0};
    if constexpr (Kind == 4)
      return {1, 0};
    return {0};
  }
};
template <unsigned Kind> bool refuses() {
  DialectRegistry registry;
  // Deliberately omit the real adapter to exercise hostile and absent models.
  registry.insert<protocol_ir::ProtocolDialect, arith::ArithDialect>();
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  // An external model cannot weaken the closed operation semantics or make
  // dependency analysis index outside its operand range.
  if constexpr (Kind != 3)
    arith::AndIOp::attachInterface<MalformedModel<Kind>>(context);
  std::string diagnostic;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &d) {
    llvm::raw_string_ostream stream(diagnostic);
    d.print(stream);
    return success();
  });
  auto module = parseSourceString<ModuleOp>(R"mlir(
module {
  "protocol.module"() ({
    "protocol.func"() ({
    ^entry(%a: i1, %b: i1):
      %and = arith.andi %a, %b : i1
      "protocol.return"(%and) : (i1) -> ()
    }) {sym_name="main", function_type=(i1, i1) -> i1, roles=["P"],
        input_roles=[["P"], ["P"]], output_roles=[["P"]]} : () -> ()
  }) {profile=#protocol.profile<protocol>} : () -> ()
})mlir",
                                            &context);
  if (module ||
      diagnostic.find("mathematical-dependencies") == std::string::npos) {
    llvm::errs() << "malformed dependency model accepted: " << diagnostic
                 << '\n';
    return false;
  }
  if constexpr (Kind == 3) {
    if (diagnostic.find("requires a registered mathematical interface") ==
        std::string::npos) {
      llvm::errs() << "missing model reported as malformed dependencies: "
                   << diagnostic << '\n';
      return false;
    }
  }
  return true;
}
} // namespace
int main() {
  return !(refuses<0>() && refuses<1>() && refuses<2>() && refuses<3>() &&
           refuses<4>());
}
