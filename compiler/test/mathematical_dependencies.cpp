#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/TypeAdapters.h"
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
  protocol::type_adapters::registerCatalogTypeInterfaces(registry);
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
  if (!module) {
    llvm::errs() << "dependency fixture must remain formed: " << diagnostic
                 << '\n';
    return false;
  }
  if (succeeded(zkc::admitStage(*module)) ||
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
  zkc::test::Cases cases;
  cases.run("out-of-range dependency", [&] {
    zkc::test::require(refuses<0>(), "out-of-range model was not refused");
  });
  cases.run("duplicate dependency", [&] {
    zkc::test::require(refuses<1>(), "duplicate model was not refused");
  });
  cases.run("missing dependency", [&] {
    zkc::test::require(refuses<2>(), "incomplete model was not refused");
  });
  cases.run("absent mathematical interface", [&] {
    zkc::test::require(refuses<3>(), "absent model was not refused");
  });
  cases.run("reordered dependencies", [&] {
    zkc::test::require(refuses<4>(), "reordered model was not refused");
  });
  return cases.result();
}
