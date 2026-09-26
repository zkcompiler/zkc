#include "zkc/Dialect/IR.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/TableLibrary.h"
#include "zkc/Source/Relations.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"
#include "zkc/Translation/Relations.h"
#include "zkc/Translation/Table.h"

// This executable links only Zkc::IR. It must neither parse frontend syntax
// nor invoke a pass to import, verify and export an independently built model.
int main() {
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  zkc::registerTableLibrary(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  // Claim dialect structure is ordinary IR, even without the optional checker
  // or translation libraries. A law declaration is structurally valid without
  // establishing any source-relative claim.
  mlir::OpBuilder claimBuilder(&context);
  mlir::OwningOpRef<mlir::ModuleOp> claims(
      mlir::ModuleOp::create(claimBuilder.getUnknownLoc()));
  claimBuilder.setInsertionPointToEnd(claims->getBody());
  mlir::OperationState law(claimBuilder.getUnknownLoc(), "claim.law");
  law.addAttribute("sym_name", claimBuilder.getStringAttr("law"));
  law.addAttribute("premise",
                   claimBuilder.getStringAttr("Explicit caller premise"));
  auto *declaration = claimBuilder.create(law);
  if (mlir::failed(mlir::verify(*claims)))
    return 13;
  declaration->removeAttr("premise");
  {
    mlir::ScopedDiagnosticHandler handler(
        &context, [](mlir::Diagnostic &) { return mlir::success(); });
    if (mlir::succeeded(mlir::verify(*claims)))
      return 14;
  }
  zkc::relation::Constraint row{{{{2, "1"}}, {{3, "1"}}, {{1, "1"}}}};
  auto relation = zkc::relation::R1CS::create("bls12-381.fr", 4, 1, 1, {row});
  if (!relation) {
    llvm::consumeError(relation.takeError());
    return 1;
  }
  zkc::source::Module source;
  source.relations.push_back(
      {{}, "Circuit", std::make_shared<const zkc::relation::R1CS>(*relation)});
  source.relationViews.push_back(
      {{}, "Rows", "Circuit", "multilinear", "specialized", {}});
  if (auto e = zkc::relation::materializeViews(source)) {
    llvm::consumeError(std::move(e));
    return 2;
  }
  auto module = zkc::protocol::importModule(source, context);
  if (!module) {
    llvm::consumeError(module.takeError());
    return 3;
  }
  auto exported = zkc::protocol::exportModule(module->get());
  if (!exported) {
    llvm::consumeError(exported.takeError());
    return 4;
  }
  if (*exported != zkc::source::encode(source))
    return 5;

  // Changing a well-formed relation without regenerating its view must still
  // fail the whole-root check, even though every local operation remains valid.
  row[0][0].coefficient = "2";
  auto changed = zkc::relation::R1CS::create("bls12-381.fr", 4, 1, 1, {row});
  if (!changed) {
    llvm::consumeError(changed.takeError());
    return 6;
  }
  mlir::Builder builder(&context);
  module->get().walk([&](zkc::R1CSRelationOp op) {
    op->setAttr("constraints",
                zkc::relation::encodeR1CSConstraints(builder, *changed));
  });
  bool sawRefusal = false;
  mlir::ScopedDiagnosticHandler handler(&context, [&](mlir::Diagnostic &d) {
    for (const auto &refusal : zkc::diagnostics::refusals(d))
      sawRefusal |= refusal.code == "relation-generated-function";
    return mlir::success();
  });
  if (mlir::succeeded(mlir::verify(module->get())) || !sawRefusal)
    return 7;

  // The separate finite-table route also works without compiler workflows.
  auto request = zkc::parseJson(R"(["zkc-request",1,"finite-source-1",
    ["trace",[["x",["scalar","f7"],["shared"],"argument"]],
      ["scalar","f7"],[["table-protocol","1"]]],[],["return",0]])");
  if (!request) {
    llvm::consumeError(request.takeError());
    return 8;
  }
  auto table = zkc::importSource(*request, context);
  if (!table) {
    llvm::consumeError(table.takeError());
    return 9;
  }
  if (mlir::failed(mlir::verify(table->get())))
    return 10;
  zkc::PIRReturnOp finish;
  table->get().walk([&](zkc::PIRReturnOp op) { finish = op; });
  if (!finish)
    return 11;
  finish->setOperands(mlir::ValueRange{});
  return mlir::succeeded(mlir::verify(table->get())) ? 12 : 0;
}
