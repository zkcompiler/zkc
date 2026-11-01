#include "mlir/IR/Builders.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/EntryBoundary.h"
#include "zkc/Translation/Entry.h"
#include "llvm/Support/MemoryBuffer.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
CheckedProject project() {
  auto file = MemoryBuffer::getFile(ZKC_ENTRY_COMPONENT_FIXTURE);
  require(bool(file), "missing authored component fixture");
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured = take(capture(
      {{"components", (*file)->getBuffer().str(), ZKC_ENTRY_COMPONENT_FIXTURE}},
      options));
  return take(analyze(captured).checkedProject());
}
void compare(const ClosedEntry &entry, mlir::ModuleOp module) {
  take(compareOriginal(entry, module));
}
} // namespace
int main() {
  Cases cases;
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto checked = project();
  cases.run("ordinary distributed source emits the exact native ABI", [&] {
    auto entry = take(closeNativeRun(checked, "components::Round"));
    auto bytes = take(emitOriginal(entry, context));
    auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
    require(bool(module), "invalid emitted original");
    compare(entry, *module);
    zkc::protocol_ir::MathematicalOp root;
    module->walk([&](zkc::protocol_ir::MathematicalOp op) { root = op; });
    require(root && root.getBody().front().getNumArguments() == 2,
            "logical root acquired another native representation");
    auto roles = root->getAttrOfType<mlir::ArrayAttr>("input_roles");
    require(roles && roles.size() == 2 &&
                mlir::cast<mlir::ArrayAttr>(roles[0]).size() == 2 &&
                mlir::cast<mlir::ArrayAttr>(roles[1]).size() == 1,
            "native role components differ from source placement");
    Layouts layouts(entry);
    auto plan = take(layouts.entryBoundary(entry.protocol(), entry.entry()));
    require(plan.inputs.size() == 4 && plan.inputs.back().native.empty(),
            "empty ordinary supply disappeared during native observation");
  });
  cases.run("equal-typed candidate input substitution refuses", [&] {
    auto entry = take(closeNativeRun(checked, "components::Round"));
    auto bytes = take(emitOriginal(entry, context));
    auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
    require(bool(module), "invalid emitted original");
    zkc::protocol_ir::MathematicalOp root;
    zkc::protocol_ir::ExchangeOp exchange;
    module->walk([&](zkc::protocol_ir::MathematicalOp op) { root = op; });
    module->walk([&](zkc::protocol_ir::ExchangeOp op) { exchange = op; });
    require(root && exchange, "fixture has no actual exchange");
    exchange->setOperand(0, root.getBody().front().getArgument(0));
    refuses(compareOriginal(entry, *module), "source.correspondence");
  });
  cases.run(
      "permuted nominal roles retain native inputs and output associations",
      [&] {
        CaptureOptions options;
        options.format = "zkc-layout";
        auto captured = take(capture({{"permuted", R"(
struct Pair roles(P, V):
    pub left: index @P
    pub right: index @V
pub protocol Forward roles(A, B)(state: Pair roles(B, A)) -> Pair roles(B, A):
    return state
)",
                                       "permuted.zkc"}},
                                     options));
        auto project = take(analyze(captured).checkedProject());
        auto entry = take(closeNativeRun(project, "permuted::Forward"));
        auto bytes = take(emitOriginal(entry, context));
        auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
        require(bool(module), "invalid permuted original");
        compare(entry, *module);
        zkc::protocol_ir::MathematicalOp root;
        module->walk([&](zkc::protocol_ir::MathematicalOp op) { root = op; });
        auto inputs = root->getAttrOfType<mlir::ArrayAttr>("input_roles");
        auto outputs = root->getAttrOfType<mlir::ArrayAttr>("output_roles");
        require(inputs == outputs && inputs.size() == 2 &&
                    mlir::cast<mlir::ArrayAttr>(inputs[0])[0] ==
                        mlir::StringAttr::get(&context, "role00000001") &&
                    mlir::cast<mlir::ArrayAttr>(inputs[1])[0] ==
                        mlir::StringAttr::get(&context, "role00000000"),
                "nominal role order was replaced by an aggregate participation "
                "union");
      });
  cases.run(
      "public proof source retains logical selections through native emission",
      [&] {
        auto entry = take(closeEntry(checked, "components::Demo"));
        auto bytes = take(emitOriginal(entry, context));
        auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
        require(bool(module), "invalid emitted proof original");
        compare(entry, *module);
        require(
            entry.entry().proof()->publicInputs.size() == 2 &&
                entry.entry().proof()->publicInputs[1].path ==
                    std::vector<unsigned>{2},
            "empty public selection vanished before native policy expansion");
      });
  for (StringRef name : {"Produce", "Check"})
    cases.run(
        "generated selected Host family source/native comparison: " + name,
        [&] {
          auto entry = take(closeEntry(checked, ("components::" + name).str()));
          auto bytes = take(emitHostOriginal(entry, context));
          auto module =
              mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
          require(bool(module), "invalid emitted Host original");
          take(compareHostOriginal(entry, *module));
        });
  return cases.result();
}
