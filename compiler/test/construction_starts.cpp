#include "../lib/Transforms/MathematicalValues.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Transforms/Passes.h"
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace {
constexpr StringLiteral fixture = R"mlir(module { "protocol.module"() ({
  "protocol.func"() ({ ^entry(%a:i1,%b:i1):
    "protocol.return"(%a) : (i1)->()
  }) {sym_name="empty",function_type=(i1,i1)->i1,roles=["A","B"],input_roles=[["A","B"],["A","B"]],output_roles=[["A","B"]]} : ()->()
  "protocol.func"() ({ ^entry(%a:i1,%b:i1):
    protocol.guard %a {owner="A",site="check"}
    %r = protocol.apply @empty(%b,%a) {roles=["B","A"],site="inner"} : (i1,i1)->i1
    "protocol.return"(%r) : (i1)->()
  }) {sym_name="child",function_type=(i1,i1)->i1,roles=["A","B"],input_roles=[["A","B"],["A","B"]],output_roles=[["A","B"]]} : ()->()
  "protocol.func"() ({ ^entry(%n:ui64,%x:i1,%y:i1):
    %a = protocol.apply @child(%x,%y) {roles=["P","V"],site="first"} : (i1,i1)->i1
    %b = protocol.apply @child(%y,%x) {roles=["P","V"],site="second"} : (i1,i1)->i1
    "protocol.repeat"(%n,%x,%y) ({ ^body(%i:ui64,%cx:i1,%cy:i1):
      %r = protocol.apply @empty(%cx,%cy) {roles=["P","V"],site="iteration"} : (i1,i1)->i1
      "protocol.yield"() : ()->()
    }) {site="loop",carried=0:i64,maximum=2:i64,roles=["P","V"],carried_roles=[]} : (ui64,i1,i1)->()
    "protocol.return"(%a,%b) : (i1,i1)->()
  }) {sym_name="main",function_type=(ui64,i1,i1)->(i1,i1),roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"]],output_roles=[["P","V"],["P","V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
protocol_ir::ProtocolModuleOp unit(ModuleOp m) {
  return cast<protocol_ir::ProtocolModuleOp>(m.getBody()->front());
}
OwningOpRef<ModuleOp> copy(ModuleOp m) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(m->clone()));
}
LogicalResult run(ModuleOp m, std::unique_ptr<Pass> pass) {
  PassManager manager(m.getContext());
  manager.addPass(std::move(pass));
  return manager.run(m);
}
protocol_ir::ConstructionStartOp boundary(ModuleOp m, StringRef site) {
  protocol_ir::ConstructionStartOp result;
  m.walk([&](protocol_ir::ConstructionStartOp op) {
    if (op.getSite() == site)
      result = op;
  });
  require(bool(result), "missing selected boundary");
  return result;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  auto inner = mathematical::expandedApplicationSite("first", "inner");
  SmallVector<mathematical::ApplicationStart> starts{
      {"main", "first", {0, 1}},
      {"main", inner, {0}},
      {"main", "iteration", {1}}};
  auto source = parseSourceString<ModuleOp>(fixture, &context);
  require(bool(source), "invalid start fixture");
  auto prepared = copy(*source);
  require(succeeded(run(*prepared, protocol::createPrepareProtocolPass(
                                       false, false, starts))),
          "selected application preparation refused");
  cases.run("empty child, nested role substitution and repeated boundary", [&] {
    unsigned count = 0;
    prepared->walk([&](protocol_ir::ConstructionStartOp) { ++count; });
    require(count == 3, "selected starts were lost or duplicated");
    require(boundary(*prepared, inner).getRoles()[0] ==
                StringAttr::get(&context, "V"),
            "nested role substitution lost");
    require(bool(boundary(*prepared, "iteration")
                     ->getParentOfType<protocol_ir::RepeatOp>()),
            "start escaped its zero-trip loop");
    require(succeeded(mathematical::verifyPreparedValues(
                unit(*source), unit(*prepared), starts)),
            "independent start correspondence refused");
  });
  cases.run("unselected application expansion stays unchanged", [&] {
    auto ordinary = copy(*source);
    require(
        succeeded(run(*ordinary, protocol::createPrepareProtocolPass(false))),
        "ordinary preparation refused");
    bool found = false;
    ordinary->walk([&](protocol_ir::ConstructionStartOp) { found = true; });
    require(!found, "unselected invocation acquired a start");
  });
  for (StringRef mutation : {"missing", "operand", "late", "unselected"})
    cases.run("independent boundary check: " + mutation, [&] {
      auto changed = copy(*prepared);
      auto start = boundary(*changed, "first");
      if (mutation == "missing")
        start.erase();
      else if (mutation == "operand")
        start->setOperand(0, start.getInputs()[1]);
      else if (mutation == "late") {
        Operation *guard = nullptr;
        changed->walk([&](protocol_ir::GuardOp op) {
          if (op.getSite() ==
              mathematical::expandedApplicationSite("first", "check"))
            guard = op;
        });
        require(guard != nullptr, "missing child guard");
        start->moveAfter(guard);
      } else
        start.setSite("unselected");
      require(succeeded(verify(*changed)),
              "boundary mutation must remain formed");
      bool diagnostic = false;
      ScopedDiagnosticHandler expected(&context, [&](Diagnostic &d) {
        diagnostic |=
            d.str().find("mathematical-correspondence") != std::string::npos;
        return success();
      });
      require(failed(mathematical::verifyPreparedValues(
                  unit(*source), unit(*changed), starts)) &&
                  diagnostic,
              "changed boundary passed correspondence");
    });
  for (StringRef selection :
       {"missing", "duplicate", "input", "duplicate-input"})
    cases.run("invalid selection: " + selection, [&] {
      auto selected = starts;
      if (selection == "missing")
        selected.front().site = "absent";
      else if (selection == "duplicate")
        selected.push_back(selected.front());
      else if (selection == "input")
        selected.front().inputs = {2};
      else
        selected.front().inputs = {0, 0};
      auto changed = copy(*source);
      bool diagnostic = false;
      ScopedDiagnosticHandler expected(&context, [&](Diagnostic &d) {
        diagnostic |=
            d.str().find("protocol-construction-start") != std::string::npos;
        return success();
      });
      require(failed(run(*changed, protocol::createPrepareProtocolPass(
                                       false, false, selected))) &&
                  diagnostic,
              "invalid boundary selection passed");
    });
  cases.run("projection preserves both participants and actual operands", [&] {
    auto projected = copy(*prepared);
    require(
        succeeded(run(*projected, protocol::createProjectProtocolPass(false))),
        "start projection refused");
    unsigned count = 0;
    projected->walk([&](protocol_ir::ConstructionStartOp) { ++count; });
    require(count == 6, "selected boundary did not reach both roles");
    require(succeeded(
                mathematical::verifyProjectionPreserved(*prepared, *projected)),
            "start projection correspondence refused");
  });
  return cases.result();
}
