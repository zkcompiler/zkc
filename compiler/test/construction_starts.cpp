#include "../lib/Transforms/MathematicalValues.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
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
  auto prepared = mathematical::prepareProtocol(*source, false, {}, starts);
  require(bool(prepared), "selected application preparation refused");
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
  cases.run("simplification preserves selected application boundaries", [&] {
    auto simplified = mathematical::prepareProtocol(*source, true, {}, starts);
    require(bool(simplified), "simplified start preparation refused");
    require(succeeded(mathematical::verifyPreparedValues(
                unit(*source), unit(*simplified), starts)),
            "simplification changed selected start operands or order");
  });
  cases.run(
      "repreparation preserves existing boundaries without selecting new ones",
      [&] {
        auto repeated = mathematical::prepareProtocol(*prepared, false);
        require(bool(repeated), "prepared start markers were refused");
        require(succeeded(mathematical::verifyPreparedValues(unit(*prepared),
                                                             unit(*repeated))),
                "repreparation changed existing ordered boundaries");
        require(succeeded(mathematical::verifyPreparedValues(
                    unit(*source), unit(*repeated), starts)),
                "repreparation lost original selected start correspondence");
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
      bool diagnostic = false;
      ScopedDiagnosticHandler expected(&context, [&](Diagnostic &d) {
        diagnostic |=
            d.str().find("protocol-construction-start") != std::string::npos;
        return success();
      });
      require(!mathematical::prepareProtocol(*source, false, {}, selected) &&
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
  for (bool operand : {false, true})
    cases.run(
        operand
            ? "repeat refuses a start using a local constant for an absent role"
            : "repeat refuses an empty start for an absent role",
        [&] {
          std::string text = R"mlir(module { "protocol.module"() ({
        "protocol.func"() ({ ^entry(%n:ui64):
          "protocol.repeat"(%n) ({ ^body(%i:ui64):
            BODY
            "protocol.yield"() : ()->()
          }) {site="loop",carried=0:i64,maximum=2:i64,roles=["P"],carried_roles=[]} : (ui64)->()
          "protocol.return"() : ()->()
        }) {sym_name="main",function_type=(ui64)->(),roles=["P","V"],input_roles=[["P"]],output_roles=[]} : ()->()
      }) {profile=#protocol.profile<protocol>} : ()->() })mlir";
          text.replace(
              text.find("BODY"), 4,
              operand
                  ? R"mlir(%x = "data.index"() {value=0 : ui64} : ()->ui64
                     "protocol.construction_start"(%x) {roles=["P","V"],site="start"} : (ui64)->())mlir"
                  : R"mlir("protocol.construction_start"() {roles=["P","V"],site="start"} : ()->())mlir");
          bool diagnosed = false;
          ScopedDiagnosticHandler expected(&context, [&](Diagnostic &d) {
            diagnosed |=
                d.str().find("mathematical-formation") != std::string::npos &&
                d.str().find("nonparticipating role") != std::string::npos;
            return success();
          });
          auto module = parseSourceString<ModuleOp>(text, &context);
          require(bool(module), "repeat participant mutation must form");
          require(failed(zkc::admitStage(*module)) && diagnosed,
                  "construction start escaped the repeat participant boundary");
        });
  return cases.result();
}
