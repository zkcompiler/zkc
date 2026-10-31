#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/ProtocolConstants.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace pir = protocol_ir;
namespace {
using Status = facts::Status;
constexpr StringLiteral source = R"mlir(
module { "protocol.module"() ({
 func.func private @identity(%value:ui64)->ui64 { return %value : ui64 }
 "protocol.func"() ({
 ^entry(%unknown:ui64):
  %one = "data.index"() {value=1:ui64} : ()->ui64
  %two = "data.index"() {value=2:ui64} : ()->ui64
  %mixed = "protocol.assemble_roles"(%one,%two) {roles=["P","V"]} : (ui64,ui64)->ui64
  %agreed = "protocol.assemble_roles"(%one,%one) {roles=["P","V"]} : (ui64,ui64)->ui64
  %view = "protocol.restrict_roles"(%mixed) {roles=["V"]} : (ui64)->ui64
  %forward = func.call @identity(%mixed) : (ui64)->ui64
  %yes = arith.constant true
  %no = arith.constant false
  %condition = "protocol.assemble_roles"(%yes,%no) {roles=["P","V"]} : (i1,i1)->i1
  %last = "protocol.repeat"(%unknown,%one,%mixed) ({
  ^body(%iteration:ui64,%carried:ui64,%capture:ui64):
   "protocol.yield"(%capture) : (ui64)->()
  }) {site="loop",carried=1:i64,maximum=4:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,ui64,ui64)->ui64
  "protocol.return"(%mixed,%agreed,%view,%forward,%condition,%last) : (ui64,ui64,ui64,ui64,i1,ui64)->()
 }) {sym_name="main",function_type=(ui64)->(ui64,ui64,ui64,ui64,i1,ui64),roles=["P","V"],input_roles=[["P","V"]],output_roles=[["P","V"],["P","V"],["V"],["P","V"],["P","V"],["P","V"]]} : ()->()
 }) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
pir::MathematicalOp program(ModuleOp module) {
  auto unit = cast<pir::ProtocolModuleOp>(module.getBody()->front());
  return SymbolTable(unit).lookup<pir::MathematicalOp>("main");
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto module = parseSourceString<ModuleOp>(source, &context);
  require(bool(module) && succeeded(admitStage(*module)),
          "constant fixture must be admitted");
  auto function = program(*module);
  auto returned = function.getBody().front().back().getOperands();
  auto loop = *function.getBody().front().getOps<pir::RepeatOp>().begin();
  MathematicalFactAnalysis mathematics(*module);
  auto observe = [&](Value value, StringRef role,
                     std::optional<uint64_t> expected) {
    uint64_t remaining = 10000;
    facts::Work work(remaining);
    auto result = observeProtocolConstant(value, role, mathematics, work);
    require(result.status == (expected ? Status::Proven : Status::Unknown) &&
                result.value == expected,
            "unexpected participant-relative constant");
  };
  Cases cases;
  cases.run("role assembly selects the actual participant component", [&] {
    observe(returned[0], "P", 1);
    observe(returned[0], "V", 2);
    observe(returned[0], "W", {});
    observe(returned[0], "", {});
    observe(returned[1], "", 1);
  });
  cases.run("restrictions never import another participant's value", [&] {
    observe(returned[2], "V", 2);
    observe(returned[2], "P", {});
  });
  cases.run("pure helper forwarding preserves role interpretation", [&] {
    observe(returned[3], "P", 1);
    observe(returned[3], "V", 2);
    observe(returned[3], "", {});
  });
  cases.run("Boolean components retain distinct stop conditions", [&] {
    observe(returned[4], "P", 1);
    observe(returned[4], "V", 0);
    observe(returned[4], "", {});
  });
  cases.run("only invariant captures forward across a repeat", [&] {
    auto args = loop.getBody().front().getArguments();
    observe(args[2], "P", 1);
    observe(args[2], "V", 2);
    observe(args[2], "", {});
    observe(args[0], "V", {});
    observe(args[1], "V", {});
    observe(returned[5], "V", {});
    observe(function.getBody().front().getArgument(0), "V", {});
  });
  cases.run("foreign values do not supply facts", [&] {
    OwningOpRef<ModuleOp> clone(cast<ModuleOp>(module->clone()));
    observe(program(*clone).getBody().front().back().getOperand(1), "", {});
  });
  cases.run("work exhaustion stays explicit and sticky on a warm subject", [&] {
    uint64_t remaining = 1;
    facts::Work work(remaining);
    for (unsigned attempt = 0; attempt != 2; ++attempt) {
      auto result = observeProtocolConstant(returned[1], "", mathematics, work);
      require(result.status == Status::Capacity && !result.value,
              "exhausted observation returned a constant");
    }
  });
  cases.run("a fresh query cannot retain a prior component after mutation",
            [&] {
              auto assembly = returned[0].getDefiningOp<pir::AssembleRolesOp>();
              auto input = assembly.getInputs()[0];
              mathematics.clear();
              assembly->setOperand(1, input);
              require(succeeded(admitStage(*module)), "mutated fixture");
              observe(returned[0], "V", 1);
              observe(returned[0], "", 1);
            });
  return cases.result();
}
