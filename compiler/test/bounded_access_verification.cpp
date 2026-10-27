#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Transforms/Passes.h"
#include <iterator>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;

namespace {
protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
func::FuncOp helper(ModuleOp module, StringRef name) {
  auto result = SymbolTable(unit(module)).lookup<func::FuncOp>(name);
  require(bool(result), "missing helper " + name);
  return result;
}
Operation *access(ModuleOp module) {
  Operation *result = nullptr;
  module.walk([&](Operation *op) {
    if (isa<data::BoundedAtOp, data::BoundedMatrixAtOp>(op)) {
      require(!result, "expected exactly one bounded access");
      result = op;
    }
  });
  require(result, "missing bounded access");
  return result;
}
bool hasFinite(ModuleOp module) {
  bool result = false;
  module.walk([&](Operation *op) { result |= finite::isComputation(op); });
  return result;
}
OwningOpRef<ModuleOp> parse(MLIRContext &context, StringRef source) {
  auto module = parseSourceString<ModuleOp>(source, &context);
  require(bool(module) && succeeded(verify(*module)), "fixture refused");
  return module;
}
void refuses(MLIRContext &context, llvm::function_ref<LogicalResult()> check,
             StringRef code) {
  SmallVector<std::string> codes;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
    for (auto &refusal : diagnostics::refusals(diagnostic))
      codes.push_back(refusal.code);
    return success();
  });
  require(failed(check()), "expected refusal " + code);
  require(llvm::is_contained(codes, code.str()),
          "missing refusal identifier " + code);
  StringRef other =
      code == "finite-bound" ? "finite-analysis-limit" : "finite-bound";
  require(!llvm::is_contained(codes, other.str()),
          "bound evidence and analysis capacity were conflated");
}
void refusesBound(ModuleOp module, StringRef code = "finite-bound") {
  // An access verified in isolation cannot certify its symbol closure.
  require(succeeded(verify(access(module))),
          "isolated operation verification followed sibling evidence");
  refuses(
      *module.getContext(), [&] { return finite::verifyClosure(unit(module)); },
      code);
  refuses(*module.getContext(), [&] { return verify(module); }, code);
}
void project(ModuleOp module) {
  PassManager manager(module.getContext());
  manager.addPass(protocol::createProjectProtocolPass(false, {false, false}));
  require(succeeded(manager.run(module)) && succeeded(verify(module)),
          "participant fixture refused");
  require(unit(module).getProfile() == protocol_ir::Profile::Participant,
          "fixture was not projected");
}

// Each case parses its own module. The no-finite form leaves an unused reader
// helper so that whole-unit admission must still check its access evidence.
std::string forwardingFixture(bool matrix, bool finite) {
  std::string source = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
)mlir";
  source +=
      matrix ? "!C = !algebra.field_matrix<\"bls12-381.fr\">\n" : "!C = !V\n";
  source += "module { \"protocol.module\"() ({\n";
  if (finite) {
    source += "\"data.domain\"() ({ ^entry(%xs:!C):\n";
    source += matrix ? "%d = \"data.domain_matrix_coordinates\"(%xs) "
                       "{order=\"row_major\"} : (!C)->!data.domain<ui64,ui64>\n"
                       "\"data.domain_yield\"(%d) : "
                       "(!data.domain<ui64,ui64>)->()\n"
                       "}) {sym_name=\"items\",sym_visibility=\"private\","
                       "function_type=(!C)->!data.domain<ui64,ui64>} : ()->()\n"
                     : "%d = \"data.domain_indices\"(%xs) {axis=0:i64} : "
                       "(!C)->!data.domain<ui64>\n"
                       "\"data.domain_yield\"(%d) : (!data.domain<ui64>)->()\n"
                       "}) {sym_name=\"items\",sym_visibility=\"private\","
                       "function_type=(!C)->!data.domain<ui64>} : ()->()\n";
  }
  source += matrix ? R"mlir(
 func.func private @read(%i:ui64,%j:ui64,%xs:!C,%other:ui64)->!F
     attributes {data.preconditions=[#data.index_bound<0,2,0>,
                                    #data.index_bound<1,2,1>]} {
   %copy = func.call @identity(%xs) : (!C)->!C
   %row = func.call @row(%i,%other) : (ui64,ui64)->ui64
   %column = func.call @column(%j,%other) : (ui64,ui64)->ui64
   %value = "data.bounded_matrix_at"(%copy,%row,%column) : (!C,ui64,ui64)->!F
   func.return %value : !F
 }
 func.func private @column(%index:ui64,%other:ui64)->ui64 {
   func.return %index : ui64
 }
)mlir"
                   : R"mlir(
 func.func private @read(%i:ui64,%xs:!C,%other:ui64)->!F
     attributes {data.preconditions=[#data.index_bound<0,1,0>]} {
   %copy = func.call @identity(%xs) : (!C)->!C
   %index = func.call @row(%i,%other) : (ui64,ui64)->ui64
   %value = "data.bounded_at"(%copy,%index) : (!C,ui64)->!F
   func.return %value : !F
 }
)mlir";
  source += R"mlir(
 func.func private @identity(%xs:!C)->!C { func.return %xs : !C }
 func.func private @row(%index:ui64,%other:ui64)->ui64 {
   func.return %index : ui64
 }
 "protocol.func"() ({ ^entry(%xs:!C,%other:ui64):
)mlir";
  source += finite ? "%result = \"algebra.finite_collect\"(%xs,%other) "
                     "{domain=@items,body=@read} : (!C,ui64)->!V\n"
                     "\"protocol.return\"(%result) : (!V)->()\n"
                     "}) {sym_name=\"main\",function_type=(!C,ui64)->!V,"
                   : "\"protocol.return\"(%xs) : (!C)->()\n"
                     "}) {sym_name=\"main\",function_type=(!C,ui64)->!C,";
  source += "roles=[\"P\"],input_roles=[[\"P\"],[\"P\"]],"
            "output_roles=[[\"P\"]]} : ()->()\n"
            "}) {profile=#protocol.profile<protocol>} : ()->() }\n";
  return source;
}

constexpr StringLiteral directFixture = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!A = !algebra.field_array<"bls12-381.fr",4>
module { "protocol.module"() ({
 func.func private @identity(%xs:!A)->!A { func.return %xs : !A }
 func.func private @index()->ui64 {
   %zero = "data.index"() {value="0"} : ()->ui64
   %other = "data.index"() {value="4"} : ()->ui64
   func.return %zero : ui64
 }
 "protocol.func"() ({ ^entry(%xs:!A):
   %copy = func.call @identity(%xs) : (!A)->!A
   %index = func.call @index() : ()->ui64
   %value = "data.bounded_at"(%copy,%index) : (!A,ui64)->!F
   "protocol.return"(%value) : (!F)->()
 }) {sym_name="main",function_type=(!A)->!F,roles=["P"],
     input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  for (bool matrix : {false, true}) {
    StringRef shape = matrix ? "matrix" : "vector";
    for (bool finite : {false, true})
      for (unsigned axis = 0; axis < (matrix ? 2u : 1u); ++axis)
        cases.run(
            shape + (finite ? " finite" : " helper-only") +
                " sibling index mutation on axis " + llvm::Twine(axis),
            [&] {
              auto module = parse(context, forwardingFixture(matrix, finite));
              require(hasFinite(*module) == finite,
                      "fixture selected the wrong closure path");
              require(succeeded(finite::verifyClosure(unit(*module))),
                      "valid forwarding lost its bound");
              auto changed = helper(*module, axis ? "column" : "row");
              changed.front().back().setOperand(0, changed.getArgument(1));
              require(succeeded(verify(changed)) &&
                          succeeded(verify(helper(*module, "read"))),
                      "valid helper mutation changed local structure");
              refusesBound(*module);
              changed.front().back().setOperand(0, changed.getArgument(0));
              require(succeeded(verify(*module)),
                      "restoring forwarding did not restore admission");
            });
    cases.run(shape + " closure preserves analysis-limit diagnostic", [&] {
      auto module = parse(context, forwardingFixture(matrix, false));
      auto *lookup = access(*module);
      OpBuilder builder(lookup);
      Value forwarded = lookup->getOperand(0);
      // Ordinary sequential identity calls preserve the bound but exceed the
      // existing extraction frame limit. They do not deepen the call graph.
      for (unsigned i = 0; i < 257; ++i)
        forwarded = func::CallOp::create(builder, lookup->getLoc(), "identity",
                                         TypeRange{forwarded.getType()},
                                         ValueRange{forwarded})
                        .getResult(0);
      lookup->setOperand(0, forwarded);
      require(succeeded(verify(helper(*module, "read"))),
              "identity forwarding changed local structure");
      refusesBound(*module, "finite-analysis-limit");
    });
    cases.run(shape + " finite participant rechecks helper access", [&] {
      auto module = parse(context, forwardingFixture(matrix, true));
      project(*module);
      require(hasFinite(*module), "projection removed the finite fixture");
      auto reader = helper(*module, "read");
      auto *lookup = access(*module);
      lookup->setOperand(matrix ? 2 : 1, reader.getArguments().back());
      require(succeeded(verify(reader)),
              "ordinary index replacement changed local structure");
      refusesBound(*module);
    });
  }
  cases.run("protocol access rechecks sibling constant return", [&] {
    auto module = parse(context, directFixture);
    require(!hasFinite(*module), "expected an ordinary helper-only unit");
    auto index = helper(*module, "index");
    auto other = *std::next(index.front().getOps<data::IndexOp>().begin());
    index.front().back().setOperand(0, other.getOutput());
    require(succeeded(verify(index)), "ordinary index return was refused");
    refusesBound(*module);
  });
  cases.run(
      "participant access rechecks constant without finite computation", [&] {
        auto module = parse(context, directFixture);
        project(*module);
        require(!hasFinite(*module), "expected no finite computation");
        auto *lookup = access(*module);
        require(bool(lookup->getParentOfType<protocol_ir::ParticipantOp>()),
                "access is not in a participant body");
        auto index = lookup->getOperand(1).getDefiningOp<data::IndexOp>();
        require(bool(index), "projection did not expand index helper");
        index.setValue("4");
        refusesBound(*module);
      });
  cases.run("execution profile still excludes bounded mathematics", [&] {
    auto module = parse(context, directFixture);
    project(*module);
    require(succeeded(finite::verifyClosure(unit(*module))),
            "positive bound evidence was lost");
    // Projection expanded all used pure helpers. Remove the now-dormant
    // mathematical definitions so execution admission reaches the actual
    // participant access, rather than refusing an earlier top-level owner.
    for (auto helper : llvm::make_early_inc_range(
             unit(*module).getBody().front().getOps<func::FuncOp>()))
      helper.erase();
    require(succeeded(verify(*module)),
            "isolated participant control malformed");
    unit(*module).setProfileAttr(
        protocol_ir::ProfileAttr::get(&context, protocol_ir::Profile::Exec));
    require(succeeded(verify(access(*module))),
            "profile selection changed local access structure");
    // Execution admission uses its own closed instruction grammar.
    auto model = protocol::readExecutionModel(module->getOperation());
    zkc::test::refuses(std::move(model), "binding-operation");
    refuses(context, [&] { return verify(*module); }, "binding-operation");
  });
  cases.run("generic module verification is structural without an owner", [&] {
    auto module = parse(context, R"mlir(
!F = !algebra.field<"bls12-381.fr">
!A = !algebra.field_array<"bls12-381.fr",4>
module {
 func.func private @read(%xs:!A)->!F {
   %index = "data.index"() {value="0"} : ()->ui64
   %value = "data.bounded_at"(%xs,%index) : (!A,ui64)->!F
   func.return %value : !F
 }
})mlir");
    require(succeeded(finite::verifyClosure(*module)),
            "positive explicit closure check failed");
    access(*module)->getOperand(1).getDefiningOp<data::IndexOp>().setValue("4");
    require(succeeded(verify(access(*module))) && succeeded(verify(*module)),
            "generic verification unexpectedly performed closure admission");
    refuses(
        context, [&] { return finite::verifyClosure(*module); },
        "finite-bound");
  });
  return cases.result();
}
