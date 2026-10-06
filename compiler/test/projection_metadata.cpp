#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Transforms/Passes.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
using namespace mlir;
using namespace zkc;
namespace {
void require(bool ok, llvm::StringRef message) {
  if (!ok) {
    llvm::errs() << message << '\n';
    std::exit(1);
  }
}
protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
OwningOpRef<ModuleOp> copy(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}
void run(ModuleOp module, std::unique_ptr<Pass> pass) {
  PassManager manager(module.getContext());
  manager.addPass(std::move(pass));
  require(succeeded(manager.run(module)), "projection test pass failed");
}
void rename(protocol_ir::ProtocolModuleOp scope, Operation *symbol,
            StringRef name) {
  auto replacement = StringAttr::get(scope.getContext(), name);
  auto uses = SymbolTable::getSymbolUses(symbol, scope);
  require(uses && !uses->empty(), "retained symbol has no MLIR uses");
  require(
      succeeded(SymbolTable::replaceAllSymbolUses(symbol, replacement, scope)),
      "symbol rename failed");
  SymbolTable::setSymbolName(symbol, replacement);
}
constexpr StringLiteral fixture = R"mlir(module { "protocol.module"() ({
  relation.declare @predicate {sym_visibility="private",kind="external", key="example/echo", revision="1", signature=(i1) -> i1, purposes=["statement"]}
  "protocol.func"() ({
  ^entry(%x: i1):
    protocol.statement @predicate(%x) {selectors=["P"], acceptance=0 : i64} : i1
    %reply = protocol.exchange %x {sender="P", receiver="V", site="echo"} : i1
    protocol.guard %reply {owner="V", site="accept"}
    "protocol.return"(%reply) : (i1) -> ()
  }) {sym_name="main", function_type=(i1) -> i1, roles=["P", "V"], input_roles=[["P"]], output_roles=[["V"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () })mlir";
void profileEdges(MLIRContext &context) {
  // Without a guard, lowering needs no generated calculations. All four
  // modules are well formed, so these refusals discriminate phase policy.
  std::string text = fixture.str();
  auto guard =
      text.find("    protocol.guard %reply {owner=\"V\", site=\"accept\"}\n");
  require(guard != std::string::npos, "missing profile fixture guard");
  text.erase(guard, text.find('\n', guard) - guard + 1);
  auto common = parseSourceString<ModuleOp>(text, &context);
  require(bool(common), "profile fixture refused");
  auto participant = copy(*common);
  run(*participant, protocol::createProjectProtocolPass());
  auto executable = copy(*participant);
  run(*executable, protocol::createLowerMathPass());
  auto physical = copy(*executable);
  run(*physical, protocol::createSelectPhysicalPass());
  for (auto module : {participant.get(), executable.get(), physical.get()})
    require(succeeded(mathematical::verifyProjectionPreserved(module, module)),
            "same-profile postcondition refused unchanged input");
  auto legacy = parseSourceString<ModuleOp>(R"mlir(module {
    "protocol.module"() ({ ^entry: }) {profile=#protocol.profile<protocol_exec>} : () -> ()
  })mlir",
                                            &context);
  require(bool(legacy), "legacy profile fixture refused");
  for (auto [before, after] : {std::pair{common.get(), common.get()},
                               std::pair{legacy.get(), executable.get()},
                               std::pair{common.get(), executable.get()},
                               std::pair{common.get(), physical.get()},
                               std::pair{participant.get(), physical.get()},
                               std::pair{executable.get(), participant.get()},
                               std::pair{physical.get(), executable.get()},
                               std::pair{physical.get(), participant.get()}}) {
    bool phaseDiagnostic = false;
    ScopedDiagnosticHandler expected(&context, [&](Diagnostic &diagnostic) {
      phaseDiagnostic |=
          diagnostic.str().find("unsupported preservation profile edge") !=
          std::string::npos;
      return success();
    });
    require(failed(mathematical::verifyProjectionPreserved(before, after)) &&
                phaseDiagnostic,
            "nonadjacent or backward profile edge passed preservation");
  }
}
void suppliedMaterialization(MLIRContext &context) {
  auto source =
      parseSourceString<ModuleOp>(R"mlir(module { "protocol.module"() ({
    "protocol.func"() ({ ^entry(%x: i1, %y: i1):
      %received = protocol.exchange %x {sender="P", receiver="V", site="message"} : i1
      "protocol.return"(%received) : (i1) -> ()
    }) {sym_name="main", function_type=(i1,i1)->i1, roles=["P","V"],
        input_roles=[["P"],["P"]], output_roles=[["V"]]} : () -> ()
  }) {profile=#protocol.profile<protocol>} : () -> () })mlir",
                                  &context);
  require(bool(source), "supplied materialization fixture refused");
  run(*source, protocol::createProjectProtocolPass());
  run(*source, protocol::createLowerMathPass());
  auto record = *unit(*source)
                     .getBody()
                     .front()
                     .getOps<protocol_ir::ProjectionOp>()
                     .begin();
  record.erase();
  require(succeeded(verify(*source)), "supplied executable is not well formed");
  auto candidate = copy(*source);
  run(*candidate, protocol::createSelectPhysicalPass());
  require(
      succeeded(mathematical::verifyProjectionPreserved(*source, *candidate)),
      "supplied materialization changed participant behavior");
  unsigned changed = 0;
  candidate->walk([&](protocol_ir::EmitOp send) {
    auto &body =
        send->getParentOfType<protocol_ir::ParticipantOp>().getBody().front();
    send->setOperand(0, body.getArgument(1));
    ++changed;
  });
  require(changed == 1 && succeeded(verify(*candidate)),
          "supplied same-typed operand mutation lost formation");
  bool dataFlowDiagnostic = false;
  ScopedDiagnosticHandler expected(&context, [&](Diagnostic &diagnostic) {
    dataFlowDiagnostic |=
        diagnostic.str().find("execution order or data flow") !=
        std::string::npos;
    return success();
  });
  require(
      failed(mathematical::verifyProjectionPreserved(*source, *candidate)) &&
          dataFlowDiagnostic,
      "supplied materialization accepted changed participant data flow");
}
void changeLocalOperand(ModuleOp module) {
  unsigned mutations = 0;
  module.walk([&](Operation *op) {
    if (mutations || !op->getParentOfType<local::FuncOp>())
      return;
    if (op->getNumOperands() == 2 && op->getOperand(0) != op->getOperand(1) &&
        op->getOperand(0).getType() == op->getOperand(1).getType()) {
      op->setOperand(0, op->getOperand(1));
      ++mutations;
    }
  });
  require(mutations == 1 && succeeded(verify(module)),
          "executable local mutation lost formation");
}
void executableIdentity(ModuleOp module) {
  auto unchanged = copy(module);
  require(
      succeeded(mathematical::verifyProjectionPreserved(module, *unchanged)),
      "same-profile executable clone refused");
  {
    auto changed = copy(module);
    changeLocalOperand(*changed);
    bool identified = false;
    ScopedDiagnosticHandler expected(module.getContext(), [&](Diagnostic &d) {
      identified |=
          d.str().find("mathematical-projection") != std::string::npos;
      return success();
    });
    require(failed(mathematical::verifyProjectionPreserved(module, *changed)) &&
                identified,
            "same-profile preservation accepted changed executable local work");
  }
  // Both supplied and metadata-bearing forms are independently well formed.
  // An adjacent check cannot manufacture a source relationship for the former.
  auto supplied = copy(module);
  auto record = *unit(*supplied)
                     .getBody()
                     .front()
                     .getOps<protocol_ir::ProjectionOp>()
                     .begin();
  record.erase();
  require(succeeded(verify(*supplied)), "supplied executable fixture refused");
  ScopedDiagnosticHandler expected(module.getContext(),
                                   [](Diagnostic &) { return success(); });
  require(failed(mathematical::verifyProjectionPreserved(*supplied, module)),
          "same-profile preservation invented projection metadata");
}
void executableEdges(ModuleOp executable, ModuleOp physical) {
  auto eraseRecord = [](ModuleOp module) {
    (*unit(module)
          .getBody()
          .front()
          .getOps<protocol_ir::ProjectionOp>()
          .begin())
        .erase();
  };
  auto expectRefusal = [](ModuleOp before, ModuleOp after, StringRef message) {
    require(succeeded(verify(before)) && succeeded(verify(after)),
            "metadata mutation lost formation");
    bool identified = false;
    ScopedDiagnosticHandler expected(before.getContext(), [&](Diagnostic &d) {
      identified |= d.str().find(message.str()) != std::string::npos;
      return success();
    });
    require(failed(mathematical::verifyProjectionPreserved(before, after)) &&
                identified,
            "adjacent edge missed its metadata refusal");
  };
  auto supplied = copy(executable);
  eraseRecord(*supplied);
  expectRefusal(*supplied, physical,
                "compilation added an ungrounded projection record");
  auto lost = copy(physical);
  eraseRecord(*lost);
  expectRefusal(executable, *lost,
                "projected compilation changed or lost a frozen interface");
  auto reordered = copy(physical);
  auto record = *unit(*reordered)
                     .getBody()
                     .front()
                     .getOps<protocol_ir::ProjectionOp>()
                     .begin();
  auto calculations = record.getCalculations();
  require(calculations.size() > 1,
          "metadata fixture needs multiple calculations");
  SmallVector<Attribute> reversed(llvm::reverse(calculations));
  record.setCalculationsAttr(ArrayAttr::get(physical.getContext(), reversed));
  expectRefusal(executable, *reordered,
                "compilation changed generated calculation origins");

  // This public query deliberately covers only participant flow and metadata
  // on Exec -> Physical. The pipeline's internal materialization validator
  // checks local bodies too (see target_decisions.cpp's mutation controls).
  auto changed = copy(physical);
  changeLocalOperand(*changed);
  require(
      succeeded(mathematical::verifyProjectionPreserved(executable, *changed)),
      "participant projection query changed its documented partial scope");
}
void scheduling(MLIRContext &context) {
  auto common =
      parseSourceString<ModuleOp>(R"mlir(module { "protocol.module"() ({
    "protocol.func"() ({
    ^entry(%x: !algebra.field<"bls12-381.fr">, %go: i1):
      %a = algebra.field_add %x, %x : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %b = algebra.field_multiply %a, %x : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      protocol.guard %go {owner="P", site="gate"}
      %first = protocol.exchange %a {sender="P", receiver="V", site="first"} : !algebra.field<"bls12-381.fr">
      %second = protocol.exchange %b {sender="P", receiver="V", site="second"} : !algebra.field<"bls12-381.fr">
      "protocol.return"(%second) : (!algebra.field<"bls12-381.fr">) -> ()
    }) {sym_name="schedule", function_type=(!algebra.field<"bls12-381.fr">, i1) -> !algebra.field<"bls12-381.fr">, roles=["P", "V"], input_roles=[["P"], ["P"]], output_roles=[["P", "V"]]} : () -> ()
  }) {profile=#protocol.profile<protocol>} : () -> () })mlir",
                                  &context);
  require(bool(common), "schedule fixture refused");
  run(*common, protocol::createProjectProtocolPass());
  auto bound = copy(*common), repeated = copy(*common);
  run(*bound, protocol::createLowerMathPass());
  run(*repeated, protocol::createLowerMathPass());
  executableIdentity(*bound);
  auto identityPhysical = copy(*bound);
  run(*identityPhysical, protocol::createSelectPhysicalPass());
  executableIdentity(*identityPhysical);
  executableEdges(*bound, *identityPhysical);
  require(OperationEquivalence::isEquivalentTo(
              bound->getOperation(), repeated->getOperation(),
              OperationEquivalence::IgnoreLocations),
          "binding schedule is not deterministic");
  protocol_ir::ParticipantOp sender;
  bound->walk([&](protocol_ir::ParticipantOp op) {
    if (op.getRole() == "P")
      sender = op;
  });
  SmallVector<local::CallOp> calls(
      sender.getBody().front().getOps<local::CallOp>());
  require(calls.size() == 3 && calls[0].getSite() == "gate" &&
              calls[0].getNumResults() == 0,
          "guard did not remain before later work");
  require(calls[1].getNumOperands() == 1 && calls[1].getNumResults() == 1 &&
              calls[1].getInputs()[0] ==
                  sender.getBody().front().getArgument(0) &&
              isa<protocol_ir::EmitOp>(calls[1]->getNextNode()),
          "first consumer was not outlined at its send");
  require(calls[2].getNumOperands() == 2 &&
              calls[2].getInputs()[0] == calls[1].getResult(0) &&
              calls[2].getInputs()[1] ==
                  sender.getBody().front().getArgument(0) &&
              isa<protocol_ir::EmitOp>(calls[2]->getNextNode()),
          "later calculation did not reuse its earlier dependency");
  auto mutated = copy(*bound);
  mutated->walk([&](protocol_ir::ParticipantOp op) {
    if (op.getRole() != "P")
      return;
    SmallVector<local::CallOp> local(
        op.getBody().front().getOps<local::CallOp>());
    local[1]->moveBefore(local[0]);
  });
  require(succeeded(verify(*mutated)),
          "schedule mutation must remain structurally valid");
  {
    ScopedDiagnosticHandler expected(&context,
                                     [](Diagnostic &) { return success(); });
    require(failed(mathematical::verifyProjectionPreserved(*bound, *mutated)),
            "frozen bound schedule allowed new work before the guard");
  }
  // Native bundle indices rely on the profile-owned positional roster check.
  {
    auto invalid = copy(*bound);
    auto record = *unit(*invalid)
                       .getBody()
                       .front()
                       .getOps<protocol_ir::ProjectionOp>()
                       .begin();
    auto interface = cast<DictionaryAttr>(record.getInterfaces()[0]);
    auto participants = interface.getAs<ArrayAttr>("participants");
    SmallVector<Attribute> reordered(participants.getValue());
    require(reordered.size() >= 2, "roster test needs distinct roles");
    std::swap(reordered[0], reordered[1]);
    NamedAttrList fields(interface);
    fields.set("participants", ArrayAttr::get(&context, reordered));
    SmallVector<Attribute> interfaces(record.getInterfaces().getValue());
    interfaces[0] = fields.getDictionary(&context);
    record.setInterfacesAttr(ArrayAttr::get(&context, interfaces));
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(verify(*invalid)), "reordered participant mapping admitted");
    auto exported = protocol::exportSource(invalid->getOperation());
    require(!exported, "export bypassed positional roster verification");
    llvm::consumeError(exported.takeError());
  }
  {
    auto invalid = copy(*bound);
    auto record = *unit(*invalid)
                       .getBody()
                       .front()
                       .getOps<protocol_ir::ProjectionOp>()
                       .begin();
    SmallVector<Attribute> origins(record.getCalculations().getValue());
    require(!origins.empty(), "calculation test needs a guard recipe");
    origins.push_back(origins.front());
    record.setCalculationsAttr(ArrayAttr::get(&context, origins));
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(verify(*invalid)), "duplicate calculation origin admitted");
  }
  auto physical = copy(*bound);
  run(*physical, protocol::createSelectPhysicalPass({}, false, true));
  require(succeeded(mathematical::verifyProjectionPreserved(*bound, *physical)),
          "storage-release pipeline changed participant control data flow");
  // Generic transformations must retain a zero-result stopping invocation.
  run(*bound, createCanonicalizerPass());
  run(*bound, createCSEPass());
  run(*bound, createSymbolDCEPass());
  unsigned guards = 0;
  bound->walk([&](local::CallOp call) { guards += call.getSite() == "gate"; });
  require(guards == 1, "generic transforms erased the zero-result guard");
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  profileEdges(context);
  suppliedMaterialization(context);
  scheduling(context);
  auto common = parseSourceString<ModuleOp>(fixture, &context);
  require(bool(common), "common fixture refused");
  auto projected = copy(*common);
  run(*projected, protocol::createProjectProtocolPass());
  require(unit(*projected).getProfile() == protocol_ir::Profile::Participant,
          "projection lowered calculations prematurely");
  require(
      succeeded(mathematical::verifyProjectionPreserved(*common, *projected)),
      "projection lost original interface");
  auto root = unit(*projected);
  auto relation = *root.getBody().front().getOps<relation::DeclareOp>().begin();
  rename(root, relation, "renamed_predicate");
  auto participant =
      *root.getBody().front().getOps<protocol_ir::ParticipantOp>().begin();
  rename(root, participant, "renamed_participant");
  auto entry =
      *root.getBody().front().getOps<protocol_ir::ProtocolEntryOp>().begin();
  rename(root, entry, "renamed_entry");
  require(succeeded(verify(*projected)),
          "nested symbol uses did not survive rename");
  run(*projected, createSymbolDCEPass());
  require(SymbolTable::lookupSymbolIn(root, "renamed_predicate") != nullptr,
          "DCE erased retained private relation");
  auto bound = copy(*projected);
  run(*bound, protocol::createLowerMathPass());
  require(
      succeeded(mathematical::verifyProjectionPreserved(*projected, *bound)),
      "lowering changed frozen interface");
  // Symbol-user verification resolves references only. The enclosing profile
  // owns the full metadata check, including malformed dictionaries. Exercise
  // both stages so a second full check cannot drift back into the symbol hook.
  for (auto stage : {projected.get(), bound.get()}) {
    auto invalid = copy(stage);
    auto record = *unit(*invalid)
                       .getBody()
                       .front()
                       .getOps<protocol_ir::ProjectionOp>()
                       .begin();
    record.setInterfacesAttr(
        ArrayAttr::get(&context, {DictionaryAttr::get(&context)}));
    SymbolTableCollection symbols;
    require(succeeded(record.verifySymbolUses(symbols)),
            "symbol hook attempted full metadata validation");
    ScopedDiagnosticHandler expected(&context,
                                     [](Diagnostic &) { return success(); });
    require(failed(verify(*invalid)),
            "module did not validate malformed metadata");
  }
  auto physical = copy(*bound);
  run(*physical, protocol::createSelectPhysicalPass());
  require(succeeded(mathematical::verifyProjectionPreserved(*bound, *physical)),
          "physical conversion changed logical metadata");
  // Absence is valid for independently supplied executable programs, but not
  // for the result of a pass that took a projected program as its input.
  auto supplied = copy(*bound);
  auto &declarations = unit(*supplied).getBody().front();
  for (auto &op : llvm::make_early_inc_range(declarations))
    if (isa<protocol_ir::ProjectionOp, relation::DeclareOp>(op))
      op.erase();
  require(succeeded(verify(*supplied)),
          "supplied exec path unexpectedly requires metadata");
  ScopedDiagnosticHandler expected(&context,
                                   [](Diagnostic &) { return success(); });
  require(failed(mathematical::verifyProjectionPreserved(*bound, *supplied)),
          "metadata loss passed frozen-input check");
  auto malformed = copy(*projected);
  auto record = *unit(*malformed)
                     .getBody()
                     .front()
                     .getOps<protocol_ir::ProjectionOp>()
                     .begin();
  record.erase();
  require(failed(verify(*malformed)),
          "participant admitted missing projection record");
  malformed = copy(*projected);
  malformed->walk([&](protocol_ir::EmitOp op) { op.setPeer("outsider"); });
  require(failed(verify(*malformed)), "exchange peer mutation admitted");
  malformed = copy(*projected);
  malformed->walk([&](protocol_ir::ParticipantOp op) {
    if (op.getRole() != "V")
      return;
    OpBuilder builder(&op.getBody().front().back());
    auto guard = *op.getBody().front().getOps<local::GuardOp>().begin();
    local::GuardOp::create(builder, op.getLoc(), guard.getCondition(),
                           "unrecorded");
  });
  require(failed(verify(*malformed)), "unrecorded participant action admitted");
  malformed = copy(*projected);
  malformed->walk([&](protocol_ir::ProtocolEntryOp op) {
    op->setAttr("trusted", UnitAttr::get(&context));
  });
  require(failed(verify(*malformed)), "unknown entry annotation admitted");
  malformed = copy(*projected);
  malformed->walk([&](relation::DeclareOp op) {
    op->setAttr("trusted", UnitAttr::get(&context));
  });
  require(failed(verify(*malformed)), "unknown relation annotation admitted");
  malformed = copy(*bound);
  malformed->walk([&](protocol_ir::ProjectionOp op) {
    op.setCalculationsAttr(ArrayAttr::get(&context, {}));
  });
  require(failed(verify(*malformed)),
          "guard recipe lost its calculation origin");
  auto structural = protocol::readExecutionModel(malformed->getOperation());
  require(bool(structural), "mutation must retain the executable grammar");
  auto exported = protocol::exportSource(malformed->getOperation());
  require(!exported, "checked export bypassed projection metadata validation");
  llvm::consumeError(exported.takeError());
  auto serialized = protocol::exportModule(malformed->getOperation());
  require(!serialized,
          "carrier export bypassed projection metadata validation");
  llvm::consumeError(serialized.takeError());
  llvm::outs() << "projection symbols, physical metadata and frozen-input "
                  "checks passed\n";
}
