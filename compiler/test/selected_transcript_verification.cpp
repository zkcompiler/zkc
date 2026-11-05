// Internal actual-IR checker tests. Include the implementation to reach the
// independent reader while source construction and projection-metadata
// admission still have selected-control migration gates. This does not test
// constructNativeProof, full candidate admission, or target execution. The
// parent integration owns registering and building this separate test target.
#include "../lib/Compiler/NativeProofVerification.cpp"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Transforms/Passes.h"

using namespace zkc;
using namespace zkc::test;
namespace req = zkc::detail;
namespace pir = zkc::protocol_ir;
namespace {
constexpr StringLiteral fixture = R"mlir(
!rng = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="constant",contract="index.constant",arguments=[],implementation="",function_type=(!runtime.scope)->!exec.outcome<(ui64)>} : ()->()
 func.func private @factory(%scope:!runtime.scope)->!exec.outcome<(ui64,ui64)>
 attributes {no_inline,runtime.origin=["factory",[]]} {
  %first = "exec.apply"(%scope) {binding=@constant,parameters=[7:ui64],site="first"} : (!runtime.scope)->!exec.outcome<(ui64)>
  "exec.dispatch"(%first)[^second,^failed] : (!exec.outcome<(ui64)>)->()
 ^second(%a:ui64):
  %next = "exec.apply"(%scope) {binding=@constant,parameters=[9:ui64],site="second"} : (!runtime.scope)->!exec.outcome<(ui64)>
  "exec.dispatch"(%next)[^done,^failed] : (!exec.outcome<(ui64)>)->()
 ^done(%b:ui64):
  %done = "exec.returned"(%a,%b) : (ui64,ui64)->!exec.outcome<(ui64,ui64)>
  func.return %done : !exec.outcome<(ui64,ui64)>
 ^failed(%stop:!exec.stop):
  %failure = "exec.failed"(%stop) : (!exec.stop)->!exec.outcome<(ui64,ui64)>
  func.return %failure : !exec.outcome<(ui64,ui64)>
 }
 "protocol.func"() ({ ^entry(%choice:i1,%other:i1,%x:ui64,%y:ui64,%coins:!rng):
  %p,%v = "protocol.branch"(%choice,%other,%x,%y) ({
  ^then(%stop:i1,%a:ui64,%b:ui64):
   "protocol.finish_if"(%stop,%a) {owner="P",site="finish_P"} : (i1,ui64)->()
   "protocol.finish_if"(%stop,%b) {owner="V",site="finish_V"} : (i1,ui64)->()
   "protocol.yield"(%a,%b) : (ui64,ui64)->()
  }, { ^else(%stop:i1,%a:ui64,%b:ui64):
   "protocol.yield"(%b,%a) : (ui64,ui64)->()
  }) {site="choose",roles=["P","V"],output_roles=[["P"],["V"]],alternatives=["then","else"]} : (i1,i1,ui64,ui64)->(ui64,ui64)
  "protocol.return"(%p,%v) : (ui64,ui64)->()
 }) {sym_name="main",function_type=(i1,i1,ui64,ui64,!rng)->(ui64,ui64),roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"],["P","V"],["V"]],output_roles=[["P"],["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";

pir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<pir::ProtocolModuleOp>(module.getBody()->front());
}
OwningOpRef<ModuleOp> copy(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}
pir::ParticipantBranchOp branch(ModuleOp module, StringRef role) {
  pir::ParticipantBranchOp result;
  module.walk([&](pir::ParticipantOp participant) {
    if (participant.getRole() == role)
      result = *participant.getBody()
                    .front()
                    .getOps<pir::ParticipantBranchOp>()
                    .begin();
  });
  require(bool(result), "missing branch");
  return result;
}
NativeProofPolicy policy() {
  NativeProofPolicy result;
  result.entry = "main";
  result.producer = "P";
  result.validator = "V";
  result.suite = "merlin3.bls12-381.fr64be/0";
  result.construction = "selected";
  result.publicInputs = {0, 1, 2, 3};
  result.services = {4};
  return result;
}
OwningOpRef<ModuleOp> source(MLIRContext &context, bool completion,
                             bool zeroState) {
  std::string text = fixture.str();
  if (zeroState) {
    auto replace = [&](StringRef from, StringRef to) {
      for (size_t pos = 0;
           (pos = text.find(from.str(), pos)) != std::string::npos;
           pos += to.size())
        text.replace(pos, from.size(), to.str());
    };
    replace("!exec.outcome<(ui64,ui64)>", "!exec.outcome<>");
    replace("\"exec.returned\"(%a,%b) : (ui64,ui64)",
            "\"exec.returned\"() : ()");
  }
  auto module = parseSourceString<ModuleOp>(text, &context);
  require(bool(module), "source parse");
  if (!completion) {
    SmallVector<Operation *> exits;
    module->walk([&](pir::FinishIfOp op) { exits.push_back(op); });
    for (auto *op : exits)
      op->erase();
  }
  require(succeeded(admitStage(*module)), "source admission");
  PassManager manager(&context);
  manager.addPass(protocol::createProjectProtocolPass(false));
  require(succeeded(manager.run(*module)) && succeeded(admitStage(*module)),
          "ordinary projection admission");
  return module;
}
protocol::ConstructionPlan plan(MLIRContext &context, bool zeroState) {
  protocol::ConstructionPlan result{};
  result.root = protocol::ConstructionPlan::Root::Local;
  result.symbol = FlatSymbolRefAttr::get(&context, "selected");
  result.initializer = FlatSymbolRefAttr::get(&context, "factory");
  result.suite = policy().suite;
  result.services = {4};
  if (!zeroState)
    result.state.assign(2,
                        IntegerType::get(&context, 64, IntegerType::Unsigned));
  return result;
}
// Materialize this fixture's explicitly stated rows, without invoking either
// production emitter. There are no replicas or coordinates in this fixture.
OwningOpRef<ModuleOp> candidate(ModuleOp original,
                                const protocol::ConstructionPlan &selected,
                                bool completion) {
  auto result = copy(original);
  OpBuilder builder(original.getContext());
  for (auto participant :
       unit(*result).getBody().front().getOps<pir::ParticipantOp>()) {
    auto &body = participant.getBody().front();
    SmallVector<Type> outputs(participant.getFunctionType().getResults());
    append_range(outputs, selected.state);
    participant.setFunctionType(builder.getFunctionType(
        participant.getFunctionType().getInputs(), outputs));
    participant->removeAttr("service_ports");
    builder.setInsertionPointToStart(&body);
    auto factory = pir::LocalCallOp::create(
        builder, participant.getLoc(), selected.state, ValueRange(),
        selected.initializer, builder.getStringAttr("initialize"),
        participant.getRoleAttr());
    SmallVector<Value> state(factory.getResults());
    auto old = *body.getOps<pir::ParticipantBranchOp>().begin();
    if (completion) {
      SmallVector<Value> inputs(old.getInputs());
      append_range(inputs, state);
      SmallVector<Type> types(old.getResultTypes());
      append_range(types, selected.state);
      OperationState replacement(old.getLoc(), old->getName());
      replacement.addOperands(inputs);
      replacement.addTypes(types);
      replacement.addAttributes(old->getAttrs());
      for (unsigned i = 0; i < old->getNumRegions(); ++i)
        replacement.addRegion();
      builder.setInsertionPoint(old);
      auto actual = cast<pir::ParticipantBranchOp>(builder.create(replacement));
      for (auto [from, to] : zip(old.getArms(), actual.getArms())) {
        to.takeBody(from);
        auto &arm = to.front();
        SmallVector<Value> captured;
        for (Type type : selected.state)
          captured.push_back(arm.addArgument(type, actual.getLoc()));
        for (auto exit : arm.getOps<pir::FinishIfOp>())
          exit->insertOperands(exit.getNumOperands(), captured);
        arm.back().insertOperands(arm.back().getNumOperands(), captured);
      }
      for (auto [from, to] : zip(old.getResults(), actual.getResults()))
        from.replaceAllUsesWith(to);
      old.erase();
      state = SmallVector<Value>(
          actual.getResults().take_back(selected.state.size()));
    }
    body.back().insertOperands(body.back().getNumOperands(), state);
  }
  auto projection =
      *unit(*result).getBody().front().getOps<pir::ProjectionOp>().begin();
  NamedAttrList interface(cast<DictionaryAttr>(projection.getInterfaces()[0]));
  SmallVector<Attribute> states;
  for (Type type : selected.state)
    states.push_back(TypeAttr::get(type));
  interface.set(
      "construction",
      builder.getDictionaryAttr(
          {builder.getNamedAttr(
               "format", builder.getStringAttr("zkc.native-construction/0")),
           builder.getNamedAttr("plan", builder.getStringAttr("selected")),
           builder.getNamedAttr("root", builder.getStringAttr("local")),
           builder.getNamedAttr("state", builder.getArrayAttr(states)),
           builder.getNamedAttr("helpers",
                                builder.getArrayAttr({selected.initializer})),
           builder.getNamedAttr("removed_services",
                                builder.getI64ArrayAttr({4})),
           builder.getNamedAttr("actions", interface.get("actions"))}));
  projection.setInterfacesAttr(
      builder.getArrayAttr({interface.getDictionary(original.getContext())}));
  return result;
}
bool check(ModuleOp original, ModuleOp actual,
           const protocol::ConstructionPlan &selected,
           size_t allowance = 1000000, bool *exhausted = nullptr) {
  auto configured = policy();
  auto requests = take(req::planNativeRequests(unit(original), configured, {}));
  auto execution = take(protocol::readSourceExecutionClosure(unit(actual)));
  req::TranscriptCorrespondence checker(unit(actual), configured, {}, &selected,
                                        {}, execution, requests, allowance);
  bool valid = checker.check(unit(original), unit(actual));
  if (exhausted)
    *exhausted = checker.exhausted();
  return valid;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("event-free source selector is checked before entering arms", [&] {
    auto original = source(context, false, false);
    auto target = branch(*original, "V");
    auto participant = target->getParentOfType<pir::ParticipantOp>();
    target->setOperand(0, participant.getBody().front().getArgument(1));
    auto configured = policy();
    refuses(req::planNativeRequests(unit(*original), configured, {}),
            "native-request-reconstruction");
  });
  cases.run("capacity exhaustion differs from a wiring mismatch", [&] {
    auto original = source(context, true, false);
    auto selected = plan(context, false);
    auto actual = candidate(*original, selected, true);
    bool exhausted = false;
    require(!check(*original, *actual, selected, 0, &exhausted) && exhausted,
            "setup exhaustion must be capacity");
    auto target = branch(*actual, "V");
    target->setOperand(0, target.getOperand(1));
    require(!check(*original, *actual, selected, 1000000, &exhausted) &&
                !exhausted,
            "selector substitution must be correspondence");
  });
  for (bool completion : {false, true})
    for (bool zeroState : {false, true})
      cases.run(Twine(completion ? "completion" : "event-free") +
                    (zeroState ? " with zero state" : " with copyable state"),
                [&] {
                  auto original = source(context, completion, zeroState);
                  auto selected = plan(context, zeroState);
                  auto actual = candidate(*original, selected, completion);
                  require(check(*original, *actual, selected),
                          "honest internal branch correspondence");
                });
  for (StringRef role : {"P", "V"})
    for (StringRef mutation :
         {"selector", "captures", "state capture", "state yield",
          "ordinary yield", "labels", "completion state"})
      cases.run(Twine(role) + " rejects " + mutation, [&] {
        auto original = source(context, true, false);
        auto selected = plan(context, false);
        auto actual = candidate(*original, selected, true);
        require(check(*original, *actual, selected), "baseline correspondence");
        auto target = branch(*actual, role);
        unsigned stateStart = target.getNumOperands() - 2;
        auto &arm = target.getArms()[0].front();
        if (mutation == "selector")
          target->setOperand(0, target.getOperand(1));
        else if (mutation == "captures") {
          Value saved = target.getOperand(2);
          target->setOperand(2, target.getOperand(3));
          target->setOperand(3, saved);
        } else if (mutation == "state capture")
          target->setOperand(stateStart, target.getOperand(2));
        else if (mutation == "state yield") {
          auto &emptyArm = target.getArms()[1].front();
          auto &yield = emptyArm.back();
          yield.setOperand(yield.getNumOperands() - 2,
                           emptyArm.getArguments().back());
        } else if (mutation == "ordinary yield")
          arm.back().setOperand(0, arm.getArgument(role == "P" ? 2 : 1));
        else if (mutation == "labels")
          target->setAttr(
              "alternatives",
              ArrayAttr::get(&context, {StringAttr::get(&context, "else"),
                                        StringAttr::get(&context, "then")}));
        else {
          auto exit = *arm.getOps<pir::FinishIfOp>().begin();
          exit->setOperand(exit.getNumOperands() - 2, arm.getArgument(1));
        }
        require(!check(*original, *actual, selected),
                "mutated internal branch accepted");
      });
  return cases.result();
}
