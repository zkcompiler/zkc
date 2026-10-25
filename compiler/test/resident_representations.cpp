#include "../lib/Conversion/Bindings.h"
#include "../lib/Target/PhysicalPlan.h"
#include "mlir/IR/Verifier.h"
#include "support/MathematicalFixture.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Protocol.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::target;
using namespace zkc::test;

namespace {
void accept(Error e) {
  if (e)
    throw std::runtime_error(toString(std::move(e)));
}
std::string chain(bool residentInitial = true, bool executionControls = false) {
  auto source =
      R"(!F = !algebra.field<"bls12-381.fr">
!G = !algebra.group<"bls12-381.g1">
)" + mathematicalFixture(
          R"(
"local.binding"() {sym_name="scale",contract="curve.scale",arguments=["bls12-381.g1"],implementation="blst/resident/curve.scale"} : ()->()
"local.binding"() {sym_name="guard",contract="control.require",arguments=[],implementation=""} : ()->()
)",
          executionControls
              ? "%g:!G,%s:!F,%c:i1,%lo:ui64,%hi:ui64,%allowed:i1,%t:!F"
              : "%g:!G,%s:!F,%c:i1,%lo:ui64,%hi:ui64",
          executionControls ? "%g,%s,%c,%lo,%hi,%allowed,%t"
                            : "%g,%s,%c,%lo,%hi",
          executionControls ? "!G,!F,i1,ui64,ui64,i1,!F" : "!G,!F,i1,ui64,ui64",
          "!G", R"(
"local.exec.require"(%c) {binding=@guard,site="first_guard",parameters=[]} : (i1)->()
%initial = "algebra.exec.group_scale"(%g,%s) {binding=@scale,site="initial",parameters=[]} : (!G,!F)->!G
%joined = "local.if"(%c,%initial,%s,%c) ({^left(%p:!G,%r:!F,%ok:i1):
  "local.exec.require"(%ok) {binding=@guard,site="left_guard",parameters=[]} : (i1)->()
  %next = "algebra.exec.group_scale"(%p,%r) {binding=@scale,site="left_scale",parameters=[]} : (!G,!F)->!G
  "local.yield"(%next) : (!G)->()
}, {^right(%p:!G,%r:!F,%ok:i1):
  %next = "algebra.exec.group_scale"(%p,%r) {binding=@scale,site="right_scale",parameters=[]} : (!G,!F)->!G
  "local.yield"(%next) : (!G)->()
}) {site="branch"} : (i1,!G,!F,i1)->!G
%result = "local.for"(%lo,%hi,%joined,%s,%c) ({^body(%i:ui64,%state:!G,%r:!F,%ok:i1):
  "local.exec.require"(%ok) {binding=@guard,site="loop_guard",parameters=[]} : (i1)->()
  %next = "algebra.exec.group_scale"(%state,%r) {binding=@scale,site="body_scale",parameters=[]} : (!G,!F)->!G
  "local.yield"(%next,%r,%ok) : (!G,!F,i1)->()
}) {site="loop"} : (ui64,ui64,!G,!F,i1)->!G
local.return %result : !G
)",
          executionControls ? 7 : 5);
  if (executionControls) {
    source = replaceText(source, "require\"(%c)", "require\"(%allowed)");
    source =
        replaceText(source, "%c,%initial,%s,%c", "%c,%initial,%s,%allowed");
    source = replaceText(source, "%lo,%hi,%joined,%s,%c",
                         "%lo,%hi,%joined,%s,%allowed");
  }
  if (!residentInitial) {
    source = replaceText(
        source,
        "%initial = \"algebra.exec.group_scale\"(%g,%s) "
        "{binding=@scale,site=\"initial\",parameters=[]} : (!G,!F)->!G",
        "");
    source = replaceText(source, "%c,%initial,%s,%c", "%c,%g,%s,%c");
    source = replaceText(source, "%lo,%hi,%joined,%s,%c", "%lo,%hi,%g,%s,%c");
  }
  return source;
}
std::string withScaleHelper(std::string source) {
  return replaceText(source, "local.func @Work", R"(
local.func private @helper(%p:!G,%r:!F)->!G attributes {logical_origin=["helper",[]]} {
  %next = "algebra.exec.group_scale"(%p,%r) {binding=@scale,site="helper_scale",parameters=[]} : (!G,!F)->!G
  local.return %next : !G
}
local.func @Work)");
}
OperationDecision &at(PhysicalPlan &plan, ModuleOp module, StringRef name) {
  auto operations = physicalPlanOperations(module);
  for (auto &d : plan.operations) {
    auto site = operations[d.operation]->getAttrOfType<StringAttr>("site");
    if (site && site.getValue() == name)
      return d;
  }
  throw std::runtime_error("missing site " + name.str());
}
PhysicalPlanOptions residentABI(ModuleOp module) {
  PhysicalPlanOptions options;
  for (auto *op : physicalPlanOperations(module)) {
    if (!isa<local::FuncOp, protocol_ir::ParticipantOp>(op))
      continue;
    auto name = op->getAttrOfType<StringAttr>("sym_name").getValue().str();
    auto type = cast<FunctionType>(
        op->getAttrOfType<TypeAttr>("function_type").getValue());
    for (bool output : {false, true}) {
      auto ports = output ? type.getResults() : type.getInputs();
      for (auto [i, port] : enumerate(ports)) {
        auto logical = take(encodeBoundType(port, false));
        if (logical.kind == "field" || logical.kind == "vector")
          options.functionPorts.push_back(
              {name, output, unsigned(i), logical.spelling() + "@blst/fr"});
        if (logical.kind == "group" || logical.kind == "groups")
          options.functionPorts.push_back(
              {name, output, unsigned(i),
               logical.spelling() + (logical.identity == "bls12-381.g1"
                                         ? "@blst/g1"
                                         : "@blst/g2")});
      }
    }
  }
  return options;
}
class MSMCandidates final : public CandidateCatalog {
public:
  Expected<std::vector<std::string>>
  implementations(const BindingApplication &op) const override {
    if (op.contract == "curve.msm")
      return std::vector<std::string>{"blst/resident/curve.msm"};
    return installedCandidates().implementations(op);
  }
  std::vector<BindingApplication>
  conversions(const BoundType &a, const BoundType &b) const override {
    return installedCandidates().conversions(a, b);
  }
};
size_t crossings(const PhysicalPlan &plan) {
  size_t count = 0;
  for (auto &op : plan.operations)
    count += op.conversions.size();
  return count;
}
program::Participants publish(ModuleOp module,
                              const CheckedPhysicalPlan &checked) {
  accept(materializePhysical(module, checked));
  require(succeeded(verify(module)), "physical module admission");
  module.walk([&](Operation *op) {
    require(!isa<UnrealizedConversionCastOp, local::ApplyOp>(op),
            "unresolved cast or helper call escaped");
    if (isa<local::CallOp>(op))
      require(!op->getParentOfType<local::FuncOp>(),
              "runtime helper call escaped");
  });
  return take(readExecutionModel(module));
}
void emitExecutionFixture(MLIRContext &context, StringRef mode) {
  require(mode == "resident" || mode == "ports" || mode == "branch" ||
              mode == "loop",
          "unknown execution fixture");
  auto source = withScaleHelper(chain(true, true));
  source = replaceText(source, "%joined =", R"(
%adjacent = "algebra.exec.group_scale"(%initial,%s) {binding=@scale,site="adjacent",parameters=[]} : (!G,!F)->!G
%expanded = local.apply @helper(%adjacent,%s) {site="expanded"} : (!G,!F)->!G
%joined =)");
  source = replaceText(source, "%c,%initial,%s,%allowed",
                       "%c,%expanded,%s,%allowed");
  // The arms have different mathematical results, making the selected branch
  // observable even when every input and output stays resident.
  source = replaceText(
      source,
      "%next = \"algebra.exec.group_scale\"(%p,%r) "
      "{binding=@scale,site=\"right_scale\",parameters=[]} : (!G,!F)->!G\n  "
      "\"local.yield\"(%next)",
      "\"local.yield\"(%p)");
  if (mode == "branch")
    source = replaceText(source, "%c,%expanded,%s,%allowed",
                         "%c,%expanded,%t,%allowed");
  if (mode == "loop")
    source = replaceText(source, "%lo,%hi,%joined,%s,%allowed",
                         "%lo,%hi,%joined,%t,%c");
  auto module = take(executableFixture(source, context));
  auto options = residentABI(*module);
  llvm::erase_if(options.functionPorts, [&](const auto &port) {
    return port.function != "helper" && !port.output &&
           (port.port == 6 || (mode == "ports" && port.port < 2));
  });
  auto plan =
      take(proposePhysical(*module, installedCandidates(), {}, options));
  require(crossings(plan) == (mode == "resident" ? 0
                              : mode == "ports"  ? 6
                                                 : 1),
          "unexpected execution fixture conversions");
  auto checked = take(validatePhysical(*module, plan));
  auto model = publish(*module, checked);
  accept(program::checkStructure(model));
  outs() << printJson(program::encode(model)) << '\n';
}
} // namespace

int main(int argc, char **argv) {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  if (argc != 1) {
    if (argc != 3 || StringRef(argv[1]) != "--emit") {
      errs() << "usage: " << argv[0]
             << " [--emit resident|ports|branch|loop]\n";
      return 2;
    }
    try {
      emitExecutionFixture(context, argv[2]);
      return 0;
    } catch (const std::exception &failure) {
      errs() << failure.what() << '\n';
      return 1;
    }
  }
  Cases cases;
  cases.run("exact flat representations and direct conversion law", [&] {
    for (auto spelling :
         {"field:bls12-381.fr@blst/fr", "vector:bls12-381.fr@blst/fr",
          "group:bls12-381.g1@blst/g1", "groups:bls12-381.g1@blst/g1",
          "group:bls12-381.g2@blst/g2", "groups:bls12-381.g2@blst/g2"}) {
      auto resident = take(parseBoundType(spelling, true));
      auto logical = resident;
      logical.representation.clear();
      auto ordinary = take(defaultRepresentation(logical));
      for (bool reverse : {false, true}) {
        auto from = reverse ? resident : ordinary;
        auto to = reverse ? ordinary : resident;
        BindingApplication application{"representation.convert",
                                       {logical.spelling()},
                                       "native/representation.convert",
                                       {from.spelling(), to.spelling()}};
        auto signature = take(resolveBinding(application, true));
        require(signature.inputs == std::vector<BoundType>{from} &&
                    signature.outputs == std::vector<BoundType>{to},
                "exact direct conversion ports");
        accept(checkDirectConversion(application, from, to));
        refuses(resolveBinding(application, false), "binding-conversion");
        application.physicalArguments[1] = application.physicalArguments[0];
        refuses(resolveBinding(application, true), "binding-conversion");
        application.implementation += "/unknown";
        refuses(resolveBinding(application, true), "binding-conversion");
      }
    }
    for (auto spelling :
         {"group:bls12-381.gt@blst/g1", "field:bn254.fr@blst/fr",
          "sequence<field:bls12-381.fr>@blst/fr",
          "sequence<field:bls12-381.fr@blst/fr>@logical.sequence/0",
          "field_array<bls12-381.fr,2>@blst/fr"}) {
      auto parsed = parseBoundType(spelling, true);
      require(!parsed, "unsupported aggregate layout admitted");
      consumeError(parsed.takeError());
    }
  });
  cases.run(
      "field defaults and explicit variable-time MSM remain unchanged", [&] {
        for (auto contract : {"field.add", "vector.mul", "curve.msm"}) {
          BindingApplication op{contract,
                                {StringRef(contract).starts_with("curve.")
                                     ? "bls12-381.g1"
                                     : "bls12-381.fr"},
                                ""};
          auto choices = take(installedCandidates().implementations(op));
          require(choices == std::vector<std::string>{"arkworks/" +
                                                      std::string(contract)},
                  "automatic resident choice");
          op.implementation = "blst/" + std::string(contract);
          refuses(resolveBinding(op, true), "binding-implementation");
        }
      });
  for (auto domain : {"bls12-381.g1", "bls12-381.g2"}) {
    cases.run(Twine("resident branch and loop ports: ") + domain, [&] {
      auto module = take(executableFixture(
          replaceText(chain(), "bls12-381.g1", domain), context));
      auto plan = take(proposePhysical(*module));
      require(crossings(plan) == 6, "unexpected resident conversion count");
      require(at(plan, *module, "initial").conversions.size() == 2,
              "operand conversions missing");
      require(at(plan, *module, "initial").conversions[0].operand == 0 &&
                  at(plan, *module, "initial").conversions[1].operand == 1,
              "conversion operand order");
      require(at(plan, *module, "branch").conversions.empty() &&
                  at(plan, *module, "loop").conversions.empty(),
              "conversion hoisted to control");
      require(at(plan, *module, "body_scale").conversions.size() == 1,
              "body scalar conversion missing");
      auto changed = plan;
      at(changed, *module, "loop").blockArguments[0][1] = decodeBoundType(
          &context, take(defaultRepresentation(take(parseBoundType(
                        std::string("group:") + domain, false)))));
      refuses(validatePhysical(*module, changed),
              "binding-operation-signature");
      changed = plan;
      at(changed, *module, "branch").outputs[0] = decodeBoundType(
          &context, take(parseBoundType("field:bls12-381.fr@blst/fr", true)));
      refuses(validatePhysical(*module, changed),
              "binding-operation-signature");
      changed = plan;
      std::reverse(at(changed, *module, "initial").conversions.begin(),
                   at(changed, *module, "initial").conversions.end());
      refuses(validatePhysical(*module, changed), "binding-no-conversion");
      auto checked = take(validatePhysical(*module, plan));
      publish(*module, checked);
    });
    cases.run(Twine("explicit entry and return ABI stays resident: ") + domain,
              [&] {
                auto module = take(executableFixture(
                    replaceText(chain(), "bls12-381.g1", domain), context));
                auto options = residentABI(*module);
                auto plan = take(proposePhysical(*module, installedCandidates(),
                                                 {}, options));
                require(crossings(plan) == 0,
                        "resident ABI reconstructed Ark values");
                publish(*module, take(validatePhysical(*module, plan)));
              });
  }
  cases.run(
      "untaken branch and zero-trip loop retain reached conversions", [&] {
        auto module = take(executableFixture(chain(false), context));
        auto plan = take(proposePhysical(*module));
        require(at(plan, *module, "branch").conversions.empty() &&
                    at(plan, *module, "loop").conversions.empty(),
                "partial conversions became unconditional");
        require(at(plan, *module, "left_scale").conversions.size() == 2 &&
                    at(plan, *module, "body_scale").conversions.size() == 2,
                "reached conversions missing");
        auto checked = take(validatePhysical(*module, plan));
        publish(*module, checked);
        module->walk([&](local::LocalForOp loop) {
          auto &block = loop.getBody().front();
          require(
              isa<plan::ApplyOp>(block.front()) &&
                  block.front().getAttrOfType<StringAttr>("site").getValue() ==
                      "loop_guard",
              "conversion crossed earlier failure");
          auto *yield = block.getTerminator();
          require(yield->getPrevNode()
                          ->getAttrOfType<StringAttr>("implementation")
                          .getValue() == "native/representation.convert",
                  "backedge conversion left body");
        });
      });
  cases.run("entry selections are exact and independently checked", [&] {
    auto module = take(executableFixture(chain(), context));
    auto options = residentABI(*module);
    auto plan =
        take(proposePhysical(*module, installedCandidates(), {}, options));
    auto changed = plan;
    for (auto &d : changed.operations) {
      if (!d.functionType || d.blockArguments.empty())
        continue;
      auto inputs = SmallVector<Type>(d.functionType.getInputs());
      inputs[0] = decodeBoundType(
          &context, take(defaultRepresentation(
                        take(parseBoundType("group:bls12-381.g1", false)))));
      d.functionType =
          FunctionType::get(&context, inputs, d.functionType.getResults());
      d.blockArguments[0][0] = inputs[0];
      break;
    }
    refuses(validatePhysical(*module, changed), "binding-operation-signature");
    auto duplicate = options;
    duplicate.functionPorts.push_back(options.functionPorts.front());
    refuses(proposePhysical(*module, installedCandidates(), {}, duplicate),
            "binding-duplicate-selection");
    auto unknown = options;
    unknown.functionPorts.front().function = "not_installed";
    refuses(proposePhysical(*module, installedCandidates(), {}, unknown),
            "binding-unknown-selection");
    auto invalid = options;
    invalid.functionPorts.front().physicalType = "group:bls12-381.g1@blst/fr";
    refuses(proposePhysical(*module, installedCandidates(), {}, invalid),
            "binding-representation");
    PhysicalPlanOptions incompatible;
    for (auto *op : physicalPlanOperations(*module))
      if (isa<local::FuncOp>(op)) {
        incompatible.functionPorts.push_back(
            {op->getAttrOfType<StringAttr>("sym_name").getValue().str(), false,
             0, "group:bls12-381.g1@blst/g1"});
        break;
      }
    refuses(proposePhysical(*module, installedCandidates(), {}, incompatible),
            "binding-no-conversion");
    auto checked = take(validatePhysical(*module, plan));
    (*module)->setAttr("changed", UnitAttr::get(&context));
    refuses(validatePhysical(*module, plan), "binding-stale-selection");
    auto stale = checked.checkInput(*module);
    require(bool(stale), "checked entry snapshot was not guarded");
    consumeError(std::move(stale));
  });
  for (bool usePass : {false, true})
    cases.run(
        usePass ? "public physical pass retains explicit entry choices"
                : "public physical lowering accepts explicit entry ABI",
        [&] {
          auto module = take(executableFixture(chain(), context));
          auto options = residentABI(*module);
          if (usePass) {
            PassManager pipeline(&context);
            pipeline.addPass(createSelectPhysicalPass({}, false, false, nullptr,
                                                      options.functionPorts));
            options.functionPorts.clear();
            require(succeeded(pipeline.run(*module)),
                    "selected public physical pass refused");
          } else
            require(succeeded(lowerPhysical(*module, {}, false, nullptr, false,
                                            options.functionPorts)),
                    "selected public physical lowering refused");
          require(succeeded(verify(*module)), "selected physical admission");
          take(readExecutionModel(*module));
          module->walk([&](plan::ApplyOp op) {
            require(op.getImplementation() != "native/representation.convert",
                    "public entry ABI silently reverted to Ark");
          });
        });
  cases.run("partial conversion occurrence cannot be hoisted or shared", [&] {
    auto module = take(executableFixture(chain(false), context));
    auto plan = take(proposePhysical(*module));
    auto checked = take(validatePhysical(*module, plan));
    auto candidate = OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
    auto own = take(proposePhysical(*candidate));
    publish(*candidate, take(validatePhysical(*candidate, own)));
    accept(verifyPhysicalMaterialization(*module, *candidate, checked));
    plan::ApplyOp conversion, guard;
    candidate->walk([&](local::LocalForOp loop) {
      for (auto op : loop.getBody().front().getOps<plan::ApplyOp>()) {
        if (op.getImplementation() == "native/representation.convert" &&
            !conversion)
          conversion = op;
        if (op.getSite() == "loop_guard")
          guard = op;
      }
    });
    require(conversion && guard, "missing reached body operations");
    conversion->moveBefore(guard);
    require(succeeded(verify(*candidate)),
            "failure-order mutation must retain type formation");
    auto error = verifyPhysicalMaterialization(*module, *candidate, checked);
    require(bool(error), "moved partial failure escaped checker");
    consumeError(std::move(error));
  });
  cases.run("unsupported protocol region residency independently refuses", [&] {
    auto module = take(executableFixture(R"(
!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%n:ui64,%x:!F):
  %out = "protocol.repeat"(%n,%x) ({ ^body(%i:ui64,%state:!F):
   "protocol.yield"(%state) : (!F)->()
  }) {site="rounds",carried=1:i64,maximum=4:i64,roles=["P"],carried_roles=[["P"]]} : (ui64,!F)->!F
  "protocol.return"(%out) : (!F)->()
 }) {sym_name="main",function_type=(ui64,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })",
                                         context));
    auto plan = take(proposePhysical(*module));
    auto changed = plan;
    at(changed, *module, "rounds").blockArguments[0][1] = decodeBoundType(
        &context, take(parseBoundType("field:bls12-381.fr@blst/fr", true)));
    refuses(validatePhysical(*module, changed), "binding-operation-signature");
    publish(*module, take(validatePhysical(*module, plan)));
  });
  cases.run("conditional loop and terminal branch retain resident ports", [&] {
    auto source = replaceText(
        chain(), "\"local.yield\"(%next,%r,%ok) : (!G,!F,i1)->()",
        "\"local.condition\"(%ok,%next,%r,%ok) : (i1,!G,!F,i1)->()");
    source = replaceText(
        source,
        "%next = \"algebra.exec.group_scale\"(%p,%r) "
        "{binding=@scale,site=\"right_scale\",parameters=[]} : (!G,!F)->!G\n  "
        "\"local.yield\"(%next) : (!G)->()",
        "\"local.stop\"() {reason=\"reject\",site=\"stopped\"} : ()->()");
    auto module = take(executableFixture(source, context));
    auto plan = take(proposePhysical(*module));
    require(at(plan, *module, "loop").conversions.empty(),
            "conditional loop speculated conversions");
    publish(*module, take(validatePhysical(*module, plan)));
  });
  cases.run("expanded local helper preserves resident ABI", [&] {
    auto source = withScaleHelper(chain());
    source = replaceText(
        source,
        "%next = \"algebra.exec.group_scale\"(%p,%r) "
        "{binding=@scale,site=\"left_scale\",parameters=[]} : (!G,!F)->!G",
        "%next = local.apply @helper(%p,%r) {site=\"expanded\"} : (!G,!F)->!G");
    auto module = take(executableFixture(source, context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {},
                                     residentABI(*module)));
    require(crossings(plan) == 0, "expanded helper broke resident edges");
    publish(*module, take(validatePhysical(*module, plan)));
  });
  cases.run("MSM preference cannot authorize variable-time residency", [&] {
    auto source = R"(!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!G = !algebra.group<"bls12-381.g1">
!GS = !algebra.group_vector<"bls12-381.g1">
)" + mathematicalFixture(R"(
"local.binding"() {sym_name="msm",contract="curve.msm",arguments=["bls12-381.g1"],implementation=""} : ()->()
)",
                         "%s:!V,%g:!GS", "%s,%g", "!V,!GS", "!G", R"(
%out = "algebra.exec.group_msm"(%s,%g) {binding=@msm,site="msm",parameters=[]} : (!V,!GS)->!G
local.return %out : !G
)",
                         2);
    auto module = take(executableFixture(source, context));
    MSMCandidates catalog;
    refuses(proposePhysical(*module, catalog), "binding-implementation");
    auto forged = take(proposePhysical(*module));
    for (auto &binding : forged.bindings)
      if (binding.binding.application.contract == "curve.msm")
        binding.binding.application.implementation = "blst/resident/curve.msm";
    refuses(validatePhysical(*module, forged, catalog),
            "binding-implementation");
  });
  cases.run("default sequence layout packs converted resident leaves", [&] {
    auto source = R"(!F = !algebra.field<"bls12-381.fr">
!S = !data.sequence<!algebra.field<"bls12-381.fr">>
)" + mathematicalFixture(R"(
"local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation="blst/resident/field.add"} : ()->()
"local.binding"() {sym_name="empty",contract="sequence.empty",arguments=["field:bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="append",contract="sequence.append",arguments=["field:bls12-381.fr"],implementation=""} : ()->()
)",
                         "%a:!F,%b:!F", "%a,%b", "!F,!F", "!S", R"(
%x = "algebra.exec.field_add"(%a,%b) {binding=@add,site="add",parameters=[]} : (!F,!F)->!F
%empty = "data.exec.sequence_empty"() {binding=@empty,site="empty",parameters=[]} : ()->!S
%packed = "data.exec.sequence_append"(%empty,%x) {binding=@append,site="packed",parameters=[]} : (!S,!F)->!S
local.return %packed : !S
)",
                         2);
    auto module = take(executableFixture(source, context));
    auto options = residentABI(*module);
    auto plan =
        take(proposePhysical(*module, installedCandidates(), {}, options));
    require(crossings(plan) == 1 &&
                at(plan, *module, "packed").conversions[0].operand == 1,
            "aggregate leaf did not convert exactly at pack");
    auto invalid = options;
    auto function =
        *cast<protocol_ir::ProtocolModuleOp>(module->getBody()->front())
             .getBody()
             .front()
             .getOps<local::FuncOp>()
             .begin();
    invalid.functionPorts.push_back(
        {function.getSymName().str(), true, 0, "blst/fr"});
    refuses(proposePhysical(*module, installedCandidates(), {}, invalid),
            "binding-representation");
    publish(*module, take(validatePhysical(*module, plan)));
  });
  cases.run("non-curve field and vector chain remains resident", [&] {
    auto source = R"(!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
)" + mathematicalFixture(R"(
"local.binding"() {sym_name="mul",contract="vector.mul",arguments=["bls12-381.fr"],implementation="blst/resident/vector.mul"} : ()->()
"local.binding"() {sym_name="sum",contract="vector.sum",arguments=["bls12-381.fr"],implementation="blst/resident/vector.sum"} : ()->()
"local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation="blst/resident/field.add"} : ()->()
)",
                         "%a:!V,%b:!V,%x:!F", "%a,%b,%x", "!V,!V,!F", "!F", R"(
%product = "algebra.exec.vector_mul"(%a,%b) {binding=@mul,site="mul",parameters=[]} : (!V,!V)->!V
%sum = "algebra.exec.vector_sum"(%product) {binding=@sum,site="sum",parameters=[]} : (!V)->!F
%out = "algebra.exec.field_add"(%sum,%x) {binding=@add,site="add",parameters=[]} : (!F,!F)->!F
local.return %out : !F
)",
                         3);
    auto module = take(executableFixture(source, context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {},
                                     residentABI(*module)));
    require(crossings(plan) == 0, "non-curve chain reconstructed Ark values");
    publish(*module, take(validatePhysical(*module, plan)));
  });
  cases.run(
      "match captures propagate independently of default payload layout", [&] {
        auto variant =
            encodeVariant({"ResidentChoice",
                           {{"none", {}}, {"some", {"field:bls12-381.fr"}}}});
        require(bool(variant), "variant fixture");
        auto source =
            "!Tag = !data.variant<\"" + *variant + "\">\n" +
            R"(!F = !algebra.field<"bls12-381.fr">
!G = !algebra.group<"bls12-381.g1">
)" +
            mathematicalFixture(R"(
"local.binding"() {sym_name="scale",contract="curve.scale",arguments=["bls12-381.g1"],implementation="blst/resident/curve.scale"} : ()->()
)",
                                "%g:!G,%s:!F", "%g,%s", "!G,!F", "!G", R"(
%x = "algebra.exec.group_scale"(%g,%s) {binding=@scale,site="initial",parameters=[]} : (!G,!F)->!G
%tag = "local.variant_inject"(%s) {alternative="some",site="pack"} : (!F)->!Tag
%out = "local.match"(%tag,%x) ({ ^none(%p:!G):
 "local.yield"(%p) : (!G)->()
}, { ^some(%r:!F,%p:!G):
 %next = "algebra.exec.group_scale"(%p,%r) {binding=@scale,site="matched_scale",parameters=[]} : (!G,!F)->!G
 "local.yield"(%next) : (!G)->()
}) {alternatives=["none","some"],site="match"} : (!Tag,!G)->!G
local.return %out : !G
)",
                                2);
        auto module = take(executableFixture(source, context));
        auto options = residentABI(*module);
        auto plan =
            take(proposePhysical(*module, installedCandidates(), {}, options));
        require(at(plan, *module, "match").conversions.empty(),
                "resident match capture reconstructed Ark");
        require(at(plan, *module, "pack").conversions.empty() &&
                    at(plan, *module, "matched_scale").conversions.empty(),
                "selected variant payload inserted a conversion");
        auto changed = plan;
        auto &args = at(changed, *module, "match").blockArguments[1];
        args[0] = decodeBoundType(
            &context,
            take(parseBoundType("field:bls12-381.fr@arkworks.fr/0", true)));
        refuses(validatePhysical(*module, changed),
                "binding-operation-signature");
        publish(*module, take(validatePhysical(*module, plan)));
      });
  return cases.result();
}
