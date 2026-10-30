#include "../lib/Conversion/Bindings.h"
#include "../lib/Target/ExecutionPorts.h"
#include "../lib/Target/PhysicalPlan.h"
#include "mlir/IR/Verifier.h"
#include "support/NativeCases.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "support/ScopedFixture.h"
#include "support/VariantFixture.h"
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
namespace sc = scopedComputation;
namespace sf = scopedFinite;
std::string printed(ModuleOp module) {
  std::string result;
  raw_string_ostream stream(result);
  module.print(stream);
  return result;
}
std::string encodedSite(StringRef name) {
  return "lc_" + std::to_string(name.size()) + "_" + name.str();
}
std::string chain(MLIRContext &context, bool residentInitial = true,
                  StringRef mode = {}, bool helperInArm = false,
                  bool conditional = false, bool stoppedArm = false) {
  const bool execution = !mode.empty();
  auto text =
      R"(!F = !algebra.field<"bls12-381.fr">
!G = !algebra.group<"bls12-381.g1">
)" + scopedFixture(
          R"(
"runtime.binding"() {sym_name="scale",contract="curve.scale",arguments=["bls12-381.g1"],implementation="blst/resident/curve.scale"} : ()->()
"runtime.binding"() {sym_name="guard",contract="control.require",arguments=[],implementation=""} : ()->()
)",
          execution ? "%g:!G,%s:!F,%c:i1,%lo:ui64,%hi:ui64,%allowed:i1,%t:!F"
                    : "%g:!G,%s:!F,%c:i1,%lo:ui64,%hi:ui64",
          execution ? "%g,%s,%c,%lo,%hi,%allowed,%t" : "%g,%s,%c,%lo,%hi",
          execution ? "!G,!F,i1,ui64,ui64,i1,!F" : "!G,!F,i1,ui64,ui64", "!G",
          scopedReturn("%g", "!G"), execution ? 7 : 5);
  auto module = parseSourceString<ModuleOp>(text, &context);
  require(bool(module), "resident chain fixture parse");
  auto work = sf::function(*module, "Work");
  work.getBody().dropAllReferences();
  work.getBody().getBlocks().clear();
  OpBuilder builder(&context);
  builder.setInsertionPointToEnd(work.addEntryBlock());
  auto group = work.getArgument(1).getType();
  auto field = work.getArgument(2).getType();
  auto boolean = builder.getI1Type();
  auto index = work.getArgument(4).getType();
  if (execution || helperInArm) {
    auto helper = sc::region(builder, work, "helper", {group, field}, {group});
    helper->removeAttr("runtime.region");
    helper->setAttr("runtime.origin",
                    builder.getArrayAttr({builder.getStringAttr("helper"),
                                          builder.getArrayAttr({})}));
    exec::ScopedExecutionBuilder control(builder, helper);
    control.returned(sc::apply(control, builder, "scale", "helper_scale",
                               helper.getArguments().drop_front(), {group}));
  }
  builder.setInsertionPointToEnd(&work.front());
  exec::ScopedExecutionBuilder control(builder, work);
  auto allowed = work.getArgument(execution ? 6 : 3);
  sc::apply(control, builder, "guard", "first_guard", {allowed}, {});
  Value initial = work.getArgument(1);
  if (residentInitial)
    initial = sc::apply(control, builder, "scale", "initial",
                        {initial, work.getArgument(2)}, {group})[0];
  auto invokeHelper = [&](exec::ScopedExecutionBuilder &nested, Value point,
                          Value scalar) {
    return nested.invoke(
        "func.call", {group}, nested.scoped({point, scalar}),
        {builder.getNamedAttr("callee",
                              FlatSymbolRefAttr::get(&context, "helper")),
         builder.getNamedAttr("runtime.site",
                              builder.getStringAttr("expanded"))})[0];
  };
  if (execution) {
    initial = sc::apply(control, builder, "scale", "adjacent",
                        {initial, work.getArgument(2)}, {group})[0];
    initial = invokeHelper(control, initial, work.getArgument(2));
  }
  auto joined = control.conditional(
      work.getArgument(3),
      {initial, work.getArgument(mode == "branch" ? 7 : 2), allowed}, {group},
      "branch", [&](unsigned arm) {
        auto region = sc::region(builder, work, arm ? "right" : "left",
                                 {group, field, boolean}, {group});
        exec::ScopedExecutionBuilder nested(builder, region);
        if (arm && stoppedArm) {
          nested.reject("reject", "stopped");
          return region;
        }
        if (!arm)
          sc::apply(nested, builder, "guard", "left_guard",
                    {region.getArgument(3)}, {});
        Value next = region.getArgument(1);
        if (!arm && helperInArm)
          next = invokeHelper(nested, next, region.getArgument(2));
        else if (!arm || !execution)
          next = sc::apply(nested, builder, "scale",
                           arm ? "right_scale" : "left_scale",
                           {next, region.getArgument(2)}, {group})[0];
        nested.complete({next});
        return region;
      });
  auto result = control.loop(
      work.getArgument(4), work.getArgument(5),
      {residentInitial ? joined.front() : work.getArgument(1)},
      {work.getArgument(mode == "loop" ? 7 : 2),
       mode == "loop" ? work.getArgument(3) : allowed},
      {group}, conditional, "loop", [&](unsigned) {
        SmallVector<Type> results;
        if (conditional)
          results.push_back(boolean);
        results.push_back(group);
        auto region = sc::region(builder, work, "iteration",
                                 {index, group, field, boolean}, results);
        exec::ScopedExecutionBuilder nested(builder, region);
        sc::apply(nested, builder, "guard", "loop_guard",
                  {region.getArgument(4)}, {});
        auto next =
            sc::apply(nested, builder, "scale", "body_scale",
                      {region.getArgument(2), region.getArgument(3)}, {group});
        if (conditional)
          next.insert(next.begin(), region.getArgument(4));
        nested.complete(next);
        return region;
      });
  control.returned(result);
  require(succeeded(verify(*module)), "resident chain fixture formation");
  return printed(*module);
}
OperationDecision &at(PhysicalPlan &plan, ModuleOp module, StringRef name) {
  auto operations = physicalPlanOperations(module);
  for (auto &d : plan.operations) {
    auto site = operations[d.operation]->getAttrOfType<StringAttr>("site");
    if (site && site.getValue() ==
                    (operations[d.operation]->getParentOfType<func::FuncOp>()
                         ? encodedSite(name)
                         : name.str()))
      return d;
  }
  throw std::runtime_error("missing site " + name.str());
}
Operation *semanticOperation(ModuleOp module, StringRef name) {
  auto flow = take(ExecutionPorts::read(module));
  for (auto *op : flow.operations())
    if (flow.get(op).step)
      if (auto site = op->getAttrOfType<StringAttr>("site"))
        if (site.getValue() == encodedSite(name))
          return op;
  throw std::runtime_error("missing semantic site " + name.str());
}
OperationDecision &bodyDecision(PhysicalPlan &plan, ModuleOp module,
                                StringRef name, unsigned index = 0) {
  auto flow = take(ExecutionPorts::read(module));
  auto *operation = semanticOperation(module, name);
  const auto &bodies = flow.get(operation).bodies;
  require(index < bodies.size(), "missing scoped control body");
  auto *owner = flow.body(bodies[index]).owner;
  auto operations = physicalPlanOperations(module);
  for (auto &decision : plan.operations)
    if (operations[decision.operation] == owner) {
      require(decision.blockArguments.size() == 1,
              "missing outlined data argument ports");
      return decision;
    }
  throw std::runtime_error("missing outlined body decision");
}
StringRef implementation(exec::ApplyOp op) {
  return SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
             op, op.getBindingAttr())
      .getImplementation();
}
// Move the complete checked invocation, including its success/failure edges.
// The mutant remains well-formed while changing the first observable failure.
void moveInvocationBefore(exec::ApplyOp moved, exec::ApplyOp before) {
  IRRewriter rewriter(moved.getContext());
  auto *prefix = before->getBlock();
  auto *tail = rewriter.splitBlock(prefix, before->getIterator());
  auto stop = cast<exec::DispatchOp>(before->getNextNode()).getStopped();
  OpBuilder builder(moved.getContext());
  builder.setInsertionPointToEnd(prefix);
  exec::ScopedExecutionBuilder control(builder,
                                       before->getParentOfType<func::FuncOp>());
  control.setLocation(moved.getLoc());
  auto values =
      control.invoke("exec.apply", moved.getOutcome().getType().getPayload(),
                     moved->getOperands(), moved->getAttrs(), stop);
  rewriter.mergeBlocks(tail, builder.getInsertionBlock());
  sc::omit(moved, values);
}
std::string variantSource(MLIRContext &context, StringRef descriptor) {
  auto text = "!Tag = " + variantAssembly(descriptor) + "\n" +
              R"(!F = !algebra.field<"bls12-381.fr">
!G = !algebra.group<"bls12-381.g1">
)" +
              scopedFixture(R"(
"runtime.binding"() {sym_name="scale",contract="curve.scale",arguments=["bls12-381.g1"],implementation="blst/resident/curve.scale"} : ()->()
)",
                            "%g:!G,%s:!F", "%g,%s", "!G,!F", "!G",
                            scopedReturn("%g", "!G"), 2);
  auto module = parseSourceString<ModuleOp>(text, &context);
  require(bool(module), "variant source parse");
  auto work = sf::function(*module, "Work");
  work.getBody().dropAllReferences();
  work.getBody().getBlocks().clear();
  OpBuilder builder(&context);
  builder.setInsertionPointToEnd(work.addEntryBlock());
  auto group = work.getArgument(1).getType();
  auto field = work.getArgument(2).getType();
  auto variant = zkc::test::variantType(&context, descriptor);
  exec::ScopedExecutionBuilder control(builder, work);
  auto point = sc::apply(control, builder, "scale", "initial",
                         work.getArguments().drop_front(), {group})[0];
  auto tag = control.invoke(
      "exec.variant", {variant}, control.scoped({work.getArgument(2)}),
      {builder.getNamedAttr("alternative", builder.getStringAttr("some")),
       builder.getNamedAttr("site", builder.getStringAttr("pack"))})[0];
  auto result = control.match(
      tag, {point}, {group}, {"none", "some"}, "match", [&](unsigned arm) {
        SmallVector<Type> arguments;
        if (arm)
          arguments.push_back(field);
        arguments.push_back(group);
        auto region = sc::region(builder, work, arm ? "some" : "none",
                                 arguments, {group});
        exec::ScopedExecutionBuilder nested(builder, region);
        Value next = region.getArgument(arm ? 2 : 1);
        if (arm)
          next = sc::apply(nested, builder, "scale", "matched_scale",
                           {next, region.getArgument(1)}, {group})[0];
        nested.complete({next});
        return region;
      });
  control.returned(result);
  require(succeeded(verify(*module)), "variant source formation");
  return printed(*module);
}
PhysicalPlanOptions residentABI(ModuleOp module) {
  PhysicalPlanOptions options;
  auto flow = take(ExecutionPorts::read(module));
  for (auto *op : flow.operations()) {
    auto type = flow.get(op).callable;
    if (!type || op->hasAttr("runtime.region"))
      continue;
    auto name = SymbolTable::getSymbolName(op).getValue().str();
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
    require(!isa<UnrealizedConversionCastOp>(op), "unresolved cast escaped");
    require(op->getName().getDialectNamespace() != "local" &&
                op->getName().getDialectNamespace() != "plan",
            "replaced execution owner escaped");
  });
  return take(readExecutionModel(module));
}
void emitExecutionFixture(MLIRContext &context, StringRef mode) {
  require(mode == "resident" || mode == "ports" || mode == "branch" ||
              mode == "loop",
          "unknown execution fixture");
  auto source = chain(context, true, mode);
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
          replaceText(chain(context), "bls12-381.g1", domain), context));
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
      bodyDecision(changed, *module, "loop").blockArguments[0][1] =
          decodeBoundType(&context,
                          take(defaultRepresentation(take(parseBoundType(
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
    cases.run(
        Twine("explicit entry and return ABI stays resident: ") + domain, [&] {
          auto module = take(executableFixture(
              replaceText(chain(context), "bls12-381.g1", domain), context));
          auto options = residentABI(*module);
          auto plan = take(
              proposePhysical(*module, installedCandidates(), {}, options));
          require(crossings(plan) == 0,
                  "resident ABI reconstructed Ark values");
          publish(*module, take(validatePhysical(*module, plan)));
        });
  }
  cases.run(
      "untaken branch and zero-trip loop retain reached conversions", [&] {
        auto module = take(executableFixture(chain(context, false), context));
        auto plan = take(proposePhysical(*module));
        require(at(plan, *module, "branch").conversions.empty() &&
                    at(plan, *module, "loop").conversions.empty(),
                "partial conversions became unconditional");
        require(at(plan, *module, "left_scale").conversions.size() == 2 &&
                    at(plan, *module, "body_scale").conversions.size() == 2,
                "reached conversions missing");
        auto checked = take(validatePhysical(*module, plan));
        publish(*module, checked);
        auto flow = take(ExecutionPorts::read(*module));
        auto *range = semanticOperation(*module, "loop");
        const auto &body = flow.body(flow.get(range).bodies.front());
        require(isa<exec::ApplyOp>(body.instructions.front()) &&
                    cast<exec::ApplyOp>(body.instructions.front()).getSite() ==
                        encodedSite("loop_guard"),
                "conversion crossed earlier failure");
        require(body.instructions.size() >= 2 &&
                    isa<exec::CompleteOp>(body.instructions.back()) &&
                    implementation(cast<exec::ApplyOp>(
                        body.instructions[body.instructions.size() - 2])) ==
                        "native/representation.convert",
                "backedge conversion left body");
      });
  cases.run("entry selections are exact and independently checked", [&] {
    auto module = take(executableFixture(chain(context), context));
    auto options = residentABI(*module);
    auto plan =
        take(proposePhysical(*module, installedCandidates(), {}, options));
    auto changed = plan;
    auto operations = physicalPlanOperations(*module);
    for (auto &d : changed.operations) {
      if (!d.functionType || d.blockArguments.empty() ||
          operations[d.operation]->hasAttr("runtime.region"))
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
      if (isa<func::FuncOp>(op) && !op->hasAttr("runtime.region")) {
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
          auto module = take(executableFixture(chain(context), context));
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
          module->walk([&](exec::ApplyOp op) {
            require(implementation(op) != "native/representation.convert",
                    "public entry ABI silently reverted to Ark");
          });
        });
  cases.run("partial conversion occurrence cannot be hoisted or shared", [&] {
    auto module = take(executableFixture(chain(context, false), context));
    auto plan = take(proposePhysical(*module));
    auto checked = take(validatePhysical(*module, plan));
    auto candidate = OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
    auto own = take(proposePhysical(*candidate));
    publish(*candidate, take(validatePhysical(*candidate, own)));
    accept(verifyPhysicalMaterialization(*module, *candidate, checked));
    auto flow = take(ExecutionPorts::read(*candidate));
    auto *range = semanticOperation(*candidate, "loop");
    exec::ApplyOp conversion, guard;
    for (auto *operation :
         flow.body(flow.get(range).bodies.front()).instructions)
      if (auto op = dyn_cast<exec::ApplyOp>(operation)) {
        if (implementation(op) == "native/representation.convert" &&
            !conversion)
          conversion = op;
        if (op.getSite() == encodedSite("loop_guard"))
          guard = op;
      }
    require(conversion && guard, "missing reached body operations");
    moveInvocationBefore(conversion, guard);
    require(succeeded(verify(*candidate)),
            "failure-order mutation must retain type formation");
    auto error = verifyPhysicalMaterialization(*module, *candidate, checked);
    require(bool(error), "moved partial failure escaped checker");
    consumeError(std::move(error));
  });
  cases.run("protocol repetition checks carried representation edges", [&] {
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
    // The returning body reads the changed port before the enclosing loop's
    // final signature check. Its undeclared conversion is the first refusal.
    refuses(validatePhysical(*module, changed), "binding-no-conversion");
    changed = plan;
    at(changed, *module, "rounds").blockArguments[0][1] = decodeBoundType(
        &context, take(parseBoundType("group:bls12-381.g1@blst/g1", true)));
    refuses(validatePhysical(*module, changed), "binding-operation-signature");
    publish(*module, take(validatePhysical(*module, plan)));
  });
  cases.run("conditional loop and terminal branch retain resident ports", [&] {
    auto source = chain(context, true, {}, false, true, true);
    auto module = take(executableFixture(source, context));
    auto plan = take(proposePhysical(*module));
    require(at(plan, *module, "loop").conversions.empty(),
            "conditional loop speculated conversions");
    publish(*module, take(validatePhysical(*module, plan)));
  });
  cases.run("expanded scoped helper preserves resident ABI", [&] {
    auto source = chain(context, true, {}, true);
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
)" + scopedFixture(R"(
"runtime.binding"() {sym_name="msm",contract="curve.msm",arguments=["bls12-381.g1"],implementation=""} : ()->()
)",
                   "%s:!V,%g:!GS", "%s,%g", "!V,!GS", "!G", R"(
%msm_attempt = "exec.apply"(%scope,%s,%g) {binding=@msm,site="msm",parameters=[]} : (!runtime.scope,!V,!GS)->!exec.outcome<(!G)>
"exec.dispatch"(%msm_attempt)[^msm,^failed] : (!exec.outcome<(!G)>)->()
^msm(%out:!G):
%done = "exec.returned"(%out) : (!G)->!exec.outcome<(!G)>
func.return %done : !exec.outcome<(!G)>
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
)" + scopedFixture(R"(
"runtime.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation="blst/resident/field.add"} : ()->()
"runtime.binding"() {sym_name="empty",contract="sequence.empty",arguments=["field:bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="append",contract="sequence.append",arguments=["field:bls12-381.fr"],implementation=""} : ()->()
)",
                   "%a:!F,%b:!F", "%a,%b", "!F,!F", "!S", R"(
%add_attempt = "exec.apply"(%scope,%a,%b) {binding=@add,site="add",parameters=[]} : (!runtime.scope,!F,!F)->!exec.outcome<(!F)>
"exec.dispatch"(%add_attempt)[^add,^failed] : (!exec.outcome<(!F)>)->()
^add(%x:!F):
%empty_attempt = "exec.apply"(%scope) {binding=@empty,site="empty",parameters=[]} : (!runtime.scope)->!exec.outcome<(!S)>
"exec.dispatch"(%empty_attempt)[^empty,^failed] : (!exec.outcome<(!S)>)->()
^empty(%empty:!S):
%packed_attempt = "exec.apply"(%scope,%empty,%x) {binding=@append,site="packed",parameters=[]} : (!runtime.scope,!S,!F)->!exec.outcome<(!S)>
"exec.dispatch"(%packed_attempt)[^packed,^failed] : (!exec.outcome<(!S)>)->()
^packed(%packed:!S):
%done = "exec.returned"(%packed) : (!S)->!exec.outcome<(!S)>
func.return %done : !exec.outcome<(!S)>
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
             .getOps<func::FuncOp>()
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
)" + scopedFixture(R"(
"runtime.binding"() {sym_name="mul",contract="vector.mul",arguments=["bls12-381.fr"],implementation="blst/resident/vector.mul"} : ()->()
"runtime.binding"() {sym_name="sum",contract="vector.sum",arguments=["bls12-381.fr"],implementation="blst/resident/vector.sum"} : ()->()
"runtime.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation="blst/resident/field.add"} : ()->()
)",
                   "%a:!V,%b:!V,%x:!F", "%a,%b,%x", "!V,!V,!F", "!F", R"(
%mul_attempt = "exec.apply"(%scope,%a,%b) {binding=@mul,site="mul",parameters=[]} : (!runtime.scope,!V,!V)->!exec.outcome<(!V)>
"exec.dispatch"(%mul_attempt)[^mul,^failed] : (!exec.outcome<(!V)>)->()
^mul(%product:!V):
%sum_attempt = "exec.apply"(%scope,%product) {binding=@sum,site="sum",parameters=[]} : (!runtime.scope,!V)->!exec.outcome<(!F)>
"exec.dispatch"(%sum_attempt)[^sum,^failed] : (!exec.outcome<(!F)>)->()
^sum(%sum:!F):
%add_attempt = "exec.apply"(%scope,%sum,%x) {binding=@add,site="add",parameters=[]} : (!runtime.scope,!F,!F)->!exec.outcome<(!F)>
"exec.dispatch"(%add_attempt)[^add,^failed] : (!exec.outcome<(!F)>)->()
^add(%out:!F):
%done = "exec.returned"(%out) : (!F)->!exec.outcome<(!F)>
func.return %done : !exec.outcome<(!F)>
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
        auto source = variantSource(context, *variant);
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
        auto &args =
            bodyDecision(changed, *module, "match", 1).blockArguments[0];
        args[0] = decodeBoundType(
            &context,
            take(parseBoundType("field:bls12-381.fr@arkworks.fr/0", true)));
        refuses(validatePhysical(*module, changed),
                "binding-operation-signature");
        publish(*module, take(validatePhysical(*module, plan)));
      });
  return cases.result();
}
