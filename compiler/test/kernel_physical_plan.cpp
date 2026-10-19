#include "../lib/Conversion/Bindings.h"
#include "../lib/Target/PhysicalPlan.h"
#include "mlir/IR/Verifier.h"
#include "support/MathematicalFixture.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Transforms/Kernel.h"
#include "zkc/Transforms/MathematicalTrace.h"
#include "zkc/Transforms/Protocol.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::target;
using namespace zkc::test;

namespace {
constexpr StringLiteral scalarSource = R"mlir(
!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%a:!F,%b:!F):
   %difference = algebra.field_subtract %a,%b : (!F,!F)->!F
   %product = algebra.field_multiply %difference,%b : (!F,!F)->!F
   "protocol.return"(%difference,%product) : (!F,!F)->()
 }) {sym_name="main",function_type=(!F,!F)->(!F,!F),roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";

std::string pinnedSource() {
  return R"mlir(
!F = !algebra.field<"bls12-381.fr">
!T = !poly.multilinear<"bls12-381.fr">
)mlir" + mathematicalFixture(R"mlir(
func.func private @difference(%a:!F,%b:!F)->!F {
  %v = algebra.field_subtract %a,%b : (!F,!F)->!F
  func.return %v : !F
}
local.realize @realized = @difference : (!F,!F)->!F
"local.binding"() {sym_name="pinned",contract="poly.fold",arguments=["bls12-381.fr"],implementation="arkworks-msb/poly.fold"} : ()->()
)mlir",
                             "%table:!T,%other:!T,%a:!F,%b:!F",
                             "%table,%other,%a,%b", "!T,!T,!F,!F", "!T", R"mlir(
%difference = local.apply @realized(%a,%b) {site="calculate"} : (!F,!F)->!F
%folded = "poly.exec.fold"(%table,%difference) {binding=@pinned,site="pinned_fold",parameters=[]} : (!T,!F)->!T
local.return %folded : !T
)mlir",
                             4);
}

std::string nestedSource() {
  return R"mlir(!F = !algebra.field<"bls12-381.fr">
)mlir" + mathematicalFixture(R"mlir(
kernel.module @difference {
  func.func @evaluate(%a:!F,%b:!F)->!F {
    %v = algebra.field_subtract %a,%b : (!F,!F)->!F
    func.return %v : !F
  }
}
"local.binding"() {sym_name="require",contract="control.require",arguments=[],implementation=""} : ()->()
)mlir",
                             "%a:!F,%b:!F,%enabled:i1", "%a,%b,%enabled",
                             "!F,!F,i1", "!F", R"mlir(
%result = "local.if"(%enabled,%a,%b,%enabled) ({
^chosen(%left:!F,%right:!F,%condition:i1):
  %inner = "local.if"(%condition,%left,%right,%condition) ({
  ^calculate(%x:!F,%y:!F,%allowed:i1):
    "local.exec.require"(%allowed) {binding=@require,site="before",parameters=[]} : (i1)->()
    %difference = kernel.call @difference::@evaluate(%x,%y) {site="calculate",policy=[false,false,false]} : (!F,!F)->!F
    "local.exec.require"(%allowed) {binding=@require,site="after",parameters=[]} : (i1)->()
    "local.yield"(%difference) : (!F)->()
  }, {
  ^unchanged(%x:!F,%y:!F,%allowed:i1):
    "local.yield"(%x) : (!F)->()
  }) {site="inner"} : (i1,!F,!F,i1)->!F
  "local.yield"(%inner) : (!F)->()
}, {
^disabled(%left:!F,%right:!F,%condition:i1):
  "local.stop"() {site="disabled",reason="abort"} : ()->()
}) {site="outer"} : (i1,!F,!F,i1)->!F
local.return %result : !F
)mlir",
                             3);
}

std::string fixtureText(StringRef path) {
  auto bytes = MemoryBuffer::getFile(
      (Twine(ZKC_KERNEL_PHYSICAL_FIXTURES) + "/" + path).str());
  require(bool(bytes), "cannot read Kernel physical planning fixture");
  return (*bytes)->getBuffer().str();
}

protocol_ir::ProtocolModuleOp owner(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}

template <typename Op> Op first(ModuleOp module) {
  Op found;
  module.walk([&](Op op) {
    if (!found)
      found = op;
  });
  require(bool(found), "missing expected fixture operation");
  return found;
}

OwningOpRef<ModuleOp> copy(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}

OwningOpRef<ModuleOp> executable(StringRef text, MLIRContext &context,
                                 MathematicalSelectionPolicy policy = {}) {
  auto module = parseSourceString<ModuleOp>(text, &context);
  require(bool(module), "Kernel planning fixture did not parse/admit");
  PassManager pipeline(&context);
  pipeline.addPass(createProjectProtocolPass(false, policy));
  pipeline.addPass(createLowerMathPass(policy));
  require(succeeded(pipeline.run(*module)), "Kernel fixture lowering failed");
  require(owner(*module).getProfile() == protocol_ir::Profile::Exec &&
              succeeded(verify(*module)),
          "fixture is not admitted Exec IR");
  first<kernel::ModuleOp>(*module);
  first<kernel::CallOp>(*module);
  return module;
}

std::string printed(ModuleOp module) {
  std::string text;
  raw_string_ostream out(text);
  module->print(out, OpPrintingFlags().printGenericOpForm().enableDebugInfo());
  return text;
}

class FrozenInput {
  std::string text;
  SmallVector<Operation *> operations;

public:
  explicit FrozenInput(ModuleOp module)
      : text(printed(module)), operations(physicalPlanOperations(module)) {}
  void check(ModuleOp module) const {
    require(printed(module) == text &&
                physicalPlanOperations(module) == operations,
            "physical planning changed or replaced original Kernel input");
  }
};

void accept(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}

void reject(Error error, StringRef code) {
  auto message = toString(std::move(error));
  require(namesIdentifier(message, code), "unexpected refusal: " + message);
}

CheckedPhysicalPlan
checkedPlan(ModuleOp module,
            const CandidateCatalog &catalog = installedCandidates()) {
  FrozenInput before(module);
  auto proposal = take(proposePhysical(module, catalog));
  before.check(module);
  auto checked = take(validatePhysical(module, proposal, catalog));
  before.check(module);
  return checked;
}

void admitPhysical(ModuleOp module) {
  require(owner(module).getProfile() == protocol_ir::Profile::Physical &&
              succeeded(verify(module)),
          "materialized output did not admit the Physical profile");
  bool residual = false;
  module.walk([&](Operation *op) {
    residual |=
        isa<kernel::ModuleOp, kernel::CallOp, func::FuncOp, data::DomainOp>(
            op) ||
        mathematical::isTotal(op);
  });
  require(!residual, "physical output retained Kernel or source mathematics");
}

OwningOpRef<ModuleOp> materializedCopy(ModuleOp source,
                                       const CheckedPhysicalPlan &checked) {
  FrozenInput before(source);
  auto candidate = copy(source);
  auto own = checkedPlan(*candidate);
  accept(materializePhysical(*candidate, own));
  admitPhysical(*candidate);
  accept(verifyPhysicalMaterialization(source, *candidate, checked));
  before.check(source);
  return candidate;
}

const BindingDecision &bindingFor(const PhysicalPlan &proposal,
                                  StringRef contract) {
  for (const auto &decision : proposal.bindings)
    if (decision.binding.application.contract == contract)
      return decision;
  throw std::runtime_error("missing selected contract " + contract.str());
}

plan::ApplyOp application(ModuleOp module, StringRef implementation) {
  plan::ApplyOp found;
  module.walk([&](plan::ApplyOp op) {
    if (op.getImplementation() == implementation && !found)
      found = op;
  });
  require(bool(found), "missing selected physical application");
  return found;
}

// Answers use fixed preferences and an optional fixed withholding rule.
// Instrumentation never edits the input, installs code or changes preferences.
class CountingCatalog final : public CandidateCatalog {
  const std::string withheldContract;
  mutable unsigned queries = 0;

public:
  explicit CountingCatalog(StringRef withheld = {})
      : withheldContract(withheld.str()) {}
  unsigned queryCount() const { return queries; }
  Expected<std::vector<std::string>>
  implementations(const BindingApplication &application) const override {
    ++queries;
    if (application.contract == withheldContract)
      return std::vector<std::string>{};
    if (application.contract == "poly.fold" &&
        application.arguments == std::vector<std::string>{"bls12-381.fr"})
      return std::vector<std::string>{"arkworks-msb/poly.fold",
                                      "arkworks/poly.fold"};
    return installedCandidates().implementations(application);
  }
  std::vector<std::string> diagonalImplementations(
      const BindingApplication &application) const override {
    ++queries;
    return installedCandidates().diagonalImplementations(application);
  }
  std::vector<BindingApplication>
  conversions(const BoundType &from, const BoundType &to) const override {
    ++queries;
    return installedCandidates().conversions(from, to);
  }
};

void mutateSource(ModuleOp module, StringRef mutation) {
  auto call = first<kernel::CallOp>(module);
  if (mutation == "body") {
    auto entry = kernel::getEntry(first<kernel::ModuleOp>(module));
    entry.front().back().setOperand(0, entry.getArgument(0));
  } else if (mutation == "private-helper") {
    auto unit = first<kernel::ModuleOp>(module);
    auto helper = SymbolTable(unit).lookup<func::FuncOp>("unused_helper");
    require(bool(helper), "missing private source helper");
    helper.front().back().setOperand(0, helper.getArgument(0));
  } else if (mutation == "dormant") {
    auto unit =
        SymbolTable(owner(module)).lookup<kernel::ModuleOp>("alternative");
    require(bool(unit), "missing dormant source unit");
    auto entry = kernel::getEntry(unit);
    entry.front().back().setOperand(0, entry.getArgument(0));
  } else if (mutation == "callee") {
    call->setAttr("callee", SymbolRefAttr::get(
                                module.getContext(), "alternative",
                                call.getCalleeAttr().getNestedReferences()));
  } else if (mutation == "policy") {
    OpBuilder builder(module.getContext());
    call->setAttr("policy", builder.getBoolArrayAttr({false, true, false}));
  } else if (mutation == "collect-fold-policy") {
    OpBuilder builder(module.getContext());
    call->setAttr("policy", builder.getBoolArrayAttr({true, false, true}));
  } else if (mutation == "operand") {
    require(call->getNumOperands() == 2 &&
                call->getOperand(0) != call->getOperand(1),
            "operand mutation requires distinct same-typed inputs");
    call->setOperand(1, call->getOperand(0));
  } else {
    throw std::runtime_error("unknown source mutation");
  }
  require(succeeded(verify(module)), "source mutation must remain admitted");
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;

  for (StringRef identity : {"bls12-381.fr", "koala-bear.ext8-binomial3"})
    cases.run("original multi-result Kernel plans for " + identity, [&] {
      auto module = executable(
          replaceText(scalarSource.str(), "bls12-381.fr", identity), context);
      auto call = first<kernel::CallOp>(*module);
      require(call->getNumResults() == 2,
              "fixture lost its multiple numerical results");
      auto checked = checkedPlan(*module);
      const auto &sub = bindingFor(checked.choices(), "field.sub");
      const auto &mul = bindingFor(checked.choices(), "field.mul");
      auto backend = identity == "bls12-381.fr" ? "arkworks" : "plonky3";
      require(sub.binding.application.arguments ==
                      std::vector<std::string>{identity.str()} &&
                  sub.binding.application.implementation ==
                      std::string(backend) + "/field.sub" &&
                  mul.binding.application.implementation ==
                      std::string(backend) + "/field.mul",
              "checked plan lost numerical domain or selected implementations");
      auto candidate = materializedCopy(*module, checked);
      application(*candidate, sub.binding.application.implementation);
      application(*candidate, mul.binding.application.implementation);
    });

  cases.run(
      "fixed native operation survives planning beside Kernel arithmetic", [&] {
        auto module = executable(pinnedSource(), context);
        SmallVector<StringRef> beforeSites;
        module->walk([&](Operation *op) {
          if (op->getName().getStringRef() == "poly.exec.fold")
            beforeSites.push_back(
                op->getAttrOfType<StringAttr>("site").getValue());
        });
        auto checked = checkedPlan(*module);
        const auto &pin = bindingFor(checked.choices(), "poly.fold");
        require(pin.fixed && pin.binding.name == "pinned" &&
                    pin.binding.application.implementation ==
                        "arkworks-msb/poly.fold",
                "checked plan replaced the existing fixed native choice");
        bindingFor(checked.choices(), "field.sub");
        auto candidate = materializedCopy(*module, checked);
        SmallVector<StringRef> afterSites;
        candidate->walk([&](plan::ApplyOp op) {
          if (op.getImplementation() == "arkworks-msb/poly.fold")
            afterSites.push_back(op.getSite());
        });
        require(!beforeSites.empty() && afterSites == beforeSites,
                "fixed native operations lost their input sites or order");
      });

  cases.run(
      "materialization uses owned checked choices without catalog queries",
      [&] {
        auto module =
            executable(replaceText(pinnedSource(),
                                   "implementation=\"arkworks-msb/poly.fold\"",
                                   "implementation=\"\""),
                       context);
        auto original = copy(*module);
        CountingCatalog catalog;
        auto originalChecked = checkedPlan(*original, catalog);
        FrozenInput before(*module);
        auto proposal = take(proposePhysical(*module, catalog));
        before.check(*module);
        auto checked = take(validatePhysical(*module, proposal, catalog));
        before.check(*module);
        const auto &fold = bindingFor(checked.choices(), "poly.fold");
        require(!fold.fixed && fold.binding.application.implementation ==
                                   "arkworks-msb/poly.fold",
                "catalog preference was not retained as an automatic choice");
        auto queries = catalog.queryCount();
        require(queries != 0, "counting catalog was never consulted");
        proposal.bindings.clear();
        proposal.operations.clear();
        accept(materializePhysical(*module, checked));
        admitPhysical(*module);
        application(*module, "arkworks-msb/poly.fold");
        accept(
            verifyPhysicalMaterialization(*original, *module, originalChecked));
        require(catalog.queryCount() == queries,
                "materialization or correspondence queried candidates");
      });

  cases.run("Kernel plan conversions reject another same-typed table", [&] {
    auto module = executable(pinnedSource(), context);
    auto checked = checkedPlan(*module);
    size_t conversions = 0;
    for (const auto &decision : checked.choices().operations)
      conversions += decision.conversions.size();
    require(conversions != 0, "pinned representation needs no conversion");
    auto candidate = materializedCopy(*module, checked);
    auto crossing = application(*candidate, "arkworks/table.relayout");
    auto function = crossing->getParentOfType<local::FuncOp>();
    Value other;
    for (auto argument : function.getArguments())
      if (argument.getType() == crossing->getOperand(0).getType() &&
          argument != crossing->getOperand(0)) {
        other = argument;
        break;
      }
    require(bool(other), "missing distinct same-typed table");
    crossing->setOperand(0, other);
    admitPhysical(*candidate);
    reject(verifyPhysicalMaterialization(*module, *candidate, checked),
           "binding-materialization-correspondence");
  });

  cases.run("inspection clones cannot mutate proposed or checked payloads",
            [&] {
              auto module = executable(scalarSource, context);
              FrozenInput before(*module);
              auto proposal = take(proposePhysical(*module));
              {
                auto inspection = take(proposal.cloneSelectedSubject(*module));
                require(physicalPlanOperations(*inspection).size() ==
                            proposal.operations.size(),
                        "inspection clone does not use the selected decision "
                        "index space");
                inspection->getBodyRegion().getBlocks().clear();
              }
              auto checked = take(validatePhysical(*module, proposal));
              {
                auto direct = take(checked.cloneSelectedSubject(*module));
                auto throughChoices =
                    take(checked.choices().cloneSelectedSubject(*module));
                direct->getBodyRegion().getBlocks().clear();
                throughChoices->getBodyRegion().getBlocks().clear();
              }
              before.check(*module);
              auto candidate = materializedCopy(*module, checked);
              application(*candidate, "arkworks/field.sub");
              application(*candidate, "arkworks/field.mul");
            });

  for (StringRef mutation : {"body", "callee", "policy", "collect-fold-policy",
                             "operand", "private-helper", "dormant"})
    for (bool afterValidation : {false, true})
      cases.run(
          Twine("Kernel source ") + mutation +
              (afterValidation ? " changes after validation"
                               : " changes before validation"),
          [&] {
            auto module = executable(scalarSource, context);
            if (mutation == "callee" || mutation == "dormant") {
              auto unit = first<kernel::ModuleOp>(*module);
              OpBuilder builder(unit);
              auto alternative =
                  cast<kernel::ModuleOp>(builder.clone(*unit.getOperation()));
              SymbolTable::setSymbolName(alternative, "alternative");
              require(succeeded(verify(*module)),
                      "alternate Kernel fixture did not admit");
            }
            if (mutation == "private-helper") {
              auto entry = kernel::getEntry(first<kernel::ModuleOp>(*module));
              OpBuilder builder(entry);
              auto helper = cast<func::FuncOp>(builder.clone(*entry));
              SymbolTable::setSymbolName(helper, "unused_helper");
              helper.setPrivate();
              require(succeeded(verify(*module)),
                      "private helper input did not admit");
            }
            FrozenInput before(*module);
            auto proposal = take(proposePhysical(*module));
            before.check(*module);
            if (afterValidation) {
              auto checked = take(validatePhysical(*module, proposal));
              before.check(*module);
              auto candidate = materializedCopy(*module, checked);
              mutateSource(*module, mutation);
              FrozenInput changed(*module);
              reject(checked.checkInput(*module), "binding-stale-selection");
              reject(materializePhysical(*module, checked),
                     "binding-stale-selection");
              reject(
                  verifyPhysicalMaterialization(*module, *candidate, checked),
                  "binding-stale-selection");
              changed.check(*module);
            } else {
              mutateSource(*module, mutation);
            }
            FrozenInput changed(*module);
            refuses(validatePhysical(*module, proposal),
                    "binding-stale-selection");
            changed.check(*module);
          });

  for (StringRef mutation : {"operand", "site", "implementation"})
    cases.run("physical numerical candidate rejects changed " + mutation, [&] {
      auto module = executable(scalarSource, context);
      auto checked = checkedPlan(*module);
      auto candidate = materializedCopy(*module, checked);
      auto subtract = application(*candidate, "arkworks/field.sub");
      if (mutation == "operand") {
        require(subtract->getOperand(0) != subtract->getOperand(1),
                "candidate requires distinct subtraction operands");
        subtract->setOperand(1, subtract->getOperand(0));
      } else if (mutation == "site") {
        subtract->setAttr("site", StringAttr::get(&context, "other"));
      } else {
        // Change the matching declaration too, so same-port implementation
        // substitution remains admitted and must fail correspondence.
        auto reference = subtract->getAttrOfType<FlatSymbolRefAttr>("binding");
        require(bool(reference), "physical subtraction lost its binding");
        auto binding =
            SymbolTable(owner(*candidate))
                .lookup<local::OperationBindingOp>(reference.getValue());
        require(bool(binding), "physical subtraction binding did not resolve");
        binding->setAttr("contract", StringAttr::get(&context, "field.add"));
        binding->setAttr("implementation",
                         StringAttr::get(&context, "arkworks/field.add"));
        subtract->setAttr("implementation",
                          StringAttr::get(&context, "arkworks/field.add"));
      }
      admitPhysical(*candidate);
      FrozenInput before(*module), changed(*candidate);
      reject(verifyPhysicalMaterialization(*module, *candidate, checked),
             "binding-materialization-correspondence");
      before.check(*module);
      changed.check(*candidate);
    });

  for (StringRef mutation : {"coverage", "signature", "implementation", "pin"})
    cases.run(
        "invalid Kernel physical choices do not publish: " + mutation, [&] {
          auto module = executable(pinnedSource(), context);
          FrozenInput before(*module);
          auto proposal = take(proposePhysical(*module));
          before.check(*module);
          StringRef code;
          if (mutation == "coverage") {
            require(!proposal.operations.empty(), "missing plan choices");
            proposal.operations.pop_back();
            code = "binding-plan-coverage";
          } else if (mutation == "signature") {
            bool changed = false;
            // Indices describe the selected executable payload. Never
            // dereference them in the original Kernel-bearing module.
            for (auto &decision : proposal.operations)
              if (decision.binding &&
                  proposal.bindings[*decision.binding]
                          .binding.application.contract == "field.sub") {
                require(!decision.outputs.empty(),
                        "selected subtraction lacks an output");
                decision.outputs[0] = Type{};
                changed = true;
                break;
              }
            require(changed, "missing numerical operation choice");
            code = "binding-operation-signature";
          } else {
            bool changed = false;
            for (auto &binding : proposal.bindings)
              if (binding.binding.application.contract ==
                  (mutation == "pin" ? "poly.fold" : "field.sub")) {
                binding.binding.application.implementation =
                    mutation == "pin" ? "arkworks/poly.fold" : "test/field.sub";
                changed = true;
                break;
              }
            require(changed, "missing selected binding to mutate");
            code = mutation == "pin" ? "binding-selection-conflict"
                                     : "binding-implementation";
          }
          refuses(validatePhysical(*module, proposal), code);
          before.check(*module);
          auto valid = checkedPlan(*module);
          materializedCopy(*module, valid);
          before.check(*module);
        });

  cases.run(
      "failed numerical candidate selection preserves original Kernel", [&] {
        auto module = executable(scalarSource, context);
        FrozenInput before(*module);
        CountingCatalog catalog("field.sub");
        refuses(proposePhysical(*module, catalog), "binding-implementation");
        require(catalog.queryCount() != 0,
                "refusal never reached numerical candidate selection");
        before.check(*module);
        auto checked = checkedPlan(*module);
        materializedCopy(*module, checked);
      });

  cases.run(
      "failed public selection does not publish expanded numerical work", [&] {
        auto module = executable(pinnedSource(), context);
        FrozenInput before(*module);
        std::vector<std::string> codes;
        ScopedDiagnosticHandler capture(&context, [&](Diagnostic &value) {
          for (const auto &refusal : diagnostics::refusals(value))
            codes.push_back(refusal.code);
          return success();
        });
        require(
            failed(lowerPhysical(*module, {{"pinned", "arkworks/poly.fold"}})),
            "conflicting fixed physical selection was accepted");
        require(codes == std::vector<std::string>{"binding-selection-conflict"},
                "public selection lost its stable refusal identifier");
        before.check(*module);
      });

  cases.run("withheld bulk operation refuses without numerical fallback", [&] {
    auto module = executable(
        fixtureText("structured-source/realization-finite.mlir"), context);
    CountingCatalog catalog("vector.sum");
    FrozenInput before(*module);
    refuses(proposePhysical(*module, catalog), "binding-implementation");
    before.check(*module);
    auto checked = checkedPlan(*module);
    bindingFor(checked.choices(), "vector.sum");
  });

  for (bool bulk : {false, true})
    cases.run(bulk ? "finite Kernel retains selected bulk reduction"
                   : "finite Kernel retains selected ordered reduction",
              [&] {
                auto module = executable(
                    fixtureText("structured-source/realization-finite.mlir"),
                    context, {bulk, false});
                auto checked = checkedPlan(*module);
                if (bulk)
                  bindingFor(checked.choices(), "vector.sum");
                auto candidate = materializedCopy(*module, checked);
                bool loop = false;
                candidate->walk([&](local::LocalForOp) { loop = true; });
                require(
                    loop == !bulk,
                    "physical materialization changed retained finite policy");
              });

  cases.run(
      "one Kernel unit retains distinct bulk and ordered invocations", [&] {
        auto module = executable(
            fixtureText("structured-source/realization-finite.mlir"), context);
        auto bulk = first<kernel::CallOp>(*module);
        OpBuilder builder(&context);
        bulk->setAttr("policy", builder.getBoolArrayAttr({true, false, false}));
        builder.setInsertionPointAfter(bulk);
        auto ordered = cast<kernel::CallOp>(builder.clone(*bulk));
        ordered->setAttr("site", builder.getStringAttr("ordered_repeat"));
        ordered->setAttr("policy",
                         builder.getBoolArrayAttr({false, false, false}));
        require(succeeded(verify(*module)),
                "mixed numerical policy input did not admit");
        auto checked = checkedPlan(*module);
        bindingFor(checked.choices(), "vector.sum");
        auto candidate = materializedCopy(*module, checked);
        unsigned loops = 0, sums = 0;
        candidate->walk([&](local::LocalForOp) { ++loops; });
        candidate->walk([&](plan::ApplyOp op) {
          sums += op.getImplementation() == "arkworks/vector.sum";
        });
        require(
            loops == 1 && sums == 1,
            "numerical choice leaked between calls to the same Kernel unit");
      });

  cases.run("nested Kernel arithmetic remains between ordered guards", [&] {
    auto module = executable(nestedSource(), context);
    auto call = first<kernel::CallOp>(*module);
    auto inner = call->getParentOfType<local::LocalIfOp>();
    require(inner && inner->getParentOfType<local::LocalIfOp>(),
            "fixture does not contain a nested Kernel invocation");
    auto checked = checkedPlan(*module);
    auto candidate = materializedCopy(*module, checked);
    auto subtract = application(*candidate, "arkworks/field.sub");
    auto parent = subtract->getParentOfType<local::LocalIfOp>();
    require(parent && parent->getParentOfType<local::LocalIfOp>(),
            "physical arithmetic escaped nested control");
    SmallVector<StringRef> order;
    for (auto &op : *subtract->getBlock())
      if (auto applied = dyn_cast<plan::ApplyOp>(op))
        order.push_back(applied.getImplementation() == "arkworks/field.sub"
                            ? StringRef("arithmetic")
                            : applied.getSite());
    require(order == SmallVector<StringRef>{"before", "arithmetic", "after"},
            "numerical materialization crossed an ordered guard");
    subtract->moveBefore(subtract->getPrevNode());
    admitPhysical(*candidate);
    reject(verifyPhysicalMaterialization(*module, *candidate, checked),
           "binding-materialization-correspondence");
  });

  cases.run("shared polynomial Kernel cuts admit physical publication", [&] {
    auto module =
        executable(fixtureText("kernel/shared-polynomial.mlir"), context);
    auto checked = checkedPlan(*module);
    materializedCopy(*module, checked);
  });

  cases.run(
      "standalone lowering traces candidate and caller publication separately",
      [&] {
        auto traced = executable(scalarSource, context);
        auto plain = copy(*traced);
        mathematical::RealizationTrace trace;
        require(succeeded(kernel::lowerKernels(*traced, {}, &trace)) &&
                    succeeded(kernel::lowerKernels(*plain)),
                "standalone Kernel lowering refused");
        require(printed(*traced) == printed(*plain),
                "tracing changed executable output");
        unsigned returned = 0, published = 0;
        for (const auto &event : trace.events)
          if (auto *publication =
                  std::get_if<mathematical::PublicationDecision>(
                      &event.payload)) {
            if (event.service == "propose-kernel-lowering") {
              require(publication->boundary ==
                          mathematical::PublicationBoundary::ReturnedCandidate,
                      "proposal claimed caller publication");
              ++returned;
            }
            if (event.service == "lower-kernels") {
              require(publication->boundary ==
                          mathematical::PublicationBoundary::PublishedToCaller,
                      "standalone lowering lost caller publication");
              ++published;
            }
          }
        require(
            returned == 1 && published == 1 && trace.activeScopes.empty() &&
                trace.declarationOrigins.empty(),
            "trace lost nested publication boundaries or leaked scope state");
        OwningOpRef<ModuleOp> empty(
            ModuleOp::create(UnknownLoc::get(&context)));
        FrozenInput before(*empty);
        require(failed(kernel::lowerKernels(*empty, {}, &trace)),
                "missing executable owner was accepted");
        before.check(*empty);
        bool refused = false;
        for (const auto &event : trace.events) {
          require(
              !std::holds_alternative<mathematical::PublicationDecision>(
                  event.payload),
              "refused lowering retained publication from a previous trace");
          refused |= std::holds_alternative<mathematical::DiscardDecision>(
              event.payload);
        }
        require(refused && trace.activeScopes.empty() &&
                    trace.declarationOrigins.empty(),
                "refusal leaked trace scope state");
      });

  cases.run("existing executable input without Kernel still materializes", [&] {
    auto module = take(executableFixture(pinnedSource(), context));
    bool hasKernel = false;
    module->walk([&](Operation *op) {
      hasKernel |= isa<kernel::ModuleOp, kernel::CallOp>(op);
    });
    require(!hasKernel, "control fixture still contains Kernel operations");
    auto checked = checkedPlan(*module);
    materializedCopy(*module, checked);
  });

  return cases.result();
}
