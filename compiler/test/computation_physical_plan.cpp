#include "../lib/Conversion/Bindings.h"
#include "../lib/Target/ExecutionPorts.h"
#include "../lib/Target/PhysicalPlan.h"
#include "../lib/Transforms/Computation/Support.h"
#include "mlir/IR/Verifier.h"
#include "support/NativeCases.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "support/ScopedFixture.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Computation.h"
#include "zkc/Transforms/Mathematical.h"
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
namespace sc = scopedComputation;
namespace sf = scopedFinite;
std::string compute(StringRef callee, StringRef site, StringRef inputs,
                    StringRef types, StringRef output, StringRef result,
                    StringRef policy = "[false,false,false]") {
  auto outcome = "!exec.outcome<(" + result.str() + ")>";
  auto name = site.str();
  return "%" + name + "_attempt = \"exec.compute\"(%scope," + inputs.str() +
         ") {callee=@" + callee.str() + ",site=\"" + name +
         "\",policy=" + policy.str() + "} : (!runtime.scope," + types.str() +
         ")->" + outcome + "\n\"exec.dispatch\"(%" + name + "_attempt)[^" +
         name + ",^failed] : (" + outcome + ")->()\n^" + name + "(" +
         output.str() + ":" + result.str() + "):\n";
}

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
)mlir" + scopedFixture(R"mlir(
func.func private @difference(%a:!F,%b:!F)->!F {
  %v = algebra.field_subtract %a,%b : (!F,!F)->!F
  func.return %v : !F
}
"runtime.binding"() {sym_name="pinned",contract="poly.fold",arguments=["bls12-381.fr"],implementation="arkworks-msb/poly.fold"} : ()->()
)mlir",
                       "%table:!T,%other:!T,%a:!F,%b:!F", "%table,%other,%a,%b",
                       "!T,!T,!F,!F", "!T",
                       compute("difference", "calculate", "%a,%b", "!F,!F",
                               "%difference", "!F") +
                           scopedApply("pinned", "pinned_fold",
                                       "%table,%difference", "!T,!F", "%folded",
                                       "!T") +
                           scopedReturn("%folded", "!T"),
                       4);
}

std::string mappedSource() {
  return R"mlir(!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
)mlir" + scopedFixture(R"mlir(
module @mapped attributes {exec.computation} {
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @step(%acc:!F,%x:!F,%xs:!V,%a:!F,%b:!F)->!F {
   %scaled = "algebra.field_multiply"(%x,%a) : (!F,!F)->!F
   %term = "algebra.field_add"(%scaled,%b) : (!F,!F)->!F
   %sum = "algebra.field_add"(%acc,%term) : (!F,!F)->!F
   func.return %sum : !F
 }
 func.func @evaluate(%xs:!V,%a:!F,%b:!F)->!F {
   %zero = "algebra.constant"() {value="0"} : ()->!F
   %sum = "algebra.finite_fold"(%xs,%zero,%a,%b) {domain=@items,step=@step} : (!V,!F,!F,!F)->!F
   func.return %sum : !F
 }
}
)mlir",
                       "%xs:!V,%a:!F,%b:!F", "%xs,%a,%b", "!V,!F,!F", "!F",
                       compute("mapped::@evaluate", "mapped", "%xs,%a,%b",
                               "!V,!F,!F", "%result", "!F",
                               "[true,false,false]") +
                           scopedReturn("%result", "!F"),
                       3);
}

std::string printed(ModuleOp module);
SmallVector<Value> invokeComputation(exec::ScopedExecutionBuilder &control,
                                     OpBuilder &builder, StringRef callee,
                                     StringRef site, ValueRange inputs,
                                     TypeRange outputs) {
  return control.invoke(
      "exec.compute", outputs, control.scoped(inputs),
      {builder.getNamedAttr("callee",
                            SymbolRefAttr::get(builder.getContext(), callee)),
       builder.getNamedAttr("site", builder.getStringAttr(site))});
}

std::string mixedMapSource(MLIRContext &context) {
  auto text = mappedSource();
  text.insert(text.find("module @mapped"), R"mlir(
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="late_items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @late_formula(%x:!F,%xs:!V,%a:!F,%b:!F)->!F {
   %m = algebra.field_multiply %x,%a : (!F,!F)->!F
   %r = algebra.field_add %m,%b : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @late_map(%xs:!V,%a:!F,%b:!F)->!V {
   %v = "algebra.finite_collect"(%xs,%a,%b) {domain=@late_items,body=@late_formula} : (!V,!F,!F)->!V
   func.return %v : !V
 }
)mlir");
  auto module = parseSourceString<ModuleOp>(text, &context);
  require(bool(module), "mixed source parse");
  auto work = sf::function(*module, "Work");
  auto old = cast<exec::ComputeOp>(work.front().front());
  auto attrs = NamedAttrList(old->getAttrs());
  work.getBody().dropAllReferences();
  work.getBody().getBlocks().clear();
  OpBuilder builder(&context);
  builder.setInsertionPointToEnd(work.addEntryBlock());
  exec::ScopedExecutionBuilder control(builder, work);
  auto vector = work.getArgument(1).getType(),
       field = work.getArgument(2).getType();
  auto enabled = control.invoke(
      "exec.boolean", {builder.getI1Type()}, {control.getScope()},
      {builder.getNamedAttr("value", builder.getBoolAttr(true)),
       builder.getNamedAttr("site", builder.getStringAttr("map_enabled"))})[0];
  control.conditional(
      enabled, work.getArguments().drop_front(), {vector}, "map_branch",
      [&](unsigned arm) {
        auto body = sc::region(builder, work, arm ? "map_no" : "map_yes",
                               {vector, field, field}, {vector});
        exec::ScopedExecutionBuilder nested(builder, body);
        Value value = body.getArgument(1);
        if (!arm)
          value =
              invokeComputation(nested, builder, "late_map", "late_map_call",
                                body.getArguments().drop_front(), {vector})[0];
        nested.complete({value});
        return body;
      });
  auto result = control.invoke("exec.compute", {field}, work.getArguments(),
                               attrs.getAttrs());
  control.returned(result);
  require(succeeded(verify(*module)), "mixed scoped source admission");
  return printed(*module);
}
std::string fixedPeerSource() {
  return R"mlir(!F = !algebra.field<"bls12-381.fr">
!T = !poly.multilinear<"bls12-381.fr">
)mlir" + scopedFixture(R"mlir(
module @difference attributes {exec.computation} {
 func.func @evaluate(%a:!F,%b:!F)->!F {
   %r = algebra.field_subtract %a,%b : (!F,!F)->!F
   func.return %r : !F
 }
}
"runtime.binding"() {sym_name="fold",contract="poly.fold",arguments=["bls12-381.fr"],implementation="arkworks-msb/poly.fold"} : ()->()
"runtime.binding"() {sym_name="product",contract="poly.product_sum",arguments=["bls12-381.fr"],implementation=""} : ()->()
)mlir",
                       "%table:!T,%other:!T,%a:!F,%b:!F", "%table,%other,%a,%b",
                       "!T,!T,!F,!F", "!F",
                       compute("difference::@evaluate", "difference", "%a,%b",
                               "!F,!F", "%r", "!F") +
                           scopedApply("fold", "fold", "%table,%r", "!T,!F",
                                       "%folded", "!T") +
                           scopedApply("product", "product", "%folded,%other",
                                       "!T,!T", "%product", "!F") +
                           scopedReturn("%product", "!F"),
                       4);
}

std::string nestedSource(MLIRContext &context) {
  auto text = R"mlir(!F = !algebra.field<"bls12-381.fr">
)mlir" + scopedFixture(R"mlir(
func.func private @difference(%a:!F,%b:!F)->!F {
  %v = algebra.field_subtract %a,%b : (!F,!F)->!F
  func.return %v : !F
}
"runtime.binding"() {sym_name="require",contract="control.require",arguments=[],implementation=""} : ()->()
)mlir",
                       "%a:!F,%b:!F,%enabled:i1", "%a,%b,%enabled", "!F,!F,i1",
                       "!F", scopedReturn("%a", "!F"), 3);
  auto module = parseSourceString<ModuleOp>(text, &context);
  require(bool(module), "nested source parse");
  auto work = sf::function(*module, "Work");
  work.getBody().dropAllReferences();
  work.getBody().getBlocks().clear();
  OpBuilder builder(&context);
  builder.setInsertionPointToEnd(work.addEntryBlock());
  exec::ScopedExecutionBuilder control(builder, work);
  auto field = work.getArgument(1).getType();
  auto flag = builder.getI1Type();
  auto result = control.conditional(
      work.getArgument(3), work.getArguments().drop_front(), {field}, "outer",
      [&](unsigned arm) {
        auto outer = sc::region(builder, work, arm ? "disabled" : "chosen",
                                {field, field, flag}, {field});
        exec::ScopedExecutionBuilder branch(builder, outer);
        if (arm) {
          branch.reject("abort", "disabled");
          return outer;
        }
        auto inner = branch.conditional(
            outer.getArgument(3), outer.getArguments().drop_front(), {field},
            "inner", [&](unsigned innerArm) {
              auto body = sc::region(builder, outer,
                                     innerArm ? "unchanged" : "calculate",
                                     {field, field, flag}, {field});
              exec::ScopedExecutionBuilder nested(builder, body);
              Value value = body.getArgument(1);
              if (!innerArm) {
                sc::apply(nested, builder, "require", "before",
                          {body.getArgument(3)}, {});
                value = invokeComputation(
                    nested, builder, "difference", "calculate",
                    {value, body.getArgument(2)}, {field})[0];
                sc::apply(nested, builder, "require", "after",
                          {body.getArgument(3)}, {});
              }
              nested.complete({value});
              return body;
            });
        branch.complete(inner);
        return outer;
      });
  control.returned(result);
  require(succeeded(verify(*module)), "nested scoped source admission");
  return printed(*module);
}

std::string finiteSource(bool bulk = true) {
  return R"mlir(!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
)mlir" + scopedFixture(
             R"mlir(
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @step(%acc:!F,%x:!F,%xs:!V)->!F {
   %s = "algebra.field_add"(%acc,%x) : (!F,!F)->!F
   func.return %s : !F
 }
 func.func private @sum(%xs:!V)->!F {
   %zero = "algebra.constant"() {value="0"} : ()->!F
   %sum = "algebra.finite_fold"(%xs,%zero) {domain=@items,step=@step} : (!V,!F)->!F
   func.return %sum : !F
 }
)mlir",
             "%xs:!V", "%xs", "!V", "!F",
             compute("sum", "sum", "%xs", "!V", "%result", "!F",
                     bulk ? "[true,false,false]" : "[false,false,false]") +
                 scopedReturn("%result", "!F"),
             1);
}
std::string fixtureText(StringRef path) {
  auto bytes = MemoryBuffer::getFile(
      (Twine(ZKC_COMPUTATION_PHYSICAL_FIXTURES) + "/" + path).str());
  require(bool(bytes), "cannot read computation physical planning fixture");
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
  require(bool(module), "computation planning fixture did not parse/admit");
  PassManager pipeline(&context);
  pipeline.addPass(createProjectProtocolPass(false, policy));
  pipeline.addPass(createLowerMathPass(policy));
  require(succeeded(pipeline.run(*module)),
          "computation fixture lowering failed");
  require(owner(*module).getProfile() == protocol_ir::Profile::Exec &&
              succeeded(verify(*module)),
          "fixture is not admitted Exec IR");
  first<mlir::ModuleOp>(*module);
  first<exec::ComputeOp>(*module);
  return module;
}

// Ordered work outside computation must survive preparation unchanged. Its size
// makes redundant whole-source snapshots visible under the shared copy bound.
void addUnchangedContext(ModuleOp module, unsigned count) {
  OpBuilder builder(module.getContext());
  auto root = owner(module);
  builder.setInsertionPointToEnd(&root.getBody().front());
  OperationState binding(module.getLoc(),
                         runtime::BindingOp::getOperationName());
  binding.addAttribute("sym_name", builder.getStringAttr("context_add"));
  binding.addAttribute("contract", builder.getStringAttr("field.add"));
  binding.addAttribute("arguments", builder.getStrArrayAttr({"bls12-381.fr"}));
  binding.addAttribute("implementation", builder.getStringAttr(""));
  builder.create(binding);
  auto function = func::FuncOp::create(
      builder, module.getLoc(), "unchanged_context",
      builder.getFunctionType({runtime::ScopeType::get(module.getContext())},
                              exec::OutcomeType::get(module.getContext(), {})));
  function->setAttr("no_inline", builder.getUnitAttr());
  function->setAttr("runtime.origin",
                    builder.getArrayAttr({builder.getStringAttr("context"),
                                          builder.getArrayAttr({})}));
  builder.setInsertionPointToEnd(function.addEntryBlock());
  exec::ScopedExecutionBuilder control(builder, function);
  for (unsigned index = 0; index < count; ++index)
    control.invoke("exec.boolean", {builder.getI1Type()}, {control.getScope()},
                   {builder.getNamedAttr("value", builder.getBoolAttr(true)),
                    builder.getNamedAttr(
                        "site", builder.getStringAttr("unchanged_" +
                                                      std::to_string(index)))});
  control.returned({});
  require(succeeded(verify(module)),
          "unchanged planning context did not admit");
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
            "physical planning changed or replaced original computation input");
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
    residual |= mathematical::isComputationUnit(op) ||
                isa<exec::ComputeOp, data::DomainOp>(op) ||
                (isa<func::FuncOp>(op) &&
                 (cast<func::FuncOp>(op).getArgumentTypes().empty() ||
                  !isa<runtime::ScopeType>(
                      cast<func::FuncOp>(op).getArgumentTypes().front())));
  });
  auto flow = take(ExecutionPorts::read(module));
  for (auto *operation : flow.operations())
    residual |= flow.get(operation).step && mathematical::isTotal(operation);
  require(!residual,
          "physical output retained computation or source mathematics");
}

OwningOpRef<ModuleOp>
materializedCopy(ModuleOp source, const CheckedPhysicalPlan &checked,
                 const CandidateCatalog &catalog = installedCandidates()) {
  FrozenInput before(source);
  auto candidate = copy(source);
  auto own = checkedPlan(*candidate, catalog);
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

StringRef implementation(exec::ApplyOp op) {
  return SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
             op, op.getBindingAttr())
      .getImplementation();
}

exec::ApplyOp application(ModuleOp module, StringRef selected) {
  exec::ApplyOp found;
  module.walk([&](exec::ApplyOp op) {
    if (implementation(op) == selected && !found)
      found = op;
  });
  require(bool(found), "missing selected physical application");
  return found;
}

// Answers use fixed preferences and an optional fixed withholding rule.
// Instrumentation never edits the input, installs code or changes preferences.
class CountingCatalog final : public CandidateCatalog {
  const std::vector<std::string> withheldContracts;
  mutable unsigned queries = 0;

public:
  explicit CountingCatalog(StringRef withheld = {})
      : withheldContracts{withheld.str()} {}
  explicit CountingCatalog(std::initializer_list<StringRef> withheld)
      : withheldContracts([&] {
          std::vector<std::string> result;
          for (auto name : withheld)
            result.push_back(name.str());
          return result;
        }()) {}
  unsigned queryCount() const { return queries; }
  Expected<std::vector<std::string>>
  implementations(const BindingApplication &application) const override {
    ++queries;
    if (is_contained(withheldContracts, application.contract))
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

class DirectionalCatalog final : public CandidateCatalog {
public:
  Expected<std::vector<std::string>>
  implementations(const BindingApplication &application) const override {
    if (application.contract == "poly.product_sum")
      return std::vector<std::string>{"arkworks/poly.product_sum",
                                      "arkworks-msb/poly.product_sum"};
    return installedCandidates().implementations(application);
  }
  std::vector<BindingApplication>
  conversions(const BoundType &from, const BoundType &to) const override {
    auto pinned = take(resolveBinding(
        {"poly.fold", {"bls12-381.fr"}, "arkworks-msb/poly.fold"}, true));
    if (from.representation == pinned.outputs[0].representation)
      return {};
    return installedCandidates().conversions(from, to);
  }
};

void mutateSource(ModuleOp module, StringRef mutation) {
  auto call = first<exec::ComputeOp>(module);
  if (mutation == "body") {
    auto entry =
        mathematical::getComputationEntry(first<mlir::ModuleOp>(module));
    entry.front().back().setOperand(0, entry.getArgument(0));
  } else if (mutation == "private-helper") {
    auto unit = first<mlir::ModuleOp>(module);
    auto helper = SymbolTable(unit).lookup<func::FuncOp>("unused_helper");
    require(bool(helper), "missing private source helper");
    helper.front().back().setOperand(0, helper.getArgument(0));
  } else if (mutation == "dormant") {
    auto unit =
        SymbolTable(owner(module)).lookup<mlir::ModuleOp>("alternative");
    require(bool(unit), "missing dormant source unit");
    auto entry = mathematical::getComputationEntry(unit);
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
    require(call.getInputs().size() == 2 &&
                call.getInputs()[0] != call.getInputs()[1],
            "operand mutation requires distinct same-typed inputs");
    call.getInputsMutable()[1].set(call.getInputs()[0]);
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
    cases.run("original multi-result computation plans for " + identity, [&] {
      auto module = executable(
          replaceText(scalarSource.str(), "bls12-381.fr", identity), context);
      auto call = first<exec::ComputeOp>(*module);
      require(call.getOutcome().getType().getPayload().size() == 2,
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

  for (StringRef domain : {"bls12-381.g1", "bls12-381.g2"})
    cases.run(
        "resident provider retains fixed exact-port binding for " + domain,
        [&] {
          auto source = std::string(R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!G = !algebra.group<"bls12-381.g1">
!GS = !algebra.group_vector<"bls12-381.g1">
)mlir") + scopedFixture(R"mlir(
module @difference attributes {exec.computation} {
 func.func @evaluate(%a:!F,%b:!F)->!F {
   %r = algebra.field_subtract %a,%b : (!F,!F)->!F
   func.return %r : !F
 }
}
"runtime.binding"() {sym_name="msm",contract="curve.msm",arguments=["bls12-381.g1"],implementation="blst/resident/curve.msm"} : ()->()
"runtime.binding"() {sym_name="scale",contract="curve.scale",arguments=["bls12-381.g1"],implementation=""} : ()->()
)mlir",
                        "%s:!V,%p:!GS,%a:!F,%b:!F", "%s,%p,%a,%b",
                        "!V,!GS,!F,!F", "!G",
                        compute("difference::@evaluate", "difference", "%a,%b",
                                "!F,!F", "%difference", "!F") +
                            scopedApply("msm", "msm", "%s,%p", "!V,!GS", "%out",
                                        "!G") +
                            scopedApply("scale", "scaled", "%out,%difference",
                                        "!G,!F", "%scaled", "!G") +
                            scopedReturn("%scaled", "!G"),
                        4);
          auto module =
              executable(replaceText(source, "bls12-381.g1", domain), context);
          auto checked = checkedPlan(*module);
          const auto &choice = bindingFor(checked.choices(), "curve.msm");
          require(choice.fixed && choice.binding.application.implementation ==
                                      "blst/resident/curve.msm",
                  "physical planning replaced an explicit foreign provider");
          auto candidate = materializedCopy(*module, checked);
          application(*candidate, "blst/resident/curve.msm");
        });

  cases.run(
      "fixed native operation survives planning beside computation arithmetic",
      [&] {
        auto module = executable(pinnedSource(), context);
        SmallVector<StringRef> beforeSites;
        module->walk([&](Operation *op) {
          if (auto apply = dyn_cast<exec::ApplyOp>(op);
              apply && sf::contract(apply) == "poly.fold")
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
        candidate->walk([&](exec::ApplyOp op) {
          if (implementation(op) == "arkworks-msb/poly.fold")
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

  cases.run(
      "computation plan conversions reject another same-typed table", [&] {
        auto module = executable(pinnedSource(), context);
        auto checked = checkedPlan(*module);
        size_t conversions = 0;
        for (const auto &decision : checked.choices().operations)
          conversions += decision.conversions.size();
        require(conversions != 0, "pinned representation needs no conversion");
        auto candidate = materializedCopy(*module, checked);
        auto crossing = application(*candidate, "arkworks/table.relayout");
        auto function = crossing->getParentOfType<func::FuncOp>();
        Value other;
        for (auto argument : function.getArguments())
          if (argument.getType() == crossing.getInputs()[0].getType() &&
              argument != crossing.getInputs()[0]) {
            other = argument;
            break;
          }
        require(bool(other), "missing distinct same-typed table");
        crossing.getInputsMutable()[0].set(other);
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
          Twine("computation source ") + mutation +
              (afterValidation ? " changes after validation"
                               : " changes before validation"),
          [&] {
            auto module = executable(scalarSource, context);
            if (mutation == "callee" || mutation == "dormant") {
              auto unit = first<mlir::ModuleOp>(*module);
              OpBuilder builder(unit);
              auto alternative =
                  cast<mlir::ModuleOp>(builder.clone(*unit.getOperation()));
              SymbolTable::setSymbolName(alternative, "alternative");
              require(succeeded(verify(*module)),
                      "alternate computation fixture did not admit");
            }
            if (mutation == "private-helper") {
              auto entry = mathematical::getComputationEntry(
                  first<mlir::ModuleOp>(*module));
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
        require(subtract.getInputs()[0] != subtract.getInputs()[1],
                "candidate requires distinct subtraction operands");
        subtract.getInputsMutable()[1].set(subtract.getInputs()[0]);
      } else if (mutation == "site") {
        subtract->setAttr("site", StringAttr::get(&context, "other"));
      } else {
        // Change the matching declaration too, so same-port implementation
        // substitution remains admitted and must fail correspondence.
        auto reference = subtract->getAttrOfType<FlatSymbolRefAttr>("binding");
        require(bool(reference), "physical subtraction lost its binding");
        auto binding = SymbolTable(owner(*candidate))
                           .lookup<runtime::BindingOp>(reference.getValue());
        require(bool(binding), "physical subtraction binding did not resolve");
        binding->setAttr("contract", StringAttr::get(&context, "field.add"));
        binding->setAttr("implementation",
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
        "invalid computation physical choices do not publish: " + mutation,
        [&] {
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
            // dereference them in the original computation-bearing module.
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
      "failed numerical candidate selection preserves original computation",
      [&] {
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

  cases.run(
      "withheld vector reduction selects another checked executable", [&] {
        auto module = executable(finiteSource(), context);
        CountingCatalog catalog("vector.sum");
        FrozenInput before(*module);
        auto checked = checkedPlan(*module, catalog);
        for (const auto &binding : checked.choices().bindings)
          require(binding.binding.application.contract != "vector.sum",
                  "withheld vector reduction survived selection");
        auto local = take(checked.cloneSelectedSubject(*module));
        require(succeeded(
                    computation::verifyComputationRealization(*module, *local)),
                "fallback lost original-source correspondence");
        auto selected = materializedCopy(*module, checked, catalog);
        before.check(*module);
        auto own = checkedPlan(*module, catalog);
        auto queries = catalog.queryCount();
        accept(materializePhysical(*module, own));
        require(catalog.queryCount() == queries,
                "materialization searched the numerical menu again");
      });

  cases.run(
      "unavailable native and vector reductions retain ordered execution", [&] {
        auto module = executable(mappedSource(), context);
        CountingCatalog catalog({"vector.sum", "numerical.sum"});
        auto checked = checkedPlan(*module, catalog);
        auto selected = materializedCopy(*module, checked, catalog);
        bool loop = false;
        selected->walk([&](exec::RangeOp) { loop = true; });
        require(loop,
                "exhausted reduction menu did not retain the ordered loop");
      });

  cases.run(
      "failure at one computation preserves its neighbor's preferred recipe",
      [&] {
        auto text = finiteSource();
        auto at = text.find(" func.func private @sum");
        require(at != std::string::npos, "missing sum fixture definition");
        text.insert(at, R"(
 func.func private @multiply(%acc:!F,%x:!F,%xs:!V)->!F {
   %p = "algebra.field_multiply"(%acc,%x) : (!F,!F)->!F
   func.return %p : !F
 }
)");
        at = text.find("   func.return %sum : !F");
        require(at != std::string::npos, "missing sum fixture result");
        text.replace(at, std::string("   func.return %sum : !F").size(), R"(
   %one = "algebra.constant"() {value="1"} : ()->!F
   %product = "algebra.finite_fold"(%xs,%one) {domain=@items,step=@multiply} : (!V,!F)->!F
   %both = "algebra.field_add"(%sum,%product) : (!F,!F)->!F
   func.return %both : !F
)");
        auto module = executable(text, context);
        unsigned computations = 0;
        SymbolTableCollection symbols;
        auto entry = first<exec::ComputeOp>(*module).resolveCallee(symbols);
        require(bool(entry), "missing actual numerical entry");
        entry.walk([&](Operation *op) {
          computations += op->getName().getStringRef() == "algebra.finite_fold";
        });
        require(computations == 2,
                "fixture lost its two computation occurrences");
        CountingCatalog catalog({"vector.sum", "numerical.sum"});
        auto checked = checkedPlan(*module, catalog);
        bindingFor(checked.choices(), "vector.product");
        auto selected = materializedCopy(*module, checked, catalog);
        unsigned loops = 0, products = 0;
        selected->walk([&](exec::RangeOp) { ++loops; });
        selected->walk([&](exec::ApplyOp op) {
          products += implementation(op) == "arkworks/vector.product";
        });
        require(loops == 1 && products == 1,
                "fallback changed an unrelated computation's preferred recipe");
      });

  cases.run(
      "physical retries settle the caller's cumulative work account", [&] {
        auto module = executable(finiteSource(), context);
        FrozenInput before(*module);
        CountingCatalog catalog({"vector.sum", "numerical.sum"});
        mathematical::RealizationWork work;
        uint64_t copies = 1000000, siteBytes = 16 * 1024 * 1024;
        PhysicalPlanOptions options;
        options.numericalWork = &work;
        options.numericalCopy = &copies;
        options.numericalSiteBytes = &siteBytes;
        auto first = take(proposePhysical(*module, catalog, {}, options));
        take(validatePhysical(*module, first, catalog));
        auto previous = work;
        auto previousCopies = copies, previousBytes = siteBytes;
        require(
            work.discardedRecipeCopy <
                    mathematical::RealizationWork{}.discardedRecipeCopy &&
                copies < 1000000 && siteBytes < 16 * 1024 * 1024 &&
                !work.numericalSelection && !work.numericalOccurrence,
            "failed physical candidates were not charged to discard reserve");
        auto second = take(proposePhysical(*module, catalog, {}, options));
        take(validatePhysical(*module, second, catalog));
        require(work.matching.structural < previous.matching.structural &&
                    work.discardedRecipeCopy < previous.discardedRecipeCopy &&
                    copies < previousCopies && siteBytes < previousBytes,
                "another proposal reset catalog or discarded-copy accounting");
        before.check(*module);
      });

  for (bool requested : {false, true})
    cases.run(
        requested
            ? "bounded computation preparation applies pins without a source "
              "clone"
            : "bounded computation preparation retains large ordered context",
        [&] {
          auto module = executable(scalarSource, context);
          addUnchangedContext(*module, 4096);
          FrozenInput frozen(*module);
          uint64_t sourceCost = 0;
          module->walk([&](Operation *op) {
            sourceCost += 1 + op->getNumOperands() + op->getNumResults();
          });
          // Includes complete context checking, the selected candidate and
          // final preflight. Repeated unused source snapshots do not fit.
          uint64_t copies = 8 * sourceCost;
          protocol::Assignments requests;
          if (requested)
            requests.emplace_back("context_add", "arkworks/field.add");
          PhysicalPlanOptions options;
          options.numericalCopy = &copies;
          unsigned preflights = 0;
          options.programCapacity = [&](ModuleOp candidate,
                                        const PhysicalPlan &)
              -> Expected<SmallVector<OperationIndex>> {
            ++preflights;
            unsigned constants = 0;
            candidate.walk([&](exec::BooleanOp) { ++constants; });
            require(constants == 4096,
                    "preflight lost unchanged ordered context");
            return SmallVector<OperationIndex>{};
          };
          auto plan = take(proposePhysical(*module, installedCandidates(),
                                           requests, options));
          require(preflights == 1 && copies < 8 * sourceCost,
                  "required candidate copying was not settled once");
          const auto &binding = bindingFor(plan, "field.add");
          require(binding.fixed == requested &&
                      binding.binding.application.implementation ==
                          "arkworks/field.add",
                  "preparation changed a requested physical choice");
          take(validatePhysical(*module, plan));
          auto selected = take(plan.cloneSelectedSubject(*module));
          auto retained = SymbolTable(owner(*selected))
                              .lookup<runtime::BindingOp>("context_add");
          require(retained && retained.getImplementation().empty(),
                  "temporary requests changed retained source declarations");
          auto changed = first<exec::BooleanOp>(*selected);
          changed->setAttr("value", BoolAttr::get(&context, false));
          require(succeeded(verify(*selected)),
                  "unchanged-context mutation must remain admitted");
          {
            ScopedDiagnosticHandler quiet(
                &context, [](Diagnostic &) { return success(); });
            require(failed(mathematical::verifyNumericalLowering(
                        *module, *selected, {}, requests)),
                    "independent readback accepted altered dormant work");
          }
          take(validatePhysical(*module, plan));
          frozen.check(*module);
        });

  cases.run("required candidate and preflight settle exact copy capacity", [&] {
    auto module = executable(scalarSource, context);
    FrozenInput frozen(*module);
    uint64_t copies = 1000000;
    unsigned preflights = 0;
    PhysicalPlanOptions options;
    options.numericalCopy = &copies;
    options.programCapacity =
        [&](ModuleOp,
            const PhysicalPlan &) -> Expected<SmallVector<OperationIndex>> {
      ++preflights;
      return SmallVector<OperationIndex>{};
    };
    auto measured =
        take(proposePhysical(*module, installedCandidates(), {}, options));
    uint64_t consumed = 1000000 - copies;
    require(consumed > 0 && preflights == 1,
            "copy-capacity control did not perform a complete preflight");
    copies = consumed;
    preflights = 0;
    auto exact =
        take(proposePhysical(*module, installedCandidates(), {}, options));
    require(copies == 0 && preflights == 1,
            "exact copy capacity did not settle the actual debit");
    take(validatePhysical(*module, exact));
    copies = consumed - 1;
    preflights = 0;
    refuses(proposePhysical(*module, installedCandidates(), {}, options),
            "computation-realization");
    require(preflights == 0 && copies < consumed - 1,
            "one-short capacity invoked preflight or refunded failed work");
    take(validatePhysical(*module, measured));
    frozen.check(*module);
  });

  cases.run(
      "required numerical capacity is terminal before catalog search", [&] {
        auto module = executable(finiteSource(), context);
        FrozenInput before(*module);
        CountingCatalog catalog;
        mathematical::RealizationWork work;
        work.finiteExpressions = 0;
        const auto beforeWork = work;
        PhysicalPlanOptions options;
        options.numericalWork = &work;
        ScopedDiagnosticHandler quiet(&context,
                                      [](Diagnostic &) { return success(); });
        refuses(proposePhysical(*module, catalog, {}, options),
                "computation-realization");
        require(
            catalog.queryCount() == 0 && work.finiteExpressions == 0 &&
                work.discardedRecipeCopy == beforeWork.discardedRecipeCopy &&
                work.discardedRecipeSiteBytes ==
                    beforeWork.discardedRecipeSiteBytes &&
                work.discardedRecipeExpansion ==
                    beforeWork.discardedRecipeExpansion,
            "required capacity refusal retried or replenished its allowance");
        before.check(*module);
      });

  cases.run(
      "final capacity callback advances only its reported operation", [&] {
        auto module = executable(mappedSource(), context);
        PhysicalPlanOptions options;
        unsigned calls = 0;
        options.programCapacity = [&](ModuleOp, const PhysicalPlan &plan)
            -> Expected<SmallVector<OperationIndex>> {
          ++calls;
          for (const auto &decision : plan.operations)
            if (decision.binding &&
                plan.bindings[*decision.binding].binding.application.contract ==
                    "numerical.sum")
              return SmallVector<OperationIndex>{decision.operation};
          return SmallVector<OperationIndex>{};
        };
        auto proposal =
            take(proposePhysical(*module, installedCandidates(), {}, options));
        require(calls == 2,
                "attributable program-capacity refusal was not advanced once");
        for (const auto &binding : proposal.bindings)
          require(binding.binding.application.contract != "numerical.sum",
                  "declined inline body remained in the retained payload");
        take(validatePhysical(*module, proposal));
      });

  cases.run("unclassified program-preflight errors are terminal", [&] {
    auto module = executable(mappedSource(), context);
    FrozenInput before(*module);
    PhysicalPlanOptions options;
    unsigned calls = 0;
    options.programCapacity =
        [&](ModuleOp,
            const PhysicalPlan &) -> Expected<SmallVector<OperationIndex>> {
      ++calls;
      return error("source-string");
    };
    refuses(proposePhysical(*module, installedCandidates(), {}, options),
            "source-string");
    require(calls == 1,
            "generic preflight failure was swallowed as optional capacity");
    before.check(*module);
  });

  for (StringRef mutation :
       {"capture", "body", "mask", "field", "mode", "seed"})
    cases.run(
        "retained numerical candidate independently rejects " + mutation, [&] {
          auto module = executable(mappedSource(), context);
          auto checked = checkedPlan(*module);
          bindingFor(checked.choices(), "numerical.sum");
          auto selected = take(checked.cloneSelectedSubject(*module));
          SymbolTable symbols(owner(*selected));
          Operation *call = nullptr;
          runtime::BindingOp binding;
          selected->walk([&](Operation *op) {
            auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
            auto declaration =
                ref ? symbols.lookup<runtime::BindingOp>(ref.getValue())
                    : runtime::BindingOp();
            if (declaration && declaration.getContract() == "numerical.sum") {
              call = op;
              binding = declaration;
            }
          });
          require(call && call->getNumOperands() >= 4,
                  "native candidate lost its distinct same-typed captures");
          OpBuilder builder(&context);
          if (mutation == "capture") {
            auto left = call->getOperand(call->getNumOperands() - 2);
            auto right = call->getOperand(call->getNumOperands() - 1);
            require(left != right && left.getType() == right.getType(),
                    "fixture lacks distinct equal-typed captures");
            call->setOperand(call->getNumOperands() - 2, right);
            call->setOperand(call->getNumOperands() - 1, left);
          } else if (mutation == "body") {
            auto parameters = call->getAttrOfType<ArrayAttr>("parameters");
            auto body = cast<StringAttr>(parameters[0]).getValue().str();
            auto at = body.find("\"add\"");
            require(at != std::string::npos,
                    "native body has no addition to alter");
            body.replace(at, 5, "\"mul\"");
            call->setAttr("parameters", builder.getStrArrayAttr({body}));
          } else if (mutation == "seed") {
            auto combine = sf::application(
                call->getParentOfType<func::FuncOp>(), "field.add");
            require(combine.getInputs().size() == 2,
                    "native aggregate lost its external seed combiner");
            combine.getInputsMutable()[0].set(call->getOperands().back());
          } else if (mutation == "mode") {
            binding->setAttr("contract",
                             builder.getStringAttr("numerical.product"));
          } else {
            SmallVector<Attribute> arguments(binding.getArguments().begin(),
                                             binding.getArguments().end());
            if (mutation == "field")
              arguments[0] = builder.getStringAttr("bn254.fr");
            else {
              auto mask = cast<StringAttr>(arguments[1]).getValue().str();
              require(!mask.empty(), "native row mask was empty");
              mask[0] = mask[0] == '0' ? '1' : '0';
              arguments[1] = builder.getStringAttr(mask);
            }
            binding->setAttr("arguments", builder.getArrayAttr(arguments));
          }
          ScopedDiagnosticHandler quiet(&context,
                                        [](Diagnostic &) { return success(); });
          require(failed(computation::verifyComputationRealization(*module,
                                                                   *selected)),
                  "independent original-source reader accepted altered "
                  "numerical facts");
          auto intact = take(checked.cloneSelectedSubject(*module));
          require(succeeded(computation::verifyComputationRealization(*module,
                                                                      *intact)),
                  "inspection mutation changed the private retained payload");
        });

  cases.run(
      "unknown and duplicate selections fail before numerical discovery", [&] {
        auto module = executable(scalarSource, context);
        FrozenInput before(*module);
        CountingCatalog catalog;
        refuses(
            proposePhysical(*module, catalog, {{"unknown", "test/missing"}}),
            "binding-unknown-selection");
        refuses(proposePhysical(*module, catalog,
                                {{"unknown", "one"}, {"unknown", "two"}}),
                "binding-duplicate-selection");
        require(catalog.queryCount() == 0,
                "explicit selection refusal performed optional discovery");
        before.check(*module);
      });

  for (bool bulk : {false, true})
    cases.run(
        bulk ? "finite computation retains selected bulk reduction"
             : "finite computation retains selected ordered reduction",
        [&] {
          auto module = executable(finiteSource(bulk), context, {bulk, false});
          auto checked = checkedPlan(*module);
          if (bulk)
            bindingFor(checked.choices(), "vector.sum");
          auto candidate = materializedCopy(*module, checked);
          bool loop = false;
          candidate->walk([&](exec::RangeOp) { loop = true; });
          require(loop == !bulk,
                  "physical materialization changed retained finite policy");
        });

  cases.run(
      "one computation unit retains distinct bulk and ordered invocations",
      [&] {
        auto module = executable(finiteSource(), context);
        auto bulk = first<exec::ComputeOp>(*module);
        OpBuilder builder(&context);
        bulk->setAttr("policy", builder.getBoolArrayAttr({true, false, false}));
        auto ordered = cast<exec::ComputeOp>(sc::duplicateInvocation(
            bulk, bulk->getParentOfType<func::FuncOp>(), "ordered_repeat"));
        ordered->setAttr("site", builder.getStringAttr("ordered_repeat"));
        ordered->setAttr("policy",
                         builder.getBoolArrayAttr({false, false, false}));
        require(succeeded(verify(*module)),
                "mixed numerical policy input did not admit");
        auto checked = checkedPlan(*module);
        bindingFor(checked.choices(), "vector.sum");
        auto candidate = materializedCopy(*module, checked);
        unsigned loops = 0, sums = 0;
        candidate->walk([&](exec::RangeOp) { ++loops; });
        candidate->walk([&](exec::ApplyOp op) {
          sums += implementation(op) == "arkworks/vector.sum";
        });
        require(loops == 1 && sums == 1, "numerical choice leaked between "
                                         "calls to the same computation unit");
      });

  cases.run("nested numerical arithmetic remains between ordered guards", [&] {
    auto module = executable(nestedSource(context), context);
    auto call = first<exec::ComputeOp>(*module);
    auto checkNesting = [&](ModuleOp subject, Operation *operation) {
      auto closure =
          take(owner(subject).getProfile() == protocol_ir::Profile::Physical
                   ? protocol::readExecutionClosure(owner(subject), true)
                   : protocol::readSourceExecutionClosure(owner(subject)));
      auto parent = operation->getParentOfType<func::FuncOp>();
      for (unsigned depth = 0; depth < 2; ++depth) {
        require(parent->hasAttr("runtime.region"),
                "arithmetic escaped an outlined region");
        SmallVector<Operation *> callers;
        for (const auto &[name, body] : closure.bodies)
          for (const auto &step : body)
            if (llvm::is_contained(step.regions, parent))
              callers.push_back(step.operation);
        require(callers.size() == 1 && isa<exec::TestOp>(callers.front()),
                "arithmetic lost its conditional parent");
        parent = callers.front()->getParentOfType<func::FuncOp>();
      }
    };
    checkNesting(*module, call);
    auto checked = checkedPlan(*module);
    auto candidate = materializedCopy(*module, checked);
    auto subtract = application(*candidate, "arkworks/field.sub");
    checkNesting(*candidate, subtract);
    auto parent = subtract->getParentOfType<func::FuncOp>();
    SmallVector<StringRef> order;
    for (auto applied : sf::applications(parent))
      order.push_back(implementation(applied) == "arkworks/field.sub"
                          ? StringRef("arithmetic")
                          : applied.getSite());
    require(order == SmallVector<StringRef>{"lc_6_before", "arithmetic",
                                            "lc_5_after"},
            "numerical materialization crossed an ordered guard");
    auto before = sf::application(parent, "control.require");
    IRRewriter rewriter(&context);
    auto *prefix = before->getBlock();
    auto *tail = rewriter.splitBlock(prefix, before->getIterator());
    auto stop = cast<exec::DispatchOp>(before->getNextNode()).getStopped();
    OpBuilder builder(&context);
    builder.setInsertionPointToEnd(prefix);
    exec::ScopedExecutionBuilder control(builder, parent);
    auto values = control.invoke(
        "exec.apply", subtract.getOutcome().getType().getPayload(),
        subtract->getOperands(), subtract->getAttrs(), stop);
    rewriter.mergeBlocks(tail, builder.getInsertionBlock());
    sc::omit(subtract, values);
    admitPhysical(*candidate);
    reject(verifyPhysicalMaterialization(*module, *candidate, checked),
           "binding-materialization-correspondence");
  });

  cases.run("shared polynomial computation cuts admit physical publication",
            [&] {
              auto module = executable(
                  fixtureText("computation/shared-polynomial.mlir"), context);
              auto checked = checkedPlan(*module);
              materializedCopy(*module, checked);
            });

  cases.run(
      "standalone lowering traces candidate and caller publication separately",
      [&] {
        auto traced = executable(scalarSource, context);
        auto plain = copy(*traced);
        mathematical::RealizationTrace trace;
        require(
            succeeded(computation::realizeComputations(*traced, {}, &trace)) &&
                succeeded(computation::realizeComputations(*plain)),
            "standalone computation lowering refused");
        require(printed(*traced) == printed(*plain),
                "tracing changed executable output");
        unsigned returned = 0, published = 0;
        for (const auto &event : trace.events)
          if (auto *publication =
                  std::get_if<mathematical::PublicationDecision>(
                      &event.payload)) {
            if (event.service == "propose-computation-realization") {
              require(publication->boundary ==
                          mathematical::PublicationBoundary::ReturnedCandidate,
                      "proposal claimed caller publication");
              ++returned;
            }
            if (event.service == "realize-computations") {
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
        require(failed(computation::realizeComputations(*empty, {}, &trace)),
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

  cases.run(
      "existing executable input without computation still materializes", [&] {
        auto module = take(executableFixture(pinnedSource(), context));
        require(succeeded(computation::realizeComputations(*module)),
                "ordinary executable control lowering failed");
        bool hasComputation = false;
        module->walk([&](Operation *op) {
          hasComputation |=
              (mathematical::isComputationUnit(op) || isa<exec::ComputeOp>(op));
        });
        require(!hasComputation,
                "control fixture still contains computation operations");
        auto checked = checkedPlan(*module);
        materializedCopy(*module, checked);
      });

  for (uint64_t reserve : {uint64_t(0), uint64_t(1)}) {
    cases.run(
        "ordered computation survives exhausted optional work and reserve " +
            std::to_string(reserve),
        [&] {
          auto module = executable(mappedSource(), context);
          FrozenInput frozen(*module);
          mathematical::RealizationWork work;
          work.matching.structural = 0;
          work.discardedRecipeCopy = reserve;
          work.discardedRecipeSiteBytes = reserve;
          PhysicalPlanOptions options;
          options.numericalWork = &work;
          auto plan = take(
              proposePhysical(*module, installedCandidates(), {}, options));
          auto selected = take(plan.cloneSelectedSubject(*module));
          bool loop = false, native = false;
          SymbolTable symbols(owner(*selected));
          selected->walk([&](Operation *op) {
            loop |= isa<exec::RangeOp>(op);
            if (auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding"))
              if (auto binding =
                      symbols.lookup<runtime::BindingOp>(ref.getValue()))
                native |= binding.getContract() == "numerical.sum" ||
                          binding.getContract() == "numerical.map";
          });
          require(loop && !native && work.selectionBookkeeping < 1000000,
                  "mandatory bookkeeping or optional construction lost ordered "
                  "execution");
          take(validatePhysical(*module, plan));
          frozen.check(*module);
        });
  }
  cases.run(
      "one scoped executable composes structured maps and computations", [&] {
        auto module = executable(mixedMapSource(context), context);
        FrozenInput frozen(*module);
        CountingCatalog catalog;
        auto plan = take(proposePhysical(*module, catalog));
        auto selected = take(plan.cloneSelectedSubject(*module));
        bool map = false, sum = false;
        selected->walk([&](Operation *op) {
          require(!mathematical::isComputationUnit(op) &&
                      !isa<exec::ComputeOp, exec::CollectOp, exec::FoldOp>(op),
                  "mixed final subject retained source work");
          auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
          auto binding = ref ? SymbolTable(owner(*selected))
                                   .lookup<runtime::BindingOp>(ref.getValue())
                             : runtime::BindingOp();
          if (binding) {
            map |= binding.getContract() == "numerical.map";
            sum |= binding.getContract() == "numerical.sum";
          }
        });
        require(map && sum &&
                    succeeded(mathematical::verifyNumericalLowering(*module,
                                                                    *selected)),
                "mixed retained body lost one numerical family");
        auto checked = take(validatePhysical(*module, plan, catalog));
        auto queries = catalog.queryCount();
        frozen.check(*module);
        accept(materializePhysical(*module, checked));
        admitPhysical(*module);
        require(catalog.queryCount() == queries,
                "mixed materialization searched again");
      });
  cases.run(
      "a fixed conversion endpoint permits its automatic peer to change", [&] {
        auto module = executable(fixedPeerSource(), context);
        FrozenInput frozen(*module);
        DirectionalCatalog catalog;
        auto plan = take(proposePhysical(*module, catalog));
        require(bindingFor(plan, "poly.fold").fixed &&
                    bindingFor(plan, "poly.fold")
                            .binding.application.implementation ==
                        "arkworks-msb/poly.fold" &&
                    !bindingFor(plan, "poly.product_sum").fixed &&
                    bindingFor(plan, "poly.product_sum")
                            .binding.application.implementation ==
                        "arkworks-msb/poly.product_sum",
                "fixed endpoint blocked or changed an automatic peer choice");
        take(validatePhysical(*module, plan, catalog));
        frozen.check(*module);
      });
  return cases.result();
}
