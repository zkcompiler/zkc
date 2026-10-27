#include "../lib/Conversion/Bindings.h"
#include "../lib/Target/PhysicalPlan.h"
#include "../lib/Transforms/NumericalSelection.h"
#include "mlir/IR/OperationSupport.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "support/ScopedFixture.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Computation.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace sf = zkc::test::scopedFinite;
namespace sc = zkc::test::scopedComputation;
namespace {
std::string invoke(StringRef operation, StringRef attributes, StringRef site,
                   StringRef inputs, StringRef types, StringRef output,
                   StringRef result) {
  auto text = scopedApply("unused", site, inputs, types, output, result);
  text = replaceText(text, "\"exec.apply\"", "\"" + operation.str() + "\"");
  text = replaceText(text, "binding=@unused", attributes);
  text = replaceText(text, ",parameters=[]", "");
  return operation == "func.call" ? replaceText(text, "site=", "runtime.site=")
                                  : text;
}
std::string functionText(StringRef name, StringRef arguments, StringRef result,
                         StringRef body, bool privateFunction = false) {
  auto outcome = "!exec.outcome<(" + result.str() + ")>";
  return std::string(privateFunction ? "func.func private @" : "func.func @") +
         name.str() + "(%scope:!runtime.scope," + arguments.str() + ")->" +
         outcome + " attributes {no_inline,runtime.origin=[\"" + name.str() +
         "\",[]]} {\n" + body.str() +
         (body.contains("^failed")
              ? "\n^failed(%reason:!exec.stop):\n%failure = "
                "\"exec.failed\"(%reason) : (!exec.stop)->" +
                    outcome + "\nfunc.return %failure : " + outcome
              : "") +
         "\n}\n";
}
constexpr StringLiteral aliases = R"mlir(
!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
)mlir";
constexpr StringLiteral domain = R"mlir(
"data.domain"() ({^entry(%a:!V,%b:!V,%c:!V):
  %as = "data.domain_elements"(%a) : (!V)->!data.domain<!F>
  %bs = "data.domain_elements"(%b) : (!V)->!data.domain<!F>
  %cs = "data.domain_elements"(%c) : (!V)->!data.domain<!F>
  %rows = "data.domain_zip"(%as,%bs,%cs) : (!data.domain<!F>,!data.domain<!F>,!data.domain<!F>)->!data.domain<!F,!F,!F>
  "data.domain_yield"(%rows) : (!data.domain<!F,!F,!F>)->()
}) {sym_name="rows",sym_visibility="private",function_type=(!V,!V,!V)->!data.domain<!F,!F,!F>} : ()->()
)mlir";
std::string reductionFixture(bool repeated = false) {
  std::string definitions = R"mlir(
"runtime.binding"() {sym_name="sum",contract="vector.sum",arguments=["koala-bear"],implementation=""} : ()->()
func.func private @formula(%a:!F,%b:!F,%unused:!F)->!F {
  %r = algebra.field_multiply %a,%b : (!F,!F)->!F
  func.return %r : !F
}
)mlir";
  definitions += domain.str();
  definitions +=
      functionText("row", "%a:!F,%b:!F,%c:!F,%xs:!V,%ys:!V,%zs:!V", "!F",
                   invoke("exec.compute", "callee=@formula", "calculate",
                          "%a,%b,%c", "!F,!F,!F", "%r", "!F") +
                       scopedReturn("%r", "!F"),
                   true);
  std::string body;
  for (unsigned i = 0; i != (repeated ? 2u : 1u); ++i) {
    std::string suffix = i ? "_second" : "";
    body += invoke("exec.collect", "domain=@rows,body=@row", "map" + suffix,
                   "%a,%b,%c", "!V,!V,!V", "%v" + suffix, "!V");
    body += scopedApply("sum", "sum" + suffix, "%v" + suffix, "!V",
                        "%r" + suffix, "!F");
  }
  body += scopedReturn(repeated ? "%r_second" : "%r", "!F");
  return aliases.str() + scopedFixture(definitions, "%a:!V,%b:!V,%c:!V",
                                       "%a,%b,%c", "!V,!V,!V", "!F", body, 3);
}
std::string unaryDeclarations(bool identity) {
  std::string definitions = R"mlir(
"data.domain"() ({^entry(%xs:!V):
  %items = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
  "data.domain_yield"(%items) : (!data.domain<!F>)->()
}) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
func.func private @formula(%x:!F)->!F {
)mlir";
  if (!identity)
    definitions += "  %square = algebra.field_multiply %x,%x : (!F,!F)->!F\n";
  definitions +=
      identity ? "func.return %x : !F\n}\n" : "func.return %square : !F\n}\n";
  definitions += functionText("row", "%x:!F,%xs:!V", "!F",
                              invoke("exec.compute", "callee=@formula",
                                     "calculate", "%x", "!F", "%r", "!F") +
                                  scopedReturn("%r", "!F"),
                              true);
  return definitions;
}
std::string repeatedMapFixture() {
  auto definitions = unaryDeclarations(false);
  definitions +=
      functionText("work", "%xs:!V", "!V,!V",
                   invoke("exec.collect", "domain=@items,body=@row", "first",
                          "%xs", "!V", "%first", "!V") +
                       invoke("exec.collect", "domain=@items,body=@row",
                              "second", "%xs", "!V", "%second", "!V") +
                       scopedReturn("%first,%second", "!V,!V"));
  return aliases.str() + "module { \"protocol.module\"() ({\n" + definitions +
         R"mlir(
"protocol.func"() ({^entry(%xs:!V):
  %r:2 = "protocol.local_call"(%xs) {callee=@work,role="P",site="work"} : (!V)->(!V,!V)
  "protocol.return"(%r#0,%r#1) : (!V,!V)->()
}) {sym_name="main",function_type=(!V)->(!V,!V),roles=["P"],input_roles=[["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
}
OwningOpRef<ModuleOp> identityCaptureFixture(MLIRContext &context,
                                             StringRef kind) {
  auto text =
      aliases.str() + R"mlir(
!tag = !data.variant<"variant:5b227a6b632e76617269616e742f30222c5b2243686f696365222c226c656674222c5b5d2c5b2231222c2232225d2c227269676874222c5b2234222c2232225d2c5b2233222c2235225d2c5b2230222c2236225d5d5d">
)mlir" +
      scopedFixture(unaryDeclarations(true),
                    "%xs:!V,%other:!V,%flag:i1,%lo:ui64,%hi:ui64,%tag:!tag",
                    "%xs,%other,%flag,%lo,%hi,%tag", "!V,!V,i1,ui64,ui64,!tag",
                    "!V", scopedReturn("%xs", "!V"), 6);
  auto module = parseSourceString<ModuleOp>(text, &context);
  require(bool(module), "identity fixture refused");
  auto function = sf::function(*module, "Work");
  auto end = sc::returned(function);
  auto *block = end->getBlock();
  end->getNextNode()->erase();
  end.erase();
  OpBuilder builder(block, block->end());
  exec::ScopedExecutionBuilder control(builder, function);
  auto vector = function.getArgument(1).getType();
  auto xs = function.getArgument(1), other = function.getArgument(2),
       flag = function.getArgument(3);
  auto alias = control.invoke(
      "exec.collect", vector, control.scoped(xs),
      {builder.getNamedAttr("domain",
                            FlatSymbolRefAttr::get(&context, "items")),
       builder.getNamedAttr("body", FlatSymbolRefAttr::get(&context, "row")),
       builder.getNamedAttr("site", builder.getStringAttr("identity"))})[0];
  SmallVector<Value> captures{xs, alias, other};
  bool loop = kind == "for" || kind == "condition";
  auto outline = [&](unsigned arm) {
    SmallVector<Type> inputs;
    if (loop)
      llvm::append_range(inputs,
                         TypeRange{function.getArgument(4).getType(), vector});
    llvm::append_range(inputs, TypeRange{vector, vector, vector});
    if (loop)
      inputs.push_back(flag.getType());
    SmallVector<Type> outputs;
    if (kind == "condition")
      outputs.push_back(flag.getType());
    outputs.push_back(vector);
    auto body = sc::region(builder, function, "control_" + std::to_string(arm),
                           inputs, outputs);
    exec::ScopedExecutionBuilder inner(builder, body);
    SmallVector<Value> values;
    if (kind == "condition")
      values.push_back(body.getArgument(6));
    values.push_back(body.getArgument(loop ? 4 : arm == 0 ? 2 : 3));
    inner.complete(values);
    return body;
  };
  SmallVector<Value> result;
  if (loop) {
    captures.push_back(flag);
    result =
        control.loop(function.getArgument(4), function.getArgument(5), other,
                     captures, vector, kind == "condition", "control", outline);
  } else if (kind == "if")
    result = control.conditional(flag, captures, vector, "control", outline);
  else
    result = control.match(function.getArgument(6), captures, vector,
                           {"left", "right"}, "control", outline);
  control.returned(result);
  require(succeeded(verify(*module)), "identity control source malformed");
  return module;
}
std::string fixture() {
  std::string definitions = R"mlir(
func.func private @square(%x:!F)->!F {
  %r = algebra.field_multiply %x,%x : (!F,!F)->!F
  func.return %r : !F
}
func.func private @formula(%a:!F,%b:!F,%unused:!F,%s:!F)->!F {
  %sq = func.call @square(%a) : (!F)->!F
  %m = algebra.field_multiply %sq,%b : (!F,!F)->!F
  %r = algebra.field_add %m,%s : (!F,!F)->!F
  %dead = func.call @square(%unused) : (!F)->!F
  func.return %r : !F
}
func.func private @unrelated(%x:!F)->!F {func.return %x : !F}
)mlir";
  definitions += domain.str();
  definitions +=
      functionText("row", "%a:!F,%b:!F,%c:!F,%xs:!V,%ys:!V,%zs:!V,%s:!F", "!F",
                   invoke("exec.compute", "callee=@formula", "calculate",
                          "%a,%b,%c,%s", "!F,!F,!F,!F", "%r", "!F") +
                       scopedReturn("%r", "!F"),
                   true);
  definitions +=
      functionText("identity", "%x:!F", "!F", scopedReturn("%x", "!F"));
  for (StringRef name : {"through", "dormant"})
    definitions +=
        functionText(name, "%a:!V,%b:!V,%c:!V,%s:!F", "!V",
                     invoke("exec.collect", "domain=@rows,body=@row",
                            name == "through" ? "map" : "unused_map",
                            "%a,%b,%c,%s", "!V,!V,!V,!F", "%r", "!V") +
                         scopedReturn("%r", "!V"));
  definitions +=
      functionText("work", "%a:!V,%b:!V,%c:!V,%s:!F", "!V",
                   invoke("func.call", "callee=@identity", "ordinary", "%s",
                          "!F", "%t", "!F") +
                       invoke("func.call", "callee=@through", "nested",
                              "%a,%b,%c,%t", "!V,!V,!V,!F", "%r", "!V") +
                       scopedReturn("%r", "!V"));
  return aliases.str() + "module { \"protocol.module\"() ({\n" + definitions +
         R"mlir(
"protocol.func"() ({^entry(%a:!V,%b:!V,%c:!V,%s:!F):
  %p = "protocol.local_call"(%a,%b,%c,%s) {callee=@work,role="P",site="p_work"} : (!V,!V,!V,!F)->!V
  %q = "protocol.local_call"(%a,%b,%c,%s) {callee=@work,role="Q",site="q_work"} : (!V,!V,!V,!F)->!V
  "protocol.return"(%p,%q) : (!V,!V)->()
}) {sym_name="main",function_type=(!V,!V,!V,!F)->(!V,!V),roles=["P","Q"],input_roles=[["P","Q"],["P","Q"],["P","Q"],["P","Q"]],output_roles=[["P"],["Q"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
}
protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
bool same(Operation *a, Operation *b) {
  return OperationEquivalence::isEquivalentTo(
      a, b, OperationEquivalence::IgnoreLocations);
}
OwningOpRef<ModuleOp> project(ModuleOp source) {
  auto candidate = sf::clone(source);
  PassManager manager(source.getContext());
  manager.addPass(protocol::createProjectProtocolPass(false));
  require(succeeded(manager.run(*candidate)), "scoped projection refused");
  return candidate;
}
OwningOpRef<ModuleOp> executable(ModuleOp source) {
  auto projected = project(source);
  auto candidate = protocol::expandScopedHelpers(*projected);
  require(bool(candidate) &&
              succeeded(protocol::verifyScopedHelperExpansionPreserved(
                  *projected, *candidate)),
          "scoped helper expansion refused");
  unit(*candidate).setProfile(protocol_ir::Profile::Exec);
  require(succeeded(verify(*candidate)), "logical scoped subject refused");
  return candidate;
}
class Withheld final : public target::CandidateCatalog {
  std::vector<std::string> contracts;

public:
  explicit Withheld(std::vector<std::string> contracts = {})
      : contracts(std::move(contracts)) {}
  llvm::Expected<std::vector<std::string>> implementations(
      const protocol::BindingApplication &application) const override {
    if (llvm::is_contained(contracts, application.contract))
      return std::vector<std::string>{};
    return target::installedCandidates().implementations(application);
  }
  std::vector<std::string> diagonalImplementations(
      const protocol::BindingApplication &application) const override {
    return target::installedCandidates().diagonalImplementations(application);
  }
  std::vector<protocol::BindingApplication>
  conversions(const protocol::BoundType &from,
              const protocol::BoundType &to) const override {
    return target::installedCandidates().conversions(from, to);
  }
};
SmallVector<exec::ApplyOp> callsOf(ModuleOp module, StringRef contract) {
  return sf::applications(module, contract);
}
void removeUnusedFailureBlocks(ModuleOp module) {
  module.walk([&](func::FuncOp function) {
    if (!protocol::isScopedExecutionFunction(function))
      return;
    for (auto &block : llvm::make_early_inc_range(function.getBody()))
      if (&block != &function.front() && block.hasNoPredecessors())
        block.erase();
  });
}
void sourceBulk(ModuleOp source, bool enabled) {
  Builder builder(source.getContext());
  source.walk([&](exec::ComputeOp op) {
    op->setAttr("policy", builder.getBoolArrayAttr({enabled, false, false}));
  });
}
OwningOpRef<ModuleOp>
prepareFinite(ModuleOp source,
              MathematicalSelectionPolicy policy = {true, true, false},
              mathematical::RealizationWork *account = nullptr,
              const llvm::DenseSet<Operation *> *fixed = nullptr) {
  mathematical::RealizationWork local;
  uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
  std::optional<CapacityCause> capacity;
  auto result = protocol::prepareScopedFinite(
      source, account ? *account : local, copy, bytes, capacity, policy, fixed);
  require(bool(result), "finite preparation refused");
  return result;
}
LogicalResult
compareFinite(ModuleOp source, ModuleOp actual,
              MathematicalSelectionPolicy policy = {true, true, false},
              const llvm::DenseSet<Operation *> *fixed = nullptr) {
  mathematical::RealizationWork work;
  return protocol::verifyScopedFinitePreparation(source, actual, work, policy,
                                                 nullptr, fixed);
}
void noResidualNumerics(ModuleOp module) {
  module.walk([&](Operation *op) {
    auto name = op->getName().getStringRef();
    require(!mathematical::isComputationUnit(op) &&
                !isa<exec::CollectOp, exec::FoldOp, exec::ComputeOp,
                     data::DomainOp>(op) &&
                !name.starts_with("local.") && !name.starts_with("plan.") &&
                !name.starts_with("kernel."),
            "selected scoped execution retained unresolved/replaced work");
    if (auto helper = dyn_cast<func::FuncOp>(op))
      require(protocol::isScopedExecutionFunction(helper),
              "plain mathematics survived numerical lowering");
  });
}
OwningOpRef<ModuleOp> materialized(
    ModuleOp source,
    const target::CandidateCatalog &catalog = target::installedCandidates(),
    target::PhysicalPlanOptions options = {}) {
  auto result = sf::clone(source);
  auto plan = take(target::proposePhysical(*result, catalog, {}, options));
  auto checked = take(target::validatePhysical(*result, plan, catalog));
  if (auto error = protocol::materializePhysical(*result, checked))
    throw std::runtime_error(llvm::toString(std::move(error)));
  require(succeeded(verify(*result)), "physical materialization malformed");
  noResidualNumerics(*result);
  take(protocol::readExecutionModel(*result));
  return result;
}
// Exchange complete independent length invocations: operands, occurrence and
// continuation values. Merely moving an operation would break scoped CFG.
void exchangeLengths(exec::ApplyOp first, exec::ApplyOp second) {
  auto firstInput = first.getInputs()[0], secondInput = second.getInputs()[0];
  auto firstSite = first.getSiteAttr(), secondSite = second.getSiteAttr();
  auto a = sc::payload(first)[0], b = sc::payload(second)[0];
  SmallVector<OpOperand *> usesA, usesB;
  for (auto &use : a.getUses())
    usesA.push_back(&use);
  for (auto &use : b.getUses())
    usesB.push_back(&use);
  first->setOperand(1, secondInput);
  second->setOperand(1, firstInput);
  first.setSiteAttr(secondSite);
  second.setSiteAttr(firstSite);
  for (auto *use : usesA)
    use->set(b);
  for (auto *use : usesB)
    use->set(a);
}
Operation *completion(func::FuncOp function) {
  Operation *result = nullptr;
  function.walk([&](Operation *op) {
    if (isa<exec::CompleteOp, exec::ReturnOp>(op)) {
      require(!result, "multiple root completions");
      result = op;
    }
  });
  require(result, "missing root completion");
  return result;
}
void appendInvocation(exec::ApplyOp original, func::FuncOp function) {
  auto *end = completion(function);
  auto *stop = cast<exec::DispatchOp>(original->getNextNode()).getStopped();
  IRRewriter rewriter(function.getContext());
  auto *before = end->getBlock();
  auto *tail = rewriter.splitBlock(before, end->getIterator());
  OpBuilder builder(function.getContext());
  builder.setInsertionPointToEnd(before);
  exec::ScopedExecutionBuilder control(builder, function);
  NamedAttrList attributes(original->getAttrs());
  attributes.set("site", builder.getStringAttr("extra_length"));
  control.invoke("exec.apply", original.getOutcome().getType().getPayload(),
                 original->getOperands(), attributes.getAttrs(), stop);
  rewriter.mergeBlocks(tail, builder.getInsertionBlock());
}
bool named(MLIRContext &context, StringRef code,
           llvm::function_ref<LogicalResult()> action) {
  bool seen = false;
  ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &diagnostic) {
    seen |= namesIdentifier(diagnostic.str(), code);
    return success();
  });
  return failed(action()) && seen;
}
void refusesError(llvm::Error error, StringRef code) {
  require(bool(error), "expected refusal: " + code);
  auto message = llvm::toString(std::move(error));
  require(namesIdentifier(message, code), "unexpected refusal: " + message);
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry, MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  Cases cases;
  auto parse = [&](StringRef text) {
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "scoped late-selection source refused");
    return module;
  };
  cases.run(
      "ordinary helpers expand while exact collection closures remain", [&] {
        auto source = parse(fixture()), unchanged = sf::clone(*source);
        auto prepared = mathematical::prepareProtocol(*source, false);
        require(bool(prepared) && same(*source, *unchanged),
                "preparation changed its source");
        auto expanded = protocol::expandScopedHelpers(*prepared);
        require(bool(expanded) &&
                    succeeded(protocol::verifyScopedHelperExpansionPreserved(
                        *prepared, *expanded)),
                "actual scoped helper expansion refused");
        for (StringRef name : {"square", "formula"})
          require(
              same(sf::function(*source, name), sf::function(*prepared, name)),
              "retained mathematics changed");
        unsigned requests = 0, calls = 0;
        expanded->walk([&](exec::CollectOp) { ++requests; });
        expanded->walk([&](func::CallOp call) {
          if (call->getParentOfType<func::FuncOp>()->hasAttr("runtime.origin"))
            ++calls;
        });
        require(requests == 3 && calls == 0,
                "nested or dormant request lost, or helper not expanded");
      });
  cases.run("two participant roles share one exact mathematical closure", [&] {
    auto source = parse(fixture()), projected = project(*source);
    // Projection preserves the complete admitted authored inventory. Removing
    // dormant definitions is a separately checked numerical-lowering decision.
    for (StringRef name : {"formula", "square", "unrelated", "dormant"})
      require(same(sf::function(*source, name), sf::function(*projected, name)),
              "projected mathematics changed");
    unsigned roles = 0;
    for (auto participant : unit(*projected)
                                .getBody()
                                .front()
                                .getOps<protocol_ir::ParticipantOp>()) {
      unsigned calls = 0;
      participant.walk([&](protocol_ir::LocalCallOp call) {
        require(call.getCallee() == "work", "participant changed scoped root");
        ++calls;
      });
      require(calls == 1, "participant lost its invocation");
      ++roles;
    }
    require(roles == 2 && succeeded(verify(*projected)),
            "two-role projection refused");
  });
  for (StringRef change :
       {"transitive return", "unused work", "capture", "helper reference"})
    cases.run("retention freezes " + change, [&] {
      auto source = parse(fixture()), before = project(*source),
           after = sf::clone(*before);
      if (change == "transitive return") {
        auto square = sf::function(*after, "square");
        square.front().back().setOperand(0, square.getArgument(0));
      } else if (change == "unused work") {
        func::CallOp dead;
        sf::function(*after, "formula").walk([&](func::CallOp op) {
          if (op->use_empty())
            dead = op;
        });
        require(bool(dead), "missing unused helper call");
        dead.erase();
      } else if (change == "capture") {
        exec::CollectOp collection;
        after->walk([&](exec::CollectOp op) { collection = op; });
        require(bool(collection), "missing retained collection");
        auto first = collection.getInputs()[0];
        collection->setOperand(1, collection.getInputs()[1]);
        collection->setOperand(2, first);
      } else {
        auto formula = sf::function(*after, "formula");
        OpBuilder builder(formula);
        auto alternate = cast<func::FuncOp>(builder.clone(*formula));
        alternate.setSymName("alternate");
        after->walk([&](exec::ComputeOp op) {
          op.setCalleeAttr(FlatSymbolRefAttr::get(&context, "alternate"));
        });
      }
      require(succeeded(verify(*after)), "retained-context mutation malformed");
      require(named(context, "native-local-policy",
                    [&] {
                      return mathematical::verifyAuthoredLocalsPreserved(
                          unit(*before), unit(*after));
                    }),
              "changed retained subject escaped exact preservation");
    });
  for (bool cycle : {false, true})
    cases.run(cycle ? "logical admission rejects cyclic mathematical closure"
                    : "logical admission rejects public transitive helper",
              [&] {
                auto source = parse(fixture()), candidate = executable(*source);
                auto helper = sf::function(*candidate, "square");
                if (cycle) {
                  OpBuilder builder(&helper.front().back());
                  auto call = func::CallOp::create(
                      builder, helper.getLoc(), helper, helper.getArguments());
                  helper.front().back().setOperand(0, call.getResult(0));
                } else
                  helper.setPublic();
                require(named(context, "mathematical-formation",
                              [&] { return verify(*candidate); }),
                        "logical request bypassed closure admission");
              });
  for (StringRef body : {"missing", "through"})
    cases.run("dormant collection refuses invalid callback " + body, [&] {
      auto source = parse(fixture()), candidate = executable(*source);
      auto dormant = sf::function(*candidate, "dormant");
      dormant.walk([&](exec::CollectOp op) {
        op->setAttr("body", FlatSymbolRefAttr::get(&context, body));
      });
      require(named(context, "finite-formation",
                    [&] { return verify(*candidate); }),
              "invalid dormant callback admitted");
    });
  cases.run("ordinary dormant scoped calls retain their actual ABI", [&] {
    auto source = parse(fixture());
    auto dormant = sf::function(*source, "dormant");
    exec::CollectOp collection;
    dormant.walk([&](exec::CollectOp op) { collection = op; });
    OpBuilder builder(collection);
    auto call = func::CallOp::create(builder, collection.getLoc(),
                                     sf::function(*source, "through"),
                                     collection->getOperands());
    call->setAttr("runtime.site", collection.getSiteAttr());
    collection.getOutcome().replaceAllUsesWith(call.getResult(0));
    collection.erase();
    require(succeeded(verify(*source)), "ordinary scoped call refused");
    auto expanded = protocol::expandScopedHelpers(*source);
    require(bool(expanded) &&
                succeeded(protocol::verifyScopedHelperExpansionPreserved(
                    *source, *expanded)),
            "ordinary dormant call failed checked expansion");
  });
  cases.run("dormant collection requests cannot be published", [&] {
    auto source = parse(fixture()), candidate = executable(*source);
    SmallVector<exec::CollectOp> active;
    candidate->walk([&](exec::CollectOp op) {
      if (op->getParentOfType<func::FuncOp>().getSymName() != "dormant")
        active.push_back(op);
    });
    for (auto collection : active)
      sc::omit(collection, collection.getInputs().front());
    removeUnusedFailureBlocks(*candidate);
    require(succeeded(verify(*candidate)), "dormant-only source refused");
    auto output = protocol::readExecutionModel(*candidate);
    require(!output, "unresolved dormant request reached publication");
    llvm::consumeError(output.takeError());
    unit(*candidate).setProfile(protocol_ir::Profile::Physical);
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    require(failed(verify(*candidate)),
            "physical profile admitted pending collection");
  });
  cases.run(
      "map-only physical selection consumes the exact retained subject", [&] {
        auto source = parse(fixture()), original = executable(*source),
             frozen = sf::clone(*original);
        auto identities = target::physicalPlanOperations(*original);
        auto proposal = take(target::proposePhysical(*original));
        auto selected = take(proposal.cloneSelectedSubject(*original));
        noResidualNumerics(*selected);
        auto maps = callsOf(*selected, "numerical.map");
        require(!maps.empty(), "native map occurrence missing");
        maps.front()->setOperand(3, maps.front().getInputs()[1]);
        auto retained = take(proposal.cloneSelectedSubject(*original));
        require(!same(*selected, *retained),
                "inspection changed retained candidate");
        auto checked = take(target::validatePhysical(*original, proposal));
        auto physical = sf::clone(*original);
        auto physicalProposal = take(target::proposePhysical(*physical));
        auto physicalChecked =
            take(target::validatePhysical(*physical, physicalProposal));
        if (auto error =
                protocol::materializePhysical(*physical, physicalChecked))
          throw std::runtime_error(llvm::toString(std::move(error)));
        require(succeeded(verify(*physical)), "physical output refused");
        noResidualNumerics(*physical);
        if (auto error = protocol::verifyPhysicalMaterialization(
                *original, *physical, checked))
          throw std::runtime_error(llvm::toString(std::move(error)));
        take(protocol::readExecutionModel(*physical));
        require(same(*original, *frozen) &&
                    target::physicalPlanOperations(*original) == identities,
                "plan transaction changed original identities");
      });
  for (auto profile :
       {protocol_ir::Profile::Protocol, protocol_ir::Profile::Participant,
        protocol_ir::Profile::Exec})
    for (bool enabled : {false, true})
      cases.run(
          "requested fusion policy in profile " +
              std::to_string(unsigned(profile)) +
              " enabled=" + std::to_string(enabled),
          [&] {
            auto source = parse(reductionFixture());
            auto subject =
                profile == protocol_ir::Profile::Protocol ? sf::clone(*source)
                : profile == protocol_ir::Profile::Exec   ? executable(*source)
                                                          : project(*source);
            auto frozen = sf::clone(*subject);
            MathematicalSelectionPolicy policy{true, enabled, false};
            auto actual = prepareFinite(*subject, policy);
            require(same(*subject, *frozen) &&
                        succeeded(compareFinite(*subject, *actual, policy)),
                    "late finite selection changed source or failed readback");
            auto dots = callsOf(*actual, "vector.dot");
            require(dots.size() == unsigned(enabled),
                    "selection ignored the requested fusion policy");
            if (enabled) {
              dots.front()->setOperand(2, dots.front().getInputs()[0]);
              require(succeeded(verify(*actual)), "dot mutation malformed");
              ScopedDiagnosticHandler quiet(
                  &context, [](Diagnostic &) { return success(); });
              require(failed(compareFinite(*subject, *actual, policy)),
                      "finite reader accepted substituted dot payload");
            } else {
              auto fused = prepareFinite(*subject, {true, true, false});
              require(callsOf(*fused, "vector.dot").size() == 1,
                      "enabled fusion control missing");
              ScopedDiagnosticHandler quiet(
                  &context, [](Diagnostic &) { return success(); });
              require(failed(compareFinite(*subject, *fused, policy)),
                      "independent reader ignored disabled fusion");
            }
          });
  cases.run("dormant mathematical declarations are admitted and consumed", [&] {
    auto source = parse(fixture()), original = executable(*source);
    SmallVector<exec::CollectOp> collections;
    original->walk([&](exec::CollectOp op) { collections.push_back(op); });
    for (auto collection : collections)
      sc::omit(collection, collection.getInputs().front());
    removeUnusedFailureBlocks(*original);
    require(succeeded(verify(*original)), "dormant source refused");
    auto plan = take(target::proposePhysical(*original));
    auto selected = take(plan.cloneSelectedSubject(*original));
    noResidualNumerics(*selected);
    take(target::validatePhysical(*original, plan));
  });
  const std::vector<std::vector<std::string>> missing = {
      {},
      {"vector.dot"},
      {"vector.dot", "numerical.sum"},
      {"vector.dot", "numerical.sum", "numerical.map"},
      {"vector.dot", "numerical.sum", "numerical.map", "vector.mul"}};
  for (unsigned rung = 0; rung != missing.size(); ++rung)
    cases.run(
        "physical map/sum capability alternative " + std::to_string(rung), [&] {
          auto source = parse(reductionFixture()),
               original = executable(*source);
          Withheld catalog(missing[rung]);
          target::PhysicalPlanOptions options;
          options.numericalPolicy.vectorReductionFusion = true;
          auto plan =
              take(target::proposePhysical(*original, catalog, {}, options));
          auto selected = take(plan.cloneSelectedSubject(*original));
          noResidualNumerics(*selected);
          require(
              callsOf(*selected, "vector.dot").size() == unsigned(rung == 0) &&
                  callsOf(*selected, "numerical.sum").size() ==
                      unsigned(rung == 1) &&
                  callsOf(*selected, "numerical.map").size() ==
                      unsigned(rung == 2) &&
                  callsOf(*selected, "vector.sum").size() ==
                      unsigned(rung >= 2) &&
                  callsOf(*selected, "vector.mul").size() ==
                      unsigned(rung == 3) &&
                  sf::hasLoop(sf::function(*selected, "Work")) == (rung == 4),
              "capability ladder lost the permitted or required alternative");
          take(target::validatePhysical(*original, plan, catalog));
        });
  cases.run("general Ring collection/sum selects numerical sum", [&] {
    auto source = parse(replaceText(
        reductionFixture(), "algebra.field_multiply", "algebra.field_add"));
    auto original = executable(*source);
    target::PhysicalPlanOptions options;
    options.numericalPolicy.vectorReductionFusion = true;
    auto plan = take(target::proposePhysical(
        *original, target::installedCandidates(), {}, options));
    auto selected = take(plan.cloneSelectedSubject(*original));
    require(callsOf(*selected, "numerical.sum").size() == 1 &&
                callsOf(*selected, "vector.dot").empty(),
            "general sum lost its admitted expression");
    take(target::validatePhysical(*original, plan));
  });
  for (bool vectorOnly : {false, true})
    cases.run("persisted callback restriction with vector-only=" +
                  std::to_string(vectorOnly),
              [&] {
                auto source = parse(reductionFixture());
                sourceBulk(*source, false);
                auto original = executable(*source);
                target::PhysicalPlanOptions options;
                options.numericalPolicy.vectorReductionFusion = true;
                if (vectorOnly)
                  options.numericalPolicy.numericalExpressions =
                      NumericalExpressionMode::VectorOnly;
                auto plan = take(target::proposePhysical(
                    *original, target::installedCandidates(), {}, options));
                auto selected = take(plan.cloneSelectedSubject(*original));
                require(callsOf(*selected, "vector.sum").size() == 1 &&
                            callsOf(*selected, "vector.dot").empty() &&
                            callsOf(*selected, "numerical.sum").empty() &&
                            callsOf(*selected, "numerical.map").empty() &&
                            sf::hasLoop(sf::function(*selected, "Work")),
                        "late selection changed explicit source or "
                        "representation policy");
                take(target::validatePhysical(*original, plan));
              });
  cases.run("source and requested sum pins independently restrict fusion", [&] {
    auto source = parse(reductionFixture()), original = executable(*source);
    target::PhysicalPlanOptions options;
    options.numericalPolicy.vectorReductionFusion = true;
    auto fused = prepareFinite(*original);
    auto binding =
        SymbolTable(unit(*original)).lookup<runtime::BindingOp>("sum");
    llvm::DenseSet<Operation *> fixed{binding};
    require(succeeded(compareFinite(*original, *fused)),
            "unrestricted baseline failed");
    {
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      require(
          failed(compareFinite(*original, *fused, {true, true, false}, &fixed)),
          "independent finite reader ignored fixed sum");
    }
    protocol::Assignments selections{{"sum", "plonky3/vector.sum"}};
    auto requested = take(target::proposePhysical(
        *original, target::installedCandidates(), selections, options));
    auto selected = take(requested.cloneSelectedSubject(*original));
    require(callsOf(*selected, "vector.sum").size() == 1 &&
                callsOf(*selected, "numerical.map").size() == 1,
            "requested implementation disappeared into fusion");
    take(target::validatePhysical(*original, requested));
    binding.setImplementation("plonky3/vector.sum");
    auto pinned = take(target::proposePhysical(
        *original, target::installedCandidates(), {}, options));
    auto pinnedSelected = take(pinned.cloneSelectedSubject(*original));
    require(callsOf(*pinnedSelected, "vector.sum").size() == 1,
            "source implementation disappeared into fusion");
    take(target::validatePhysical(*original, pinned));
  });
  for (bool fusion : {false, true})
    cases.run(
        "complete-program refusal changes only one occurrence, fusion=" +
            std::to_string(fusion),
        [&] {
          auto source = parse(reductionFixture(true)),
               original = executable(*source), frozen = sf::clone(*original);
          mathematical::RealizationWork work;
          target::PhysicalPlanOptions options;
          options.numericalWork = &work;
          options.numericalPolicy.vectorReductionFusion = fusion;
          unsigned visits = 0;
          StringRef rejected = fusion ? "vector.dot" : "numerical.map";
          options.programCapacity = [&](ModuleOp,
                                        const target::PhysicalPlan &plan)
              -> llvm::Expected<SmallVector<target::OperationIndex>> {
            if (++visits == 1)
              for (const auto &operation : plan.operations)
                if (operation.binding &&
                    plan.bindings[*operation.binding]
                            .binding.application.contract == rejected)
                  return SmallVector<target::OperationIndex>{
                      operation.operation};
            return SmallVector<target::OperationIndex>{};
          };
          auto plan = take(target::proposePhysical(
              *original, target::installedCandidates(), {}, options));
          auto selected = take(plan.cloneSelectedSubject(*original));
          require(
              visits == 2 && callsOf(*selected, rejected).size() == 1 &&
                  callsOf(*selected, fusion ? "numerical.sum" : "vector.sum")
                          .size() == (fusion ? 1u : 2u) &&
                  work.discardedRecipeCopy <
                      mathematical::RealizationWork{}.discardedRecipeCopy &&
                  same(*original, *frozen),
              "attributed refusal replaced both shared occurrences "
              "or refunded work");
          take(target::validatePhysical(*original, plan));
        });
  for (StringRef mutation : {"unused-guard", "guard-order", "extent",
                             "formula-input", "extra-work", "result-use"})
    cases.run("physical map reader rejects " + mutation, [&] {
      auto source = parse(fixture()), original = executable(*source);
      auto plan = take(target::proposePhysical(*original));
      auto checked = take(target::validatePhysical(*original, plan));
      auto actual = materialized(*original);
      if (auto error = protocol::verifyPhysicalMaterialization(
              *original, *actual, checked))
        throw std::runtime_error(llvm::toString(std::move(error)));
      auto map = callsOf(*actual, "numerical.map").front();
      auto function = map->getParentOfType<func::FuncOp>();
      auto lengths = sf::applications(function, "vector.length");
      require(lengths.size() == 3 &&
                  sf::applications(function, "control.require").size() == 2,
              "missing complete unused-row guard inventory");
      if (mutation == "unused-guard")
        lengths[2]->setOperand(1, lengths[0].getInputs()[0]);
      else if (mutation == "guard-order")
        exchangeLengths(lengths[1], lengths[2]);
      else if (mutation == "extent")
        map->setOperand(1, sc::payload(lengths[1])[0]);
      else if (mutation == "formula-input")
        map->setOperand(3, map.getInputs()[1]);
      else if (mutation == "extra-work")
        appendInvocation(lengths[0], function);
      else
        completion(function)->setOperand(1, function.getArgument(1));
      require(succeeded(verify(*actual)),
              "semantic mutation must remain admitted");
      refusesError(
          protocol::verifyPhysicalMaterialization(*original, *actual, checked),
          "binding-materialization-correspondence");
    });
  cases.run("physical summed expression rejects an admitted wrong extent", [&] {
    auto source = parse(reductionFixture()), original = executable(*source);
    Withheld catalog({"vector.dot"});
    target::PhysicalPlanOptions options;
    options.numericalPolicy.vectorReductionFusion = true;
    auto plan = take(target::proposePhysical(*original, catalog, {}, options));
    auto checked = take(target::validatePhysical(*original, plan, catalog));
    auto actual = materialized(*original, catalog, options);
    if (auto error = protocol::verifyPhysicalMaterialization(*original, *actual,
                                                             checked))
      throw std::runtime_error(llvm::toString(std::move(error)));
    auto sums = callsOf(*actual, "numerical.sum");
    auto lengths = callsOf(*actual, "vector.length");
    require(sums.size() == 1 && lengths.size() == 3,
            "summed expression lost guards");
    sums[0]->setOperand(1, sc::payload(lengths[2])[0]);
    require(succeeded(verify(*actual)), "extent mutation malformed");
    refusesError(
        protocol::verifyPhysicalMaterialization(*original, *actual, checked),
        "binding-materialization-correspondence");
  });
  for (bool optional : {false, true})
    cases.run(
        "finite reader exact and one-short optional=" +
            std::to_string(optional),
        [&] {
          auto source = parse(reductionFixture()),
               original = executable(*source);
          MathematicalSelectionPolicy policy{optional, false, false};
          auto actual = prepareFinite(*original, policy);
          mathematical::RealizationWork measured;
          mathematical::VerificationDecision outcome;
          require(succeeded(protocol::verifyScopedFinitePreparation(
                      *original, *actual, measured, policy, &outcome)),
                  "reader measurement refused");
          auto spent = 1000000 - (optional ? measured.optionalFiniteChecking
                                           : measured.requiredFiniteChecking);
          require(spent > 0, "reader did not charge its work");
          mathematical::RealizationWork exact;
          (optional ? exact.optionalFiniteChecking
                    : exact.requiredFiniteChecking) = spent;
          require(succeeded(protocol::verifyScopedFinitePreparation(
                      *original, *actual, exact, policy, &outcome)) &&
                      (optional ? exact.optionalFiniteChecking
                                : exact.requiredFiniteChecking) == 0,
                  "exact reader allowance refused");
          mathematical::RealizationWork shortWork;
          (optional ? shortWork.optionalFiniteChecking
                    : shortWork.requiredFiniteChecking) = spent - 1;
          {
            ScopedDiagnosticHandler quiet(
                &context, [](Diagnostic &) { return success(); });
            require(failed(protocol::verifyScopedFinitePreparation(
                        *original, *actual, shortWork, policy, &outcome)) &&
                        outcome.outcome ==
                            (optional ? mathematical::VerificationObservation::
                                            OptionalCapacity
                                      : mathematical::VerificationObservation::
                                            RequiredCapacity),
                    "one-short readback lost its typed capacity outcome");
          }
          if (optional) {
            mathematical::RealizationWork retry;
            retry.optionalFiniteChecking = spent - 1;
            target::PhysicalPlanOptions options;
            options.numericalWork = &retry;
            auto plan = take(target::proposePhysical(
                *original, target::installedCandidates(), {}, options));
            auto selected = take(plan.cloneSelectedSubject(*original));
            require(
                callsOf(*selected, "numerical.map").empty() &&
                    sf::hasLoop(sf::function(*selected, "Work")) &&
                    retry.requiredFiniteChecking < 1000000,
                "optional exhaustion consumed the required ordered reserve");
            take(target::validatePhysical(*original, plan));
          }
        });
  for (uint64_t reserve : {uint64_t(0), uint64_t(1)})
    cases.run(
        "required ordered endpoint with discard reserve " +
            std::to_string(reserve),
        [&] {
          auto source = parse(fixture()), original = executable(*source);
          mathematical::RealizationWork work;
          work.matching.structural = 0;
          work.discardedRecipeCopy = work.discardedRecipeSiteBytes = reserve;
          target::PhysicalPlanOptions options;
          options.numericalWork = &work;
          auto plan = take(target::proposePhysical(
              *original, target::installedCandidates(), {}, options));
          auto selected = take(plan.cloneSelectedSubject(*original));
          require(
              callsOf(*selected, "numerical.map").empty() &&
                  sf::hasLoop(sf::function(*selected, "work")) &&
                  work.requiredFiniteChecking < 1000000 &&
                  work.selectionBookkeeping < 1000000,
              "matching or optional reserve exhaustion lost ordered execution");
          take(target::validatePhysical(*original, plan));
        });
  cases.run(
      "complete-program preflight clone exact cumulative copy boundary", [&] {
        auto source = parse(reductionFixture()), original = executable(*source);
        target::PhysicalPlanOptions options;
        options.numericalPolicy.numericalExpressions =
            NumericalExpressionMode::VectorOnly;
        uint64_t copyWork = 1000000;
        options.numericalCopy = &copyWork;
        unsigned callbacks = 0;
        options.programCapacity = [&](ModuleOp complete,
                                      const target::PhysicalPlan &)
            -> llvm::Expected<SmallVector<target::OperationIndex>> {
          ++callbacks;
          require(complete != *original && succeeded(verify(complete)),
                  "preflight did not receive a private complete candidate");
          noResidualNumerics(complete);
          return SmallVector<target::OperationIndex>{};
        };
        take(target::proposePhysical(*original, target::installedCandidates(),
                                     {}, options));
        uint64_t spent = 1000000 - copyWork;
        require(spent > 0 && callbacks == 1, "preflight measurement failed");
        copyWork = spent;
        callbacks = 0;
        take(target::proposePhysical(*original, target::installedCandidates(),
                                     {}, options));
        require(copyWork == 0 && callbacks == 1,
                "preflight clone omitted from exact allowance");
        copyWork = spent - 1;
        callbacks = 0;
        refuses(target::proposePhysical(
                    *original, target::installedCandidates(), {}, options),
                "kernel-lowering");
        require(callbacks == 0, "preflight ran before its clone was charged");
      });
  cases.run(
      "missing required scalar capability is terminal and transactional", [&] {
        auto source = parse(reductionFixture()), original = executable(*source),
             frozen = sf::clone(*original);
        auto identities = target::physicalPlanOperations(*original);
        Withheld catalog({"numerical.map", "vector.mul", "field.mul"});
        refuses(target::proposePhysical(*original, catalog),
                "binding-implementation");
        require(same(*original, *frozen) &&
                    target::physicalPlanOperations(*original) == identities,
                "required capability refusal changed original source");
      });
  for (bool native : {false, true}) {
    cases.run(
        "identity map borrows before unchanged sum, native=" +
            std::to_string(native),
        [&] {
          auto source = parse(reductionFixture());
          auto formula = sf::function(*source, "formula");
          formula.front().back().setOperand(0, formula.getArgument(0));
          auto original = executable(*source);
          target::PhysicalPlanOptions options;
          if (!native)
            options.numericalPolicy.numericalExpressions =
                NumericalExpressionMode::VectorOnly;
          auto plan = take(target::proposePhysical(
              *original, target::installedCandidates(), {}, options));
          auto selected = take(plan.cloneSelectedSubject(*original));
          auto sums = callsOf(*selected, "vector.sum");
          require(
              sums.size() == 1 && callsOf(*selected, "numerical.map").empty() &&
                  sums[0].getInputs()[0] ==
                      sf::function(*selected, "Work").getArgument(1),
              "identity collection invented a payload or consumed the suffix");
          take(target::validatePhysical(*original, plan));
        });
    for (StringRef kind : {"if", "match", "for", "condition"})
      cases.run(
          "identity capture " + kind + " native=" + std::to_string(native),
          [&] {
            auto source = identityCaptureFixture(context, kind),
                 original = executable(*source), frozen = sf::clone(*original);
            MathematicalSelectionPolicy policy;
            if (!native)
              policy.numericalExpressions = NumericalExpressionMode::VectorOnly;
            auto actual = prepareFinite(*original, policy);
            require(succeeded(compareFinite(*original, *actual, policy)),
                    "identity preparation failed readback");
            auto function = sf::function(*actual, "Work");
            auto closure =
                take(protocol::readSourceExecutionClosure(unit(*actual)));
            const protocol::SourceExecutionStep *branch = nullptr;
            for (const auto &step : closure.bodies.at("Work"))
              if (!step.regions.empty())
                branch = &step;
            bool loop = kind == "for" || kind == "condition";
            unsigned prefix = loop ? 3 : 1;
            require(branch && branch->inputs.size() == (loop ? 6u : 3u) &&
                        branch->inputs[prefix] == function.getArgument(1) &&
                        branch->inputs[prefix + 1] == function.getArgument(2),
                    "alias capture survived or distinct capture disappeared");
            for (auto region : branch->regions) {
              require(region.getNumArguments() == (loop ? 6u : 3u),
                      "outlined capture ports not canonicalized");
              auto *end = completion(region);
              require(end->getNumOperands() == (kind == "condition" ? 3u : 2u),
                      "completion carries stale capture ports");
              if (loop)
                require(end->getOperand(kind == "condition" ? 2 : 1) ==
                            region.getArgument(3),
                        "loop state lost alias substitution");
            }
            target::PhysicalPlanOptions options;
            options.numericalPolicy = policy;
            auto plan = take(target::proposePhysical(
                *original, target::installedCandidates(), {}, options));
            take(target::validatePhysical(*original, plan));
            materialized(*original, target::installedCandidates(), options);
            require(same(*original, *frozen),
                    "identity selection changed source");
            auto a = function.getArgument(1), b = function.getArgument(2);
            auto exchange = [&](MutableOperandRange operands) {
              for (auto &operand : operands) {
                if (operand.get() == a)
                  operand.set(b);
                else if (operand.get() == b)
                  operand.set(a);
              }
            };
            function.walk([&](Operation *op) {
              if (auto enter = dyn_cast<runtime::EnterScopeOp>(op))
                exchange(enter.getInputsMutable().slice(
                    loop ? 2 : 0, enter.getInputs().size() - (loop ? 2 : 0)));
              else if (auto call = dyn_cast<func::CallOp>(op))
                exchange(call.getOperandsMutable().slice(
                    loop ? 3 : 1, call.getNumOperands() - (loop ? 3 : 1)));
              else if (auto match = dyn_cast<exec::MatchOp>(op))
                exchange(match.getCapturesMutable());
            });
            require(succeeded(verify(*actual)),
                    "same-type capture mutation malformed");
            ScopedDiagnosticHandler quiet(
                &context, [](Diagnostic &) { return success(); });
            require(failed(compareFinite(*original, *actual, policy)),
                    "reader accepted permuted captures");
          });
  }
  for (bool fallback : {false, true})
    cases.run(
        "two square maps retain actual required construction, fallback=" +
            std::to_string(fallback),
        [&] {
          auto source = parse(repeatedMapFixture()),
               original = executable(*source), frozen = sf::clone(*original);
          auto identities = target::physicalPlanOperations(*original);
          Withheld catalog({"numerical.map"});
          target::PhysicalPlanOptions options;
          if (!fallback)
            options.numericalPolicy.numericalExpressions =
                NumericalExpressionMode::VectorOnly;
          mathematical::RealizationWork measure;
          options.numericalWork = &measure;
          auto baseline =
              take(target::proposePhysical(*original, catalog, {}, options));
          auto selected = take(baseline.cloneSelectedSubject(*original));
          require(callsOf(*selected, "vector.mul").size() == 2 &&
                      callsOf(*selected, "numerical.map").empty(),
                  "one repeated square occurrence disappeared");
          take(target::validatePhysical(*original, baseline, catalog));
          auto spent = 100000 - measure.finiteExpressions;
          require(spent >= 2,
                  "finite construction failed to charge both occurrences");
          require(
              !fallback ||
                  (measure.discardedRecipeCopy <
                       mathematical::RealizationWork{}.discardedRecipeCopy &&
                   measure.discardedRecipeExpansion < 16 * 1024 * 1024),
              "catalog retry refunded discarded construction");
          for (bool oneShort : {false, true}) {
            mathematical::RealizationWork work;
            work.finiteExpressions = spent - unsigned(oneShort);
            options.numericalWork = &work;
            auto proposal =
                target::proposePhysical(*original, catalog, {}, options);
            if (oneShort) {
              refuses(std::move(proposal), "kernel-lowering");
            } else {
              auto plan = take(std::move(proposal));
              auto exact = take(plan.cloneSelectedSubject(*original));
              require(callsOf(*exact, "vector.mul").size() == 2 &&
                          work.finiteExpressions == 0,
                      "exact construction did not retain both occurrences");
              take(target::validatePhysical(*original, plan, catalog));
            }
            require(same(*original, *frozen) &&
                        target::physicalPlanOperations(*original) == identities,
                    "construction changed original identities");
          }
        });
  for (bool oneShort : {false, true})
    cases.run(llvm::Twine("aggregate construction discard transfer ") +
                  (oneShort ? "one-short" : "exact") + " aggregate reserve",
              [&] {
                mathematical::RealizationWork work;
                work.helperOperations = work.finiteExpressions = 1;
                work.helperSlots = work.polynomial = 1;
                mathematical::RecipeConstructionWork snapshot(work);
                work.discardedRecipeExpansion = 3;
                require(!snapshot.canDiscard(work),
                        "speculation omitted an expansion reserve");
                work.discardedRecipeExpansion = 4;
                require(snapshot.canDiscard(work),
                        "exact aggregate incoming reserve refused");
                work.helperOperations = work.finiteExpressions = 0;
                work.helperSlots = work.polynomial = 0;
                work.discardedRecipeExpansion = oneShort ? 3 : 4;
                require(snapshot.discard(work) == !oneShort,
                        "discard transfer misclassified aggregate capacity");
                require(work.discardedRecipeExpansion == (oneShort ? 3 : 0) &&
                            work.helperOperations == unsigned(!oneShort) &&
                            work.finiteExpressions == unsigned(!oneShort) &&
                            work.helperSlots == unsigned(!oneShort) &&
                            work.polynomial == unsigned(!oneShort),
                        "discard transfer partially settled or restored before "
                        "charging its complete bounded debit");
              });
  for (bool checking : {false, true})
    cases.run(
        "failed required preparation preserves cumulative allowance, "
        "checking=" +
            std::to_string(checking),
        [&] {
          auto source = parse(reductionFixture()),
               original = executable(*source), frozen = sf::clone(*original);
          mathematical::RealizationWork work;
          uint64_t copy = checking ? 1000000 : 1, bytes = 16 * 1024 * 1024;
          if (checking)
            work.requiredFiniteChecking = 1;
          ScopedDiagnosticHandler quiet(&context,
                                        [](Diagnostic &) { return success(); });
          for (unsigned attempt = 0; attempt != 2; ++attempt) {
            std::optional<CapacityCause> capacity;
            mathematical::VerificationDecision outcome;
            auto actual = protocol::prepareScopedFinite(
                *original, work, copy, bytes, capacity, {false, false, false},
                nullptr, nullptr, &outcome);
            require(!actual && same(*original, *frozen) &&
                        (checking
                             ? work.requiredFiniteChecking == 0 &&
                                   outcome.outcome ==
                                       mathematical::VerificationObservation::
                                           RequiredCapacity &&
                                   outcome.capacity.has_value()
                             : copy == 0 && capacity.has_value()),
                    "failed attempt replenished allowance or changed source");
          }
        });
  cases.run("vector map realization guards unused rows before arithmetic", [&] {
    auto source = parse(fixture()), original = executable(*source);
    MathematicalSelectionPolicy policy;
    policy.numericalExpressions = NumericalExpressionMode::VectorOnly;
    auto actual = prepareFinite(*original, policy);
    require(succeeded(compareFinite(*original, *actual, policy)),
            "vector baseline failed finite readback");
    auto function = sf::function(*actual, "through");
    auto instructions = sf::applications(function);
    std::vector<std::string> prefix;
    for (auto instruction : ArrayRef(instructions).take_front(7))
      prefix.push_back(sf::contract(instruction).str());
    require(prefix == std::vector<std::string>{"vector.length", "vector.length",
                                               "vector.length", "index.equal",
                                               "control.require", "index.equal",
                                               "control.require"},
            "arithmetic preceded complete ordered shape checks");
    auto lengths = sf::applications(function, "vector.length");
    require(lengths.size() == 3 &&
                lengths[2].getInputs()[0] == function.getArgument(3),
            "unused row lost its extent check");
    for (bool reorder : {false, true}) {
      auto changed = sf::clone(*actual);
      auto checks =
          sf::applications(sf::function(*changed, "through"), "vector.length");
      if (reorder)
        exchangeLengths(checks[1], checks[2]);
      else
        checks[2]->setOperand(1, checks[0].getInputs()[0]);
      require(succeeded(verify(*changed)), "shape mutation malformed");
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      require(failed(compareFinite(*original, *changed, policy)),
              "finite reader accepted changed ordered checks");
    }
  });
  return cases.result();
}
