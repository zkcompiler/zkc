#include "../lib/Transforms/MathematicalSupport.h"
#include "mlir/IR/OperationSupport.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "support/ScopedFixture.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace sf = zkc::test::scopedFinite;
namespace sc = zkc::test::scopedComputation;
namespace {
const std::string declarations = R"mlir(
"runtime.binding"() {sym_name="sum",contract="vector.sum",arguments=["koala-bear"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"koala-bear">) -> !exec.outcome<(!algebra.field<"koala-bear">)>} : ()->()
"runtime.binding"() {sym_name="length_alias",contract="vector.length",arguments=["koala-bear"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"koala-bear">) -> !exec.outcome<(ui64)>} : ()->()
"runtime.binding"() {sym_name="constant",contract="field.constant",arguments=["koala-bear"],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(!algebra.field<"koala-bear">)>} : ()->()
"data.domain"() ({^entry(%a:!V,%b:!V,%c:!V):
%as = "data.domain_elements"(%a) : (!V)->!data.domain<!F>
%bs = "data.domain_elements"(%b) : (!V)->!data.domain<!F>
%cs = "data.domain_elements"(%c) : (!V)->!data.domain<!F>
%zip = "data.domain_zip"(%as,%bs,%cs) : (!data.domain<!F>,!data.domain<!F>,!data.domain<!F>)->!data.domain<!F,!F,!F>
"data.domain_yield"(%zip) : (!data.domain<!F,!F,!F>)->()
}) {sym_name="rows",sym_visibility="private",function_type=(!V,!V,!V)->!data.domain<!F,!F,!F>} : ()->()
func.func private @formula(%a:!F,%b:!F,%unused:!F,%s:!F)->!F {
%dead = algebra.field_add %s,%s : (!F,!F)->!F
%p = algebra.field_multiply %a,%b : (!F,!F)->!F
return %p : !F
}
func.func private @row(%scope:!runtime.scope,%a:!F,%b:!F,%c:!F,%xs:!V,%ys:!V,%zs:!V,%s:!F)->!exec.outcome<(!F)> attributes {no_inline,runtime.origin=["row",[]]} {
%attempt = "exec.compute"(%scope,%a,%b,%c,%s) {callee=@formula,site="product"} : (!runtime.scope,!F,!F,!F,!F)->!exec.outcome<(!F)>
"exec.dispatch"(%attempt)[^ok,^failed] : (!exec.outcome<(!F)>)->()
^ok(%p:!F):
%result = "exec.returned"(%p) : (!F)->!exec.outcome<(!F)>
func.return %result : !exec.outcome<(!F)>
^failed(%stop:!exec.stop):
%failure = "exec.failed"(%stop) : (!exec.stop)->!exec.outcome<(!F)>
func.return %failure : !exec.outcome<(!F)>
}
)mlir";

std::string call(StringRef callee, StringRef site, StringRef inputs,
                 StringRef types, StringRef output, StringRef result) {
  auto text = scopedApply(callee, site, inputs, types, output, result);
  text = replaceText(text, "\"exec.apply\"", "\"func.call\"");
  text = replaceText(text, "binding=", "callee=");
  text = replaceText(text, "site=", "runtime.site=");
  return replaceText(text, ",parameters=[]", "");
}
std::string functionText(StringRef name, StringRef arguments, StringRef type,
                         StringRef body, StringRef origin = {}) {
  auto outcome = "!exec.outcome<(" + type.str() + ")>";
  return "func.func @" + name.str() + "(%scope:!runtime.scope," +
         arguments.str() + ")->" + outcome +
         " attributes {no_inline,runtime.origin=[\"" +
         (origin.empty() ? name.str() : origin.str()) + "\",[]]} {\n" +
         body.str() +
         (body.contains("^failed")
              ? "\n^failed(%reason:!exec.stop):\n%failure = "
                "\"exec.failed\"(%reason) : (!exec.stop)->" +
                    outcome + "\nfunc.return %failure : " + outcome
              : "") +
         "\n}\n";
}
std::string collection(StringRef site = "map", StringRef output = "%v") {
  auto text =
      scopedApply("unused", site, "%a,%b,%c,%s", "!V,!V,!V,!F", output, "!V");
  text = replaceText(text, "\"exec.apply\"", "\"exec.collect\"");
  return replaceText(
      replaceText(text, "binding=@unused", "domain=@rows,body=@row"),
      ",parameters=[]", "");
}
std::string fixture() {
  auto reducer =
      functionText("reduce", "%v:!V", "!F",
                   scopedApply("sum", "sum", "%v", "!V", "%r", "!F") +
                       scopedReturn("%r", "!F"));
  auto result =
      "!F = !algebra.field<\"koala-bear\">\n!V = "
      "!algebra.field_vector<\"koala-bear\">\n" +
      scopedFixture(declarations + reducer, "%a:!V,%b:!V,%c:!V,%s:!F",
                    "%a,%b,%c,%s", "!V,!V,!V,!F", "!F",
                    replaceText(collection(), ",parameters=[]", "") +
                        call("reduce", "reduce", "%v", "!V", "%r", "!F") +
                        scopedReturn("%r", "!F"),
                    4);
  return replaceText(replaceText(result, "@Work", "@work"), "\"Work\"",
                     "\"work\"");
}
std::string edit(StringRef source, StringRef from, StringRef to) {
  auto text = source.str();
  auto position = text.find(from.str());
  require(position != std::string::npos, "missing fixture fragment " + from);
  text.replace(position, from.size(), to.str());
  return text;
}
func::FuncOp function(ModuleOp module, StringRef name = "work") {
  return sf::function(module, name);
}
exec::ApplyOp nth(ModuleOp module, StringRef contract, unsigned index = 0,
                  StringRef name = "work") {
  auto values = sf::executionApplications(module, name, contract);
  require(index < values.size(), "missing invocation " + contract);
  return values[index];
}
unsigned count(ModuleOp module, StringRef contract, StringRef name = "work") {
  return sf::executionApplications(module, name, contract).size();
}
bool same(Operation *left, Operation *right) {
  return OperationEquivalence::isEquivalentTo(
      left, right, OperationEquivalence::IgnoreLocations);
}
OwningOpRef<ModuleOp>
expand(ModuleOp source,
       std::vector<protocol::AlgorithmOrigin> *origins = nullptr) {
  auto result = protocol::expandScopedHelpers(source, origins);
  require(bool(result), "scoped helper expansion refused");
  return result;
}
OwningOpRef<ModuleOp> prepare(ModuleOp source,
                              MathematicalSelectionPolicy policy = {true, true,
                                                                    false},
                              const mathematical::MathematicalRecipes &recipes =
                                  mathematical::mathematicalRecipes()) {
  mathematical::RealizationWork work;
  uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
  std::optional<CapacityCause> capacity;
  return protocol::prepareScopedFinite(source, work, copy, bytes, capacity,
                                       policy, nullptr, nullptr, nullptr,
                                       recipes);
}
LogicalResult compare(ModuleOp before, ModuleOp after,
                      MathematicalSelectionPolicy policy = {true, true,
                                                            false}) {
  mathematical::RealizationWork work;
  return protocol::verifyScopedFinitePreparation(before, after, work, policy);
}
void run(ModuleOp module, std::unique_ptr<Pass> pass) {
  PassManager manager(module.getContext());
  auto name = pass->getName().str();
  manager.addPass(std::move(pass));
  require(succeeded(manager.run(module)), "pipeline refused: " + name);
}
// Relocate a zero-payload invocation with its complete dispatch continuation.
// Leaving the old dispatch behind would test malformed CFG, not ordered work.
void moveAfter(exec::ApplyOp operation, exec::ApplyOp after) {
  require(operation.getOutcome().getType().getPayload().empty(),
          "only zero-result invocation can be moved without SSA rebinding");
  auto inputs = llvm::to_vector(operation->getOperands());
  NamedAttrList attributes(operation->getAttrs());
  auto helper = operation->getParentOfType<func::FuncOp>();
  auto stop = cast<exec::DispatchOp>(operation->getNextNode()).getStopped();
  sc::omit(operation);
  auto *block = cast<exec::DispatchOp>(after->getNextNode()).getReturned();
  IRRewriter rewriter(helper.getContext());
  auto *tail = rewriter.splitBlock(block, block->begin());
  OpBuilder builder(helper.getContext());
  builder.setInsertionPointToEnd(block);
  exec::ScopedExecutionBuilder control(builder, helper);
  control.invoke("exec.apply", {}, inputs, attributes.getAttrs(), stop);
  rewriter.mergeBlocks(tail, builder.getInsertionBlock());
}

std::string withDefinitions(StringRef text, StringRef definitions) {
  return edit(text, "\"protocol.func\"",
              definitions.str() + "\"protocol.func\"");
}
std::string wrapper(StringRef name, StringRef callee, StringRef site,
                    unsigned repeated = 1, StringRef origin = {}) {
  std::string body;
  for (unsigned i = 0; i < repeated; ++i)
    body += call(callee,
                 repeated == 1 ? site.str() : site.str() + std::to_string(i),
                 "%a,%b,%c,%s", "!V,!V,!V,!F", "%r" + std::to_string(i), "!F");
  return functionText(
      name, "%a:!V,%b:!V,%c:!V,%s:!F", "!F",
      body + scopedReturn("%r" + std::to_string(repeated - 1), "!F"), origin);
}
std::string chain(unsigned wrappers, unsigned repeated, unsigned width,
                  bool mathematicalRow = true) {
  std::string definitions;
  for (unsigned i = 0; i < wrappers; ++i) {
    auto name = (width ? std::string(width, 'x') : "layer") + std::to_string(i);
    definitions += wrapper(
        name,
        i ? (width ? std::string(width, 'x') : "layer") + std::to_string(i - 1)
          : "work",
        "call", i + 1 == wrappers ? repeated : 1,
        width ? std::string(width, 'x') + std::to_string(i) : name);
  }
  auto source = fixture();
  if (!mathematicalRow) {
    auto original =
        declarations.substr(declarations.find("func.func private @row"));
    auto row =
        functionText("row", "%a:!F,%b:!F,%c:!F,%xs:!V,%ys:!V,%zs:!V,%s:!F",
                     "!F", scopedReturn("%a", "!F"));
    source = edit(source, original,
                  edit(row, "func.func @row", "func.func private @row"));
  }
  return withDefinitions(source, definitions);
}
func::FuncOp scopedFunction(ModuleOp module, StringRef name, TypeRange inputs,
                            TypeRange outputs) {
  OpBuilder builder(module.getContext());
  builder.setInsertionPointToStart(
      &module.getBody()->front().getRegion(0).front());
  SmallVector<Type> arguments{runtime::ScopeType::get(module.getContext())};
  llvm::append_range(arguments, inputs);
  auto helper = func::FuncOp::create(
      builder, module.getLoc(), name,
      builder.getFunctionType(
          arguments, exec::OutcomeType::get(module.getContext(),
                                            llvm::to_vector(outputs))));
  helper.setNoInline(true);
  helper->setAttr("runtime.origin",
                  builder.getArrayAttr(
                      {builder.getStringAttr(name), builder.getArrayAttr({})}));
  helper.addEntryBlock();
  return helper;
}
SmallVector<Value> invokeHelper(exec::ScopedExecutionBuilder &control,
                                OpBuilder &builder, StringRef callee,
                                StringRef site, ValueRange inputs,
                                TypeRange outputs) {
  return control.invoke(
      "func.call", outputs, control.scoped(inputs),
      {builder.getNamedAttr(
           "callee", FlatSymbolRefAttr::get(builder.getContext(), callee)),
       builder.getNamedAttr("runtime.site", builder.getStringAttr(site))});
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry, MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  Cases cases;
  auto parse = [&](StringRef text) {
    auto result = parseSourceString<ModuleOp>(text, &context);
    require(bool(result), "fixture refused");
    return result;
  };
  auto refuses = [&](llvm::function_ref<LogicalResult()> check) {
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    require(failed(check()), "independent reader accepted mutation");
  };
  auto source = parse(fixture());
  auto retained = expand(*source);
  auto fused = prepare(*retained);
  require(bool(fused), "collection/sum preparation refused");
  cases.run("retained collection and native sum through reducer wrapper", [&] {
    unsigned collections = 0;
    function(*retained).walk([&](exec::CollectOp) { ++collections; });
    require(collections == 1 && count(*retained, "vector.sum") == 1,
            "helper expansion lost the preparation boundary");
    require(succeeded(protocol::verifyScopedHelperExpansionPreserved(
                *source, *retained)),
            "independent helper checker refused");
  });
  cases.run("multiply sum with unused row and scalar", [&] {
    auto dot = nth(*fused, "vector.dot");
    require(count(*fused, "vector.dot") == 1 &&
                count(*fused, "vector.length") == 3 &&
                count(*fused, "control.require") == 2 &&
                dot.getInputs()[0] == function(*fused).getArgument(1) &&
                dot.getInputs()[1] == function(*fused).getArgument(2) &&
                nth(*fused, "vector.length", 2).getInputs()[0] ==
                    function(*fused).getArgument(3),
            "selected ports, guards or unused row changed");
    auto closure =
        take(protocol::readSourceExecutionClosure(&fused->getBody()->front()));
    const auto &steps = closure.bodies.at("work");
    bool reachedDot = false;
    for (const auto &step : steps)
      if (auto apply = dyn_cast<exec::ApplyOp>(step.operation)) {
        if (sf::contract(apply) == "vector.dot")
          reachedDot = true;
        if (sf::contract(apply) == "control.require")
          require(!reachedDot, "shape guard follows reduction");
      }
    require(succeeded(compare(*retained, *fused)),
            "fusion correspondence refused");
  });
  for (bool present : {true, false})
    cases.run(
        present ? "installed contraction preserves selected data ports"
                : "withheld contraction preserves all other recipes",
        [&] {
          const auto &installed = mathematical::mathematicalRecipes();
          auto *dot =
              installed.reduction(MathematicalIdentity::FieldAdd,
                                  MathematicalIdentity::FieldMultiply,
                                  mathematical::ReductionForm::Contraction);
          require(dot, "missing contraction recipe");
          SmallVector<mathematical::ReductionRecipe> reductions;
          for (const auto &recipe : installed.reductions)
            if (present || &recipe != dot)
              reductions.push_back(recipe);
          mathematical::MathematicalRecipes recipes{installed.lanes,
                                                    reductions};
          require(reductions.size() + unsigned(!present) ==
                          installed.reductions.size() &&
                      recipes.lane(MathematicalIdentity::FieldAdd) &&
                      recipes.lane(MathematicalIdentity::FieldMultiply),
                  "inventory control changed other recipes");
          auto candidate = prepare(*retained, {true, true, false}, recipes);
          require(bool(candidate) && succeeded(compare(*retained, *candidate)),
                  "inventory preparation refused");
          require(count(*candidate, "vector.dot") == unsigned(present),
                  "contraction ignored inventory");
          if (present)
            require(same(*candidate, *fused),
                    "equivalent inventory changed candidate");
          else
            require(count(*candidate, "control.require") == 2 &&
                        count(*candidate, "vector.length") == 3 &&
                        count(*candidate, "numerical.sum") +
                                count(*candidate, "vector.sum") ==
                            1,
                    "fallback lost shape admission or summation");
        });
  for (bool scalar : {false, true})
    cases.run(
        scalar ? "unused scalar suffix remains checked"
               : "unused vector suffix remains checked",
        [&] {
          auto original = sf::clone(*retained);
          auto helper = function(*original);
          OpBuilder builder(
              &original->getBody()->front().getRegion(0).front(),
              original->getBody()->front().getRegion(0).front().begin());
          runtime::BindingOp::create(builder, original->getLoc(), "tail",
                                     scalar ? "field.add" : "vector.add",
                                     builder.getStrArrayAttr({"koala-bear"}),
                                     "");
          Value left = helper.getArgument(scalar ? 4 : 1),
                right = helper.getArgument(scalar ? 4 : 2);
          sc::appendApply(helper, "tail", {left, right}, {left.getType()},
                          "tail");
          auto candidate = prepare(*original);
          require(bool(candidate) && count(*candidate, "vector.dot") == 1 &&
                      succeeded(compare(*original, *candidate)),
                  "suffix prevented checked fusion");
          auto tail = nth(*candidate, scalar ? "field.add" : "vector.add");
          require(sc::payload(tail)[0].use_empty(), "suffix unexpectedly used");
          tail->setOperand(
              2, scalar ? sc::payload(nth(*candidate, "vector.dot"))[0]
                        : tail.getInputs()[0]);
          require(succeeded(verify(*candidate)), "suffix mutation malformed");
          refuses([&] { return compare(*original, *candidate); });
        });
  auto mutation = [&](StringRef label,
                      llvm::function_ref<void(ModuleOp)> change) {
    cases.run(label, [&] {
      auto candidate = sf::clone(*fused);
      change(*candidate);
      require(succeeded(zkc::admitStage(*candidate)),
              "mutation must remain admitted");
      refuses([&] { return compare(*retained, *candidate); });
    });
  };
  mutation("drop a shape guard",
           [&](ModuleOp m) { sc::omit(nth(m, "control.require")); });
  mutation("move guard after contraction", [&](ModuleOp m) {
    moveAfter(nth(m, "control.require"), nth(m, "vector.dot"));
  });
  mutation("reverse shape guards", [&](ModuleOp m) {
    moveAfter(nth(m, "control.require"), nth(m, "control.require", 1));
  });
  mutation("replace ignored row", [&](ModuleOp m) {
    nth(m, "vector.length", 2)->setOperand(1, function(m).getArgument(1));
  });
  mutation("replace contraction operand", [&](ModuleOp m) {
    nth(m, "vector.dot")->setOperand(2, function(m).getArgument(1));
  });
  mutation("replace returned scalar", [&](ModuleOp m) {
    sc::returned(function(m))->setOperand(0, function(m).getArgument(4));
  });
  mutation("replace guard occurrence",
           [&](ModuleOp m) { nth(m, "control.require").setSite("forged"); });
  mutation("replace contraction occurrence",
           [&](ModuleOp m) { nth(m, "vector.dot").setSite("forged"); });
  cases.run("generated invocation may use an exactly equivalent binding", [&] {
    auto candidate = sf::clone(*fused);
    nth(*candidate, "vector.length").setBinding("length_alias");
    require(succeeded(zkc::admitStage(*candidate)) &&
                succeeded(compare(*retained, *candidate)),
            "equivalent resolved contract changed generated semantics");
  });
  mutation("replace original declaration", [&](ModuleOp m) {
    auto helper = function(m, "formula");
    helper.front().front().setOperand(1, helper.getArgument(0));
  });
  cases.run("scoped definition order does not alter resolved bodies", [&] {
    auto candidate = sf::clone(*fused);
    function(*candidate, "reduce")->moveAfter(function(*candidate));
    require(succeeded(zkc::admitStage(*candidate)) &&
                succeeded(compare(*retained, *candidate)),
            "scoped symbol-table order changed correspondence");
  });
  mutation("reorder retained mathematical declarations", [&](ModuleOp m) {
    function(m, "formula")
        ->moveBefore(&m.getBody()->front().getRegion(0).front().front());
  });
  mutation("add unrelated declaration", [&](ModuleOp m) {
    OpBuilder builder(&context);
    builder.setInsertionPointToStart(
        &m.getBody()->front().getRegion(0).front());
    runtime::BindingOp::create(builder, m.getLoc(), "extra", "control.require",
                               builder.getArrayAttr({}), "");
  });
  cases.run("retained collection capture mutation", [&] {
    auto candidate = sf::clone(*retained);
    function(*candidate).walk([](exec::CollectOp call) {
      call->setOperand(2, call->getOperand(1));
    });
    require(succeeded(verify(*candidate)), "capture mutation malformed");
    refuses([&] {
      return protocol::verifyScopedHelperExpansionPreserved(*source,
                                                            *candidate);
    });
  });
  cases.run("authored sites cannot collide with substituted helper paths", [&] {
    auto original = parse(fixture());
    uint64_t bytes = 16 * 1024 * 1024;
    auto generated =
        take(protocol::algorithmSite({{"reduce", "reduce"}}, "sum", bytes));
    function(*original).walk(
        [&](exec::CollectOp op) { op.setSite(generated); });
    require(succeeded(zkc::admitStage(*original)),
            "collision source must be admitted");
    auto candidate = expand(*original);
    require(succeeded(protocol::verifyScopedHelperExpansionPreserved(
                *original, *candidate)),
            "authored and derived site namespaces collided");
  });
  cases.run("unexpanded reducer call is not a direct sum consumer", [&] {
    auto candidate = prepare(*source);
    require(bool(candidate) && count(*candidate, "vector.dot") == 0 &&
                succeeded(compare(*source, *candidate)),
            "source adjacency prerequisite ignored");
  });
  cases.run("repeated checked expansion retains collection requests", [&] {
    auto again = expand(*retained);
    require(succeeded(protocol::verifyScopedHelperExpansionPreserved(*retained,
                                                                     *again)),
            "second expansion refused");
    unsigned collections = 0;
    function(*again).walk([&](exec::CollectOp) { ++collections; });
    require(collections == 1, "expansion consumed the pending choice");
  });

  auto selection = [&](StringRef label, StringRef text, bool selected) {
    cases.run(label, [&] {
      auto original = parse(text);
      auto prepared = expand(*original);
      auto candidate = prepare(*prepared);
      require(bool(candidate) && succeeded(compare(*prepared, *candidate)),
              "selection correspondence failed");
      require(count(*candidate, "vector.dot") == unsigned(selected),
              "wrong contraction selection");
    });
  };
  selection("square",
            edit(fixture(), "field_multiply %a,%b", "field_multiply %a,%a"),
            true);
  selection("addition nonmatch", edit(fixture(), "field_multiply", "field_add"),
            false);
  selection("scalar factor nonmatch",
            edit(fixture(), "field_multiply %a,%b", "field_multiply %a,%s"),
            false);
  selection("direct native sum",
            edit(fixture(), call("reduce", "reduce", "%v", "!V", "%r", "!F"),
                 scopedApply("sum", "reduce", "%v", "!V", "%r", "!F")),
            true);
  selection("intervening ordered work",
            edit(fixture(), call("reduce", "reduce", "%v", "!V", "%r", "!F"),
                 scopedApply("constant", "intervening", "", "", "%ignored",
                             "!F", "[#algebra.literal<!F, 1 : ui31>]") +
                     call("reduce", "reduce", "%v", "!V", "%r", "!F")),
            false);
  selection(
      "additional collection use",
      edit(fixture(), call("reduce", "reduce", "%v", "!V", "%r", "!F"),
           scopedApply("sum", "additional", "%v", "!V", "%ignored", "!F") +
               call("reduce", "reduce", "%v", "!V", "%r", "!F")),
      false);
  selection("reducer spelling is not a contract",
            edit(fixture(), scopedApply("sum", "sum", "%v", "!V", "%r", "!F"),
                 scopedApply("constant", "sum", "", "", "%r", "!F",
                             "[#algebra.literal<!F, 1 : ui31>]")),
            false);
  cases.run("ordinary preparation retains the original scalar formula", [&] {
    auto candidate = sf::clone(*source);
    run(*candidate, protocol::createPrepareProtocolPass(false));
    require(same(function(*source, "formula"), function(*candidate, "formula")),
            "preparation replaced immutable scalar mathematics");
  });

  cases.run(
      "numerical lowering preserves every pending finite dependency", [&] {
        auto original = parse(fixture());
        run(*original, protocol::createProjectProtocolPass(false));
        run(*original, protocol::createLowerMathPass());
        auto candidate = sf::clone(*original);
        run(*candidate, computation::createRealizeComputationsPass());
        require(succeeded(mathematical::verifyNumericalLowering(*original,
                                                                *candidate)),
                "mixed finite/numerical context correspondence refused");
        for (StringRef change :
             {"domain", "formula", "captures", "site", "extra"}) {
          auto mutation = sf::clone(*candidate);
          if (change == "formula") {
            auto helper = function(*mutation, "formula");
            helper.front().back().setOperand(0, helper.getArgument(0));
          } else if (change == "domain") {
            auto domain =
                SymbolTable(&mutation->getBody()->front()).lookup("rows");
            auto &entry = domain->getRegion(0).front();
            entry.front().setOperand(0, entry.getArgument(1));
          } else if (change == "extra") {
            auto helper = function(*mutation, "formula");
            OpBuilder builder(helper);
            auto *extra = builder.clone(*helper);
            SymbolTable::setSymbolName(extra, builder.getStringAttr("extra"));
          } else {
            exec::CollectOp collection;
            function(*mutation).walk(
                [&](exec::CollectOp op) { collection = op; });
            require(bool(collection), "pending collection lost");
            if (change == "site")
              collection.setSite("forged");
            else
              collection->setOperand(2, collection->getOperand(1));
          }
          require(succeeded(verify(*mutation)),
                  "mixed context mutation malformed: " + change);
          refuses([&] {
            return mathematical::verifyNumericalLowering(*original, *mutation);
          });
        }
      });
  const auto workBody = collection() +
                        call("reduce", "reduce", "%v", "!V", "%r", "!F") +
                        scopedReturn("%r", "!F");
  auto noCalls = edit(fixture(), workBody, scopedReturn("%s", "!F"));
  noCalls = edit(noCalls,
                 "^failed(%reason:!exec.stop):\n%failure=\"exec.failed\"(%"
                 "reason) : (!exec.stop)->!exec.outcome<(!F)>\nfunc.return "
                 "%failure : !exec.outcome<(!F)>",
                 "");
  for (bool withOrigins : {false, true})
    cases.run(
        withOrigins ? "call-free expansion publishes checked origins"
                    : "call-free expansion can be checked again",
        [&] {
          auto original = parse(noCalls);
          std::vector<protocol::AlgorithmOrigin> origins;
          auto candidate = expand(*original, withOrigins ? &origins : nullptr);
          require(succeeded(protocol::verifyScopedHelperExpansionPreserved(
                      *original, *candidate)),
                  "call-free expansion correspondence failed");
          auto again = expand(*candidate);
          require(succeeded(protocol::verifyScopedHelperExpansionPreserved(
                      *candidate, *again)),
                  "second call-free expansion failed independent checking");
          if (withOrigins)
            require(!origins.empty(),
                    "dormant reducer invocation lost its origin");
        });
  cases.run("checked expansion preserves dormant scalar formulas", [&] {
    auto original = parse(noCalls);
    auto candidate = expand(*original);
    auto formula = function(*candidate, "formula");
    formula.front().back().setOperand(0, formula.getArgument(0));
    require(succeeded(verify(*candidate)),
            "dormant formula mutation malformed");
    refuses([&] {
      return protocol::verifyScopedHelperExpansionPreserved(*original,
                                                            *candidate);
    });
  });
  auto deepFormula = [&](bool live, unsigned size) {
    std::string operations;
    for (unsigned i = 0; i < size; ++i)
      operations += "%d" + std::to_string(i) + " = algebra.field_add " +
                    (live && i ? "%d" + std::to_string(i - 1) : "%a") +
                    ",%a : (!F,!F)->!F\n";
    auto text = edit(fixture(), "%dead =", operations + "%dead =");
    return live ? edit(text, "return %p : !F",
                       "return %d" + std::to_string(size - 1) + " : !F")
                : text;
  };
  cases.run("live scalar chain remains ordinary checked computation", [&] {
    auto original = parse(deepFormula(true, 1024));
    auto expanded = expand(*original);
    auto candidate = prepare(*expanded);
    require(bool(candidate) && count(*candidate, "vector.dot") == 0 &&
                same(function(*original, "formula"),
                     function(*candidate, "formula")) &&
                succeeded(compare(*expanded, *candidate)),
            "general callback depth was erased or misrecognized as a product");
  });
  cases.run("changed deep formula cannot justify a stale contraction", [&] {
    auto original = parse(deepFormula(true, 1024));
    auto expanded = expand(*original);
    auto candidate = sf::clone(*fused);
    auto old = function(*candidate, "formula");
    OpBuilder builder(old);
    builder.clone(*function(*original, "formula"));
    old.erase();
    require(succeeded(verify(*candidate)),
            "stale contraction fixture malformed");
    refuses([&] { return compare(*expanded, *candidate); });
  });
  auto canonical = [&](StringRef text) {
    auto original = parse(text);
    auto expanded = expand(*original);
    auto repeated = expand(*original);
    auto direct = prepare(*expanded), repeatedCandidate = prepare(*repeated);
    require(bool(direct) && bool(repeatedCandidate) &&
                same(*direct, *repeatedCandidate),
            "fresh checked expansion changed operations or sites");
    require(succeeded(compare(*expanded, *direct)),
            "canonical preparation failed correspondence");
  };
  cases.run("canonical preparation from the same immutable source",
            [&] { canonical(fixture()); });
  auto longText = withDefinitions(
      edit(fixture(), "runtime.origin=[\"work\",[]]",
           "runtime.origin=[\"" + std::string(100, 'w') + "\",[]]"),
      wrapper("outer", "work", std::string(80, 'c')));
  longText = replaceText(longText, "@work", "@" + std::string(100, 'w'));
  cases.run("long hashed occurrence identity", [&] { canonical(longText); });
  cases.run("hashed expanded collection preserves the full original path", [&] {
    auto original = parse(longText);
    std::vector<protocol::AlgorithmOrigin> origins;
    auto expanded = expand(*original, &origins);
    exec::CollectOp collect;
    function(*expanded, "outer").walk([&](exec::CollectOp op) {
      collect = op;
    });
    require(bool(collect) && collect.getSite().starts_with("lc_h_"),
            "long collection site was not hashed");
    require(llvm::any_of(origins,
                         [&](const auto &origin) {
                           return origin.function == "outer" &&
                                  origin.site == collect.getSite() &&
                                  origin.originalSite == "map" &&
                                  origin.path == protocol::Assignments{
                                                     {std::string(80, 'c'),
                                                      std::string(100, 'w')}};
                         }),
            "original collection occurrence was not recovered independently");
    auto candidate = prepare(*expanded);
    require(bool(candidate) && count(*candidate, "vector.dot", "outer") == 1 &&
                succeeded(compare(*expanded, *candidate)),
            "hashed collection failed checked reduction");
    nth(*candidate, "control.require", 0, "outer").setSite("forged");
    require(succeeded(verify(*candidate)), "long-origin mutation malformed");
    refuses([&] { return compare(*expanded, *candidate); });
  });
  selection("well-typed unused equality remains a general callback",
            edit(fixture(), "%dead =",
                 "%equal = algebra.field_equal %a,%b : (!F,!F)->i1\n%dead ="),
            false);
  cases.run("ordinary preparation checks generated guard occurrences", [&] {
    MathematicalSelectionPolicy policy{false, false, false};
    auto candidate = prepare(*retained, policy);
    require(bool(candidate) &&
                succeeded(compare(*retained, *candidate, policy)),
            "ordinary correspondence refused");
    nth(*candidate, "control.require").setSite("changed");
    require(succeeded(verify(*candidate)), "ordinary guard mutation malformed");
    refuses([&] { return compare(*retained, *candidate, policy); });
  });
  cases.run("same vector ABI does not imply a collection product", [&] {
    auto text = withDefinitions(
        fixture(), "func.func private @vectors(%a:!V,%b:!V,%c:!V,%s:!F)->!V { "
                   "return %a : !V }\n");
    text = edit(edit(text, "\"exec.collect\"", "\"exec.compute\""),
                "domain=@rows,body=@row", "callee=@vectors");
    auto original = parse(text);
    auto expanded = expand(*original);
    auto candidate = prepare(*expanded);
    require(bool(candidate) && count(*candidate, "vector.dot") == 0 &&
                succeeded(compare(*expanded, *candidate)),
            "arbitrary computation acquired collection semantics");
  });
  const auto emptyText = withDefinitions(fixture(), R"mlir(
"runtime.binding"() {sym_name="index",contract="index.constant",arguments=[],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(ui64)>} : ()->()
"runtime.binding"() {sym_name="fill",contract="vector.fill",arguments=["koala-bear"],implementation="",function_type=(!runtime.scope, !algebra.field<"koala-bear">, ui64) -> !exec.outcome<(!algebra.field_vector<"koala-bear">)>} : ()->()
)mlir" + functionText("empty", "%s:!F", "!F",
                      scopedApply("index", "zero", "", "", "%zero", "ui64",
                                  "[0 : ui64]") +
                          scopedApply("fill", "first", "%s,%zero", "!F,ui64",
                                      "%a", "!V") +
                          scopedApply("fill", "second", "%s,%zero", "!F,ui64",
                                      "%b", "!V") +
                          call("work", "reduce", "%a,%b,%a,%s", "!V,!V,!V,!F",
                               "%r", "!F") +
                          scopedReturn("%r", "!F")));
  cases.run("empty rows preserve evaluations and every shape guard", [&] {
    auto original = parse(emptyText);
    auto expanded = expand(*original);
    auto candidate = prepare(*expanded);
    require(bool(candidate) && count(*candidate, "vector.fill", "empty") == 2 &&
                count(*candidate, "vector.length", "empty") == 3 &&
                count(*candidate, "control.require", "empty") == 2 &&
                count(*candidate, "vector.dot", "empty") == 1 &&
                succeeded(compare(*expanded, *candidate)),
            "empty-row shortcut removed ordered work");
  });
  for (bool simplify : {false, true})
    cases.run(
        simplify ? "fused projected pipeline"
                 : "fusion independent of simplification",
        [&] {
          auto candidate = parse(fixture());
          run(*candidate, protocol::createProjectProtocolPass(
                              simplify, {true, true, false}));
          run(*candidate, protocol::createLowerMathPass());
          run(*candidate, computation::createRealizeComputationsPass());
          unsigned collections = 0;
          candidate->walk([&](exec::CollectOp) { ++collections; });
          require(collections != 0,
                  "pending collection consumed before physical selection");
          run(*candidate,
              protocol::createSelectPhysicalPass({}, false, false, nullptr, {},
                                                 {true, true, false}));
          require(sf::applications(function(*candidate), "vector.dot").size() ==
                      1,
                  "contraction absent from scoped physical output");
          bool pending = false;
          candidate->walk([&](Operation *op) {
            pending |= isa<exec::CollectOp, exec::ComputeOp, exec::FoldOp>(op);
            auto dialect = op->getName().getDialectNamespace();
            require(dialect != "local" && dialect != "plan" &&
                        dialect != "kernel",
                    "retired owner in physical output");
          });
          require(!pending,
                  "pending finite computation escaped physical selection");
        });

  cases.run("row positions after a scalar capture remain distinct", [&] {
    auto text = fixture();
    auto begin = text.find("\"data.domain\"");
    auto end = text.find("func.func private @formula", begin);
    require(begin != std::string::npos && end != std::string::npos,
            "domain fixture missing");
    text.replace(begin, end - begin, R"mlir(
"data.domain"() ({^entry(%a:!F,%b:!V,%c:!V):
%bs = "data.domain_elements"(%b) : (!V)->!data.domain<!F>
%cs = "data.domain_elements"(%c) : (!V)->!data.domain<!F>
%zip = "data.domain_zip"(%bs,%cs) : (!data.domain<!F>,!data.domain<!F>)->!data.domain<!F,!F>
"data.domain_yield"(%zip) : (!data.domain<!F,!F>)->()
}) {sym_name="rows",sym_visibility="private",function_type=(!F,!V,!V)->!data.domain<!F,!F>} : ()->()
)mlir");
    text = edit(text, "field_multiply %a,%b", "field_multiply %b,%unused");
    text = edit(
        text,
        "%scope:!runtime.scope,%a:!F,%b:!F,%c:!F,%xs:!V,%ys:!V,%zs:!V,%s:!F",
        "%scope:!runtime.scope,%b:!F,%c:!F,%a:!F,%ys:!V,%zs:!V,%s:!F");
    text =
        replaceText(text, "%a:!V,%b:!V,%c:!V,%s:!F", "%a:!F,%b:!V,%c:!V,%s:!F");
    text = replaceText(text, "!V,!V,!V,!F", "!F,!V,!V,!F");
    auto original = parse(text);
    auto expanded = expand(*original);
    auto candidate = prepare(*expanded);
    require(bool(candidate) && count(*candidate, "vector.length") == 2 &&
                count(*candidate, "control.require") == 1 &&
                nth(*candidate, "vector.dot").getInputs()[0] ==
                    function(*candidate).getArgument(2) &&
                nth(*candidate, "vector.dot").getInputs()[1] ==
                    function(*candidate).getArgument(3) &&
                succeeded(compare(*expanded, *candidate)),
            "scalar capture shifted row identities");
  });
  cases.run("collection contraction remains within branches and loops", [&] {
    auto original = parse(fixture());
    auto field = function(*original).getArgument(4).getType();
    auto vector = function(*original).getArgument(1).getType();
    auto boolean = IntegerType::get(&context, 1);
    auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
    for (StringRef name : {"branches", "loop", "cross"}) {
      bool loop = name == "loop", cross = name == "cross";
      SmallVector<Type> inputs{loop ? index : boolean};
      if (loop)
        inputs.push_back(index);
      llvm::append_range(inputs, TypeRange{vector, vector, vector, field});
      auto root = scopedFunction(*original, name, inputs, {field});
      OpBuilder builder(&root.front(), root.front().end());
      exec::ScopedExecutionBuilder control(builder, root);
      SmallVector<Value> captures(root.getArguments().drop_front(loop ? 3 : 2));
      if (cross)
        captures = control.invoke(
            "exec.collect", TypeRange{vector}, control.scoped(captures),
            {builder.getNamedAttr("domain",
                                  FlatSymbolRefAttr::get(&context, "rows")),
             builder.getNamedAttr("body",
                                  FlatSymbolRefAttr::get(&context, "row")),
             builder.getNamedAttr("site", builder.getStringAttr("map"))});
      auto body = [&](unsigned arm) {
        SmallVector<Type> parameters;
        if (loop)
          parameters = {index, field, vector, vector, vector};
        else
          parameters = llvm::to_vector(TypeRange(captures));
        auto helper =
            sc::region(builder, root, name.str() + "_" + std::to_string(arm),
                       parameters, {field});
        exec::ScopedExecutionBuilder nested(builder, helper);
        SmallVector<Value> arguments(helper.getArguments().drop_front());
        if (loop)
          arguments = {helper.getArgument(3), helper.getArgument(4),
                       helper.getArgument(5), helper.getArgument(2)};
        auto values =
            invokeHelper(nested, builder, cross ? "reduce" : "work",
                         "body" + std::to_string(arm), arguments, {field});
        nested.complete(values);
        return helper;
      };
      SmallVector<Value> result;
      if (loop)
        result =
            control.loop(root.getArgument(1), root.getArgument(2),
                         root.getArgument(6), root.getArguments().slice(3, 3),
                         TypeRange{field}, false, "loop", body);
      else
        result = control.conditional(root.getArgument(1), captures,
                                     TypeRange{field}, "branch", body);
      control.returned(result);
    }
    // Retained mathematical symbols must not collide with generated regions.
    auto formula = function(*original, "formula");
    OpBuilder collisionBuilder(formula);
    auto *reserved = collisionBuilder.clone(*formula);
    SymbolTable::setSymbolName(
        reserved, collisionBuilder.getStringAttr("_execution_region_0"));
    require(succeeded(verify(*original)), "control fixture malformed");
    auto expanded = expand(*original);
    auto candidate = prepare(*expanded);
    require(bool(candidate) &&
                count(*candidate, "vector.dot", "branches") == 2 &&
                count(*candidate, "vector.dot", "loop") == 1 &&
                count(*candidate, "vector.dot", "cross") == 0 &&
                succeeded(compare(*expanded, *candidate)),
            "contraction crossed an ordered control boundary");
    auto repeated = expand(*original);
    auto again = prepare(*repeated);
    require(bool(again) && same(*candidate, *again),
            "region expansion changed canonical preparation");
  });

  // Static reference admission counts every ordinary function on a path,
  // including a mathematical body called by exec.compute. The scoped-only
  // closure has its own limit. With the row computation, 61 wrappers + work +
  // row + formula reach 64; without that edge, 62 wrappers reach the same
  // bound.
  for (bool mathematicalRow : {false, true})
    for (unsigned depth : {61u, 62u, 63u, 64u})
      cases.run(
          "helper chain with " + Twine(depth) + " wrappers and " +
              (mathematicalRow ? "mathematical row" : "direct row"),
          [&] {
            bool depthRefusal = false;
            std::string diagnostics;
            ScopedDiagnosticHandler quiet(
                &context, [&](Diagnostic &diagnostic) {
                  diagnostics += diagnostic.str() + "\n";
                  depthRefusal |=
                      namesIdentifier(diagnostic.str(), "finite-formation") &&
                      StringRef(diagnostic.str())
                          .contains("static closure exceeds analysis limit");
                  return success();
                });
            auto original = parseSourceString<ModuleOp>(
                chain(depth, 1, 0, mathematicalRow), &context);
            require(bool(original),
                    "structural source refused: " + diagnostics);
            auto admitted = admitStage(*original);
            if (depth > (mathematicalRow ? 61u : 62u)) {
              require(failed(admitted) && depthRefusal,
                      "excess static reference depth admitted: " + diagnostics);
              return;
            }
            require(succeeded(admitted),
                    "at-boundary source refused: " + diagnostics);
            auto unchanged = sf::clone(*original);
            auto expanded = protocol::expandScopedHelpers(*original);
            require(bool(expanded),
                    "at-boundary expansion refused: " + diagnostics);
            auto candidate = prepare(*expanded);
            require(bool(candidate) &&
                        succeeded(compare(*expanded, *candidate)) &&
                        same(*original, *unchanged),
                    "at-boundary expansion or preparation refused");
          });
  auto requiredPreparation = [&](ModuleOp original, uint64_t &copy,
                                 uint64_t &bytes,
                                 mathematical::RealizationWork &work,
                                 std::optional<CapacityCause> &capacity) {
    return protocol::prepareScopedFinite(original, work, copy, bytes, capacity,
                                         {false, false, false});
  };
  cases.run(
      "required preparation copy and site allowances are cumulative", [&] {
        constexpr uint64_t copyLimit = 1000000, byteLimit = 16 * 1024 * 1024;
        mathematical::RealizationWork measure;
        uint64_t copy = copyLimit, bytes = byteLimit;
        std::optional<CapacityCause> capacity;
        auto candidate =
            requiredPreparation(*retained, copy, bytes, measure, capacity);
        require(bool(candidate) && copy < copyLimit && bytes < byteLimit,
                "required preparation did not account work");
        auto usedCopy = copyLimit - copy, usedBytes = byteLimit - bytes;
        for (bool site : {false, true}) {
          mathematical::RealizationWork work;
          copy = site ? copyLimit : usedCopy;
          bytes = site ? usedBytes : byteLimit;
          auto exact =
              requiredPreparation(*retained, copy, bytes, work, capacity);
          require(bool(exact) && (site ? bytes : copy) == 0,
                  "exact allowance refused or not charged");
          auto unchanged = sf::clone(*retained);
          ScopedDiagnosticHandler quiet(&context,
                                        [](Diagnostic &) { return success(); });
          auto repeated =
              requiredPreparation(*retained, copy, bytes, work, capacity);
          require(!repeated && capacity.has_value() &&
                      same(*retained, *unchanged),
                  "second call reset a consumed allowance");
          work = mathematical::RealizationWork{};
          copy = site ? copyLimit : usedCopy - 1;
          bytes = site ? usedBytes - 1 : byteLimit;
          auto shortCandidate =
              requiredPreparation(*retained, copy, bytes, work, capacity);
          require(!shortCandidate && capacity.has_value() &&
                      same(*retained, *unchanged),
                  "one-short allowance escaped transaction boundary");
        }
      });
  cases.run(
      "two thousand repeated calls retain cumulative required accounting", [&] {
        auto original = parse(
            withDefinitions(fixture(), wrapper("many", "work", "call_", 2000)));
        auto unchanged = sf::clone(*original);
        auto expanded = expand(*original);
        auto expandedBefore = sf::clone(*expanded);
        mathematical::RealizationWork work;
        uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
        std::optional<CapacityCause> capacity;
        ScopedDiagnosticHandler quiet(&context,
                                      [](Diagnostic &) { return success(); });
        auto candidate =
            requiredPreparation(*expanded, copy, bytes, work, capacity);
        require(!candidate && capacity &&
                    capacity->owner == WorkOwner::AlgorithmExpansion &&
                    copy < 1000000 && same(*original, *unchanged) &&
                    same(*expanded, *expandedBefore),
                "large preparation reset required copy work or mutated source");
      });

  cases.run("long occurrence workloads remain bounded and transactional", [&] {
    std::string pairs;
    for (unsigned i = 0; i < 60; ++i) {
      auto number = std::to_string(i);
      pairs += collection("map" + number, "%v" + number) +
               call("reduce", "reduce" + number, "%v" + number, "!V",
                    "%r" + number, "!F");
    }
    auto original = parse(
        edit(chain(30, 1, 120), workBody, pairs + scopedReturn("%r59", "!F")));
    auto unchanged = sf::clone(*original);
    std::vector<protocol::AlgorithmOrigin> origins;
    auto expanded = expand(*original, &origins);
    require(llvm::any_of(origins,
                         [&](const auto &origin) {
                           return origin.path.size() == 30 &&
                                  origin.originalSite == "map59" &&
                                  origin.path.front().second ==
                                      std::string(120, 'x') + "28" &&
                                  StringRef(origin.site).starts_with("lc_h_");
                         }),
            "large hashed occurrence lost its full path");
    auto expandedBefore = sf::clone(*expanded);
    mathematical::RealizationWork work;
    uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
    std::optional<CapacityCause> capacity;
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    auto candidate =
        requiredPreparation(*expanded, copy, bytes, work, capacity);
    // The scoped CFG exhausts required copying before its independent origin
    // account. Keep the original workload and assert the boundary actually hit.
    require(!candidate && capacity &&
                capacity->owner == WorkOwner::AlgorithmExpansion &&
                copy < 1000000 && bytes < 16 * 1024 * 1024 &&
                same(*original, *unchanged) && same(*expanded, *expandedBefore),
            "long workload reset capacity or published a partial candidate");
  });
  cases.run(
      "hashed occurrence names charge full paths against sixteen MiB", [&] {
        protocol::Assignments path;
        for (unsigned i = 0; i < 30; ++i)
          path.emplace_back("call", std::string(120, 'x') + std::to_string(i));
        constexpr uint64_t limit = 16 * 1024 * 1024;
        uint64_t measured = limit;
        auto name = take(protocol::algorithmSite(path, "map59", measured));
        auto fullCost = limit - measured;
        require(StringRef(name).starts_with("lc_h_") && fullCost > 3600 &&
                    name.size() < fullCost,
                "long occurrence was not charged before hashing");
        uint64_t bytes = limit;
        for (uint64_t i = 0; i < limit / fullCost; ++i)
          require(take(protocol::algorithmSite(path, "map59", bytes)) == name,
                  "occurrence identity depends on remaining capacity");
        require(bytes == limit % fullCost,
                "full path charges were not cumulative");
        auto remainder = bytes;
        zkc::test::refuses(protocol::algorithmSite(path, "map59", bytes),
                           "algorithm-origin-limit");
        require(bytes == remainder, "refused occurrence changed its account");
      });
  cases.run(
      "unused scalar work remains visible to preparation accounting", [&] {
        auto original = parse(deepFormula(false, 65534));
        auto unchanged = sf::clone(*original);
        std::string diagnostics;
        ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &diagnostic) {
          diagnostics += diagnostic.str();
          return success();
        });
        auto expanded = protocol::expandScopedHelpers(*original);
        require(bool(expanded), "large formula helper expansion refused");
        auto expandedBefore = sf::clone(*expanded);
        {
          mathematical::RealizationWork work;
          uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
          std::optional<CapacityCause> capacity;
          mathematical::VerificationDecision outcome;
          auto candidate = protocol::prepareScopedFinite(
              *expanded, work, copy, bytes, capacity, {false, false, false},
              nullptr, nullptr, &outcome);
          require(
              !candidate &&
                  namesIdentifier(diagnostics, "mathematical-analysis-limit"),
              "unused scalar work escaped cumulative computation admission");
          require(std::distance(function(*expanded, "formula")
                                    .front()
                                    .without_terminator()
                                    .begin(),
                                function(*expanded, "formula")
                                    .front()
                                    .without_terminator()
                                    .end()) == 65536,
                  "large callback workload was changed");
        }
        require(same(*original, *unchanged) && same(*expanded, *expandedBefore),
                "unused scalar work changed before admission");
      });

  for (StringRef name : {"iterated-sumcheck.mlir", "helper-realization.mlir",
                         "../structured-source/map-declarations.mlir"})
    cases.run("enabled preparation preserves ordinary recipes: " + name, [&] {
      auto bytes = llvm::MemoryBuffer::getFile(std::string(ZKC_MATH_FIXTURES) +
                                               "/" + name.str());
      require(bool(bytes), "ordinary recipe fixture missing");
      // The shared scoped map has the same scalar formula and data ABI as
      // the former map fixture; preserve this control's original field.
      auto text = (*bytes)->getBuffer().str();
      if (name.ends_with("map-declarations.mlir")) {
        text = replaceText(text, "bls12-381.fr", "koala-bear");
        text = replaceText(text, "ui255", "ui31");
      }
      auto original = parse(text), enabled = sf::clone(*original);
      run(*original, protocol::createPrepareProtocolPass(false));
      run(*enabled,
          protocol::createPrepareProtocolPass(false, {true, true, false}));
      for (auto module : {original.get(), enabled.get()}) {
        run(module, protocol::createProjectProtocolPass(false));
        run(module, protocol::createLowerMathPass());
        run(module, computation::createRealizeComputationsPass());
        run(module, protocol::createSelectPhysicalPass(
                        {}, false, false, nullptr, {}, {true, true, false}));
      }
      require(same(*original, *enabled),
              "nonmatching recipe changed under enabled preparation");
    });
  return cases.result();
}
