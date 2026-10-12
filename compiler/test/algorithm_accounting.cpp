#include "../lib/Transforms/AlgorithmSupport.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Finite.h"
#include "zkc/Transforms/Mathematical.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
using Phase = protocol::AlgorithmExpansionPhase;
using State = protocol::AlgorithmExpansionState;
using Record = protocol::detail::AlgorithmExpansionRecord;
using Access = protocol::detail::AlgorithmStateAccess;
constexpr StringLiteral ordinary = R"mlir(module { "protocol.module"() ({
 "local.binding"() {sym_name="and",contract="bool.and",arguments=[],implementation=""} : ()->()
 local.func @leaf(%x:i1,%y:i1)->i1 attributes {logical_origin=["leaf",[]]} {
   %r = "algebra.exec.bool_and"(%x,%y) {binding=@and,parameters=[],site="combine"} : (i1,i1)->i1
   local.return %r : i1
 }
 local.func @first(%x:i1,%y:i1)->i1 attributes {logical_origin=["first",[]]} {
   %r = local.apply @leaf(%x,%y) {site="invoke"} : (i1,i1)->i1
   local.return %r : i1
 }
 local.func @second(%x:i1,%y:i1)->i1 attributes {logical_origin=["second",[]]} {
   %r = local.apply @leaf(%x,%y) {site="invoke"} : (i1,i1)->i1
   local.return %r : i1
 }
 // extra declarations
 "protocol.func"() ({ ^entry(%x:i1,%y:i1):
   %r = "protocol.local_call"(%x,%y) {callee=@first,role="P",site="call"} : (i1,i1)->i1
   "protocol.return"(%r) : (i1)->()
 }) {sym_name="main",function_type=(i1,i1)->i1,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
constexpr StringLiteral retained = R"mlir(
 "local.binding"() {sym_name="sum",contract="vector.sum",arguments=["koala-bear"],implementation=""} : ()->()
 func.func private @formula(%a:!F,%b:!F)->!F {
   %p = "algebra.field_multiply"(%a,%b) : (!F,!F)->!F
   func.return %p : !F
 }
 algebra.map_realize @mapped = @formula [true,true] : (!V,!V)->!V
 local.func @work(%a:!V,%b:!V)->!F attributes {logical_origin=["work",[]]} {
   %v = local.apply @wrapper(%a,%b) {site="wrapper"} : (!V,!V)->!V
   %r = local.apply @reduce(%v) {site="reduce"} : (!V)->!F
   local.return %r : !F
 }
 local.func @wrapper(%a:!V,%b:!V)->!V attributes {logical_origin=["wrapper",[]]} {
   %v = local.apply @mapped(%a,%b) {site="map"} : (!V,!V)->!V
   local.return %v : !V
 }
 local.func @reduce(%v:!V)->!F attributes {logical_origin=["reduce",[]]} {
   %r = "algebra.exec.vector_sum"(%v) {binding=@sum,parameters=[],site="sum"} : (!V)->!F
   local.return %r : !F
 }
 local.func @regions(%go:i1,%x:i1,%y:i1)->i1 attributes {logical_origin=["regions",[]]} {
   %r = "local.if"(%go,%x,%y) ({ ^left(%a:i1,%b:i1):
     %p = "algebra.exec.bool_and"(%a,%b) {binding=@and,parameters=[],site="left"} : (i1,i1)->i1
     "local.yield"(%p) : (i1)->()
   }, { ^right(%a:i1,%b:i1):
     "local.yield"(%a) : (i1)->()
   }) {site="branch"} : (i1,i1,i1)->i1
   local.return %r : i1
 }
)mlir";
constexpr StringLiteral callbacks = R"mlir(
 "local.binding"() {sym_name="add",contract="field.add",arguments=["koala-bear"],implementation=""} : ()->()
 "data.domain"() ({ ^entry(%xs:!V):
   %items = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%items) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 local.func private @scalar(%a:!F,%b:!F)->!F attributes {logical_origin=["scalar",[]]} {
   %r = "algebra.exec.field_add"(%a,%b) {binding=@add,parameters=[],site="add"} : (!F,!F)->!F
   local.return %r : !F
 }
 local.func private @scalar_wrapper(%a:!F,%b:!F)->!F attributes {logical_origin=["scalar_wrapper",[]]} {
   %r = local.apply @scalar(%a,%b) {site="scalar"} : (!F,!F)->!F
   local.return %r : !F
 }
 local.func private @step(%s:!F,%x:!F,%xs:!V,%flag:i1)->!F attributes {logical_origin=["step",[]]} {
   %r = local.apply @scalar_wrapper(%s,%x) {site="wrapper"} : (!F,!F)->!F
   local.return %r : !F
 }
 local.func private @body(%x:!F,%xs:!V,%flag:i1)->!F attributes {logical_origin=["body",[]]} {
   %r = local.apply @scalar_wrapper(%x,%x) {site="wrapper"} : (!F,!F)->!F
   local.return %r : !F
 }
 local.func private @predicate(%x:!F,%xs:!V,%flag:i1)->i1 attributes {logical_origin=["predicate",[]]} {
   %r = local.apply @first(%flag,%flag) {site="test"} : (i1,i1)->i1
   local.return %r : i1
 }
 local.func private @identity(%x:!F,%xs:!V,%flag:i1)->!F attributes {logical_origin=["identity",[]]} {
   local.return %x : !F
 }
 "local.finite_fold"() {sym_name="fold",function_type=(!V,!F,i1)->!F,domain=@items,step=@step,predicate=@predicate} : ()->()
 "local.finite_collect"() {sym_name="collect",function_type=(!V,i1)->!V,domain=@items,body=@body,predicate=@predicate} : ()->()
 "local.finite_collect"() {sym_name="direct",function_type=(!V,i1)->!V,domain=@items,body=@identity} : ()->()
 local.func @uses_step(%s:!F,%x:!F,%xs:!V,%flag:i1)->!F attributes {logical_origin=["uses_step",[]]} {
   %r = local.apply @step(%s,%x,%xs,%flag) {site="step"} : (!F,!F,!V,i1)->!F
   local.return %r : !F
 }
)mlir";
std::string withDeclarations(StringRef declarations) {
  std::string text = ordinary.str();
  text.insert(text.find(" // extra declarations"), declarations.str());
  return "!F = !algebra.field<\"koala-bear\">\n"
         "!V = !algebra.field_vector<\"koala-bear\">\n" +
         text;
}
OwningOpRef<ModuleOp> copy(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}
bool same(Operation *a, Operation *b) {
  return OperationEquivalence::isEquivalentTo(
      a, b,
      OperationEquivalence::IgnoreLocations |
          OperationEquivalence::IgnoreCommutativity);
}
local::FuncOp function(ModuleOp module, StringRef name) {
  return cast<local::FuncOp>(
      SymbolTable::lookupSymbolIn(&module.getBody()->front(), name));
}
unsigned calls(local::FuncOp function) {
  unsigned count = 0;
  function.walk([&](local::ApplyOp) { ++count; });
  return count;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  Cases cases;
  auto parse = [&](StringRef text) {
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module) && succeeded(verify(*module)), "fixture refused");
    return module;
  };
  auto named = [&](StringRef code, llvm::function_ref<LogicalResult()> action) {
    bool seen = false;
    ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &diagnostic) {
      seen |= diagnostic.str().find(code.str()) != std::string::npos;
      return success();
    });
    require(failed(action()) && seen, "missing refusal " + code);
  };
  cases.run(
      "finite callbacks expose scalar helper chains as separate roots", [&] {
        auto source = parse(withDeclarations(callbacks));
        auto module = copy(*source);
        State state;
        Record budget;
        // Three callback roots, each visiting two calls, one primitive
        // and two callee returns. The shared predicate is selected once.
        budget.work = 15;
        Access::set(state, budget);
        auto initial = state;
        std::vector<protocol::AlgorithmOrigin> origins;
        require(succeeded(protocol::expandAlgorithms(*module, Phase::RetainMaps,
                                                     state, &origins)),
                "callback retention refused");
        for (StringRef name : {"step", "body", "predicate"})
          require(calls(function(*module, name)) == 0,
                  "callback helper chain remains opaque: " + name);
        for (StringRef name : {"first", "second", "scalar_wrapper", "scalar",
                               "leaf", "uses_step", "identity"})
          require(same(function(*source, name), function(*module, name)),
                  "callback selection spread to unrelated body: " + name);
        require(Access::get(state).work == 0,
                "callback substitutions were skipped or charged twice");
        require(succeeded(protocol::verifyStagedAlgorithmExpansionPreserved(
                    *source, *module, Phase::RetainMaps, initial, state)),
                "independent callback selection disagrees");
        require(llvm::any_of(origins,
                             [](const auto &origin) {
                               return origin.function == "step" &&
                                      origin.originalSite == "add" &&
                                      origin.path ==
                                          protocol::Assignments{
                                              {"wrapper", "scalar_wrapper"},
                                              {"scalar", "scalar"}};
                             }),
                "callback helper source path was lost");
        for (StringRef name : {"step", "body", "predicate"}) {
          auto candidate = copy(*module);
          auto actual = function(*candidate, name);
          OpBuilder builder(actual);
          builder.clone(*function(*source, name));
          actual.erase();
          // A well-formed but opaque callback must not pass just because
          // its source and candidate still agree under preservation.
          require(succeeded(verify(*candidate)), "opaque control refused");
          named("algorithm-correspondence", [&] {
            return protocol::verifyStagedAlgorithmExpansionPreserved(
                *source, *candidate, Phase::RetainMaps, initial, state);
          });
        }
        auto changed = copy(*module);
        auto &add = function(*changed, "step").getBody().front().front();
        add.setOperand(1, add.getOperand(0));
        require(succeeded(verify(*changed)), "operand control refused");
        named("algorithm-correspondence", [&] {
          return protocol::verifyStagedAlgorithmExpansionPreserved(
              *source, *changed, Phase::RetainMaps, initial, state);
        });
      });
  cases.run("callback roots share the allowance and publish atomically", [&] {
    auto module = parse(withDeclarations(callbacks)), before = copy(*module);
    Record record;
    record.work = 14;
    State state;
    Access::set(state, record);
    std::vector<protocol::AlgorithmOrigin> origins{
        {"sentinel", "", "", "", {}}};
    named("algorithm-expansion-limit", [&] {
      return protocol::expandAlgorithms(*module, Phase::RetainMaps, state,
                                        &origins);
    });
    require(same(*module, *before) && record == Access::get(state) &&
                origins.size() == 1 && origins.front().function == "sentinel",
            "callback refusal published partial IR, state or origins");
  });
  for (StringRef declaration : {"fold", "collect"})
    cases.run("predicate is selected independently for " + declaration, [&] {
      auto module = parse(withDeclarations(callbacks));
      auto other = declaration == "fold" ? "collect" : "fold";
      SymbolTable::lookupSymbolIn(&module->getBody()->front(), other)
          ->removeAttr("predicate");
      State state;
      require(succeeded(protocol::expandAlgorithms(*module, Phase::RetainMaps,
                                                   state)) &&
                  calls(function(*module, "predicate")) == 0,
              "predicate selection depended on another declaration");
    });
  cases.run("realized calls prefix retained callback helper paths", [&] {
    auto module = parse(withDeclarations(callbacks));
    State state;
    require(succeeded(protocol::expandAlgorithms(*module, Phase::RetainMaps,
                                                 state)) &&
                succeeded(finite::realizeLocals(*module, {false, false})),
            "callback fallback preparation refused");
    auto before = copy(*module);
    auto input = state;
    std::vector<protocol::AlgorithmOrigin> origins;
    require(succeeded(protocol::expandAlgorithms(*module, Phase::Finish, state,
                                                 &origins)) &&
                succeeded(protocol::verifyStagedAlgorithmExpansionPreserved(
                    *before, *module, Phase::Finish, input, state)),
            "callback Finish correspondence failed");
    require(llvm::any_of(origins,
                         [](const auto &origin) {
                           return origin.function == "fold" &&
                                  origin.originalSite == "add" &&
                                  origin.path.size() == 3 &&
                                  origin.path[0].second == "step" &&
                                  origin.path[1] ==
                                      protocol::Assignments::value_type{
                                          "wrapper", "scalar_wrapper"} &&
                                  origin.path[2] ==
                                      protocol::Assignments::value_type{
                                          "scalar", "scalar"};
                         }),
            "realized call lost or duplicated a retained callback path");
    require(Access::get(state).work < Access::get(input).work,
            "Finish did not charge copies of already retained callbacks");
  });
  auto source = parse(withDeclarations(retained));
  auto selected = copy(*source);
  State initial, retainedState;
  require(succeeded(protocol::expandAlgorithms(*selected, Phase::RetainMaps,
                                               retainedState)),
          "retention refused");
  cases.run(
      "retention selects transitive maps and preserves other declarations",
      [&] {
        require(calls(function(*selected, "work")) == 1 &&
                    calls(function(*selected, "wrapper")) == 1,
                "map wrapper or reducer was not expanded");
        for (StringRef name : {"leaf", "first", "second", "regions", "reduce"})
          require(same(function(*source, name), function(*selected, name)),
                  "unrelated declaration changed: " + name);
        require(!protocol::detail::occurrence(Access::get(retainedState),
                                              "first", "invoke"),
                "raw source site was marked as previously expanded");
        require(
            succeeded(protocol::verifyStagedAlgorithmExpansionPreserved(
                *source, *selected, Phase::RetainMaps, initial, retainedState)),
            "independent selection disagrees");
      });
  cases.run("deferred calls receive canonical sites on first expansion", [&] {
    auto legacy = copy(*source), staged = copy(*selected);
    require(succeeded(mathematical::expandMapRealizations(*legacy)) &&
                succeeded(protocol::expandAlgorithms(*legacy)),
            "single-phase control refused");
    State state = retainedState;
    require(succeeded(mathematical::expandMapRealizations(*staged)),
            "map realization refused");
    auto before = copy(*staged);
    std::vector<protocol::AlgorithmOrigin> origins;
    require(succeeded(protocol::expandAlgorithms(*staged, Phase::Finish, state,
                                                 &origins)) &&
                same(*legacy, *staged),
            "staged sites or operations differ from single-phase expansion");
    require(succeeded(protocol::verifyStagedAlgorithmExpansionPreserved(
                *before, *staged, Phase::Finish, retainedState, state)),
            "Finish checker refused");
    require(llvm::any_of(origins,
                         [](const auto &origin) {
                           return origin.function == "first" &&
                                  origin.originalSite == "combine" &&
                                  origin.path ==
                                      protocol::Assignments{{"invoke", "leaf"}};
                         }),
            "deferred helper lost its source occurrence");
  });
  auto negative = [&](StringRef name,
                      llvm::function_ref<void(ModuleOp)> mutate) {
    cases.run(name, [&] {
      auto candidate = copy(*selected);
      mutate(*candidate);
      require(succeeded(verify(*candidate)), "control must remain well formed");
      named("algorithm-correspondence", [&] {
        return protocol::verifyStagedAlgorithmExpansionPreserved(
            *source, *candidate, Phase::RetainMaps, initial, retainedState);
      });
    });
  };
  negative("preserved primitive operands are checked", [&](ModuleOp module) {
    auto &op = function(module, "leaf").getBody().front().front();
    op.setOperand(1, op.getOperand(0));
  });
  negative("preserved call arguments are checked", [&](ModuleOp module) {
    auto &op = function(module, "first").getBody().front().front();
    op.setOperand(1, op.getOperand(0));
  });
  negative("preserved return aliases are checked", [&](ModuleOp module) {
    auto fn = function(module, "first");
    fn.getBody().front().back().setOperand(0, fn.getArgument(0));
  });
  negative("preserved sites are checked", [&](ModuleOp module) {
    function(module, "leaf")
        .getBody()
        .front()
        .front()
        .setAttr("site", StringAttr::get(&context, "different"));
  });
  negative("preserved region operands are checked", [&](ModuleOp module) {
    auto &op = function(module, "regions")
                   .getBody()
                   .front()
                   .front()
                   .getRegion(0)
                   .front()
                   .front();
    op.setOperand(1, op.getOperand(0));
  });
  negative("preserved region yields are checked", [&](ModuleOp module) {
    auto &block = function(module, "regions")
                      .getBody()
                      .front()
                      .front()
                      .getRegion(1)
                      .front();
    block.back().setOperand(0, block.getArgument(1));
  });
  for (bool inspection : {false, true})
    cases.run(inspection ? "checker recomputes source inspection balance"
                         : "checker recomputes substitution balance",
              [&] {
                auto state = retainedState;
                auto record = Access::get(state);
                ++(inspection ? record.inspectionWork : record.work);
                Access::set(state, record);
                named("algorithm-correspondence", [&] {
                  return protocol::verifyStagedAlgorithmExpansionPreserved(
                      *source, *selected, Phase::RetainMaps, initial, state);
                });
              });
  cases.run(
      "all definition roots share inspection and substitution allowances", [&] {
        auto module = parse(ordinary), before = copy(*module);
        Record record;
        record.work =
            6; // Two root calls, each substitutes a primitive and return.
        record.inspectionWork = 12; // Six source instructions in each phase.
        State state;
        Access::set(state, record);
        auto start = state;
        require(succeeded(protocol::expandAlgorithms(*module, Phase::RetainMaps,
                                                     state)),
                "empty retention failed");
        require(
            same(*module, *before) && Access::get(state).work == 6 &&
                Access::get(state).inspectionWork == 6,
            "empty retention charged expansion or forgot source inspection");
        require(succeeded(protocol::verifyStagedAlgorithmExpansionPreserved(
                    *before, *module, Phase::RetainMaps, start, state)),
                "empty retention was not checked");
        auto retainedInput = state;
        require(succeeded(
                    protocol::expandAlgorithms(*module, Phase::Finish, state)),
                "exact substitution allowance refused");
        require(Access::get(state).work == 0 &&
                    Access::get(state).inspectionWork == 0,
                "budgets restarted at a root or phase");
        require(succeeded(protocol::verifyStagedAlgorithmExpansionPreserved(
                    *before, *module, Phase::Finish, retainedInput, state)),
                "exact-accounting Finish failed checking");
      });
  cases.run("insufficient shared substitution allowance publishes nothing",
            [&] {
              auto module = parse(ordinary), before = copy(*module);
              Record record;
              record.work = 5;
              State state;
              Access::set(state, record);
              std::vector<protocol::AlgorithmOrigin> origins{
                  {"sentinel", "", "", "", {}}};
              named("algorithm-expansion-limit", [&] {
                return protocol::expandAlgorithms(*module, Phase::Finish, state,
                                                  &origins);
              });
              require(same(*module, *before) && record == Access::get(state) &&
                          origins.size() == 1 &&
                          origins.front().function == "sentinel",
                      "failed expansion published IR, state or origins");
            });
  for (bool checker : {false, true})
    cases.run(checker ? "unchanged-body checker remains bounded"
                      : "source inspection remains bounded",
              [&] {
                auto module = parse(ordinary), before = copy(*module);
                Record record;
                if (checker)
                  record.checkWork = 1;
                else
                  record.inspectionWork = 1;
                State state;
                Access::set(state, record);
                named(checker ? "algorithm-correspondence-limit"
                              : "algorithm-expansion-limit",
                      [&] {
                        return protocol::expandAlgorithms(
                            *module, Phase::RetainMaps, state);
                      });
                require(same(*module, *before) && record == Access::get(state),
                        "inspection failure published a partial candidate");
              });
  cases.run(
      "call-free Finish remains checked with zero substitution work", [&] {
        auto module = parse(ordinary);
        State state;
        require(succeeded(
                    protocol::expandAlgorithms(*module, Phase::Finish, state)),
                "call-free fixture construction failed");
        // Start a separate invocation on already call-free IR, with zero
        // capacity for substitutions. Inspection and independent checking must
        // still run.
        auto before = copy(*module);
        State empty;
        Record record;
        record.work = 0;
        Access::set(empty, record);
        auto start = empty;
        require(succeeded(protocol::expandAlgorithms(*module, Phase::RetainMaps,
                                                     empty)),
                "call-free retention failed");
        auto retainedInput = empty;
        std::vector<protocol::AlgorithmOrigin> origins;
        require(
            succeeded(protocol::expandAlgorithms(*module, Phase::Finish, empty,
                                                 &origins)) &&
                same(*module, *before),
            "call-free Finish changed the subject or charged substitutions");
        require(Access::get(empty).work == 0 &&
                    Access::get(empty).inspectionWork <
                        Access::get(start).inspectionWork &&
                    Access::get(empty).checkWork <
                        Access::get(retainedInput).checkWork &&
                    !origins.empty(),
                "no-op phase skipped inspection or origins");
        require(succeeded(protocol::verifyStagedAlgorithmExpansionPreserved(
                    *before, *module, Phase::Finish, retainedInput, empty)),
                "call-free Finish was not independently checked");
      });
  cases.run(
      "large unchanged declarations do not consume substitution capacity", [&] {
        std::string declarations = retained.str();
        for (unsigned f = 0; f < 36; ++f) {
          auto name = "idle" + std::to_string(f);
          declarations += "local.func @" + name +
                          "(%x:i1,%y:i1)->i1 attributes {logical_origin=[\"" +
                          name + "\",[]]} {\n";
          for (unsigned i = 0; i < 512; ++i)
            declarations += " %v" + std::to_string(i) +
                            " = \"algebra.exec.bool_and\"(%x,%y) "
                            "{binding=@and,parameters=[],site=\"s" +
                            std::to_string(i) + "\"} : (i1,i1)->i1\n";
          declarations += " local.return %v511 : i1\n}\n";
        }
        auto module = parse(withDeclarations(declarations));
        auto before = copy(*module);
        State state;
        require(succeeded(protocol::expandAlgorithms(*module, Phase::RetainMaps,
                                                     state)) &&
                    succeeded(mathematical::expandMapRealizations(*module)) &&
                    succeeded(protocol::expandAlgorithms(*module, Phase::Finish,
                                                         state)),
                "unrelated bodies exhausted expansion capacity");
        require(Access::get(state).work > 32000 &&
                    Access::get(state).inspectionWork < 1000000 - 32768,
                "work was reset or source inspection was omitted");
        for (unsigned f = 0; f < 36; ++f) {
          auto name = "idle" + std::to_string(f);
          require(same(function(*before, name), function(*module, name)),
                  "unchanged large body was rewritten");
        }
      });
  return cases.result();
}
