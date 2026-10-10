#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Transforms/VectorReductions.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
using Phase = protocol::AlgorithmExpansionPhase;
using State = protocol::AlgorithmExpansionState;
constexpr StringLiteral fixture = R"mlir(!F = !algebra.field<"koala-bear">
!V = tensor<?x!F>
module { "protocol.module"() ({
 "local.binding"() {sym_name="sum",contract="vector.sum",arguments=["koala-bear"],implementation=""} : ()->()
 "local.binding"() {sym_name="length_alias",contract="vector.length",arguments=["koala-bear"],implementation=""} : ()->()
 "local.binding"() {sym_name="constant",contract="field.constant",arguments=["koala-bear"],implementation=""} : ()->()
 func.func private @formula(%a:!F,%b:!F,%unused:!F,%s:!F)->!F {
   %dead = "algebra.field_add"(%s,%s) : (!F,!F)->!F
   %p = "algebra.field_multiply"(%a,%b) : (!F,!F)->!F
   func.return %p : !F
 }
 algebra.map_realize @mapped = @formula [true, true, true, false] : (!V,!V,!V,!F)->!V
 local.func @reduce(%v:!V)->!F attributes {logical_origin=["reduce",[]]} {
   %r = "algebra.exec.vector_sum"(%v) {binding=@sum,parameters=[],site="sum"} : (!V)->!F
   local.return %r : !F
 }
 local.func @work(%a:!V,%b:!V,%c:!V,%s:!F)->!F attributes {logical_origin=["work",[]]} {
   %v = local.apply @mapped(%a,%b,%c,%s) {site="map"} : (!V,!V,!V,!F)->!V
   %r = local.apply @reduce(%v) {site="reduce"} : (!V)->!F
   local.return %r : !F
 }
 "protocol.func"() ({ ^entry(%a:!V,%b:!V,%c:!V,%s:!F):
   %r = "protocol.local_call"(%a,%b,%c,%s) {callee=@work,role="P",site="work"} : (!V,!V,!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!V,!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
std::string edit(StringRef source, StringRef from, StringRef to) {
  std::string text = source.str();
  auto pos = text.find(from.str());
  require(pos != std::string::npos, "missing fixture fragment " + from);
  text.replace(pos, from.size(), to.str());
  return text;
}
OwningOpRef<ModuleOp> copy(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}
local::FuncOp function(ModuleOp module, StringRef name = "work") {
  return cast<local::FuncOp>(
      SymbolTable::lookupSymbolIn(&module.getBody()->front(), name));
}
Operation *nth(ModuleOp module, StringRef contract, unsigned index = 0,
               StringRef name = "work") {
  Operation *found = nullptr;
  function(module, name).walk([&](Operation *op) {
    auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    if (!reference)
      return;
    auto binding =
        SymbolTable::lookupNearestSymbolFrom<local::OperationBindingOp>(
            op, reference);
    if (binding && binding.getContract() == contract && index-- == 0)
      found = op;
  });
  require(found, "missing " + contract);
  return found;
}
unsigned count(ModuleOp module, StringRef operation, StringRef name = "work") {
  unsigned result = 0;
  function(module, name).walk([&](Operation *op) {
    result += op->getName().getStringRef() == operation;
  });
  return result;
}
void run(ModuleOp module, std::unique_ptr<Pass> pass) {
  PassManager manager(module.getContext());
  manager.addPass(std::move(pass));
  require(succeeded(manager.run(module)), "pipeline refused");
}
void retain(ModuleOp module, State &state) {
  require(
      succeeded(protocol::expandAlgorithms(module, Phase::RetainMaps, state)),
      "RetainMaps refused");
}
void finish(ModuleOp module, State &state) {
  require(succeeded(mathematical::expandMapRealizations(module)),
          "map realization refused");
  require(succeeded(protocol::expandAlgorithms(module, Phase::Finish, state)),
          "Finish refused");
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
    require(bool(module), "fixture refused");
    return module;
  };
  auto named = [&](StringRef code, llvm::function_ref<bool()> action) {
    bool seen = false;
    ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &d) {
      seen |= d.str().find(code.str()) != std::string::npos;
      return success();
    });
    return action() && seen;
  };
  auto source = parse(fixture);
  auto retained = copy(*source);
  State initial, retainedState;
  retain(*retained, retainedState);
  cases.run("retained map and native sum through reducer wrapper", [&] {
    require(count(*retained, "local.apply") == 1 &&
                count(*retained, "algebra.exec.vector_sum") == 1,
            "retained structure missing");
    require(succeeded(protocol::verifyStagedAlgorithmExpansionPreserved(
                *source, *retained, Phase::RetainMaps, initial, retainedState)),
            "independent retained checker refused");
  });
  auto fused = copy(*retained);
  State fusedState = retainedState;
  require(succeeded(mathematical::fuseVectorReductions(*fused, fusedState)),
          "fusion refused");
  cases.run("multiply sum with unused row and scalar", [&] {
    require(count(*fused, "local.apply") == 0 &&
                count(*fused, "algebra.exec.vector_dot") == 1 &&
                count(*fused, "algebra.exec.vector_length") == 3,
            "unexpected selected structure");
    auto dot = nth(*fused, "vector.dot");
    require(dot->getOperand(0) == function(*fused).getArgument(0) &&
                dot->getOperand(1) == function(*fused).getArgument(1),
            "wrong input slots");
    require(nth(*fused, "vector.length", 2)->getOperand(0) ==
                function(*fused).getArgument(2),
            "unused row not checked");
    require(nth(*fused, "control.require", 1)->isBeforeInBlock(dot),
            "guards did not precede dot");
    require(succeeded(mathematical::verifyVectorReductionsPreserved(
                *retained, *fused, retainedState, fusedState)),
            "independent fusion checker refused");
  });
  auto mutation = [&](StringRef label,
                      llvm::function_ref<void(ModuleOp)> change) {
    cases.run(label, [&] {
      auto candidate = copy(*fused);
      change(*candidate);
      require(succeeded(verify(*candidate)), "mutation must remain admitted");
      require(
          named("vector-reduction-correspondence",
                [&] {
                  return failed(mathematical::verifyVectorReductionsPreserved(
                      *retained, *candidate, retainedState, fusedState));
                }),
          "candidate mutation escaped");
    });
  };
  mutation("drop a guard",
           [&](ModuleOp m) { nth(m, "control.require")->erase(); });
  mutation("move guard after dot", [&](ModuleOp m) {
    nth(m, "control.require")->moveAfter(nth(m, "vector.dot"));
  });
  mutation("reverse guards", [&](ModuleOp m) {
    nth(m, "control.require")->moveAfter(nth(m, "control.require", 1));
  });
  mutation("replace ignored row", [&](ModuleOp m) {
    nth(m, "vector.length", 2)->setOperand(0, function(m).getArgument(0));
  });
  mutation("replace dot operand", [&](ModuleOp m) {
    nth(m, "vector.dot")->setOperand(1, function(m).getArgument(0));
  });
  mutation("replace result substitution", [&](ModuleOp m) {
    function(m).getBody().front().back().setOperand(0,
                                                    function(m).getArgument(3));
  });
  mutation("replace guard occurrence", [&](ModuleOp m) {
    nth(m, "control.require")
        ->setAttr("site", StringAttr::get(&context, "forged"));
  });
  mutation("replace dot occurrence", [&](ModuleOp m) {
    nth(m, "vector.dot")->setAttr("site", StringAttr::get(&context, "forged"));
  });
  mutation("replace binding with equivalent alias", [&](ModuleOp m) {
    nth(m, "vector.length")
        ->setAttr("binding", FlatSymbolRefAttr::get(&context, "length_alias"));
  });
  mutation("replace original declaration", [&](ModuleOp m) {
    auto helper = cast<func::FuncOp>(
        SymbolTable::lookupSymbolIn(&m.getBody()->front(), "formula"));
    helper.getBody().front().front().setOperand(1, helper.getArgument(0));
  });
  mutation("reorder retained declarations",
           [&](ModuleOp m) { function(m, "reduce")->moveAfter(function(m)); });
  mutation("add unrelated declaration", [&](ModuleOp m) {
    OpBuilder builder(&context);
    builder.setInsertionPointToStart(
        &m.getBody()->front().getRegion(0).front());
    local::OperationBindingOp::create(builder, m.getLoc(), "extra",
                                      "control.require",
                                      builder.getArrayAttr({}), "");
  });
  cases.run("retained call mutation", [&] {
    auto candidate = copy(*retained);
    function(*candidate).walk([](local::ApplyOp call) {
      call->setOperand(1, call->getOperand(0));
    });
    require(succeeded(verify(*candidate)), "retained mutation not admitted");
    require(named("algorithm-correspondence",
                  [&] {
                    return failed(
                        protocol::verifyStagedAlgorithmExpansionPreserved(
                            *source, *candidate, Phase::RetainMaps, initial,
                            retainedState));
                  }),
            "retained mutation escaped");
  });
  cases.run("Finish requires all preparation declarations realized", [&] {
    auto candidate = copy(*retained);
    State state = retainedState;
    require(named("algorithm-call-symbol",
                  [&] {
                    return failed(protocol::expandAlgorithms(
                        *candidate, Phase::Finish, state));
                  }),
            "Finish retained a preparation declaration");
  });
  cases.run("fusion requires retained state", [&] {
    auto candidate = copy(*source);
    State state;
    require(named("vector-reduction-correspondence",
                  [&] {
                    return failed(
                        mathematical::fuseVectorReductions(*candidate, state));
                  }),
            "fusion accepted unprepared state");
  });
  cases.run("phase cannot reset budgets", [&] {
    auto candidate = copy(*retained);
    State state = retainedState;
    require(named("algorithm-expansion-stage",
                  [&] {
                    return failed(protocol::expandAlgorithms(
                        *candidate, Phase::RetainMaps, state));
                  }),
            "repeated RetainMaps reset the state");
  });
  auto baseline = [&](StringRef text) {
    auto legacy = parse(text), staged = copy(*legacy);
    require(succeeded(mathematical::expandMapRealizations(*legacy)) &&
                succeeded(protocol::expandAlgorithms(*legacy)),
            "legacy sequence refused");
    State state;
    retain(*staged, state);
    finish(*staged, state);
    require(OperationEquivalence::isEquivalentTo(
                *legacy, *staged, OperationEquivalence::IgnoreLocations),
            "staged operations or sites differ from baseline");
    auto prepared = parse(text);
    run(*prepared, protocol::createPrepareProtocolPass(false));
    require(OperationEquivalence::isEquivalentTo(
                *legacy, *prepared, OperationEquivalence::IgnoreLocations),
            "default preparation path differs from baseline");
  };
  cases.run("baseline canonical identity", [&] { baseline(fixture); });
  std::string longText =
      edit(fixture, "logical_origin=[\"work\",[]]",
           "logical_origin=[\"" + std::string(100, 'w') + "\",[]]");
  const std::string wrapper =
      " local.func @outer(%a:!V,%b:!V,%c:!V,%s:!F)->!F attributes "
      "{logical_origin=[\"outer\",[]]} {\n"
      " %r = local.apply @work(%a,%b,%c,%s) {site=\"" +
      std::string(80, 'c') +
      "\"} : (!V,!V,!V,!F)->!F\n local.return %r : !F\n }\n";
  longText =
      edit(longText, " \"protocol.func\"", wrapper + " \"protocol.func\"");
  cases.run("long hashed origin identity", [&] { baseline(longText); });
  cases.run("fused hashed guards keep full paths", [&] {
    auto candidate = parse(longText);
    State state;
    retain(*candidate, state);
    require(succeeded(mathematical::fuseVectorReductions(*candidate, state)),
            "long fusion refused");
    require(succeeded(mathematical::expandMapRealizations(*candidate)),
            "long maps refused");
    std::vector<protocol::AlgorithmOrigin> origins;
    require(succeeded(protocol::expandAlgorithms(*candidate, Phase::Finish,
                                                 state, &origins)),
            "long Finish refused");
    auto guard = nth(*candidate, "control.require", 0, "outer");
    auto site = guard->getAttrOfType<StringAttr>("site").getValue();
    require(site.starts_with("lc_h_"), "expected hashed site");
    require(llvm::any_of(origins,
                         [&](const auto &origin) {
                           return origin.function == "outer" &&
                                  origin.site == site &&
                                  origin.originalSite == "map_3" &&
                                  origin.path == protocol::Assignments{
                                                     {std::string(80, 'c'),
                                                      std::string(100, 'w')},
                                                     {"map", "formula"}};
                         }),
            "full original path lost or nested encoding used");
  });
  auto selection = [&](StringRef label, StringRef text, bool selected) {
    cases.run(label, [&] {
      auto candidate = parse(text);
      State state;
      retain(*candidate, state);
      require(succeeded(mathematical::fuseVectorReductions(*candidate, state)),
              "selection refused");
      require(count(*candidate, "algebra.exec.vector_dot") ==
                  unsigned(selected),
              "wrong selection");
      finish(*candidate, state);
      require(count(*candidate, "local.apply") == 0, "Finish left an apply");
    });
  };
  selection("square",
            edit(fixture, "field_multiply\"(%a,%b)", "field_multiply\"(%a,%a)"),
            true);
  selection("direct native sum",
            edit(fixture,
                 "%r = local.apply @reduce(%v) {site=\"reduce\"} : (!V)->!F",
                 "%r = \"algebra.exec.vector_sum\"(%v) "
                 "{binding=@sum,parameters=[],site=\"reduce\"} : (!V)->!F"),
            true);
  selection("addition nonmatch", edit(fixture, "field_multiply", "field_add"),
            false);
  selection("scalar factor nonmatch",
            edit(fixture, "field_multiply\"(%a,%b)", "field_multiply\"(%a,%s)"),
            false);
  selection(
      "intervening ordered work",
      edit(
          fixture, "   %r = local.apply @reduce",
          R"(   %stop = "algebra.exec.field_constant"() {binding=@constant,parameters=["1"],site="intervening"} : ()->!F
   %r = local.apply @reduce)"),
      false);
  selection(
      "additional map use",
      edit(
          fixture, "   %r = local.apply @reduce",
          R"(   %ignored = "algebra.exec.vector_sum"(%v) {binding=@sum,parameters=[],site="additional"} : (!V)->!F
   %r = local.apply @reduce)"),
      false);
  selection(
      "custom reducer spelling is not a contract",
      edit(fixture,
           "\"algebra.exec.vector_sum\"(%v) "
           "{binding=@sum,parameters=[],site=\"sum\"} : (!V)->!F",
           "\"algebra.exec.field_constant\"() "
           "{binding=@constant,parameters=[\"1\"],site=\"sum\"} : ()->!F"),
      false);
  cases.run("row slots after a scalar input", [&] {
    auto text = edit(edit(fixture, "[true, true, true, false]",
                          "[false, true, true, false]"),
                     "field_multiply\"(%a,%b)", "field_multiply\"(%b,%unused)");
    auto replaceAll = [&](StringRef from, StringRef to) {
      size_t pos = 0;
      while ((pos = text.find(from.str(), pos)) != std::string::npos) {
        text.replace(pos, from.size(), to.str());
        pos += to.size();
      }
    };
    replaceAll("(!V,!V,!V,!F)", "(!F,!V,!V,!F)");
    replaceAll("%a:!V", "%a:!F");
    auto candidate = parse(text);
    State state;
    retain(*candidate, state);
    require(succeeded(mathematical::fuseVectorReductions(*candidate, state)),
            "shifted slots refused");
    auto dot = nth(*candidate, "vector.dot");
    require(dot->getOperand(0) == function(*candidate).getArgument(1) &&
                dot->getOperand(1) == function(*candidate).getArgument(2) &&
                count(*candidate, "algebra.exec.vector_length") == 2,
            "row slot identity lost");
    finish(*candidate, state);
  });
  cases.run("unsupported dead scalar work refused before optimization", [&] {
    auto text = edit(
        fixture, "   %dead =",
        "   %bad = \"algebra.field_equal\"(%a,%b) : (!F,!F)->i1\n   %dead =");
    require(named("algebra-map-formula",
                  [&] { return !parseSourceString<ModuleOp>(text, &context); }),
            "dead unsupported work escaped admission");
  });

  const std::string regions = edit(fixture, " \"protocol.func\"", R"(
 local.func @branches(%go:i1,%a:!V,%b:!V,%c:!V,%s:!F)->!F attributes {logical_origin=["branches",[]]} {
   %r = "local.if"(%go,%a,%b,%c,%s) ({ ^left(%x:!V,%y:!V,%z:!V,%t:!F):
     %v = local.apply @work(%x,%y,%z,%t) {site="left"} : (!V,!V,!V,!F)->!F
     "local.yield"(%v) : (!F)->()
   }, { ^right(%x:!V,%y:!V,%z:!V,%t:!F):
     %v = local.apply @work(%x,%y,%z,%t) {site="right"} : (!V,!V,!V,!F)->!F
     "local.yield"(%v) : (!F)->()
   }) {site="branch"} : (i1,!V,!V,!V,!F)->!F
   local.return %r : !F
 }
 local.func @loop(%lo:ui64,%hi:ui64,%a:!V,%b:!V,%c:!V,%s:!F)->!F attributes {logical_origin=["loop",[]]} {
   %r = "local.for"(%lo,%hi,%s,%a,%b,%c) ({ ^body(%i:ui64,%acc:!F,%x:!V,%y:!V,%z:!V):
     %v = local.apply @work(%x,%y,%z,%acc) {site="step"} : (!V,!V,!V,!F)->!F
     "local.yield"(%v,%x,%y,%z) : (!F,!V,!V,!V)->()
   }) {site="loop"} : (ui64,ui64,!F,!V,!V,!V)->!F
   local.return %r : !F
 }
 local.func @cross(%go:i1,%a:!V,%b:!V,%c:!V,%s:!F)->!F attributes {logical_origin=["cross",[]]} {
   %v = local.apply @mapped(%a,%b,%c,%s) {site="map"} : (!V,!V,!V,!F)->!V
   %r = "local.if"(%go,%v) ({ ^left(%x:!V):
     %q = local.apply @reduce(%x) {site="left"} : (!V)->!F
     "local.yield"(%q) : (!F)->()
   }, { ^right(%x:!V):
     %q = local.apply @reduce(%x) {site="right"} : (!V)->!F
     "local.yield"(%q) : (!F)->()
   }) {site="branch"} : (i1,!V)->!F
   local.return %r : !F
 }
 "protocol.func")");
  cases.run("baseline through branches and loops", [&] { baseline(regions); });
  cases.run("retain and fuse within regions without crossing them", [&] {
    auto candidate = parse(regions);
    State state;
    retain(*candidate, state);
    require(count(*candidate, "local.apply", "branches") == 2 &&
                count(*candidate, "local.apply", "loop") == 1,
            "maps not retained inside regions");
    require(succeeded(mathematical::fuseVectorReductions(*candidate, state)),
            "region fusion refused");
    require(count(*candidate, "algebra.exec.vector_dot", "branches") == 2 &&
                count(*candidate, "algebra.exec.vector_dot", "loop") == 1 &&
                count(*candidate, "algebra.exec.vector_dot", "cross") == 0,
            "region boundary or selected count changed");
    finish(*candidate, state);
  });
  const std::string empty = edit(fixture, " \"protocol.func\"", R"(
 "local.binding"() {sym_name="index",contract="index.constant",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="fill",contract="vector.fill",arguments=["koala-bear"],implementation=""} : ()->()
 local.func @empty(%s:!F)->!F attributes {logical_origin=["empty",[]]} {
   %zero = "algebra.exec.index_constant"() {binding=@index,parameters=["0"],site="zero"} : ()->ui64
   %a = "algebra.exec.vector_fill"(%s,%zero) {binding=@fill,parameters=[],site="first"} : (!F,ui64)->!V
   %b = "algebra.exec.vector_fill"(%s,%zero) {binding=@fill,parameters=[],site="second"} : (!F,ui64)->!V
   %r = local.apply @work(%a,%b,%a,%s) {site="reduce"} : (!V,!V,!V,!F)->!F
   local.return %r : !F
 }
 "protocol.func")");
  cases.run("empty rows preserve evaluations and all guards", [&] {
    auto candidate = parse(empty);
    State state;
    retain(*candidate, state);
    require(succeeded(mathematical::fuseVectorReductions(*candidate, state)),
            "empty fusion refused");
    require(count(*candidate, "algebra.exec.vector_fill", "empty") == 2 &&
                count(*candidate, "algebra.exec.vector_length", "empty") == 3 &&
                count(*candidate, "algebra.exec.vector_dot", "empty") == 1,
            "empty shortcut removed work");
    finish(*candidate, state);
  });
  cases.run("Finish checker rejects changed guard origin", [&] {
    auto maps = copy(*retained);
    require(succeeded(mathematical::expandMapRealizations(*maps)),
            "map realization refused");
    auto final = copy(*maps);
    State state = retainedState;
    require(succeeded(protocol::expandAlgorithms(*final, Phase::Finish, state)),
            "Finish refused");
    nth(*final, "control.require")
        ->setAttr("site", StringAttr::get(&context, "changed"));
    require(
        named("algorithm-correspondence",
              [&] {
                return failed(protocol::verifyStagedAlgorithmExpansionPreserved(
                    *maps, *final, Phase::Finish, retainedState, state));
              }),
        "Finish checker accepted changed site");
  });

  cases.run("cumulative expansion budget cannot reset between phases", [&] {
    std::string wrapper = " local.func @many(%a:!V,%b:!V,%c:!V,%s:!F)->!F "
                          "attributes {logical_origin=[\"many\",[]]} {\n";
    for (unsigned i = 0; i < 2000; ++i)
      wrapper += " %r" + std::to_string(i) +
                 " = local.apply @work(%a,%b,%c,%s) {site=\"call_" +
                 std::to_string(i) + "\"} : (!V,!V,!V,!F)->!F\n";
    wrapper += " local.return %r1999 : !F\n }\n";
    auto source = parse(
        edit(fixture, " \"protocol.func\"", wrapper + " \"protocol.func\""));
    auto legacy = copy(*source);
    require(succeeded(mathematical::expandMapRealizations(*legacy)) &&
                succeeded(protocol::expandAlgorithms(*legacy)),
            "baseline budget unexpectedly refused");
    State state;
    retain(*source, state);
    require(succeeded(mathematical::expandMapRealizations(*source)),
            "budget map realization refused");
    auto before = copy(*source);
    require(named("algorithm-expansion-limit",
                  [&] {
                    return failed(protocol::expandAlgorithms(
                        *source, Phase::Finish, state));
                  }),
            "Finish reset the overall work budget");
    require(OperationEquivalence::isEquivalentTo(
                *source, *before, OperationEquivalence::IgnoreLocations),
            "failed expansion changed the subject");
  });
  auto chain = [&](unsigned wrappers, unsigned repeated, unsigned width) {
    std::string definitions;
    for (unsigned i = 0; i < wrappers; ++i) {
      auto name = "layer" + std::to_string(i);
      auto callee = i ? "layer" + std::to_string(i - 1) : "work";
      auto origin = width ? std::string(width, 'x') + std::to_string(i) : name;
      definitions +=
          " local.func @" + name +
          "(%a:!V,%b:!V,%c:!V,%s:!F)->!F attributes {logical_origin=[\"" +
          origin + "\",[]]} {\n";
      for (unsigned j = 0; j < (i + 1 == wrappers ? repeated : 1); ++j)
        definitions += " %r" + std::to_string(j) + " = local.apply @" + callee +
                       "(%a,%b,%c,%s) {site=\"call" + std::to_string(j) +
                       "\"} : (!V,!V,!V,!F)->!F\n";
      definitions += " local.return %r0 : !F\n }\n";
    }
    return edit(fixture, " \"protocol.func\"",
                definitions + " \"protocol.func\"");
  };
  cases.run("call depth at the boundary survives both phases", [&] {
    auto candidate = parse(chain(63, 1, 0));
    State state;
    retain(*candidate, state);
    finish(*candidate, state);
  });
  cases.run("call depth beyond the boundary refuses", [&] {
    require(named("interactive-call-depth",
                  [&] {
                    return !parseSourceString<ModuleOp>(chain(64, 1, 0),
                                                        &context);
                  }),
            "excess call depth admitted");
  });
  cases.run("origin bytes are cumulative across stages", [&] {
    // The retained call sites fit, while the seven guards for each map would
    // exceed the remaining origin capacity. Long paths are kept in full even
    // when the visible occurrence uses a digest.
    std::string pairs;
    for (unsigned i = 0; i < 60; ++i) {
      auto n = std::to_string(i);
      pairs += "   %v" + n + " = local.apply @mapped(%a,%b,%c,%s) {site=\"map" +
               n + "\"} : (!V,!V,!V,!F)->!V\n";
      pairs += "   %r" + n + " = local.apply @reduce(%v" + n +
               ") {site=\"reduce" + n + "\"} : (!V)->!F\n";
    }
    auto text =
        edit(chain(30, 1, 120),
             "   %v = local.apply @mapped(%a,%b,%c,%s) {site=\"map\"} : "
             "(!V,!V,!V,!F)->!V\n"
             "   %r = local.apply @reduce(%v) {site=\"reduce\"} : (!V)->!F\n"
             "   local.return %r : !F",
             pairs + "   local.return %r59 : !F");
    auto candidate = parse(text);
    State state;
    retain(*candidate, state);
    require(succeeded(mathematical::expandMapRealizations(*candidate)),
            "origin fixture map refused");
    require(named("algorithm-origin-limit",
                  [&] {
                    return failed(protocol::expandAlgorithms(
                        *candidate, Phase::Finish, state));
                  }),
            "Finish forgot retained origin charges");
  });
  cases.run("expanded scalar depth cannot be optimized away", [&] {
    std::string operations;
    for (unsigned i = 0; i < 1024; ++i)
      operations += "   %d" + std::to_string(i) + " = \"algebra.field_add\"(" +
                    (i ? "%d" + std::to_string(i - 1) : "%a") +
                    ",%a) : (!F,!F)->!F\n";
    auto candidate =
        parse(edit(edit(fixture, "   %dead =", operations + "   %dead ="),
                   "func.return %p : !F", "func.return %d1023 : !F"));
    State state;
    require(named("algebra-map-formula",
                  [&] {
                    return failed(protocol::expandAlgorithms(
                        *candidate, Phase::RetainMaps, state));
                  }),
            "deep scalar formula escaped admission");
  });

  cases.run("preparation interface alone does not permit retention", [&] {
    auto text = edit(
        fixture,
        " algebra.map_realize @mapped = @formula [true, true, true, false] : "
        "(!V,!V,!V,!F)->!V",
        R"( func.func private @vectors(%a:!V,%b:!V,%c:!V,%s:!F)->!V { func.return %a : !V }
 local.realize @mapped = @vectors : (!V,!V,!V,!F)->!V)");
    auto candidate = parse(text);
    State state;
    require(named("algorithm-call-symbol",
                  [&] {
                    return failed(protocol::expandAlgorithms(
                        *candidate, Phase::RetainMaps, state));
                  }),
            "arbitrary preparation call was retained atomically");
  });
  cases.run("formula arena size includes unused supported scalar work", [&] {
    std::string operations;
    for (unsigned i = 0; i < 65534; ++i)
      operations += "   %d" + std::to_string(i) +
                    " = \"algebra.field_add\"(%a,%b) : (!F,!F)->!F\n";
    auto candidate =
        parse(edit(fixture, "   %dead =", operations + "   %dead ="));
    State state;
    require(named("algebra-map-formula",
                  [&] {
                    return failed(protocol::expandAlgorithms(
                        *candidate, Phase::RetainMaps, state));
                  }),
            "unused supported work escaped the formula size limit");
  });

  for (bool simplify : {false, true})
    cases.run(simplify ? "fused projected pipeline"
                       : "fusion independent of simplification",
              [&] {
                auto candidate = parse(fixture);
                run(*candidate,
                    protocol::createProjectProtocolPass(simplify, true));
                run(*candidate, protocol::createEliminatePolynomialsPass());
                run(*candidate, protocol::createLowerMathPass());
                require(count(*candidate, "algebra.exec.vector_dot") == 1,
                        "fusion not forwarded");
                run(*candidate, protocol::createSelectPhysicalPass());
                bool preparation = false;
                candidate->walk([&](Operation *op) {
                  preparation |= isa<local::ApplyOp, algebra::MapRealizeOp>(op);
                });
                require(!preparation, "preparation escaped to physical output");
              });
  for (StringRef name : {"iterated-sumcheck.mlir", "helper-realization.mlir",
                         "map-realization.mlir"})
    cases.run("enabled preparation preserves ordinary recipes: " + name, [&] {
      auto original = parseSourceFile<ModuleOp>(
          std::string(ZKC_MATH_FIXTURES) + "/" + name.str(), &context);
      require(bool(original), "ordinary recipe fixture refused");
      auto enabled = copy(*original);
      run(*original, protocol::createPrepareProtocolPass(false));
      run(*enabled, protocol::createPrepareProtocolPass(false, true));
      require(OperationEquivalence::isEquivalentTo(
                  *original, *enabled, OperationEquivalence::IgnoreLocations),
              "nonmatching recipe changed under enabled preparation");
    });
  return cases.result();
}
