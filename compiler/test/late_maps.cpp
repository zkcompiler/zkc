#include "../lib/Conversion/Bindings.h"
#include "../lib/Target/PhysicalPlan.h"
#include "../lib/Transforms/AlgorithmSupport.h"
#include "../lib/Transforms/MapOccurrence.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Kernel.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;

namespace {
constexpr llvm::StringLiteral fixture = R"mlir(
!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
module { "protocol.module"() ({
 func.func private @square(%x:!F)->!F {
   %r = "algebra.field_multiply"(%x,%x) : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @formula(%a:!F,%b:!F,%unused:!F,%s:!F)->!F {
   %sq = func.call @square(%a) : (!F)->!F
   %m = "algebra.field_multiply"(%sq,%b) : (!F,!F)->!F
   %r = "algebra.field_add"(%m,%s) : (!F,!F)->!F
   %dead = func.call @square(%unused) : (!F)->!F
   func.return %r : !F
 }
 func.func private @unrelated(%x:!F)->!F { func.return %x : !F }
 algebra.map_realize @mapped = @formula [true, true, true, false] : (!V,!V,!V,!F)->!V
 local.func @identity(%x:!F)->!F attributes {logical_origin=["identity",[]]} {
   local.return %x : !F
 }
 local.func @through(%a:!V,%b:!V,%c:!V,%s:!F)->!V attributes {logical_origin=["through",[]]} {
   %r = local.apply @mapped(%a,%b,%c,%s) {site="map"} : (!V,!V,!V,!F)->!V
   local.return %r : !V
 }
 local.func @work(%a:!V,%b:!V,%c:!V,%s:!F)->!V attributes {logical_origin=["work",[]]} {
   %t = local.apply @identity(%s) {site="ordinary"} : (!F)->!F
   %r = local.apply @through(%a,%b,%c,%t) {site="nested"} : (!V,!V,!V,!F)->!V
   local.return %r : !V
 }
 local.func @dormant(%a:!V,%b:!V,%c:!V,%s:!F)->!V attributes {logical_origin=["dormant",[]]} {
   %r = local.apply @mapped(%a,%b,%c,%s) {site="unused_map"} : (!V,!V,!V,!F)->!V
   local.return %r : !V
 }
 "protocol.func"() ({
 ^entry(%a:!V,%b:!V,%c:!V,%s:!F):
   %p = "protocol.local_call"(%a,%b,%c,%s) {callee=@work,role="P",site="p_work"} : (!V,!V,!V,!F)->!V
   %q = "protocol.local_call"(%a,%b,%c,%s) {callee=@work,role="Q",site="q_work"} : (!V,!V,!V,!F)->!V
   "protocol.return"(%p,%q) : (!V,!V)->()
 }) {sym_name="main",function_type=(!V,!V,!V,!F)->(!V,!V),roles=["P","Q"],input_roles=[["P","Q"],["P","Q"],["P","Q"],["P","Q"]],output_roles=[["P"],["Q"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";

constexpr llvm::StringLiteral reductionFixture = R"mlir(
!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
module { "protocol.module"() ({
 "local.binding"() {sym_name="sum",contract="vector.sum",arguments=["koala-bear"],implementation=""} : ()->()
 func.func private @formula(%a:!F,%b:!F,%unused:!F)->!F {
   %r = "algebra.field_multiply"(%a,%b) : (!F,!F)->!F
   func.return %r : !F
 }
 algebra.map_realize @mapped = @formula [true, true, true] : (!V,!V,!V)->!V
 local.func @work(%a:!V,%b:!V,%unused:!V)->!F attributes {logical_origin=["work",[]]} {
   %v = local.apply @mapped(%a,%b,%unused) {site="map"} : (!V,!V,!V)->!V
   %r = "algebra.exec.vector_sum"(%v) {binding=@sum,parameters=[],site="sum"} : (!V)->!F
   local.return %r : !F
 }
 "protocol.func"() ({ ^entry(%a:!V,%b:!V,%c:!V):
   %r = "protocol.local_call"(%a,%b,%c) {callee=@work,role="P",site="work"} : (!V,!V,!V)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!V,!V)->!F,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";

protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
bool same(Operation *a, Operation *b) {
  return OperationEquivalence::isEquivalentTo(
      a, b, OperationEquivalence::IgnoreLocations);
}
OwningOpRef<ModuleOp> copy(ModuleOp source) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
}
template <typename Op> Op symbol(ModuleOp module, llvm::StringRef name) {
  auto op =
      dyn_cast_or_null<Op>(SymbolTable::lookupSymbolIn(unit(module), name));
  require(bool(op), "missing symbol " + name);
  return op;
}
OwningOpRef<ModuleOp> project(ModuleOp source,
                              MathematicalSelectionPolicy policy = {}) {
  auto result = copy(source);
  PassManager manager(source.getContext());
  manager.addPass(protocol::createProjectProtocolPass(false, policy));
  require(succeeded(manager.run(*result)), "map projection failed");
  return result;
}
OwningOpRef<ModuleOp> executable(ModuleOp source,
                                 MathematicalSelectionPolicy policy = {}) {
  auto result = project(source, policy);
  unit(*result).setProfile(protocol_ir::Profile::Exec);
  require(succeeded(verify(*result)), "internal map execution subject refused");
  return result;
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
SmallVector<Operation *> callsOf(ModuleOp module, llvm::StringRef contract) {
  SymbolTable symbols(unit(module));
  SmallVector<Operation *> result;
  module.walk([&](Operation *op) {
    auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto binding =
        reference
            ? symbols.lookup<local::OperationBindingOp>(reference.getValue())
            : local::OperationBindingOp();
    if (binding && binding.getContract() == contract)
      result.push_back(op);
  });
  return result;
}
void duplicatePair(ModuleOp module) {
  auto work = symbol<local::FuncOp>(module, "work");
  auto first = *work.getBody().front().getOps<local::ApplyOp>().begin();
  OpBuilder builder(&work.getBody().front().back());
  IRMapping values;
  auto *second = builder.clone(*first.getOperation(), values);
  auto *sum = builder.clone(*first->getNextNode(), values);
  second->setAttr("site", builder.getStringAttr("second_map"));
  sum->setAttr("site", builder.getStringAttr("second_sum"));
  work.getBody().front().back().setOperand(0, sum->getResult(0));
}
void noResidualNumerics(ModuleOp module) {
  module.walk([&](Operation *op) {
    require(!isa<kernel::ModuleOp, kernel::CallOp, algebra::MapRealizeOp,
                 local::ApplyOp, func::FuncOp>(op),
            "final Local subject retained source numerical work");
  });
}

bool named(MLIRContext &context, llvm::StringRef code,
           llvm::function_ref<LogicalResult()> action) {
  bool seen = false;
  ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &diagnostic) {
    seen |= namesIdentifier(diagnostic.str(), code);
    return success();
  });
  return failed(action()) && seen;
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry, MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("ordinary algorithms finish while exact map closures remain", [&] {
    auto source = parseSourceString<ModuleOp>(fixture, &context);
    require(bool(source), "fixture refused");
    auto original = copy(*source);
    auto prepared = mathematical::prepareProtocol(*source, false);
    require(bool(prepared) && same(*source, *original),
            "preparation changed its immutable source");
    for (llvm::StringRef name : {"formula", "square"})
      require(same(symbol<func::FuncOp>(*source, name),
                   symbol<func::FuncOp>(*prepared, name)),
              "retained helper changed");
    require(bool(symbol<algebra::MapRealizeOp>(*prepared, "mapped")),
            "map was eagerly realized");
    unsigned requests = 0;
    prepared->walk([&](local::ApplyOp call) {
      require(call.getCallee() == "mapped", "ordinary call survived Finish");
      ++requests;
    });
    require(requests == 3, "nested or dormant map request was lost");
  });
  cases.run(
      "projection retains one exact closure for both participant roles", [&] {
        auto source = parseSourceString<ModuleOp>(fixture, &context);
        require(bool(source), "fixture refused");
        auto projected = project(*source);
        require(!SymbolTable::lookupSymbolIn(unit(*projected), "unrelated"),
                "projection copied an unrelated scalar helper");
        for (llvm::StringRef name : {"formula", "square"})
          require(same(symbol<func::FuncOp>(*source, name),
                       symbol<func::FuncOp>(*projected, name)),
                  "projection changed the scalar closure");
        unsigned roles = 0;
        for (auto participant : unit(*projected)
                                    .getBody()
                                    .front()
                                    .getOps<protocol_ir::ParticipantOp>()) {
          unsigned calls = 0;
          participant.walk([&](local::CallOp call) {
            require(call.getCallee() == "work",
                    "role call lost its Local owner");
            ++calls;
          });
          require(calls == 1, "participant lost its ordered map invocation");
          ++roles;
        }
        require(roles == 2 && succeeded(verify(*projected)),
                "two-role map projection was not admitted");
      });
  cases.run("retained transitive helper tampering fails preservation", [&] {
    auto source = parseSourceString<ModuleOp>(fixture, &context);
    require(bool(source), "fixture refused");
    auto before = project(*source);
    auto after = copy(*before);
    auto helper = symbol<func::FuncOp>(*after, "square");
    helper.getBody().front().back().setOperand(0, helper.getArgument(0));
    require(succeeded(verify(*after)), "tampering fixture is not well formed");
    require(named(context, "native-local-policy",
                  [&] {
                    return mathematical::verifyAuthoredLocalsPreserved(
                        unit(*before), unit(*after));
                  }),
            "changed reachable helper escaped the frozen Local subject");
  });
  cases.run("retention freezes unused helper work and call operands", [&] {
    auto source = parseSourceString<ModuleOp>(fixture, &context);
    require(bool(source), "fixture refused");
    auto before = project(*source);
    for (bool unusedWork : {true, false}) {
      auto after = copy(*before);
      if (unusedWork) {
        auto helper = symbol<func::FuncOp>(*after, "formula");
        func::CallOp dead;
        for (auto call : helper.getBody().front().getOps<func::CallOp>())
          if (call->use_empty())
            dead = call;
        require(bool(dead), "missing unused helper work");
        dead.erase();
      } else {
        auto function = symbol<local::FuncOp>(*after, "through");
        auto call =
            *function.getBody().front().getOps<local::ApplyOp>().begin();
        auto first = call->getOperand(0), second = call->getOperand(1);
        call->setOperand(0, second);
        call->setOperand(1, first);
      }
      require(succeeded(verify(*after)),
              "tampering fixture is not well formed");
      require(named(context, "native-local-policy",
                    [&] {
                      return mathematical::verifyAuthoredLocalsPreserved(
                          unit(*before), unit(*after));
                    }),
              "unused work or same-typed call operands escaped freezing");
    }
  });
  cases.run("retention freezes the exact map helper reference", [&] {
    auto source = parseSourceString<ModuleOp>(fixture, &context);
    require(bool(source), "fixture refused");
    auto before = project(*source);
    auto after = copy(*before);
    auto helper = symbol<func::FuncOp>(*after, "formula");
    OpBuilder builder(helper);
    auto alternate = cast<func::FuncOp>(builder.clone(*helper.getOperation()));
    alternate.setSymName("alternate");
    symbol<algebra::MapRealizeOp>(*after, "mapped")
        ->setAttr("helper", FlatSymbolRefAttr::get(&context, "alternate"));
    require(succeeded(verify(*after)), "replacement helper fixture refused");
    require(named(context, "native-local-policy",
                  [&] {
                    return mathematical::verifyAuthoredLocalsPreserved(
                        unit(*before), unit(*after));
                  }),
            "equivalent but different helper reference escaped freezing");
  });
  cases.run(
      "logical retention still rejects open and cyclic helper closures", [&] {
        auto source = parseSourceString<ModuleOp>(fixture, &context);
        require(bool(source), "fixture refused");
        auto original = executable(*source);
        for (bool cycle : {false, true}) {
          auto candidate = copy(*original);
          auto helper = symbol<func::FuncOp>(*candidate, "square");
          if (cycle) {
            OpBuilder builder(&helper.getBody().front().back());
            OperationState state(helper.getLoc(), "func.call");
            state.addAttribute("callee",
                               FlatSymbolRefAttr::get(&context, "square"));
            state.addOperands(helper.getArgument(0));
            state.addTypes(helper.getArgument(0).getType());
            auto call = builder.create(state);
            helper.getBody().front().back().setOperand(0, call->getResult(0));
          } else {
            helper.setPublic();
          }
          require(named(context, "mathematical-formation",
                        [&] {
                          return mathematical::verifyNativeLocals(
                              unit(*candidate), false);
                        }),
                  "logical retention bypassed helper scope or cycle admission");
        }
      });
  cases.run("unknown and ordinary dormant calls cannot enter logical execution",
            [&] {
              auto source = parseSourceString<ModuleOp>(fixture, &context);
              require(bool(source), "fixture refused");
              for (llvm::StringRef callee : {"missing", "through"}) {
                auto candidate = executable(*source);
                auto dormant = symbol<local::FuncOp>(*candidate, "dormant");
                auto call =
                    *dormant.getBody().front().getOps<local::ApplyOp>().begin();
                call.setCallee(callee);
                require(named(context, "native-local-policy",
                              [&] {
                                return mathematical::verifyNativeLocals(
                                    unit(*candidate), false);
                              }),
                        "dormant non-map call was accepted");
              }
            });
  cases.run("logical requests cannot be published even when dormant", [&] {
    auto source = parseSourceString<ModuleOp>(fixture, &context);
    require(bool(source), "fixture refused");
    auto candidate = executable(*source);
    refuses(protocol::readExecutionModel(*candidate), "algebra-map-context");
    unit(*candidate).setProfile(protocol_ir::Profile::Physical);
    require(named(context, "native-local-policy",
                  [&] {
                    return mathematical::verifyNativeLocals(unit(*candidate),
                                                            false);
                  }),
            "physical admission accepted a residual map request");
  });
  cases.run("eventual map realization checks unused rowwise inputs first", [&] {
    auto source = parseSourceString<ModuleOp>(fixture, &context);
    require(bool(source), "fixture refused");
    auto prepared = mathematical::prepareProtocol(*source, false);
    require(bool(prepared), "preparation failed");
    auto retained = copy(*prepared);
    require(
        succeeded(mathematical::expandMapRealizations(
            *prepared, nullptr, nullptr, NumericalExpressionMode::VectorOnly)),
        "retained map could not use its ordinary realization");
    auto function = symbol<local::FuncOp>(*prepared, "mapped");
    SymbolTable symbols(unit(*prepared));
    std::vector<std::string> prefix;
    SmallVector<Value> guarded;
    for (auto &op : function.getBody().front()) {
      auto reference = op.getAttrOfType<FlatSymbolRefAttr>("binding");
      auto binding =
          reference
              ? symbols.lookup<local::OperationBindingOp>(reference.getValue())
              : local::OperationBindingOp();
      require(bool(binding), "guard prefix ended early");
      prefix.push_back(binding.getContract().str());
      if (binding.getContract() == "vector.length")
        guarded.push_back(op.getOperand(0));
      if (prefix.size() == 7)
        break;
    }
    require(prefix == std::vector<std::string>{"vector.length", "vector.length",
                                               "index.equal", "control.require",
                                               "vector.length", "index.equal",
                                               "control.require"} &&
                llvm::equal(guarded, function.getArguments().take_front(3)),
            "map arithmetic preceded an ordered shape guard or omitted an "
            "unused input");
    auto tampered = copy(*prepared);
    auto changed = symbol<local::FuncOp>(*tampered, "mapped");
    unsigned lengths = 0;
    for (auto &op : changed.getBody().front()) {
      auto reference = op.getAttrOfType<FlatSymbolRefAttr>("binding");
      auto binding =
          reference
              ? symbols.lookup<local::OperationBindingOp>(reference.getValue())
              : local::OperationBindingOp();
      if (binding && binding.getContract() == "vector.length" &&
          ++lengths == 3) {
        op.setOperand(0, changed.getArgument(0));
        break;
      }
    }
    require(
        named(context, "algebra-map-correspondence",
              [&] {
                return mathematical::verifyMapRealizationsPreserved(*retained,
                                                                    *tampered);
              }),
        "eventual realization reader accepted an omitted unused-input guard");
    auto reordered = copy(*prepared);
    auto reorderedFunction = symbol<local::FuncOp>(*reordered, "mapped");
    SmallVector<Operation *> lengthsInOrder;
    reorderedFunction.walk(
        [&](algebra::VectorLengthOp op) { lengthsInOrder.push_back(op); });
    require(lengthsInOrder.size() == 3, "missing row guard controls");
    lengthsInOrder[2]->moveBefore(lengthsInOrder[1]);
    require(succeeded(verify(*reordered)),
            "reordered fixture is not well formed");
    require(named(context, "algebra-map-correspondence",
                  [&] {
                    return mathematical::verifyMapRealizationsPreserved(
                        *retained, *reordered);
                  }),
            "eventual realization reader accepted reordered input checks");
    require(succeeded(protocol::expandAlgorithms(*prepared)),
            "ordinary execution expansion could not consume the realized map");
    prepared->walk([&](Operation *op) {
      require(!isa<algebra::MapRealizeOp, local::ApplyOp>(op),
              "realized map left an unresolved execution request");
    });
  });
  for (auto profile :
       {protocol_ir::Profile::Protocol, protocol_ir::Profile::Participant,
        protocol_ir::Profile::Exec}) {
    cases.run(
        "late fusion checks policy and payload in profile " +
            std::to_string(unsigned(profile)),
        [&] {
          auto source = parseSourceString<ModuleOp>(reductionFixture, &context);
          require(bool(source), "reduction fixture refused");
          for (bool enabled : {false, true}) {
            MathematicalSelectionPolicy policy;
            policy.vectorReductionFusion = enabled;
            auto retained =
                mathematical::rewriteLocalAlgorithms(*source, policy);
            require(bool(retained), "map/reduction retention failed");
            auto subject = profile == protocol_ir::Profile::Protocol
                               ? copy(*retained)
                               : project(*retained, policy);
            unit(*subject).setProfile(profile);
            require(succeeded(verify(*subject)), "logical subject refused");
            auto original = copy(*subject);
            protocol::AlgorithmExpansionState allowance;
            auto latePolicy = policy;
            latePolicy.vectorReductionFusion = true;
            auto fused = mathematical::fuseRetainedMapReductions(
                *subject, latePolicy, allowance);
            require(bool(fused) && same(*subject, *original) &&
                        succeeded(
                            mathematical::verifyRetainedMapReductionsPreserved(
                                *subject, *fused, latePolicy)),
                    "late fusion changed its source or failed independent "
                    "readback");
            unsigned requests = 0;
            symbol<local::FuncOp>(*fused, "work").walk([&](local::ApplyOp) {
              ++requests;
            });
            require(requests == (enabled ? 0u : 1u),
                    "late selection lost fusion or revived a disabled family");
            if (enabled) {
              auto work = symbol<local::FuncOp>(*fused, "work");
              for (auto &op : work.getBody().front())
                if (isa<algebra::VectorDotOp>(op)) {
                  op.setOperand(1, op.getOperand(0));
                  break;
                }
              require(named(context, "vector-reduction-correspondence",
                            [&] {
                              return mathematical::
                                  verifyRetainedMapReductionsPreserved(
                                      *subject, *fused, latePolicy);
                            }),
                      "late fusion reader accepted swapped payload wiring");
            }
          }
        });
  }
  cases.run("late choices distinguish two calls to one map declaration", [&] {
    auto source = parseSourceString<ModuleOp>(reductionFixture, &context);
    require(bool(source), "reduction fixture refused");
    auto work = symbol<local::FuncOp>(*source, "work");
    auto first = *work.getBody().front().getOps<local::ApplyOp>().begin();
    OpBuilder builder(&work.getBody().front().back());
    IRMapping values;
    auto *second = builder.clone(*first.getOperation(), values);
    auto *sum = builder.clone(*first->getNextNode(), values);
    second->setAttr("site", builder.getStringAttr("second_map"));
    sum->setAttr("site", builder.getStringAttr("second_sum"));
    work.getBody().front().back().setOperand(0, sum->getResult(0));
    MathematicalSelectionPolicy policy;
    policy.vectorReductionFusion = true;
    auto subject = project(*source, policy);
    unit(*subject).setProfile(protocol_ir::Profile::Exec);
    auto original = copy(*subject);
    protocol::AlgorithmExpansionState allowance;
    unsigned visits = 0;
    auto fused = mathematical::fuseRetainedMapReductions(
        *subject, policy, allowance, nullptr,
        [&](Operation *) { return visits++ == 0; });
    require(bool(fused) && visits == 2 && same(*subject, *original) &&
                succeeded(mathematical::verifyRetainedMapReductionsPreserved(
                    *subject, *fused, policy)),
            "per-call choice lost an occurrence or changed its subject");
    unsigned maps = 0, sums = 0, dots = 0;
    symbol<local::FuncOp>(*fused, "work").walk([&](Operation *op) {
      maps += isa<local::ApplyOp>(op);
      sums += isa<algebra::VectorSumOp>(op);
      dots += isa<algebra::VectorDotOp>(op);
    });
    require(maps == 1 && sums == 1 && dots == 1,
            "one choice replaced both uses of a shared declaration");
  });
  cases.run("late fusion preserves a pinned reduction binding", [&] {
    auto source = parseSourceString<ModuleOp>(reductionFixture, &context);
    require(bool(source), "reduction fixture refused");
    auto binding = symbol<local::OperationBindingOp>(*source, "sum");
    binding.setImplementation("plonky3/vector.sum");
    MathematicalSelectionPolicy policy;
    policy.vectorReductionFusion = true;
    auto subject = project(*source, policy);
    unit(*subject).setProfile(protocol_ir::Profile::Exec);
    protocol::AlgorithmExpansionState allowance;
    auto candidate =
        mathematical::fuseRetainedMapReductions(*subject, policy, allowance);
    require(bool(candidate) && same(*subject, *candidate),
            "late fusion erased an explicit implementation restriction");
  });
  for (bool checking : {false, true}) {
    cases.run(
        checking ? "failed late checking preserves cumulative allowances"
                 : "failed late emission preserves cumulative allowances",
        [&] {
          auto source = parseSourceString<ModuleOp>(reductionFixture, &context);
          require(bool(source), "reduction fixture refused");
          MathematicalSelectionPolicy policy;
          policy.vectorReductionFusion = true;
          auto subject = project(*source, policy);
          unit(*subject).setProfile(protocol_ir::Profile::Exec);
          auto original = copy(*subject);
          protocol::AlgorithmExpansionState allowance;
          protocol::detail::AlgorithmExpansionRecord limits;
          if (checking)
            limits.checkWork = 1;
          else
            limits.work = 1;
          protocol::detail::AlgorithmStateAccess::set(allowance, limits);
          ScopedDiagnosticHandler quiet(&context,
                                        [](Diagnostic &) { return success(); });
          for (unsigned attempt = 0; attempt != 2; ++attempt) {
            auto candidate = mathematical::fuseRetainedMapReductions(
                *subject, policy, allowance);
            const auto &remaining =
                protocol::detail::AlgorithmStateAccess::get(allowance);
            require(
                !candidate && same(*subject, *original) &&
                    (checking ? remaining.checkWork == 0 : remaining.work == 0),
                "failed late attempt replenished work or changed the source");
          }
        });
  }

  cases.run("map-only physical selection consumes the exact closure", [&] {
    auto source = parseSourceString<ModuleOp>(fixture, &context);
    require(bool(source), "map fixture refused");
    auto original = executable(*source);
    auto frozen = copy(*original);
    auto identities = target::physicalPlanOperations(*original);
    auto proposal = take(target::proposePhysical(*original));
    auto selected = take(proposal.cloneSelectedSubject(*original));
    noResidualNumerics(*selected);
    require(!callsOf(*selected, "numerical.map").empty() &&
                succeeded(mathematical::verifyNumericalLowering(*original,
                                                                *selected)),
            "map-only selection did not retain checked native occurrences");
    {
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      require(failed(kernel::verifyKernelLowering(*original, *selected)),
              "strict Kernel edge admitted a map rewrite");
    }
    callsOf(*selected, "numerical.map")
        .front()
        ->setOperand(
            2, callsOf(*selected, "numerical.map").front()->getOperand(1));
    auto retained = take(proposal.cloneSelectedSubject(*original));
    require(
        succeeded(mathematical::verifyNumericalLowering(*original, *retained)),
        "inspection clone mutated retained plan state");
    auto checked = take(target::validatePhysical(*original, proposal));
    auto physical = copy(*original);
    auto physicalProposal = take(target::proposePhysical(*physical));
    auto physicalChecked =
        take(target::validatePhysical(*physical, physicalProposal));
    if (auto error = protocol::materializePhysical(*physical, physicalChecked))
      throw std::runtime_error(llvm::toString(std::move(error)));
    require(succeeded(verify(*physical)), "map physical output refused");
    noResidualNumerics(*physical);
    auto correspondence =
        protocol::verifyPhysicalMaterialization(*original, *physical, checked);
    if (correspondence)
      throw std::runtime_error(llvm::toString(std::move(correspondence)));
    require(same(*original, *frozen) &&
                target::physicalPlanOperations(*original) == identities,
            "map transaction changed original source identities");
  });
  cases.run("dormant map declarations are admitted and consumed", [&] {
    auto source = parseSourceString<ModuleOp>(fixture, &context);
    require(bool(source), "fixture refused");
    auto original = executable(*source);
    SmallVector<local::ApplyOp> calls;
    original->walk([&](local::ApplyOp call) { calls.push_back(call); });
    for (auto call : calls) {
      call.getResult(0).replaceAllUsesWith(call.getInputs().front());
      call.erase();
    }
    require(succeeded(verify(*original)), "dormant fixture refused");
    auto plan = take(target::proposePhysical(*original));
    auto selected = take(plan.cloneSelectedSubject(*original));
    noResidualNumerics(*selected);
    take(target::validatePhysical(*original, plan));
  });
  const std::vector<std::vector<std::string>> missing = {
      {},
      {"vector.dot"},
      {"vector.dot", "numerical.sum"},
      {"vector.dot", "numerical.sum", "numerical.map"}};
  for (unsigned rung = 0; rung != missing.size(); ++rung) {
    cases.run(
        "retained map/sum capability alternative " + std::to_string(rung), [&] {
          auto source = parseSourceString<ModuleOp>(reductionFixture, &context);
          require(bool(source), "fixture refused");
          MathematicalSelectionPolicy policy;
          policy.vectorReductionFusion = true;
          auto original = executable(*source, policy);
          Withheld catalog(missing[rung]);
          auto plan = take(target::proposePhysical(*original, catalog));
          auto selected = take(plan.cloneSelectedSubject(*original));
          noResidualNumerics(*selected);
          require(
              callsOf(*selected, "vector.dot").size() == (rung == 0) &&
                  callsOf(*selected, "numerical.sum").size() == (rung == 1) &&
                  callsOf(*selected, "numerical.map").size() == (rung == 2) &&
                  callsOf(*selected, "vector.sum").size() == (rung >= 2),
              "capability ladder skipped or retained the wrong expression "
              "form");
          require(succeeded(mathematical::verifyNumericalLowering(*original,
                                                                  *selected)),
                  "selected capability rung failed actual readback");
          take(target::validatePhysical(*original, plan, catalog));
        });
  }
  cases.run("general Ring map/sum selects numerical sum", [&] {
    std::string text = reductionFixture.str();
    auto at = text.find("algebra.field_multiply");
    text.replace(at, std::string("algebra.field_multiply").size(),
                 "algebra.field_add");
    auto source = parseSourceString<ModuleOp>(text, &context);
    require(bool(source), "general sum fixture refused");
    MathematicalSelectionPolicy policy;
    policy.vectorReductionFusion = true;
    auto original = executable(*source, policy);
    auto plan = take(target::proposePhysical(*original));
    auto selected = take(plan.cloneSelectedSubject(*original));
    require(callsOf(*selected, "numerical.sum").size() == 1 &&
                callsOf(*selected, "vector.dot").empty(),
            "non-product Ring sum did not use its admitted expression");
    take(target::validatePhysical(*original, plan));
  });
  cases.run("native map/sum readback rejects an admitted wrong extent", [&] {
    auto source = parseSourceString<ModuleOp>(reductionFixture, &context);
    require(bool(source), "fixture refused");
    MathematicalSelectionPolicy policy;
    policy.vectorReductionFusion = true;
    auto original = executable(*source, policy);
    Withheld catalog({"vector.dot"});
    auto plan = take(target::proposePhysical(*original, catalog));
    auto selected = take(plan.cloneSelectedSubject(*original));
    auto sums = callsOf(*selected, "numerical.sum");
    auto lengths = callsOf(*selected, "vector.length");
    require(sums.size() == 1 && lengths.size() == 3,
            "native fused candidate lost its complete guard prefix");
    sums.front()->setOperand(0, lengths[2]->getResult(0));
    require(succeeded(verify(*selected)),
            "wrong-extent mutation must remain admitted");
    require(named(context, "numerical-lowering-correspondence",
                  [&] {
                    return mathematical::verifyNumericalLowering(*original,
                                                                 *selected);
                  }),
            "native sum reader accepted a different actual extent coordinate");
  });
  for (bool vectorOnly : {false, true}) {
    cases.run(
        vectorOnly ? "VectorOnly retains required vector maps"
                   : "persisted disabled fusion remains disabled",
        [&] {
          auto source = parseSourceString<ModuleOp>(reductionFixture, &context);
          require(bool(source), "fixture refused");
          auto original = executable(*source);
          target::PhysicalPlanOptions options;
          options.numericalPolicy.vectorReductionFusion = true;
          if (vectorOnly)
            options.numericalPolicy.numericalExpressions =
                NumericalExpressionMode::VectorOnly;
          auto plan = take(target::proposePhysical(
              *original, target::installedCandidates(), {}, options));
          auto selected = take(plan.cloneSelectedSubject(*original));
          require(
              callsOf(*selected, "vector.sum").size() == 1 &&
                  callsOf(*selected, "vector.dot").empty() &&
                  callsOf(*selected, "numerical.sum").empty() &&
                  callsOf(*selected, "numerical.map").size() ==
                      unsigned(!vectorOnly),
              "late fallback changed a disabled family or expression policy");
          take(target::validatePhysical(*original, plan));
        });
  }
  cases.run(
      "source and requested reduction pins independently restrict fusion", [&] {
        auto source = parseSourceString<ModuleOp>(reductionFixture, &context);
        require(bool(source), "fixture refused");
        MathematicalSelectionPolicy policy;
        policy.vectorReductionFusion = true;
        auto original = executable(*source, policy);
        auto unconstrained = take(target::proposePhysical(*original));
        auto fused = take(unconstrained.cloneSelectedSubject(*original));
        protocol::Assignments selections{{"sum", "plonky3/vector.sum"}};
        auto requested = take(target::proposePhysical(
            *original, target::installedCandidates(), selections));
        auto selected = take(requested.cloneSelectedSubject(*original));
        require(callsOf(*selected, "vector.sum").size() == 1 &&
                    callsOf(*selected, "numerical.map").size() == 1,
                "explicit sum request consumed the fixed operation");
        take(target::validatePhysical(*original, requested));
        require(named(context, "numerical-lowering-correspondence",
                      [&] {
                        return mathematical::verifyNumericalLowering(
                            *original, *fused, {}, selections);
                      }),
                "independent reader ignored original explicit requests");
        symbol<local::OperationBindingOp>(*original, "sum")
            .setImplementation("plonky3/vector.sum");
        auto pinned = take(target::proposePhysical(*original));
        auto pinnedSelected = take(pinned.cloneSelectedSubject(*original));
        require(callsOf(*pinnedSelected, "vector.sum").size() == 1,
                "source implementation pin disappeared into fusion");
        take(target::validatePhysical(*original, pinned));
      });
  cases.run(
      "program-capacity attribution changes one call to a shared map", [&] {
        auto source = parseSourceString<ModuleOp>(reductionFixture, &context);
        require(bool(source), "fixture refused");
        duplicatePair(*source);
        auto original = executable(*source);
        auto frozen = copy(*original);
        mathematical::RealizationWork work;
        target::PhysicalPlanOptions options;
        options.numericalWork = &work;
        unsigned visits = 0;
        options.programCapacity = [&](ModuleOp,
                                      const target::PhysicalPlan &plan)
            -> llvm::Expected<SmallVector<target::OperationIndex>> {
          if (++visits == 1)
            for (const auto &operation : plan.operations)
              if (operation.binding &&
                  plan.bindings[*operation.binding]
                          .binding.application.contract == "numerical.map")
                return SmallVector<target::OperationIndex>{operation.operation};
          return SmallVector<target::OperationIndex>{};
        };
        auto plan = take(target::proposePhysical(
            *original, target::installedCandidates(), {}, options));
        auto selected = take(plan.cloneSelectedSubject(*original));
        require(
            visits == 2 && callsOf(*selected, "numerical.map").size() == 1 &&
                callsOf(*selected, "vector.sum").size() == 2 &&
                work.discardedRecipeCopy < 1000000 && same(*original, *frozen),
            "one attributed refusal globally replaced a shared declaration");
        take(target::validatePhysical(*original, plan));
      });
  for (llvm::StringRef mutation :
       {"unused-guard", "guard-order", "extent", "formula-input", "extra-work",
        "result-use"}) {
    cases.run("final map reader rejects " + mutation, [&] {
      auto source = parseSourceString<ModuleOp>(fixture, &context);
      require(bool(source), "fixture refused");
      auto original = executable(*source);
      auto plan = take(target::proposePhysical(*original));
      auto selected = take(plan.cloneSelectedSubject(*original));
      auto maps = callsOf(*selected, "numerical.map");
      require(!maps.empty(), "missing native map");
      auto *map = maps.front();
      auto function = map->getParentOfType<local::FuncOp>();
      auto lengths = callsOf(*selected, "vector.length");
      SmallVector<Operation *> localLengths;
      for (auto *length : lengths)
        if (length->getParentOfType<local::FuncOp>() == function)
          localLengths.push_back(length);
      require(localLengths.size() >= 3, "missing guard inventory");
      if (mutation == "unused-guard")
        localLengths[2]->setOperand(0, localLengths[0]->getOperand(0));
      else if (mutation == "guard-order")
        localLengths[2]->moveBefore(localLengths[1]);
      else if (mutation == "extent")
        map->setOperand(0, localLengths[1]->getResult(0));
      else if (mutation == "formula-input")
        map->setOperand(2, map->getOperand(1));
      else if (mutation == "extra-work") {
        OpBuilder builder(map);
        auto *extra = builder.clone(*localLengths[0]);
        extra->setAttr("site", builder.getStringAttr("extra_length"));
      } else
        function.getBody().front().back().setOperand(0,
                                                     function.getArgument(0));
      require(succeeded(verify(*selected)),
              "negative mutation must remain admitted");
      require(named(context, "numerical-lowering-correspondence",
                    [&] {
                      return mathematical::verifyNumericalLowering(*original,
                                                                   *selected);
                    }),
              "final independent map reader accepted a semantic mutation");
    });
  }
  for (bool native : {false, true}) {
    cases.run(
        native ? "optional map checking exact and one-short boundaries"
               : "required vector checking exact and one-short boundaries",
        [&] {
          auto source = parseSourceString<ModuleOp>(reductionFixture, &context);
          require(bool(source), "fixture refused");
          auto original = executable(*source);
          target::PhysicalPlanOptions options;
          if (!native)
            options.numericalPolicy.numericalExpressions =
                NumericalExpressionMode::VectorOnly;
          auto plan = take(target::proposePhysical(
              *original, target::installedCandidates(), {}, options));
          auto selected = take(plan.cloneSelectedSubject(*original));
          mathematical::RealizationWork measured;
          mathematical::VerificationDecision outcome;
          require(succeeded(mathematical::verifyNumericalLowering(
                      *original, *selected, options.numericalPolicy, {},
                      &measured, &outcome)),
                  "map checking measurement refused");
          auto spent = 1000000 - (native ? measured.optionalMapChecking
                                         : measured.requiredMapChecking);
          require(spent > 0, "map checking did not charge work");
          mathematical::RealizationWork exact;
          (native ? exact.optionalMapChecking : exact.requiredMapChecking) =
              spent;
          require(succeeded(mathematical::verifyNumericalLowering(
                      *original, *selected, options.numericalPolicy, {}, &exact,
                      &outcome)) &&
                      (native ? exact.optionalMapChecking
                              : exact.requiredMapChecking) == 0,
                  "exact successful allowance was classified as exhausted");
          mathematical::RealizationWork shortWork;
          (native ? shortWork.optionalMapChecking
                  : shortWork.requiredMapChecking) = spent - 1;
          require(failed(mathematical::verifyNumericalLowering(
                      *original, *selected, options.numericalPolicy, {},
                      &shortWork, &outcome)) &&
                      outcome.outcome ==
                          (native ? mathematical::VerificationObservation::
                                        OptionalCapacity
                                  : mathematical::VerificationObservation::
                                        RequiredCapacity),
                  "one-short capacity lost its typed classification");
          if (native) {
            mathematical::RealizationWork retry;
            retry.optionalMapChecking = spent - 1;
            options.numericalWork = &retry;
            auto retried = take(target::proposePhysical(
                *original, target::installedCandidates(), {}, options));
            auto required = take(retried.cloneSelectedSubject(*original));
            require(callsOf(*required, "numerical.map").empty() &&
                        retry.requiredMapChecking < 1000000,
                    "optional exhaustion consumed the required vector reserve");
            take(target::validatePhysical(*original, retried));
          }
        });
  }
  for (uint64_t reserve : {uint64_t(0), uint64_t(1)}) {
    cases.run("map vector endpoint survives discard reserve " +
                  std::to_string(reserve),
              [&] {
                auto source = parseSourceString<ModuleOp>(fixture, &context);
                require(bool(source), "fixture refused");
                auto original = executable(*source);
                mathematical::RealizationWork work;
                work.matching.structural = 0;
                work.discardedRecipeCopy = reserve;
                work.discardedRecipeSiteBytes = reserve;
                target::PhysicalPlanOptions options;
                options.numericalWork = &work;
                auto plan = take(target::proposePhysical(
                    *original, target::installedCandidates(), {}, options));
                auto selected = take(plan.cloneSelectedSubject(*original));
                require(callsOf(*selected, "numerical.map").empty() &&
                            !callsOf(*selected, "vector.mul").empty() &&
                            work.requiredMapChecking < 1000000 &&
                            work.selectionBookkeeping < 1000000,
                        "optional reserve or matching exhaustion lost the "
                        "required vector endpoint");
                take(target::validatePhysical(*original, plan));
              });
  }
  for (bool native : {false, true}) {
    cases.run(
        native ? "identity map borrows before its unchanged sum"
               : "vector identity map borrows before its unchanged sum",
        [&] {
          auto source = parseSourceString<ModuleOp>(reductionFixture, &context);
          require(bool(source), "fixture refused");
          auto helper = symbol<func::FuncOp>(*source, "formula");
          helper.front().back().setOperand(0, helper.getArgument(0));
          auto original = executable(*source);
          target::PhysicalPlanOptions options;
          if (!native)
            options.numericalPolicy.numericalExpressions =
                NumericalExpressionMode::VectorOnly;
          auto plan = take(target::proposePhysical(
              *original, target::installedCandidates(), {}, options));
          auto selected = take(plan.cloneSelectedSubject(*original));
          auto sums = callsOf(*selected, "vector.sum");
          require(sums.size() == 1 &&
                      callsOf(*selected, "numerical.map").empty() &&
                      sums.front()->getOperand(0) ==
                          sums.front()
                              ->getParentOfType<local::FuncOp>()
                              .getArgument(0) &&
                      succeeded(mathematical::verifyNumericalLowering(
                          *original, *selected, options.numericalPolicy)),
                  "identity map consumed the suffix or invented a payload");
          take(target::validatePhysical(*original, plan));
        });
  }
  cases.run(
      "complete program preflight clone has an exact cumulative copy boundary",
      [&] {
        auto source = parseSourceString<ModuleOp>(reductionFixture, &context);
        require(bool(source), "fixture refused");
        auto original = executable(*source);
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
                  "preflight did not receive the complete private candidate");
          noResidualNumerics(complete);
          return SmallVector<target::OperationIndex>{};
        };
        auto measured = take(target::proposePhysical(
            *original, target::installedCandidates(), {}, options));
        uint64_t spent = 1000000 - copyWork;
        require(spent > 0 && callbacks == 1,
                "preflight measurement did not run once");
        copyWork = spent;
        callbacks = 0;
        take(target::proposePhysical(*original, target::installedCandidates(),
                                     {}, options));
        require(copyWork == 0 && callbacks == 1,
                "exact copy allowance did not include preflight");
        copyWork = spent - 1;
        callbacks = 0;
        refuses(target::proposePhysical(
                    *original, target::installedCandidates(), {}, options),
                "kernel-lowering");
        require(callbacks == 0,
                "capacity callback ran before its clone was charged");
      });
  cases.run(
      "required vector capability failure is terminal and transactional", [&] {
        auto source = parseSourceString<ModuleOp>(reductionFixture, &context);
        require(bool(source), "fixture refused");
        auto original = executable(*source);
        auto frozen = copy(*original);
        auto identities = target::physicalPlanOperations(*original);
        Withheld missing({"numerical.map", "vector.mul"});
        refuses(target::proposePhysical(*original, missing),
                "binding-implementation");
        require(same(*original, *frozen) &&
                    target::physicalPlanOperations(*original) == identities,
                "required vector refusal mutated original source");
      });
  return cases.result();
}
