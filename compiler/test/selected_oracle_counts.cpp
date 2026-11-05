#include "../lib/Compiler/NativeRequest.h"
#include "../lib/Target/Cpu/Run.h"
#include "../lib/Transforms/OracleCommonPlan.h"
#include "../lib/Transforms/OracleCommonRealization.h"
#include "../lib/Transforms/OracleNativeCommon.h"
#include "../lib/Transforms/OracleOwnedRealization.h"
#include "../lib/Transforms/RealizedProtocol.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Json.h"
#include "zkc/Target/Cpu/Stages.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Stages.h"
#include <iterator>
#include <optional>
#include <type_traits>

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;
namespace pir = protocol_ir;
static_assert(!std::is_default_constructible_v<OracleOwnedRealization>);
static_assert(!std::is_copy_constructible_v<OracleOwnedRealization>);
static_assert(!std::is_constructible_v<
              OracleOwnedRealization, OracleCommonRealization,
              OracleRealizationFacts, std::vector<OracleCommonAnalysis>,
              OracleRealizationPolicy, std::vector<OracleRootSelection>,
              OracleNativeSourcePreflight, OracleNativeSourcePreflight>);
namespace {
// Same actual selected source grammar as the parent's Oracle integration test.
// This file exercises public ownership and external-pair checking, without any
// synthetic count-equation map or inspection-clone admission authority.
std::string fixture(unsigned trips, bool outerRepeat) {
  std::string text = R"mlir(
#K = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear.ext4-binomial3">, 2:ui64]>
!F = !algebra.field<"koala-bear.ext4-binomial3">
!D = !data.field_vector<"koala-bear.ext4-binomial3">
!H = !protocol.oracle<#K>
!Choice = !data.variant<#data.identity<["atom", "OracleChoice"]>, [#data.alternative<"left", [ui64]>, #data.alternative<"right", [ui64]>]>
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%choice:!Choice,%data:!D,%other:!D,%position:ui64,%allow:i1):
)mlir";
  text += " %trips = \"data.index\"() {value=" + std::to_string(trips) +
          ":ui64} : ()->ui64\n";
  if (outerRepeat)
    text += R"mlir(
 "protocol.repeat"(%trips,%choice,%data,%other,%position,%allow,%trips) ({
 ^outer(%iteration:ui64,%choice:!Choice,%data:!D,%other:!D,%position:ui64,%allow:i1,%trips:ui64):
)mlir";
  text += R"mlir(
 %chosen = "protocol.branch"(%choice,%data,%other,%position,%trips,%allow) ({
 ^left(%payload:ui64,%rows:!D,%other_rows:!D,%fallback:ui64,%count:ui64,%go:i1):
   %two = "data.index"() {value=2:ui64} : ()->ui64
   %table = "protocol.oracle_send"(%rows,%two) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="left_table"} : (!D,ui64)->!H
   "protocol.repeat"(%count,%table,%payload) ({
   ^inner(%i:ui64,%handle:!H,%index:ui64):
     %answer = "protocol.oracle_query"(%handle,%index) {site="left_inner",owner="V"} : (!H,ui64)->!F
     "protocol.yield"() : ()->()
   }) {site="left_rounds",carried=0:i64,maximum=3:i64,roles=["P","V"],carried_roles=[]} : (ui64,!H,ui64)->()
   %first = "protocol.oracle_query"(%table,%payload) {site="left_first",owner="V"} : (!H,ui64)->!F
   %duplicate = "protocol.oracle_query"(%table,%payload) {site="left_duplicate",owner="V"} : (!H,ui64)->!F
   "protocol.guard"(%go) {owner="V",site="left_guard"} : (i1)->()
   "protocol.finish_if"(%go) {owner="V",site="left_finish"} : (i1)->()
   "protocol.yield"(%table) : (!H)->()
 }, {
 ^right(%payload:ui64,%rows:!D,%other_rows:!D,%fallback:ui64,%count:ui64,%go:i1):
   %two = "data.index"() {value=2:ui64} : ()->ui64
   %table = "protocol.oracle_send"(%other_rows,%two) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="right_table"} : (!D,ui64)->!H
   %answer = "protocol.oracle_query"(%table,%payload) {site="right_read",owner="V"} : (!H,ui64)->!F
   "protocol.yield"(%table) : (!H)->()
 }) {site="choose",roles=["P","V"],output_roles=[["P","V"]],alternatives=["left","right"]} : (!Choice,!D,!D,ui64,ui64,i1)->!H
 %after = "protocol.oracle_query"(%chosen,%position) {site="after_join",owner="V"} : (!H,ui64)->!F
)mlir";
  if (outerRepeat)
    text += R"mlir(
 "protocol.yield"() : ()->()
 }) {site="outer_rounds",carried=0:i64,maximum=3:i64,roles=["P","V"],carried_roles=[]} : (ui64,!Choice,!D,!D,ui64,i1,ui64)->()
)mlir";
  text += R"mlir(
 "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(!Choice,!D,!D,ui64,i1)->(),roles=["P","V"],input_roles=[["P","V"],["P"],["P"],["V"],["V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
  if (outerRepeat) {
    auto begin = text.find("^outer(");
    auto end = text.find("}) {site=\"outer_rounds\"", begin);
    auto body = text.substr(begin, end - begin);
    for (StringRef name :
         {"choice", "data", "other", "position", "allow", "trips"}) {
      auto from = ("%" + name).str();
      auto to = ("%outer_" + name).str();
      size_t at = 0;
      while ((at = body.find(from, at)) != std::string::npos) {
        body.replace(at, from.size(), to);
        at += to.size();
      }
    }
    text.replace(begin, end - begin, body);
  }
  return text;
}
OracleRealizationPolicy policy(OracleAuthentication authentication) {
  OracleRealizationPolicy result;
  result.roots = OracleTableRealization{
      "rows.merkle-keccak256.koala-bear.ext4-binomial3/0"};
  result.authentication = authentication;
  return result;
}
mathematical::RealizedProtocol
realized(MLIRContext &context, unsigned trips = 1, bool outer = false,
         OracleAuthentication authentication = OracleAuthentication::PerQuery) {
  auto source = parseSourceString<ModuleOp>(fixture(trips, outer), &context);
  require(bool(source), "source parse failed");
  auto prepared = mathematical::PreparedProtocol::prepare(*source);
  require(bool(prepared), "public preparation failed");
  return take(mathematical::RealizedProtocol::realize(std::move(*prepared),
                                                      policy(authentication)));
}
void checked(Error result) {
  if (result)
    throw std::runtime_error(toString(std::move(result)));
}
void refused(Error result) {
  require(bool(result), "mutated external pair was accepted");
  consumeError(std::move(result));
}
pir::LocalCallOp call(ModuleOp module, StringRef purpose,
                      unsigned ordinal = 0) {
  pir::LocalCallOp found;
  module.walk([&](pir::LocalCallOp op) {
    if (op.getSite().ends_with(purpose) && !found) {
      if (!ordinal)
        found = op;
      else
        --ordinal;
    }
  });
  require(bool(found), "missing actual generated call: " + purpose);
  return found;
}
pir::RepeatOp requests(ModuleOp module) {
  pir::RepeatOp found;
  module.walk([&](pir::RepeatOp op) {
    if (!found && op.getSite().ends_with("_query_requests"))
      found = op;
  });
  require(bool(found), "missing actual request Repeat");
  return found;
}
func::FuncOp callee(pir::LocalCallOp op) {
  auto result = SymbolTable::lookupNearestSymbolFrom<func::FuncOp>(
      op, op.getCalleeAttr());
  require(bool(result), "missing live count helper");
  return result;
}
runtime::BindingOp binding(exec::ApplyOp op) {
  auto result = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
      op, op.getBindingAttr());
  require(bool(result), "missing live native binding");
  return result;
}
exec::ApplyOp arithmetic(func::FuncOp helper, StringRef contract,
                         unsigned ordinal = 0) {
  exec::ApplyOp found;
  helper.walk([&](exec::ApplyOp op) {
    if (!found && binding(op).getContract() == contract) {
      if (!ordinal)
        found = op;
      else
        --ordinal;
    }
  });
  require(bool(found), "missing live arithmetic: " + contract);
  return found;
}
void lower(ModuleOp module) {
  PassManager execution(module.getContext());
  buildClosedExecutionPipeline(execution, false, false);
  require(succeeded(execution.run(module)), "Participant execution lowering");
  PassManager physical(module.getContext());
  PhysicalPipelineOptions options;
  buildPhysicalPipeline(physical, options);
  require(succeeded(physical.run(module)), "CPU physical lowering");
}
std::string virtualSource(unsigned children) {
  std::string body;
  for (unsigned i = 0; i < children; ++i)
    body += " %answer" + std::to_string(i) +
            " = \"protocol.oracle_query\"(%handle,%position) {site=\"child" +
            std::to_string(i) + "\"} : (!H,ui64)->!F\n";
  if (!children)
    body = " %answer0 = \"algebra.constant\"() "
           "{value=#algebra.literal<!F, 9:ui31>} : ()->!F\n";
  return std::string(R"mlir(
#K = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear">,2:ui64]>
!F = !algebra.field<"koala-bear">
!D = !data.field_vector<"koala-bear">
!H = !protocol.oracle<#K>
module { "protocol.module"() ({
 relation.declare @admissible {kind="external",key="test/count-view",revision="0",signature=(!D)->i1,purposes=["witness"]}
 "protocol.oracle"() ({ ^entry(%handle:!H,%position:ui64):
)mlir") + body +
         R"mlir(
 "protocol.oracle_yield"(%answer0) : (!F)->()
 }) {sym_name="view",function_type=(!H,ui64)->!F,kind=#K,shape_arguments={},shape_bounds={},admissibility=@admissible} : ()->()
 "protocol.func"() ({ ^entry(%choice:i1,%data:!D,%position:ui64):
 %two = "data.index"() {value=2:ui64} : ()->ui64
 %base = "protocol.oracle_send"(%data,%two) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="table"} : (!D,ui64)->!H
 %graph = "protocol.oracle_virtual"(%base) {callee=@view,holder="P",receivers=["V"]} : (!H)->!H
 "protocol.branch"(%choice,%graph,%position) ({ ^left(%handle:!H,%index:ui64):
 %answer = "protocol.oracle_query"(%handle,%index) {owner="V",site="read"} : (!H,ui64)->!F
 "protocol.yield"() : ()->()
 }, { ^right(%handle:!H,%index:ui64):
 "protocol.yield"() : ()->()
 }) {site="choose",roles=["P","V"],output_roles=[],alternatives=["then","else"]} : (i1,!H,ui64)->()
 "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(i1,!D,ui64)->(),roles=["P","V"],input_roles=[["P","V"],["P"],["P","V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
}
// Ordinary generic iteration keeps its joint runtime count rule. The two Local
// results really are independent opaque actions, even though both helpers
// return one. An authenticated query is a separate later source occurrence.
std::string genericCountSource(unsigned queries = 1, bool includeLoop = true) {
  std::string text = R"mlir(
#K = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear.ext4-binomial3">,2:ui64]>
!F = !algebra.field<"koala-bear.ext4-binomial3">
!D = !data.field_vector<"koala-bear.ext4-binomial3">
!H = !protocol.oracle<#K>
module { "protocol.module"() ({
 func.func private @one(%scope:!runtime.scope,%one:ui64)->!exec.outcome<(ui64)>
 attributes {no_inline,runtime.origin=["one",[]]} {
   %done = "exec.returned"(%one) : (ui64)->!exec.outcome<(ui64)>
   func.return %done : !exec.outcome<(ui64)>
 }
 "protocol.func"() ({ ^entry(%data:!D,%position:ui64):
)mlir";
  if (includeLoop)
    text += R"mlir(
 %one = "data.index"() {value=1:ui64} : ()->ui64
 %p = "protocol.local_call"(%one) {callee=@one,role="P",site="p_count"} : (ui64)->ui64
 %v = "protocol.local_call"(%one) {callee=@one,role="V",site="v_count"} : (ui64)->ui64
 %count = "protocol.assemble_roles"(%p,%v) {roles=["P","V"]} : (ui64,ui64)->ui64
 "protocol.repeat"(%count) ({ ^body(%iteration:ui64):
   "protocol.yield"() : ()->()
 }) {site="ordinary",carried=0:i64,maximum=1:i64,roles=["P","V"],carried_roles=[]} : (ui64)->()
)mlir";
  text += R"mlir(
 %two = "data.index"() {value=2:ui64} : ()->ui64
 %table = "protocol.oracle_send"(%data,%two) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="table"} : (!D,ui64)->!H
)mlir";
  for (unsigned i = 0; i < queries; ++i)
    text += " %answer" + std::to_string(i) +
            " = \"protocol.oracle_query\"(%table,%position) "
            "{owner=\"V\",site=\"read_" +
            std::to_string(i) + "\"} : (!H,ui64)->!F\n";
  text += R"mlir(
 "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(!D,ui64)->(),roles=["P","V"],input_roles=[["P"],["V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
  return text;
}
pir::MathematicalOp entry(ModuleOp module, StringRef name = "main") {
  auto unit = cast<pir::ProtocolModuleOp>(module.getBody()->front());
  return cast<pir::MathematicalOp>(SymbolTable::lookupSymbolIn(unit, name));
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler diagnostics(&context,
                                      [](Diagnostic &) { return success(); });
  Cases cases;
  for (auto authentication :
       {OracleAuthentication::PerQuery, OracleAuthentication::AtomicBlocks}) {
    cases.run(
        Twine(
            "branch-free opaque generic count keeps runtime policy, policy=") +
            Twine(unsigned(authentication)),
        [&] {
          auto source =
              parseSourceString<ModuleOp>(genericCountSource(2), &context);
          require(bool(source) && succeeded(admitStage(*source)),
                  "ordinary opaque generic count was not admitted");
          uint64_t remaining = 1000000;
          facts::Work strictSource(remaining);
          refuses(deriveCommonControlRequirements(entry(*source), strictSource),
                  "common-control-provenance");
          auto selected = policy(authentication);
          auto actual = take(emitOracleRealization(*source, selected));
          auto checkedFacts =
              take(checkOracleRealization(*source, actual, selected));
          require(checkedFacts.sourceRequirements.empty() &&
                      checkedFacts.candidateRequirements.empty(),
                  "equations added an unrelated generic input obligation");
          require(bool(requests(*actual.module)),
                  "missing separate authenticated query");
          // Public raw admission retains its ordinary branch-free selection
          // policy. An explicit full derivation still refuses these opaque
          // Local counts.
          require(
              succeeded(admitStage(*actual.module)),
              "raw generic admission acquired a stronger static loop policy");
          remaining = 1000000;
          facts::Work strictCandidate(remaining);
          refuses(deriveCommonControlRequirements(entry(*actual.module),
                                                  strictCandidate),
                  "common-control-provenance");
          auto publication =
              take(exportOracleRealization(*source, actual, selected));
          checked(checkOracleRealization(*source, *actual.module,
                                         publication.bytes, selected));
          // Raw formation succeeds after a live helper mutation; only the
          // complete pair check may establish the generated equation.
          auto divide = arithmetic(
              callee(call(*actual.module, "_query_round_count")), "index.div");
          divide->setOperand(2, divide->getOperand(1));
          require(succeeded(admitStage(*actual.module)),
                  "generic mutation formation");
          auto changed = checkOracleRealization(*source, actual, selected);
          require(!changed,
                  "equation-only traversal omitted the actual helper check");
          consumeError(changed.takeError());
        });
    cases.run(
        Twine("interior query lookup exhaustion in emission and reader, "
              "policy=") +
            Twine(unsigned(authentication)),
        [&] {
          auto source = parseSourceString<ModuleOp>(
              genericCountSource(1, false), &context);
          require(bool(source), "interior exhaustion source parse");
          auto selected = policy(authentication);
          auto actual = take(emitOracleRealization(*source, selected));
          auto selections =
              take(resolveOracleRealizationSelection(*source, selected));
          auto requirements =
              take(oracleRequirements(*source, "main", selections));
          const auto &item = actual.entries.front();
          require(!item.remotes.empty(), "no authenticated remote query");
          auto materialize = [&](ArrayRef<OracleCommonController> controllers,
                                 OracleNativeWork &work) {
            return materializeOracleCommon(
                *source, "main", requirements, controllers, item.allocators,
                item.merkle, authentication, item.remotes, item.batches, &work);
          };
          auto read = [&](ArrayRef<OracleCommonController> controllers,
                          OracleNativeWork &work) {
            return readOracleCommon(*source, *actual.module, "main",
                                    requirements, controllers, item.allocators,
                                    item.merkle, authentication, item.remotes,
                                    item.batches, &work);
          };
          // This scratch model fails immediately after the second source lookup
          // and its role reconstruction, before reading the first count call.
          // Measure the actual generated prefix, then subtract the exact lookup
          // and role charges for this direct-send fixture to locate lookup
          // entry.
          auto missingCount = item.controllers;
          missingCount[item.remotes.front().receiver].body.leafCounts.clear();
          auto exercise = [&](auto &&operation) {
            OracleNativeWork successful;
            auto plan = take(operation(item.controllers, successful));
            uint64_t used = 1000000 - successful.remaining;
            OracleNativeWork prefix;
            refuses(operation(missingCount, prefix),
                    "oracle-common-communication-profile");
            uint64_t cutoff = 1000000 - prefix.remaining;
            require(plan.queryBlocks.size() == 1 &&
                        plan.queryBlocks.front().queries.size() == 1,
                    "expected one actual authenticated query prefix");
            const auto &coordinate = plan.queryBlocks.front().queries.front();
            require(coordinate.size() == 1,
                    "prefix is not a direct entry query");
            auto &body = entry(*source).getBody().front();
            auto query = dyn_cast<pir::OracleQueryOp>(
                &*std::next(body.begin(), coordinate.front()));
            auto send = query ? query.getHandle()
                                    .template getDefiningOp<pir::OracleSendOp>()
                              : pir::OracleSendOp{};
            require(bool(send), "prefix handle is not the actual direct send");
            auto roles = entry(*source).getRoles();
            uint64_t roleCost =
                1 + roles.size() + roles.size() * send.getReceivers().size();
            for (Attribute attribute : roles) {
              auto role = cast<StringAttr>(attribute).getValue();
              if (role == send.getSender() ||
                  is_contained(send.getReceivers(), attribute))
                roleCost += role.size();
            }
            uint64_t lookupCost = 1 + uint64_t(coordinate.front());
            require(!prefix.exhausted && cutoff > roleCost + lookupCost + 64,
                    "query lookup prefix was not strictly interior");
            uint64_t lookupStart = cutoff - roleCost - lookupCost;
            require(lookupCost <= 8 && lookupStart + 8 < used,
                    "73 quotas do not span the actual repeated lookup");
            // Include allowances immediately before, within and after the
            // actual repeated lookup charge, using the measured generated
            // prefix above.
            for (uint64_t allowance = lookupStart - 64;
                 allowance <= lookupStart + 8; ++allowance) {
              OracleNativeWork limited;
              limited.remaining = allowance;
              refuses(operation(item.controllers, limited),
                      "oracle-common-limit");
              require(
                  limited.exhausted && limited.remaining == 0 &&
                      !limited.charge(0),
                  "interior refusal reset or published an exhausted allowance");
            }
            OracleNativeWork fresh;
            take(operation(item.controllers, fresh));
          };
          exercise(materialize);
          exercise(read);
        });
  }
  for (bool throughCaller : {false, true})
    cases.run(
        Twine("ordinary selected closure keeps full opaque-count refusal, "
              "caller=") +
            Twine(unsigned(throughCaller)),
        [&] {
          auto text = genericCountSource();
          auto replace = [&](StringRef from, StringRef to) {
            auto at = text.find(from.str());
            require(at != std::string::npos,
                    "missing selected-closure fixture slot");
            text.replace(at, from.size(), to.str());
          };
          replace("^entry(%data:!D,%position:ui64):",
                  "^entry(%data:!D,%position:ui64,%choice:i1):");
          replace("function_type=(!D,ui64)->()",
                  "function_type=(!D,ui64,i1)->()");
          replace("input_roles=[[\"P\"],[\"V\"]]",
                  "input_roles=[[\"P\"],[\"V\"],[\"P\",\"V\"]]");
          std::string branch = R"mlir(
 "protocol.branch"(%choice) ({ "protocol.yield"() : ()->()
 }, { "protocol.yield"() : ()->()
 }) {site="selected",roles=["P","V"],output_roles=[],alternatives=["then","else"]} : (i1)->()
)mlir";
          if (throughCaller) {
            std::string helper =
                "\"protocol.func\"() ({ ^entry(%choice:i1):\n" + branch +
                R"mlir(
 "protocol.return"() : ()->()
 }) {sym_name="selected_helper",function_type=(i1)->(),roles=["P","V"],input_roles=[["P","V"]],output_roles=[]} : ()->()
)mlir";
            replace("\"protocol.func\"", helper + "\"protocol.func\"");
            // Match the main return after inserting the helper's return.
            auto at = text.rfind(" \"protocol.return\"()");
            text.insert(
                at,
                " protocol.apply @selected_helper(%choice) "
                "{site=\"selected_call\",roles=[\"P\",\"V\"]} : (i1)->()\n");
          } else
            replace(" \"protocol.return\"()",
                    branch + " \"protocol.return\"()");
          auto source = parseSourceString<ModuleOp>(text, &context);
          require(bool(source) &&
                      succeeded(zkc::detail::verifyStageStructure(*source)),
                  "selected opaque-count countercontrol lost structure");
          require(failed(admitStage(*source)),
                  "selected definition or caller lost its full count demands");
        });
  for (auto authentication :
       {OracleAuthentication::PerQuery, OracleAuthentication::AtomicBlocks})
    for (bool outer : {false, true})
      for (unsigned trips : {0u, 1u, 3u})
        cases.run(
            Twine("paired owner and external record, policy=") +
                Twine(unsigned(authentication)) +
                ", outer=" + Twine(unsigned(outer)) + ", trips=" + Twine(trips),
            [&] {
              auto owner = realized(context, trips, outer, authentication);
              auto original = owner.preparedSnapshot();
              auto candidate = owner.candidateSnapshot();
              require(bool(original) && bool(candidate),
                      "inspection snapshots");
              require(succeeded(verify(*candidate)),
                      "candidate MLIR formation");
              require(failed(admitStage(*candidate)),
                      "standalone candidate acquired count agreement");
              checked(checkOracleRealization(*original, *candidate,
                                             owner.realizationRecord(),
                                             policy(authentication)));
              for (bool simplify : {false, true}) {
                auto participant = owner.project(simplify);
                require(bool(participant) &&
                            succeeded(admitStage(*participant)),
                        "owner projection did not retain admission");
              }
              auto observation = take(owner.observationSnapshot());
              require(!observation.dataExchanges.empty(),
                      "owner observation lost opening-request associations");
            });

  for (auto authentication :
       {OracleAuthentication::PerQuery, OracleAuthentication::AtomicBlocks})
    cases.run(
        Twine("owned publication equals fresh independent export, policy=") +
            Twine(unsigned(authentication)),
        [&] {
          auto owner = realized(context, 1, true, authentication);
          auto original = owner.preparedSnapshot();
          auto selected = policy(authentication);
          require(bool(original), "missing complete retained original");
          auto raw = take(emitOracleRealization(*original, selected));
          auto fresh = take(exportOracleRealization(*original, raw, selected));
          require(equalNaturalJson(fresh.data, owner.realizationData()),
                  "retained independent analyses changed publication fields");
          checked(checkOracleRealization(*original, *raw.module,
                                         owner.realizationRecord(), selected));
          // Export never accepts prior emission/publication as authority after
          // a mutation, even though the raw associations and source are
          // unchanged.
          auto divide = arithmetic(
              callee(call(*raw.module, "_query_round_count")), "index.div");
          divide->setOperand(2, divide->getOperand(1));
          refuses(exportOracleRealization(*original, raw, selected),
                  "oracle-common-body");
          require(bool(owner.project(false)),
                  "raw export mutation changed owner");
        });

  auto mutation = [&](StringRef name, llvm::function_ref<void(ModuleOp)> mutate,
                      OracleAuthentication authentication =
                          OracleAuthentication::PerQuery) {
    cases.run(name, [&] {
      auto owner = realized(context, 1, false, authentication);
      auto original = owner.preparedSnapshot();
      auto candidate = owner.candidateSnapshot();
      mutate(*candidate);
      refused(checkOracleRealization(*original, *candidate,
                                     owner.realizationRecord(),
                                     policy(authentication)));
      require(bool(owner.project(false)), "inspection mutation changed owner");
    });
  };
  mutation(
      "round count cannot use another leaf result",
      [&](ModuleOp module) {
        pir::LocalCallOp round;
        module.walk([&](pir::LocalCallOp op) {
          if (!round && op.getSite().ends_with("_query_round_count") &&
              op.getInputs().size() > 1)
            round = op;
        });
        require(bool(round), "missing ordered duplicate-query block");
        // Both are dominating, same-role, equal-typed leaf results. Formation
        // cannot establish which exact query occurrence this count consumes.
        round->setOperand(0, round.getInputs()[1]);
        require(succeeded(verify(module)),
                "leaf substitution broke MLIR formation");
      },
      OracleAuthentication::AtomicBlocks);
  mutation("rounds must use the actual division", [&](ModuleOp module) {
    auto divide =
        arithmetic(callee(call(module, "_query_round_count")), "index.div");
    // exec.apply has a scope operand first; replace width by the numerator.
    require(divide.getNumOperands() == 3, "division operand shape");
    divide->setOperand(2, divide->getOperand(1));
  });
  mutation("guard must inspect the actual total", [&](ModuleOp module) {
    auto guard =
        arithmetic(callee(call(module, "_query_round_count")), "index.less");
    guard->setOperand(1, guard->getOperand(2));
  });
  mutation("sum preserves ordered query multiplicity", [&](ModuleOp module) {
    auto sum =
        arithmetic(callee(call(module, "_query_round_count")), "index.add");
    sum->setOperand(2, sum->getOperand(1));
  });
  mutation("allocation stores the actual construction leaf count",
           [&](ModuleOp module) {
             auto allocation = call(module, "_allocate");
             require(allocation.getNumOperands() >= 3 &&
                         allocation.getOperand(1).getType() ==
                             allocation.getOperand(2).getType(),
                     "missing distinct row/count allocation fields");
             allocation->setOperand(2, allocation.getOperand(1));
           });
  mutation("the actual normal-return count result is bound",
           [&](ModuleOp module) {
             auto helper = callee(call(module, "_query_round_count"));
             exec::ReturnOp returned;
             helper.walk([&](exec::ReturnOp op) { returned = op; });
             require(bool(returned) && returned.getNumOperands() == 1,
                     "missing actual count return");
             returned->setOperand(0, helper.getArgument(1));
           });
  mutation("assembly components cannot exchange roles", [&](ModuleOp module) {
    auto assembly =
        requests(module).getInputs()[0].getDefiningOp<pir::AssembleRolesOp>();
    require(bool(assembly) && assembly.getNumOperands() == 2,
            "paired selector assembly");
    Value first = assembly.getOperand(0);
    assembly->setOperand(0, assembly.getOperand(1));
    assembly->setOperand(1, first);
  });
  mutation("maximum cannot stand in for the actual count",
           [&](ModuleOp module) {
             auto loop = requests(module);
             auto count = call(module, "_query_round_count");
             loop->setOperand(0, count.getResult(0));
           });
  mutation("generated Repeat maximum is bound", [&](ModuleOp module) {
    auto loop = requests(module);
    loop->setAttr("maximum", Builder(&context).getI64IntegerAttr(17));
  });
  mutation("zero capacity cannot replace the checked positive width",
           [&](ModuleOp module) {
             auto width = arithmetic(callee(call(module, "_query_round_count")),
                                     "index.constant", 3);
             auto literal = cast<IntegerAttr>(width.getParameters()[0]);
             Builder builder(&context);
             width->setAttr("parameters",
                            builder.getArrayAttr({builder.getIntegerAttr(
                                literal.getType(), 0)}));
           });
  mutation(
      "ceiling offset cannot introduce word overflow", [&](ModuleOp module) {
        auto offset = arithmetic(callee(call(module, "_query_round_count")),
                                 "index.constant", 2);
        auto literal = cast<IntegerAttr>(offset.getParameters()[0]);
        Builder builder(&context);
        offset->setAttr("parameters",
                        builder.getArrayAttr(
                            {builder.getIntegerAttr(literal.getType(), -1)}));
      });
  mutation("sibling branch arms cannot exchange count occurrences",
           [&](ModuleOp module) {
             pir::BranchOp branch;
             module.walk([&](pir::BranchOp op) {
               if (!branch)
                 branch = op;
             });
             require(bool(branch) && branch->getNumRegions() == 2,
                     "missing source-associated branch");
             Region first;
             first.takeBody(branch->getRegion(0));
             branch->getRegion(0).takeBody(branch->getRegion(1));
             branch->getRegion(1).takeBody(first);
           });
  mutation(
      "leaf count must capture its actual immutable store",
      [&](ModuleOp module) {
        pir::LocalCallOp count;
        module.walk([&](pir::LocalCallOp op) {
          if (!count && op.getSite().ends_with("_query_count") &&
              isa<pir::BranchOp>(op->getParentOp()))
            count = op;
        });
        require(bool(count), "missing count after branch-local construction");
        auto &body = *count->getBlock();
        for (Value operand : count.getInputs().drop_front()) {
          for (auto argument : body.getArguments())
            if (argument.getType() == operand.getType() &&
                argument != operand) {
              for (auto &use : count->getOpOperands())
                if (use.get() == operand) {
                  use.set(argument);
                  return;
                }
            }
        }
        throw std::runtime_error("fixture lacks a distinct incoming store");
      });
  mutation("a correct unused helper cannot rescue a changed live helper",
           [&](ModuleOp module) {
             auto helper = callee(call(module, "_query_round_count"));
             auto *unused = helper->clone();
             SymbolTable::setSymbolName(unused, "unused_correct_count");
             helper->getBlock()->push_back(unused);
             auto divide = arithmetic(helper, "index.div");
             divide->setOperand(2, divide->getOperand(1));
           });
  mutation("source count call role is exact", [&](ModuleOp module) {
    auto round = call(module, "_query_round_count");
    round->setAttr("role", Builder(&context).getStringAttr("P"));
  });

  cases.run("retained source selector requirements are not discharged", [&] {
    auto source = parseSourceString<ModuleOp>(fixture(3, true), &context);
    auto actual = take(
        emitOracleRealization(*source, policy(OracleAuthentication::PerQuery)));
    auto facts = take(checkOracleRealization(
        *source, actual, policy(OracleAuthentication::PerQuery)));
    bool selector = false;
    for (const auto &requirement : facts.sourceRequirements)
      selector |= requirement.control &&
                  isa<pir::BranchOp>(requirement.control) &&
                  requirement.tagOnly && requirement.components.size() == 2;
    require(selector, "original tag obligation disappeared during lowering");
  });
  cases.run("source coordinates and enclosing counts remain requirements", [&] {
    auto source = parseSourceString<ModuleOp>(R"mlir(
#K = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear.ext4-binomial3">,2:ui64]>
!F = !algebra.field<"koala-bear.ext4-binomial3">
!D = !data.field_vector<"koala-bear.ext4-binomial3">
!H = !protocol.oracle<#K>
!S = !protocol.oracle_sequence<#K,2>
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%data:!D,%rounds:ui64,%position:ui64):
 %two = "data.index"() {value=2:ui64} : ()->ui64
 %table = "protocol.oracle_send"(%data,%two) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="table"} : (!D,ui64)->!H
 %empty = "protocol.oracle_sequence_empty"() : ()->!S
 %one = "protocol.oracle_sequence_append"(%empty,%table) {roles=["P","V"],site="append"} : (!S,!H)->!S
 %selected = "protocol.oracle_sequence_at"(%one,%position) {roles=["P","V"],site="select"} : (!S,ui64)->!H
 "protocol.repeat"(%rounds,%selected,%position) ({ ^body(%iteration:ui64,%handle:!H,%index:ui64):
 %answer = "protocol.oracle_query"(%handle,%index) {owner="V",site="read"} : (!H,ui64)->!F
 "protocol.yield"() : ()->()
 }) {site="outer",carried=0:i64,maximum=3:i64,roles=["P","V"],carried_roles=[]} : (ui64,!H,ui64)->()
 "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(!D,ui64,ui64)->(),roles=["P","V"],input_roles=[["P"],["P","V"],["P","V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir",
                                              &context);
    require(bool(source), "source coordinate/count parse");
    auto selected = policy(OracleAuthentication::PerQuery);
    auto actual = take(emitOracleRealization(*source, selected));
    auto facts = take(checkOracleRealization(*source, actual, selected));
    bool coordinate = false, count = false;
    for (const auto &requirement : facts.sourceRequirements) {
      if (!requirement.control || requirement.components.size() != 2 ||
          requirement.tagOnly || requirement.extentAxis)
        continue;
      coordinate |= isa<pir::OracleSequenceAtOp>(requirement.control) &&
                    requirement.components[0].input == 2 &&
                    requirement.components[1].input == 2;
      count |= isa<pir::RepeatOp>(requirement.control) &&
               requirement.components[0].input == 1 &&
               requirement.components[1].input == 1;
    }
    require(coordinate && count, "source observations were discharged or lost");
    bool candidateCount = false;
    for (const auto &requirement : facts.candidateRequirements) {
      auto repeat = requirement.control
                        ? dyn_cast<pir::RepeatOp>(requirement.control)
                        : pir::RepeatOp();
      candidateCount |= repeat && repeat.getSite() == "outer" &&
                        requirement.components.size() == 2 &&
                        requirement.components[0].input == 1 &&
                        requirement.components[1].input == 1;
    }
    require(candidateCount,
            "removing source sequence access lost the original full selection");
    auto prepared = mathematical::PreparedProtocol::prepare(*source);
    require(bool(prepared), "source coordinate/count preparation");
    auto owner = take(mathematical::RealizedProtocol::realize(
        std::move(*prepared), selected));
    require(bool(owner.project(false)) && bool(owner.project(true)),
            "retained source observations broke owner projection");
  });
  cases.run("forged publication cannot grant candidate admission", [&] {
    auto owner = realized(context);
    auto original = owner.preparedSnapshot();
    auto candidate = owner.candidateSnapshot();
    refused(checkOracleRealization(*original, *candidate, "{}",
                                   policy(OracleAuthentication::PerQuery)));
    require(failed(admitStage(*candidate)), "forged record changed admission");
  });
  cases.run(
      "same-typed original instances cannot exchange count equations", [&] {
        auto owner = realized(context, 1, false);
        auto wrong = parseSourceString<ModuleOp>(fixture(3, false), &context);
        auto candidate = owner.candidateSnapshot();
        require(bool(wrong) && succeeded(admitStage(*wrong)),
                "wrong-instance source");
        refused(checkOracleRealization(*wrong, *candidate,
                                       owner.realizationRecord(),
                                       policy(OracleAuthentication::PerQuery)));
      });
  cases.run(
      "equation matching shares the paired allowance through completion", [&] {
        auto source = parseSourceString<ModuleOp>(fixture(1, false), &context);
        auto selected = policy(OracleAuthentication::PerQuery);
        auto actual = take(emitOracleRealization(*source, selected));
        OracleNativeWork measured;
        take(checkOracleRealizationWithWork(*source, actual, selected,
                                            measured));
        auto used = uint64_t(1000000) - measured.remaining;
        require(used > 1, "paired work was not charged");
        OracleNativeWork limited;
        limited.remaining = used - 1;
        refuses(
            checkOracleRealizationWithWork(*source, actual, selected, limited),
            "common-control-capacity");
        require(limited.exhausted && !limited.charge(0),
                "paired completion reset its exhausted allowance");
      });
  for (unsigned children : {0u, 1u, 2u, 3u})
    for (auto authentication :
         {OracleAuthentication::PerQuery, OracleAuthentication::AtomicBlocks})
      cases.run(
          Twine("structural virtual leaves, children=") + Twine(children) +
              ", policy=" + Twine(unsigned(authentication)),
          [&] {
            auto source =
                parseSourceString<ModuleOp>(virtualSource(children), &context);
            require(bool(source), "virtual graph parse");
            auto preparation = mathematical::PreparedProtocol::prepare(*source);
            require(bool(preparation), "virtual graph preparation");
            auto selected = policy(authentication);
            selected.roots =
                OracleTableRealization{"rows.merkle-keccak256.koala-bear/0"};
            auto owner = take(mathematical::RealizedProtocol::realize(
                std::move(*preparation), selected));
            auto original = owner.preparedSnapshot();
            auto candidate = owner.candidateSnapshot();
            checked(checkOracleRealization(
                *original, *candidate, owner.realizationRecord(), selected));
            require(bool(owner.project(false)) && bool(owner.project(true)),
                    "empty or repeated-child graph lost owner projection");
          });
  cases.run(
      "ordinary selected helpers retain owner routes and substitutions", [&] {
        auto source = parseSourceString<ModuleOp>(R"mlir(
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:i1):
 "protocol.branch"(%choice) ({ "protocol.yield"() : ()->()
 }, { "protocol.yield"() : ()->()
 }) {site="choose",roles=["A","B"],output_roles=[],alternatives=["then","else"]} : (i1)->()
 "protocol.return"() : ()->()
 }) {sym_name="child",function_type=(i1)->(),roles=["A","B"],input_roles=[["A","B"]],output_roles=[]} : ()->()
 "protocol.func"() ({ ^entry(%choice:i1):
 protocol.apply @child(%choice) {site="first",roles=["P","V"]} : (i1)->()
 protocol.apply @child(%choice) {site="second",roles=["V","P"]} : (i1)->()
 "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(i1)->(),roles=["P","V"],input_roles=[["P","V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir",
                                                  &context);
        require(bool(source), "ordinary helper parse");
        auto prepared = mathematical::PreparedProtocol::prepare(*source);
        require(bool(prepared), "ordinary helper preparation");
        auto owner =
            take(mathematical::RealizedProtocol::realize(std::move(*prepared)));
        require(bool(owner.project(false)) && bool(owner.project(true)),
                "ordinary helper ownership path refused");
      });
  cases.run(
      "inspection pairs survive owner destruction by fresh checking", [&] {
        OwningOpRef<ModuleOp> original, candidate;
        std::string record;
        {
          auto owner = realized(context);
          original = owner.preparedSnapshot();
          candidate = owner.candidateSnapshot();
          record = owner.realizationRecord().str();
          auto moved = std::move(owner);
          require(!owner.candidateSnapshot() && bool(moved.project(false)),
                  "moved-from owner retained authority");
        }
        checked(checkOracleRealization(*original, *candidate, record,
                                       policy(OracleAuthentication::PerQuery)));
        require(failed(admitStage(*candidate)),
                "clone inherited expired borrow");
      });
  cases.run("native request counts use the public owner projection", [&] {
    auto owner = realized(context);
    auto participant = owner.project(false);
    require(bool(participant), "ordinary projection");
    NativeProofPolicy selected;
    selected.entry = "main";
    selected.producer = "P";
    selected.validator = "V";
    auto unit = cast<pir::ProtocolModuleOp>(participant->getBody()->front());
    auto counts =
        take(zkc::detail::readNativeRequestCounts(owner, unit, selected));
    require(!counts.empty(), "request consumer did not recover exact counts");
  });
  cases.run("request count comparison shares the complete subject budget", [&] {
    auto owner = realized(context);
    auto participant = owner.project(false);
    require(bool(participant), "ordinary projection");
    auto unit = cast<pir::ProtocolModuleOp>(participant->getBody()->front());
    NativeProofPolicy selected;
    selected.entry = "main";
    selected.producer = "P";
    selected.validator = "V";
    take(zkc::detail::readNativeRequestCounts(owner, unit, selected));
    auto attributes = unit->getAttrDictionary();
    for (auto [bytes, code] :
         {std::pair{600000u, "native-request-count-correspondence"},
          std::pair{1000001u, "native-request-count-limit"}}) {
      // Immutable storage is inspected once per allowance. The original
      // 600k probe now fits storage admission and fails exact equivalence;
      // the larger probe exceeds 1m by its first string visit alone.
      unit->setAttr("capacity_probe",
                    StringAttr::get(&context, std::string(bytes, 'x')));
      auto changed = unit->getAttrDictionary();
      refuses(zkc::detail::readNativeRequestCounts(owner, unit, selected),
              code);
      require(unit->getAttrDictionary() == changed,
              "capacity comparison mutated the supplied projection");
    }
    unit->setAttrs(attributes);
    take(zkc::detail::readNativeRequestCounts(owner, unit, selected));
  });
  cases.run("CPU run verification retains the exact common owner", [&] {
    auto owner = realized(context);
    auto physical = owner.project(false);
    require(bool(physical), "CPU participant projection");
    lower(*physical);
    auto bundle = take(zkc::detail::buildRunBundle(owner, *physical, "main"));
    checked(zkc::detail::verifyRunBundle(owner, *physical, bundle, "main"));
    auto detached = owner.candidateSnapshot();
    refused(zkc::detail::verifyRunBundle(*detached, *physical, bundle, "main"));
    auto other = realized(context, 3, true);
    refused(zkc::detail::verifyRunBundle(other, *physical, bundle, "main"));
  });
  for (bool simplify : {false, true})
    cases.run(
        Twine("production CPU compilation, simplify=") +
            Twine(unsigned(simplify)),
        [&] {
          RunOptions options;
          options.simplify = simplify;
          options.oracleRealization = policy(OracleAuthentication::PerQuery);
          auto compiled = take(compileRun(
              fixture(1, false), "oracle-counts.mlir", options, registry));
          require(!compiled.bundle.empty(), "production run bundle missing");
          auto snapshot = compiled.compilation.oracleRealizationSnapshot();
          require(bool(snapshot), "compiled run dropped paired owner");
          checked(checkOracleRealization(*snapshot->prepared,
                                         *snapshot->candidate, snapshot->record,
                                         options.oracleRealization));
        });
  return cases.result();
}
