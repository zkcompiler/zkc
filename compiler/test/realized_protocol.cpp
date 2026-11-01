#include "../lib/Transforms/OracleCommonRealization.h"
#include "../lib/Transforms/RealizedProtocol.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/ProtocolObservations.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/Construction.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/MemoryBuffer.h"
#include <algorithm>
#include <type_traits>

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::mathematical;
using namespace zkc::test;
static_assert(!std::is_copy_constructible_v<RealizedProtocol>);
static_assert(!std::is_default_constructible_v<RealizedProtocol>);
namespace {
constexpr StringLiteral ordinaryFixture = R"mlir(
module { "protocol.module"() ({
  "protocol.func"() ({ ^bb0(%value: ui64):
    "protocol.return"(%value) : (ui64) -> ()
  }) {sym_name="main",function_type=(ui64)->ui64,roles=["V"],
      input_roles=[["V"]],output_roles=[["V"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
)mlir";
constexpr StringLiteral constructionFixture = R"mlir(
!rng = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
  func.func private @initialize(%scope: !runtime.scope) -> !exec.outcome<>
      attributes {no_inline, runtime.origin=["initialize",[]]} {
    %done = "exec.returned"() : () -> !exec.outcome<>
    return %done : !exec.outcome<>
  }
  func.func private @start(%scope: !runtime.scope, %public: ui64)
      -> !exec.outcome<> attributes {no_inline, runtime.origin=["start",[]]} {
    %done = "exec.returned"() : () -> !exec.outcome<>
    return %done : !exec.outcome<>
  }
  "protocol.func"() ({ ^entry(%x:ui64,%y:ui64,%coins:!rng):
    "protocol.return"(%x) : (ui64)->()
  }) {sym_name="leaf",function_type=(ui64,ui64,!rng)->ui64,
      roles=["P","V"],input_roles=[["P","V"],["P","V"],["V"]],
      output_roles=[["P","V"]]} : ()->()
  "protocol.func"() ({ ^entry(%x:ui64,%y:ui64,%coins:!rng):
    %result = protocol.apply @leaf(%y,%x,%coins)
        {roles=["P","V"],site="step"} : (ui64,ui64,!rng)->ui64
    "protocol.return"(%result) : (ui64)->()
  }) {sym_name="main",function_type=(ui64,ui64,!rng)->ui64,
      roles=["P","V"],input_roles=[["P","V"],["P","V"],["V"]],
      output_roles=[["P","V"]]} : ()->()
  "protocol.construction"() {
    sym_name="Child",target=@leaf,provider="test/transcript",root="local",
    state=[],initializer=@initialize,suite="",services=array<i64:2>,
    native_base=false,root_only=false,applications=[],
    rules=[{kind="start",handler=@start,sites=[],inputs=array<i64:0>,
            payload=[],chunks=[]}]
  } : ()->()
  "protocol.construction"() {
    sym_name="Parent",target=@main,provider="test/transcript",root="local",
    state=[],initializer=@initialize,suite="",services=array<i64:2>,
    native_base=false,root_only=false,
    applications=[{site="step",construction=@Child}],
    rules=[{kind="start",handler=@initialize,sites=[],inputs=array<i64>,
            payload=[],chunks=[]}]
  } : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
bool equivalent(ModuleOp left, ModuleOp right) {
  return OperationEquivalence::isEquivalentTo(
      left, right, OperationEquivalence::IgnoreLocations);
}
OwningOpRef<ModuleOp> fixture(MLIRContext &context, StringRef name) {
  auto file =
      MemoryBuffer::getFile(ZKC_REALIZED_FIXTURES "/" + name.str() + ".mlir");
  require(bool(file), "missing fixture: " + name);
  auto source = parseSourceString<ModuleOp>((*file)->getBuffer(), &context);
  require(bool(source), "invalid fixture: " + name);
  return source;
}
PreparedProtocol prepare(ModuleOp source) {
  auto result = PreparedProtocol::prepare(source);
  require(bool(result), "valid source did not prepare");
  return std::move(*result);
}
PreparedProtocol prepareConstruction(ModuleOp source) {
  SmallVector<ApplicationStart> starts{{"main", "step", {0}}};
  auto result = PreparedProtocol::prepare(source, {}, nullptr, starts);
  require(bool(result), "valid construction source did not prepare");
  return std::move(*result);
}
OwningOpRef<ModuleOp> constructionSource(MLIRContext &context) {
  auto source = parseSourceString<ModuleOp>(constructionFixture, &context);
  require(bool(source), "invalid construction fixture");
  return source;
}
void refusesConstruction(PreparedProtocol &owner, StringRef selection,
                         MLIRContext &context) {
  auto before = owner.snapshot(), original = owner.originalSnapshot();
  bool diagnostic = false;
  ScopedDiagnosticHandler expected(&context, [&](Diagnostic &value) {
    for (const auto &refusal : diagnostics::refusals(value))
      diagnostic |= refusal.code == "protocol-construction";
    return success();
  });
  require(failed(owner.consumeConstruction(selection)) && diagnostic,
          "construction selection did not refuse with its identifier");
  auto after = owner.snapshot(), retained = owner.originalSnapshot();
  require(equivalent(*before, *after) && equivalent(*original, *retained),
          "failed construction consumption changed its owner");
}
void checked(const RealizedProtocol &owner,
             const protocol::OracleRealizationPolicy &policy = {}) {
  auto original = owner.preparedSnapshot();
  auto candidate = owner.candidateSnapshot();
  require(bool(original) && bool(candidate), "checked edge lost a side");
  if (auto failure = protocol::checkOracleRealization(
          *original, *candidate, owner.realizationRecord(), policy))
    throw std::runtime_error(toString(std::move(failure)));
}
void changeRelation(ModuleOp module) {
  auto unit = cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  auto declarations = unit.getBody().front().getOps<relation::DeclareOp>();
  require(!declarations.empty(), "fixture has no logical relation");
  (*declarations.begin()).setKey("test/changed-predicate");
  require(succeeded(verify(module)), "mutation must remain well formed");
}
} // namespace
int main(int argc, char **argv) {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  // Inspect a real checked candidate without truncating it through diagnostic
  // dump limits. This optional integration probe does not publish a public-coin
  // or construction judgment; the ordinary CTest mode runs the owner controls.
  if (argc == 5) {
    try {
      auto source = parseSourceFile<ModuleOp>(argv[1], &context);
      require(bool(source), "invalid observation source");
      auto prepared = prepare(*source);
      require(succeeded(prepared.selectEntries({argv[2]})),
              "invalid observation entry");
      protocol::OracleRealizationPolicy policy;
      policy.roots = protocol::OracleTableRealization{
          StringRef(argv[4]) == "ideal" ? "" : argv[4],
          protocol::OracleLeafGrouping::Individual,
          protocol::OracleLeafOrder::Natural};
      policy.order = protocol::OracleQueryOrder::AfterFinalDraw;
      policy.authentication = protocol::OracleAuthentication::AtomicBlocks;
      auto owner = take(RealizedProtocol::realize(std::move(prepared), policy));
      auto snapshot = take(owner.observationSnapshot());
      auto actual = std::move(snapshot.module);
      auto entry = SymbolTable(unit(*actual))
                       .lookup<protocol_ir::MathematicalOp>(argv[2]);
      require(bool(entry), "realization lost observation entry");
      // Bounded diagnostic inventory for independently writing a requirement.
      // This is not a coverage judgment and never selects a service for it.
      for (auto [port, type] : enumerate(entry.getFunctionType().getInputs()))
        outs() << "input " << port << ": " << type << " "
               << entry.getInputRoles()[port] << '\n';
      entry.walk([&](Operation *op) {
        if (auto query = dyn_cast<protocol_ir::QueryOp>(op);
            query && query.getOwner() == argv[3])
          outs() << "query: " << query.getSite() << '\n';
        if (auto send = dyn_cast<protocol_ir::ExchangeOp>(op);
            send && send.getSender() == argv[3] &&
            !is_contained(snapshot.dataExchanges, op))
          outs() << "delivery: " << send.getSite() << '\n';
      });
      ProtocolObservationAnalysis analysis(*actual, snapshot.dataExchanges);
      uint64_t remaining = 1000000;
      facts::Work work(remaining);
      const auto *summary = take(analysis.get(entry, argv[3], work));
      outs() << "query families: " << summary->queryFamilies
             << ", generated data exchanges: " << snapshot.dataExchanges.size()
             << ", work used: " << 1000000 - remaining
             << ", pending input/output: " << unsigned(summary->pending.input)
             << '/' << unsigned(summary->pending.output) << '\n';
      return 0;
    } catch (const std::exception &failure) {
      errs() << failure.what() << '\n';
      return 1;
    }
  }
  if (argc != 1)
    return 2;
  ScopedDiagnosticHandler silence(&context,
                                  [](Diagnostic &) { return success(); });
  auto file = MemoryBuffer::getFile(ZKC_REALIZED_FIXTURES "/common-input.mlir");
  require(bool(file), "missing common input fixture");
  auto text = (*file)->getBuffer();
  auto source = parseSourceString<ModuleOp>(text, &context);
  require(bool(source), "invalid common input fixture");
  auto prepared = prepare(*source);
  auto frozen = prepared.snapshot();
  auto owner = take(RealizedProtocol::realize(std::move(prepared)));
  Cases cases;
  cases.run("native realization checks actual bodies without a record", [&] {
    auto actual = take(protocol::emitOracleRealization(*frozen));
    auto facts = take(protocol::checkOracleRealization(*frozen, actual));
    for (Operation *op : facts.openingRequests)
      require(op->getParentOfType<ModuleOp>() == *actual.module &&
                  isa<protocol_ir::ExchangeOp>(op),
              "native fact refers outside its checked candidate");
    // The proposal is typed, but its inventory still carries no authority.
    actual.entries.clear();
    refuses(protocol::checkOracleRealization(*frozen, actual),
            "oracle-common-body");
  });
  cases.run("native realization rejects handles into another candidate", [&] {
    auto actual = take(protocol::emitOracleRealization(*frozen));
    auto retained = std::move(actual.module);
    actual.module = OwningOpRef<ModuleOp>(cast<ModuleOp>(retained->clone()));
    // Structurally equal modules do not have the same operation identities.
    refuses(protocol::checkOracleRealization(*frozen, actual),
            "oracle-controller-body");
  });
  cases.run(
      "observation transport associations come from the checked owner", [&] {
        auto source = fixture(context, "query-blocks");
        protocol::OracleRealizationPolicy policy;
        policy.roots = protocol::OracleTableRealization{
            "rows.merkle-keccak256.koala-bear.ext4-binomial3/0",
            protocol::OracleLeafGrouping::Individual,
            protocol::OracleLeafOrder::Natural};
        policy.authentication = protocol::OracleAuthentication::AtomicBlocks;
        auto owner = take(RealizedProtocol::realize(prepare(*source), policy));
        auto snapshot = take(owner.observationSnapshot());
        auto entry = SymbolTable(unit(*snapshot.module))
                         .lookup<protocol_ir::MathematicalOp>("main");
        require(bool(entry) && !snapshot.dataExchanges.empty(),
                "missing generated data transport");
        for (Operation *op : snapshot.dataExchanges)
          require(op->getParentOfType<ModuleOp>() == *snapshot.module &&
                      isa<protocol_ir::ExchangeOp>(op),
                  "transport refers to another snapshot");
        ProtocolObservationAnalysis strict(*snapshot.module);
        uint64_t remaining = 1000000;
        facts::Work work(remaining);
        refuses(strict.get(entry, "V", work),
                "protocol-observation-unsupported");
        ProtocolObservationAnalysis selected(*snapshot.module,
                                             snapshot.dataExchanges);
        const auto *summary = take(selected.get(entry, "V", work));
        require(
            summary->queryFamilies == 0 && summary->mayStop &&
                summary->pending.output ==
                    ProtocolPendingTransfer::Output::Empty,
            "checked data transport acquired a challenge law or lost stops");
        auto fresh = take(owner.observationSnapshot());
        require(
            fresh.dataExchanges.front() != snapshot.dataExchanges.front() &&
                equivalent(*fresh.module, *snapshot.module),
            "observation snapshot aliases its owner or changes the subject");
      });
  cases.run(
      "preparation retains authored calls and exact application starts", [&] {
        auto source = constructionSource(context);
        auto prepared = prepareConstruction(*source);
        auto authored = prepared.originalSnapshot();
        auto expanded = prepared.snapshot();
        require(equivalent(*source, *authored),
                "preparation changed the retained full original");
        auto main = cast<protocol_ir::MathematicalOp>(
            SymbolTable::lookupSymbolIn(unit(*expanded), "main"));
        auto &body = main.getBody().front();
        auto starts = body.getOps<protocol_ir::ConstructionStartOp>();
        require(llvm::hasSingleElement(starts),
                "selected application start was lost or duplicated");
        auto start = *starts.begin();
        require(start.getInputs().size() == 1,
                "start lost its selected callee input");
        Value input = start.getInputs().front();
        while (auto restricted =
                   input.getDefiningOp<protocol_ir::RestrictRolesOp>())
          input = restricted.getInput();
        require(start.getSite() == "step" && input == body.getArgument(1) &&
                    start.getRoles() == main.getRoles(),
                "start lost the exact selected callee input or roles");
        require(body.getOps<protocol_ir::ApplyOp>().empty(),
                "prepared call was not expanded");
        auto originalMain = cast<protocol_ir::MathematicalOp>(
            SymbolTable::lookupSymbolIn(unit(*authored), "main"));
        require(
            llvm::hasSingleElement(
                originalMain.getBody().front().getOps<protocol_ir::ApplyOp>()),
            "retained original lost the authored application");
      });
  for (StringRef mutation : {"site", "input"})
    cases.run("owned preparation checks application start " + mutation, [&] {
      auto source = constructionSource(context);
      SmallVector<ApplicationStart> starts{{"main", "step", {0}}};
      if (mutation == "site")
        starts.front().site = "missing";
      else
        starts.front().inputs = {2};
      auto frozen = OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
      bool diagnostic = false;
      ScopedDiagnosticHandler expected(&context, [&](Diagnostic &value) {
        for (const auto &refusal : diagnostics::refusals(value))
          diagnostic |= refusal.code == "protocol-construction-start";
        return success();
      });
      require(!PreparedProtocol::prepare(*source, {}, nullptr, starts) &&
                  diagnostic,
              "invalid application starts bypassed owned preparation");
      require(equivalent(*source, *frozen),
              "failed preparation changed the caller's source");
    });
  cases.run("construction closure refusals are transactional", [&] {
    auto source = constructionSource(context);
    auto prepared = prepareConstruction(*source);
    for (StringRef selection : {"", "missing", "main", "Child"})
      refusesConstruction(prepared, selection, context);
    require(succeeded(prepared.consumeConstruction("Parent")),
            "complete original closure refused after failed selections");
    auto consumed = prepared.snapshot(), authored = prepared.originalSnapshot();
    require(unit(*consumed)
                    .getBody()
                    .front()
                    .getOps<protocol_ir::ConstructionOp>()
                    .empty() &&
                succeeded(zkc::admitStage(*consumed)),
            "consumed preparation retained construction declarations");
    require(equivalent(*source, *authored),
            "successful consumption changed its retained original");
    for (StringRef name : {"initialize", "start", "leaf", "main"})
      require(SymbolTable::lookupSymbolIn(unit(*consumed), name) != nullptr,
              "consumption removed an ordinary declaration");
    refusesConstruction(prepared, "Parent", context);
    refusesConstruction(prepared, "", context);
  });
  cases.run("construction consumption refuses unrelated declarations", [&] {
    auto source = constructionSource(context);
    auto child = cast<protocol_ir::ConstructionOp>(
        SymbolTable::lookupSymbolIn(unit(*source), "Child"));
    auto extra = cast<protocol_ir::ConstructionOp>(child->clone());
    extra.setSymName("Unrelated");
    unit(*source).getBody().front().push_back(extra);
    auto prepared = prepareConstruction(*source);
    refusesConstruction(prepared, "Parent", context);
  });
  cases.run("construction consumption independently checks child agreement",
            [&] {
              auto source = constructionSource(context);
              auto parent = cast<protocol_ir::ConstructionOp>(
                  SymbolTable::lookupSymbolIn(unit(*source), "Parent"));
              parent.setProvider("test/different-transcript");
              auto prepared = prepareConstruction(*source);
              refusesConstruction(prepared, "Parent", context);
            });
  cases.run("entry selection follows checked construction consumption", [&] {
    auto source = constructionSource(context);
    auto prepared = prepareConstruction(*source);
    auto before = prepared.snapshot();
    require(failed(prepared.selectEntries({"main"})),
            "entry selection discarded a live construction target");
    auto after = prepared.snapshot();
    require(equivalent(*before, *after),
            "failed entry selection changed its owner");
    require(succeeded(prepared.consumeConstruction("Parent")) &&
                succeeded(prepared.selectEntries({"main"})),
            "selected entry did not survive checked consumption");
    auto selected = prepared.snapshot(), original = prepared.originalSnapshot();
    require(SymbolTable::lookupSymbolIn(unit(*selected), "main") &&
                !SymbolTable::lookupSymbolIn(unit(*selected), "leaf") &&
                equivalent(*source, *original),
            "entry selection lost its root or changed the retained source");
    require(failed(prepared.selectEntries({})) &&
                failed(prepared.selectEntries({"missing"})) &&
                failed(prepared.selectEntries({"main", "main"})),
            "entry selection ceased failing closed after consumption");
    auto unchanged = prepared.snapshot();
    require(equivalent(*selected, *unchanged),
            "failed post-consumption selection changed its owner");
  });
  cases.run("prepared snapshots cannot change construction authority", [&] {
    auto source = constructionSource(context);
    auto prepared = prepareConstruction(*source);
    auto retained = prepared.originalSnapshot();
    auto snapshot = prepared.snapshot(), original = prepared.originalSnapshot();
    for (ModuleOp module : {*source, *snapshot, *original})
      cast<protocol_ir::ConstructionOp>(
          SymbolTable::lookupSymbolIn(unit(module), "Parent"))
          .setProvider("test/changed-inspection");
    require(succeeded(prepared.consumeConstruction("Parent")),
            "snapshot or caller mutation changed checked consumption");
    auto authored = prepared.originalSnapshot();
    require(equivalent(*retained, *authored),
            "inspection changed the retained construction source");
  });
  cases.run(
      "checked owner retains both sides and serialized interpretation", [&] {
        checked(owner);
        auto original = owner.preparedSnapshot();
        require(OperationEquivalence::isEquivalentTo(
                    *original, *frozen, OperationEquivalence::IgnoreLocations),
                "realization altered the retained prepared original");
        auto record = take(json::parse(owner.realizationRecord()));
        auto entries = record.getAsObject()->getArray("entries");
        require(
            entries && entries->size() == 1 &&
                entries->front().getAsObject()->getObject("contracts") &&
                entries->front().getAsObject()->getObject("logical_interface"),
            "owned record lost logical associations");
      });
  cases.run("normalized selection records exact roots with canonical bytes", [&] {
    require(
        owner.normalizedSelection() ==
            R"json({"authentication":"per-query","format":"zkc.oracle-selection/0","order":"unrestricted","roots":{"entries":[{"entry":"main","grouping":"individual","order":"natural","path":[0],"scheme":""}],"kind":"exact"}})json",
        "normalized inventory disagrees with the C++/Rust wire policy");
    auto policy = take(
        protocol::parseOracleRealizationPolicy(owner.normalizedSelection()));
    auto roots =
        std::get_if<std::vector<protocol::OracleRootSelection>>(&policy.roots);
    require(roots && *roots ==
                         std::vector<protocol::OracleRootSelection>{
                             {"main", {0}, {}}},
            "uniform request was not normalized to its actual root");
    require(printJson(take(protocol::encodeOracleRealizationPolicy(policy))) ==
                owner.normalizedSelection(),
            "normalized policy is not canonical on re-encoding");
  });
  cases.run(
      "uniform and shuffled exact selections have one normalized inventory",
      [&] {
        auto source = fixture(context, "common-entries");
        protocol::OracleRealizationPolicy policy;
        policy.order = protocol::OracleQueryOrder::AfterFinalDraw;
        policy.authentication = protocol::OracleAuthentication::AtomicBlocks;
        auto uniform =
            take(RealizedProtocol::realize(prepare(*source), policy));
        auto normalized = take(protocol::parseOracleRealizationPolicy(
            uniform.normalizedSelection()));
        require(normalized.order == policy.order &&
                    normalized.authentication == policy.authentication,
                "normalization changed ordering or authentication");
        auto &roots = std::get<std::vector<protocol::OracleRootSelection>>(
            normalized.roots);
        require(roots ==
                    std::vector<protocol::OracleRootSelection>{
                        {"companion", {1}, {}}, {"main", {1}, {}}},
                "normalization invented a virtual root or lost a sibling");
        require(
            uniform.normalizedSelection() ==
                R"json({"authentication":"atomic-blocks","format":"zkc.oracle-selection/0","order":"after-final-draw","roots":{"entries":[{"entry":"companion","grouping":"individual","order":"natural","path":[1],"scheme":""},{"entry":"main","grouping":"individual","order":"natural","path":[1],"scheme":""}],"kind":"exact"}})json",
            "exact roots do not use canonical selector and object order");
        std::reverse(roots.begin(), roots.end());
        auto exact =
            take(RealizedProtocol::realize(prepare(*source), normalized));
        require(uniform.normalizedSelection() == exact.normalizedSelection(),
                "caller selector order changed normalized ownership");
        checked(uniform, policy);
        checked(exact, normalized);
      });
  for (StringRef mutation : {"uncovered", "unknown", "duplicate", "layout"})
    cases.run(
        "checked owner refuses invalid actual-root policy " + mutation, [&] {
          auto source = fixture(context, "common-input");
          protocol::OracleRealizationPolicy policy;
          std::vector<protocol::OracleRootSelection> roots{{"main", {0}, {}}};
          if (mutation == "uncovered")
            roots.clear();
          else if (mutation == "unknown")
            roots.front().path = {99};
          else if (mutation == "duplicate")
            roots.push_back(roots.front());
          else
            roots.front().realization.grouping =
                protocol::OracleLeafGrouping::AntipodalPairs;
          policy.roots = std::move(roots);
          refuses(RealizedProtocol::realize(prepare(*source), policy),
                  "oracle-realization-selection");
        });
  for (StringRef mutation : {"unknown", "layout", "order", "authentication"})
    cases.run(
        "checked owner validates policy without base roots " + mutation, [&] {
          auto source = fixture(context, "common-empty");
          protocol::OracleRealizationPolicy policy;
          if (mutation == "unknown")
            policy.roots =
                std::vector<protocol::OracleRootSelection>{{"ghost", {0}, {}}};
          else if (mutation == "layout")
            policy.roots = protocol::OracleTableRealization{
                "", protocol::OracleLeafGrouping::AntipodalPairs};
          else if (mutation == "order")
            policy.order = static_cast<protocol::OracleQueryOrder>(99);
          else
            policy.authentication =
                static_cast<protocol::OracleAuthentication>(99);
          refuses(RealizedProtocol::realize(prepare(*source), policy),
                  "oracle-realization-selection");
        });
  cases.run("consumed preparation grants no second realization", [&] {
    refuses(RealizedProtocol::realize(std::move(prepared)),
            "oracle-realization-source");
  });
  cases.run("candidate snapshot mutation cannot change checked ownership", [&] {
    auto selection = owner.normalizedSelection().str();
    auto original = owner.preparedSnapshot();
    auto candidate = owner.candidateSnapshot();
    changeRelation(*candidate);
    auto failure = protocol::checkOracleRealization(*original, *candidate,
                                                    owner.realizationRecord());
    require(bool(failure), "changed actual predicate retained correspondence");
    consumeError(std::move(failure));
    checked(owner);
    require(owner.normalizedSelection() == selection,
            "candidate snapshot changed normalized selection");
  });
  cases.run(
      "original and caller mutations cannot rebind the checked edge", [&] {
        auto selection = owner.normalizedSelection().str();
        auto original = owner.preparedSnapshot();
        auto candidate = owner.candidateSnapshot();
        changeRelation(*original);
        changeRelation(*source);
        auto failure = protocol::checkOracleRealization(
            *original, *candidate, owner.realizationRecord());
        require(bool(failure), "changed original retained correspondence");
        consumeError(std::move(failure));
        checked(owner);
        require(owner.normalizedSelection() == selection,
                "original snapshot changed normalized selection");
      });
  cases.run("ordinary modules use an exact identity edge", [&] {
    auto ordinary = parseSourceString<ModuleOp>(ordinaryFixture, &context);
    require(bool(ordinary), "invalid ordinary fixture");
    auto identity = take(RealizedProtocol::realize(prepare(*ordinary)));
    checked(identity);
    auto left = identity.preparedSnapshot(),
         right = identity.candidateSnapshot();
    require(OperationEquivalence::isEquivalentTo(
                *left, *right, OperationEquivalence::IgnoreLocations),
            "identity edge altered ordinary source");
    auto record = take(json::parse(identity.realizationRecord()));
    require(record.getAsObject()->getArray("entries")->empty(),
            "identity edge invented an oracle entry");
    require(
        identity.normalizedSelection() ==
            R"json({"authentication":"per-query","format":"zkc.oracle-selection/0","order":"unrestricted","roots":{"entries":[],"kind":"exact"}})json",
        "ordinary identity edge did not normalize to exact empty roots");
  });
  cases.run(
      "empty construction selection requires an empty declaration inventory",
      [&] {
        auto ordinary = parseSourceString<ModuleOp>(ordinaryFixture, &context);
        require(bool(ordinary), "invalid ordinary fixture");
        auto prepared = prepare(*ordinary);
        auto before = prepared.snapshot();
        require(succeeded(prepared.consumeConstruction("")),
                "empty selection refused an empty inventory");
        auto after = prepared.snapshot();
        require(equivalent(*before, *after),
                "empty consumption changed an ordinary module");
        refusesConstruction(prepared, "missing", context);
        protocol::OracleRealizationPolicy policy;
        policy.roots = std::vector<protocol::OracleRootSelection>{};
        auto exact =
            take(RealizedProtocol::realize(std::move(prepared), policy));
        checked(exact, policy);
        require(
            exact.normalizedSelection() ==
                R"json({"authentication":"per-query","format":"zkc.oracle-selection/0","order":"unrestricted","roots":{"entries":[],"kind":"exact"}})json",
            "exact empty normalization changed at checked ownership");
      });
  auto clausesFile =
      MemoryBuffer::getFile(ZKC_REALIZED_FIXTURES "/common-clauses.mlir");
  require(bool(clausesFile), "missing logical clause fixture");
  auto logical =
      parseSourceString<ModuleOp>((*clausesFile)->getBuffer(), &context);
  require(bool(logical), "logical clause fixture must be admitted");
  auto clauses = take(RealizedProtocol::realize(prepare(*logical)));
  auto main = [](ModuleOp module) {
    auto unit = cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
    return cast<protocol_ir::MathematicalOp>(
        SymbolTable::lookupSymbolIn(unit, "main"));
  };
  auto rejects = [&](ModuleOp original, ModuleOp candidate, StringRef record,
                     StringRef code) {
    auto failure =
        protocol::checkOracleRealization(original, candidate, record);
    require(bool(failure), "changed edge retained correspondence");
    require(namesIdentifier(toString(std::move(failure)), code),
            "unexpected correspondence refusal");
  };
  cases.run("logical clauses stay on the original signature", [&] {
    checked(clauses);
    auto original = clauses.preparedSnapshot(),
         candidate = clauses.candidateSnapshot();
    require(main(*original).getContracts()->size() == 5,
            "original lost a clause");
    require(!main(*candidate).getContracts(),
            "native signature inherited logical clauses");
    require(main(*candidate)
                .getBody()
                .front()
                .getOps<protocol_ir::StatementOp>()
                .empty(),
            "native candidate inherited a logical statement");
    auto record = take(json::parse(clauses.realizationRecord()));
    auto entry =
        record.getAsObject()->getArray("entries")->front().getAsObject();
    auto contracts = entry->getObject("contracts");
    auto selections = contracts->getArray("statements");
    require(contracts->getArray("clauses")->size() == 5 &&
                selections->size() == 1 &&
                selections->front().getAsObject()->getInteger("operation") ==
                    1 &&
                selections->front().getAsObject()->getInteger("target") == 4,
            "record lost the original clause inventory or exact selection");
    require(
        entry->getObject("logical_interface")->getArray("outputs")->size() ==
                1 &&
            entry->getArray("result_references")->size() == 1 &&
            !entry->getArray("result_stores")->empty(),
        "returned anchor lost its actual representation associations");
  });
  cases.run("equal predicates do not merge named target selections", [&] {
    auto original = clauses.preparedSnapshot(),
         candidate = clauses.candidateSnapshot();
    auto record = take(json::parse(clauses.realizationRecord()));
    auto entry =
        record.getAsObject()->getArray("entries")->front().getAsObject();
    (*entry->getObject("contracts")->getArray("statements"))[0].getAsObject()->
    operator[]("target") = 3;
    std::string changed;
    raw_string_ostream(changed) << record;
    rejects(*original, *candidate, changed, "oracle-realization-record");
  });
  cases.run("identical native code cannot substitute a logical target", [&] {
    auto original = clauses.preparedSnapshot(),
         candidate = clauses.candidateSnapshot();
    auto statements =
        main(*original).getBody().front().getOps<protocol_ir::StatementOp>();
    (*statements.begin())
        ->setAttr("target", StringAttr::get(&context, "decoy"));
    require(succeeded(zkc::admitStage(*original)),
            "alternate target must be admitted");
    auto changed = take(RealizedProtocol::realize(prepare(*original)));
    checked(changed);
    auto other = changed.candidateSnapshot();
    require(OperationEquivalence::isEquivalentTo(
                *candidate, *other, OperationEquivalence::IgnoreLocations),
            "logical target unexpectedly changed native code");
    require(changed.realizationRecord() != clauses.realizationRecord(),
            "record collapsed distinct logical selections");
    rejects(*original, *candidate, clauses.realizationRecord(),
            "oracle-realization-record");
  });
  cases.run("candidate cannot insert its own ordinary clause", [&] {
    auto original = owner.preparedSnapshot(),
         candidate = owner.candidateSnapshot();
    main(*candidate)
        ->setAttr("contracts", main(*original)->getAttr("contracts"));
    require(succeeded(zkc::admitStage(*candidate)),
            "ordinary clause mutation must be admitted");
    rejects(*original, *candidate, owner.realizationRecord(),
            "oracle-common-body");
    checked(owner);
  });
  return cases.result();
}
