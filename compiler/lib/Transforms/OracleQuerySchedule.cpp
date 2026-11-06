#include "OracleQuerySchedule.h"
#include "OracleAccounting.h"
#include "OracleNativeCommon.h"
#include "OracleQueryBlocks.h"
#include "zkc/Analysis/Interactions.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLFunctionalExtras.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
namespace pir = protocol_ir;
// Kind numbering and resume helpers are controller-local. Only the transported
// alternatives, actual constructor/store inventory and selected Merkle meaning
// are shared; each root replays with its own controller.
bool compatible(const OracleQueryExchange &left,
                const OracleQueryExchange &right) {
  if (left.holder != right.holder || left.request != right.request ||
      left.response != right.response ||
      left.receiverStores != right.receiverStores ||
      left.holderStores != right.holderStores ||
      left.arms.size() != right.arms.size())
    return false;
  for (const auto &[a, b] : zip(left.arms, right.arms))
    if (a.constructor != b.constructor || a.receiverSlot != b.receiverSlot ||
        a.alternative != b.alternative || a.reference != b.reference ||
        a.opened != b.opened || a.openingState != b.openingState ||
        a.holderRows != b.holderRows || a.root != b.root ||
        a.receiverRows != b.receiverRows || a.open != b.open ||
        a.authenticate != b.authenticate)
      return false;
  return true;
}
} // namespace
Expected<OracleQuerySchedule>
planOracleQuerySchedule(ModuleOp source, StringRef entry,
                        const OracleCommonRequirements &requirements,
                        ArrayRef<OracleCommonController> controllers,
                        ArrayRef<OracleMerkleFunctions> merkle,
                        OracleAuthentication authentication) {
  OracleNativeWork common;
  auto preflight = OracleNativeSourcePreflight::read(source, common);
  if (!preflight)
    return preflight.takeError();
  return planOracleQueryScheduleWithWork(source, entry, requirements,
                                         controllers, merkle, authentication,
                                         common, *preflight);
}
Expected<OracleQuerySchedule> planOracleQueryScheduleWithWork(
    ModuleOp source, StringRef entry,
    const OracleCommonRequirements &requirements,
    ArrayRef<OracleCommonController> controllers,
    ArrayRef<OracleMerkleFunctions> merkle, OracleAuthentication authentication,
    OracleNativeWork &common, const OracleNativeSourcePreflight &preflight) {
  return oracleExpectedWithWork(common, [&]() -> Expected<OracleQuerySchedule> {
    if (auto e = checkOracleNativePreflight(source, common, &preflight))
      return std::move(e);
    if (!preflight.reserveTraversal(source))
      return error("oracle-common-limit");
    auto unit = cast<pir::ProtocolModuleOp>(source.getBody()->front());
    auto program = dyn_cast_or_null<pir::MathematicalOp>(
        preflight.getSymbols().getSymbolTable(unit).lookup(entry));
    if (!program || !hasSingleElement(program.getBody()))
      return error("oracle-query-block-source");
    OracleQuerySchedule result;
    DominanceInfo dominance(source);
    unsigned remaining = 100000;
    auto controller = [&](StringRef role,
                          pir::OracleKindAttr kind) -> std::optional<unsigned> {
      for (auto [i, item] : enumerate(controllers)) {
        if (!common.charge(1 + item.role.size()))
          return std::nullopt;
        if (item.role == role &&
            item.access == OracleControllerAccess::Available &&
            sameOracleReferenceKind(item.kind, kind))
          return unsigned(i);
      }
      return std::nullopt;
    };
    auto remote =
        [&](pir::OracleQueryOp query) -> Expected<std::optional<unsigned>> {
      auto receiver =
          controller(*query.getOwner(), query.getHandle().getType().getKind());
      if (!receiver)
        return error("oracle-common-helper");
      const auto &body = controllers[*receiver].body;
      if (body.evaluate)
        return std::optional<unsigned>();
      for (auto [i, item] : enumerate(result.remotes)) {
        if (!common.charge())
          return error("oracle-common-limit");
        if (item.receiver == *receiver)
          return std::optional<unsigned>(unsigned(i));
      }
      StringRef holderRole;
      for (const auto &item : body.constructors) {
        if (!common.charge())
          return error("oracle-common-limit");
        if (item.source >= requirements.storage.constructors.size())
          return error("oracle-common-helper");
        const auto &anchor = requirements.storage.constructors[item.source];
        if (anchor.constructor == OracleAnchorConstructor::Kind::Virtual)
          continue;
        if (anchor.scheme.empty() || anchor.holder == body.role ||
            (!holderRole.empty() && holderRole != anchor.holder))
          return error("oracle-common-communication-profile");
        holderRole = anchor.holder;
      }
      auto holder =
          controller(holderRole, query.getHandle().getType().getKind());
      if (holderRole.empty() || !holder)
        return error("oracle-common-communication-profile");
      if (!common.charge(1 + requirements.storage.constructors.size() +
                         body.constructors.size()))
        return error("oracle-common-limit");
      auto exchange = planOracleQueryExchangeWithWork(
          requirements.storage, body, controllers[*holder].body, merkle,
          common);
      if (!exchange)
        return exchange.takeError();
      result.remotes.push_back({*receiver, *holder, std::move(*exchange)});
      return std::optional<unsigned>(unsigned(result.remotes.size() - 1));
    };
    facts::Work work([&](uint64_t amount) {
      if (!common.charge(amount) || amount > remaining) {
        remaining = 0;
        return false;
      }
      remaining -= amount;
      return true;
    });
    InteractionAnalysis interactions(source);
    auto view = interactions.get(program, work);
    if (!view) {
      consumeError(view.takeError());
      return error(work.exhausted() ? "oracle-query-block-limit"
                                    : "oracle-query-block-source");
    }
    // Consume the same immutable lexical inventory as capacity and observation
    // analyses. A selected window contains adjacent actions in one actual
    // block; skipping its remaining queries never skips a nested repeat body.
    unsigned skipped = 0;
    for (const auto &action : (*view)->getActions()) {
      if (!work.charge())
        return error("oracle-query-block-limit");
      if (skipped) {
        --skipped;
        continue;
      }
      auto path = action.getPath();
      auto query = dyn_cast<pir::OracleQueryOp>(action.getOperation());
      if (!query)
        continue;
      auto first = remote(query);
      if (!first)
        return first.takeError();
      if (!*first)
        continue;
      auto selected = selectOracleQueryWindow(query, authentication,
                                              requirements.queryCapacity,
                                              dominance, remaining, &common);
      if (!selected)
        return selected.takeError();
      OracleBatchRequirement batch;
      for (auto candidate : selected->queries) {
        if (!common.charge(1 + path.size()))
          return error("oracle-common-limit");
        auto item = remote(candidate);
        if (!item)
          return item.takeError();
        const auto &firstExchange = result.remotes[**first].exchange;
        if (!common.charge(1 + firstExchange.holder.size() +
                           firstExchange.receiverStores.size() +
                           firstExchange.holderStores.size() +
                           firstExchange.arms.size()))
          return error("oracle-common-limit");
        if (!*item || !compatible(result.remotes[**first].exchange,
                                  result.remotes[**item].exchange))
          break;
        std::vector<unsigned> coordinate(path.begin(), path.end());
        coordinate.back() += batch.queries.size();
        batch.queries.push_back(std::move(coordinate));
        batch.remotes.push_back(**item);
        batch.leaves +=
            requirements.queryCapacity.queries.lookup(candidate).leaves;
      }
      if (batch.queries.empty() || batch.leaves >= 1048576)
        return error("oracle-query-block-limit");
      skipped = batch.queries.size() - 1;
      if (authentication == OracleAuthentication::AtomicBlocks)
        result.capacity = std::max(result.capacity, batch.leaves);
      result.batches.push_back(std::move(batch));
    }
    return result;
  });
}
} // namespace zkc::protocol
