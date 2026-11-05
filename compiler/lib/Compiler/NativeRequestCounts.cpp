#include "../Transforms/OracleNativeCommon.h"
#include "../Transforms/RealizedProtocol.h"
#include "NativeRequest.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringMap.h"

using namespace mlir;
using namespace llvm;
namespace zkc::detail {
namespace {
namespace pir = protocol_ir;
Error refuse() { return error("native-request-count-correspondence"); }
Error capacity() { return error("native-request-count-limit"); }
} // namespace
Expected<SmallVector<NativeRequestCountPair>>
readNativeRequestCounts(const mathematical::RealizedProtocol &owner,
                        pir::ProtocolModuleOp projected,
                        const NativeProofPolicy &policy) {
  protocol::OracleNativeWork work;
  auto bound = [&](Operation *subject) {
    if (auto failure = protocol::boundOracleNativeIR(subject, &work)) {
      consumeError(std::move(failure));
      return false;
    }
    return true;
  };
  // Check caller-controlled storage before obtaining owner snapshots. The
  // owner's snapshot/projection phases have their own bounds; this allowance
  // covers this consumer's complete comparison, indexes and matching work.
  if (!projected || !hasSingleElement(projected.getBody()))
    return refuse();
  if (!bound(projected))
    return capacity();
  auto common = owner.candidateSnapshot();
  auto ordinary = owner.project(false);
  if (!common || !ordinary || !hasSingleElement(*ordinary->getBody()))
    return refuse();
  if (!bound(*common) || !bound(*ordinary))
    return capacity();
  // Reserve another complete traversal for the two-subject equivalence check;
  // admission metadata or the supplied projection's shape cannot replace it.
  if (!bound(projected) || !bound(*ordinary))
    return capacity();
  if (!OperationEquivalence::isEquivalentTo(
          &ordinary->getBody()->front(), projected,
          OperationEquivalence::IgnoreLocations))
    return refuse();
  // The immutable owner's independent reader established actual allocation,
  // count, multiplicity and ceiling arithmetic. Its typed associations retain
  // source coordinates without decoding the external realization publication.
  auto unit = cast<pir::ProtocolModuleOp>(common->getBody()->front());
  auto program = dyn_cast_or_null<pir::MathematicalOp>(
      SymbolTable::lookupSymbolIn(unit, policy.entry));
  pir::ParticipantOp producer, validator;
  for (auto p : projected.getBody().front().getOps<pir::ParticipantOp>()) {
    if (!work.charge() || !work.charge(p.getRole().size()) ||
        !work.charge(policy.producer.size()) ||
        !work.charge(policy.validator.size()))
      return capacity();
    if (p.getRole() == policy.producer)
      producer = p;
    if (p.getRole() == policy.validator)
      validator = p;
  }
  if (!program || !producer || !validator)
    return refuse();
  StringMap<Operation *> commonSites, pSites, vSites;
  bool valid = true;
  auto index = [&](Operation *root, StringMap<Operation *> &sites) {
    root->walk([&](Operation *op) {
      if (!work.charge()) {
        valid = false;
        return WalkResult::interrupt();
      }
      if (auto site = op->getAttrOfType<StringAttr>("site")) {
        if (!work.charge(site.getValue().size())) {
          valid = false;
          return WalkResult::interrupt();
        }
        valid &= sites.try_emplace(site.getValue(), op).second;
      }
      return WalkResult::advance();
    });
  };
  index(program, commonSites);
  index(producer, pSites);
  index(validator, vSites);
  if (!valid)
    return work.exhausted ? capacity() : refuse();
  SmallVector<NativeRequestCountPair> result;
  for (const auto &entry : owner.realizationFacts()) {
    if (!work.charge() || !work.charge(entry.entry.size()) ||
        !work.charge(policy.entry.size()))
      return capacity();
    if (entry.entry != policy.entry)
      continue;
    // Keys borrow immutable facts retained by owner. Hashing each full path
    // is charged; no repeated vector copies or loop-by-query-block scan.
    using Path = ArrayRef<unsigned>;
    using Occurrence = protocol::OracleCommonOccurrence;
    llvm::DenseMap<Path, SmallVector<const Occurrence *>> rounds;
    llvm::DenseMap<Path, const protocol::OracleCommonQueryBlock *> blocks;
    SmallVector<const Occurrence *> loops;
    for (const auto &block : entry.queryBlocks) {
      if (!work.charge() || (!block.queries.empty() &&
                             !work.charge(block.queries.front().size())))
        return capacity();
      if (block.queries.empty() ||
          !blocks.try_emplace(block.queries.front(), &block).second)
        return refuse();
    }
    for (const auto &occurrence : entry.occurrences) {
      if (!work.charge() || !work.charge(occurrence.purpose.size()) ||
          !work.charge(occurrence.sourcePath.size()))
        return capacity();
      if (occurrence.purpose == "query_round_count")
        rounds[occurrence.sourcePath].push_back(&occurrence);
      else if (occurrence.purpose == "query_requests")
        loops.push_back(&occurrence);
    }
    for (const auto *occurrence : loops) {
      const auto &item = *occurrence;
      if (!work.charge() || !work.charge(item.role.size()) ||
          !work.charge(policy.validator.size()) ||
          !work.chargeProduct(item.site.size(), 3) ||
          !work.chargeProduct(item.sourcePath.size(), 2))
        return capacity();
      if (item.role != policy.validator)
        continue;
      auto sourceLoop =
          dyn_cast_or_null<pir::RepeatOp>(commonSites.lookup(item.site));
      auto pLoop =
          dyn_cast_or_null<pir::ProtocolLoopOp>(pSites.lookup(item.site));
      auto vLoop =
          dyn_cast_or_null<pir::ProtocolLoopOp>(vSites.lookup(item.site));
      if (!sourceLoop || !pLoop || !vLoop ||
          pLoop.getMaximumAttr() != sourceLoop.getMaximumAttr() ||
          vLoop.getMaximumAttr() != sourceLoop.getMaximumAttr())
        return refuse();
      auto assembly =
          sourceLoop.getInputs()[0].getDefiningOp<pir::AssembleRolesOp>();
      if (!assembly)
        return refuse();
      Value pCount, vCount;
      auto found = rounds.find(item.sourcePath);
      if (found == rounds.end() || found->second.size() != 2)
        return refuse();
      for (const auto *occurrence : found->second) {
        const auto &round = *occurrence;
        if (!work.charge() || !work.chargeProduct(round.site.size(), 2) ||
            !work.charge(round.role.size()) ||
            !work.charge(policy.producer.size()) ||
            !work.charge(policy.validator.size()) ||
            !work.chargeProduct(assembly.getRoles().size(),
                                round.role.size() + 1))
          return capacity();
        auto sourceCall =
            dyn_cast_or_null<pir::LocalCallOp>(commonSites.lookup(round.site));
        auto actual = dyn_cast_or_null<pir::LocalCallOp>(
            (round.role == policy.producer ? pSites : vSites)
                .lookup(round.site));
        if (!sourceCall || !actual ||
            actual.getCalleeAttr() != sourceCall.getCalleeAttr() ||
            actual.getNumResults() != 1 || sourceCall.getNumResults() != 1 ||
            assembly.getComponent(round.role) != sourceCall.getResult(0))
          return refuse();
        if (round.role == policy.producer)
          pCount = actual.getResult(0);
        else if (round.role == policy.validator)
          vCount = actual.getResult(0);
        else
          return refuse();
      }
      if (!pCount || !vCount || pLoop.getInputs()[0] != pCount ||
          vLoop.getInputs()[0] != vCount)
        return refuse();
      // Source query-block inventory is ordered and multiplicity preserving.
      // Its first occurrence is the lexical identity of this generated loop.
      auto block = blocks.find(item.sourcePath);
      if (block == blocks.end() || !block->second->packetCapacity ||
          *block->second->packetCapacity == 0 ||
          *block->second->packetCapacity >= 1048576)
        return refuse();
      if (!work.charge())
        return capacity();
      result.push_back({pCount, vCount});
    }
  }
  return result;
}
} // namespace zkc::detail
