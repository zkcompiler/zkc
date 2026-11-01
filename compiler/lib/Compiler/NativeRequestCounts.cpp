#include "../Transforms/RealizedProtocol.h"
#include "NativeRequest.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringMap.h"
#include <map>

using namespace mlir;
using namespace llvm;
namespace zkc::detail {
namespace {
namespace pir = protocol_ir;
Error refuse() { return error("native-request-count-correspondence"); }
struct Occurrence {
  std::string site, role;
  std::vector<unsigned> path;
};
} // namespace
Expected<SmallVector<NativeRequestCountPair>>
readNativeRequestCounts(const mathematical::RealizedProtocol &owner,
                        pir::ProtocolModuleOp projected,
                        const NativeProofPolicy &policy) {
  auto common = owner.candidateSnapshot();
  auto ordinary = owner.project(false);
  if (!common || !ordinary || !hasSingleElement(*ordinary->getBody()) ||
      !OperationEquivalence::isEquivalentTo(
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
    if (p.getRole() == policy.producer)
      producer = p;
    if (p.getRole() == policy.validator)
      validator = p;
  }
  if (!program || !producer || !validator)
    return refuse();
  StringMap<Operation *> commonSites, pSites, vSites;
  unsigned remaining = 1000000;
  bool valid = true;
  auto index = [&](Operation *root, StringMap<Operation *> &sites) {
    root->walk([&](Operation *op) {
      if (!remaining) {
        valid = false;
        return WalkResult::interrupt();
      }
      --remaining;
      if (auto site = op->getAttrOfType<StringAttr>("site"))
        valid &= sites.try_emplace(site.getValue(), op).second;
      return WalkResult::advance();
    });
  };
  index(program, commonSites);
  index(producer, pSites);
  index(validator, vSites);
  if (!valid)
    return refuse();
  SmallVector<NativeRequestCountPair> result;
  for (const auto &entry : owner.realizationFacts()) {
    if (entry.entry != policy.entry)
      continue;
    std::map<std::vector<unsigned>, SmallVector<Occurrence>> rounds;
    SmallVector<Occurrence> loops;
    for (const auto &occurrence : entry.occurrences) {
      if (occurrence.purpose != "query_round_count" &&
          occurrence.purpose != "query_requests")
        continue;
      Occurrence value{occurrence.site, occurrence.role, occurrence.sourcePath};
      if (occurrence.purpose == "query_round_count")
        rounds[value.path].push_back(value);
      else
        loops.push_back(value);
    }
    for (const auto &item : loops) {
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
      auto found = rounds.find(item.path);
      if (found == rounds.end() || found->second.size() != 2)
        return refuse();
      for (const auto &round : found->second) {
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
      bool blockFound = false;
      for (const auto &block : entry.queryBlocks) {
        if (block.queries.empty())
          return refuse();
        if (block.queries.front() == item.path) {
          if (blockFound || !block.packetCapacity ||
              *block.packetCapacity == 0 || *block.packetCapacity >= 1048576)
            return refuse();
          blockFound = true;
        }
      }
      if (!blockFound)
        return refuse();
      result.push_back({pCount, vCount});
    }
  }
  return result;
}
} // namespace zkc::detail
