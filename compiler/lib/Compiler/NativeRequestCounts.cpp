#include "../Transforms/RealizedProtocol.h"
#include "NativeRequest.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringMap.h"

using namespace mlir;
using namespace llvm;
namespace zkc::detail {
namespace {
namespace pir = protocol_ir;
Error refuse() { return error("native-request-count-correspondence"); }
struct Occurrence {
  std::string site, role, path;
};
std::string pathKey(const json::Array &path) {
  return printJson(json::Value(json::Array(path)));
}
} // namespace
Expected<SmallVector<NativeRequestCountPair>>
readNativeRequestCounts(const mathematical::RealizedProtocol &owner,
                        pir::ProtocolModuleOp projected,
                        const NativeProofPolicy &policy) {
  auto source = owner.preparedSnapshot();
  auto common = owner.candidateSnapshot();
  auto ordinary = owner.project(false);
  if (!source || !common || !ordinary ||
      !hasSingleElement(*ordinary->getBody()) ||
      !OperationEquivalence::isEquivalentTo(
          &ordinary->getBody()->front(), projected,
          OperationEquivalence::IgnoreLocations))
    return refuse();
  // Construction of the immutable owner uses the independent realization
  // reader to check actual allocation
  // order, child lookup operands, stored construction counts, multiplicity,
  // overflow bounds and the per-block ceiling calculation. The record below
  // supplies association only, after those actual-body premises have passed.
  auto record = json::parse(owner.realizationRecord());
  auto *object = record ? record->getAsObject() : nullptr;
  auto *entries = object ? object->getArray("entries") : nullptr;
  if (!entries) {
    if (!record)
      consumeError(record.takeError());
    return refuse();
  }
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
  for (const auto &entryValue : *entries) {
    auto *entry = entryValue.getAsObject();
    if (!entry || entry->getString("entry") != policy.entry)
      continue;
    auto *occurrences = entry->getArray("occurrences");
    auto *blocks = entry->getArray("query_blocks");
    if (!occurrences || !blocks || occurrences->size() > 100000)
      return refuse();
    StringMap<SmallVector<Occurrence>> rounds;
    SmallVector<Occurrence> loops;
    for (const auto &row : *occurrences) {
      auto *occurrence = row.getAsObject();
      auto purpose =
          occurrence ? occurrence->getString("purpose") : std::nullopt;
      if (!purpose ||
          (*purpose != "query_round_count" && *purpose != "query_requests"))
        continue;
      auto site = occurrence->getString("site"),
           role = occurrence->getString("role");
      auto *path = occurrence->getArray("path");
      if (!site || !role || !path)
        return refuse();
      Occurrence value{site->str(), role->str(), pathKey(*path)};
      if (*purpose == "query_round_count")
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
      for (const auto &value : *blocks) {
        auto *block = value.getAsObject();
        auto *queries = block ? block->getArray("queries") : nullptr;
        if (!queries || queries->empty() || !queries->front().getAsArray())
          return refuse();
        if (pathKey(*queries->front().getAsArray()) == item.path) {
          auto capacity = block->getInteger("packet_capacity");
          if (blockFound || !capacity || *capacity <= 0 || *capacity >= 1048576)
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
