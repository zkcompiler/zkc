//===- CanonicalEncoder.cpp - Canonical protocol encoding -------*- C++ -*-===//
// The identity walk (kernel.md §8). The encoding is fully positional:
// author labels never appear, so renaming is id-stable (≅ is a real
// equivalence, not string equality — carrier.md §6). Three position
// spaces mirror the kernel geometry: event position (≤ block order of
// the spine), claim position (production order over the transformer
// walk), and transformer position (the normalized source-then-reduce
// sequence). Every reference — challenge deps, check inputs, terminal
// selections, material endpoints, consumed claims, membership instances —
// is one of these positions.
// Nothing outside the kernel identity set enters, so evidence metadata
// can never perturb an id.
//===----------------------------------------------------------------------===//

#include "zkc/Encoding/CanonicalEncoder.h"

#include "zkc/Dialect/Oir/OirOps.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Encoding/EncodingDomain.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/TypeSwitch.h"
#include "llvm/Support/SHA256.h"

#include <set>

using namespace mlir;
using llvm::json::Array;
using JValue = llvm::json::Value;

namespace zkc {
namespace encoding {

/// Validate before build for op-level string fields: constructing a
/// json::Value from invalid UTF-8 traps in checked builds, so every
/// string is admitted to the encoding domain before its row is built —
/// the same principle attributeToCanonicalJson applies inside attribute trees.
static llvm::Error checkStrings(std::initializer_list<StringRef> strings) {
  for (StringRef value : strings)
    if (!zkc::encoding::inEncodingDomain(value))
      return llvm::createStringError(
          "string leaves the canonical encoding domain (printable ASCII)");
  return llvm::Error::success();
}

llvm::Expected<std::string> canonicalSourceClaimKey(llvm::StringRef profile,
                                                    const JValue &anchors) {
  std::string key = profile.str();
  key.push_back('\0');
  llvm::raw_string_ostream os(key);
  if (llvm::Error err = writeCanonicalJson(anchors, os))
    return std::move(err);
  return key;
}

llvm::Expected<JValue> canonicalClaimDescriptor(llvm::StringRef profile,
                                                DictionaryAttr anchors) {
  if (llvm::Error err = checkStrings({profile}))
    return std::move(err);
  auto anchorJson = attributeToCanonicalJson(anchors);
  if (!anchorJson)
    return anchorJson.takeError();
  return JValue(Array{profile, std::move(*anchorJson)});
}

CanonicalIndex canonicalEventIndex(Block &body) {
  CanonicalIndex index;
  int64_t position = 0;
  auto record = [&](Operation *operation, Value value = Value()) {
    index.eventOperationPositions[operation] = position;
    if (value)
      index.eventPositions[value] = position;
    else
      index.checkPositions[operation] = position;
    ++position;
  };
  for (Operation &operation : body)
    llvm::TypeSwitch<Operation *>(&operation)
        .Case<pir::BindOp>([&](auto op) { record(&operation, op.getVal()); })
        .Case<pir::SlotOp>([&](auto op) { record(&operation, op.getVal()); })
        .Case<pir::ChalOp>([&](auto op) { record(&operation, op.getVal()); })
        .Case<pir::CheckOp>([&](auto) { record(&operation); })
        // A bounded artifact verification is a spine event: it threads the
        // transcript and must reach the endpoint decision, so it occupies a
        // canonical event position like any other (kernel.md §1.1).
        .Case<pir::ArtifactVerifyOp>([&](auto op) {
          record(&operation, op.getOut());
        })
        .Default([](Operation *) {});
  return index;
}

std::optional<int64_t> canonicalEventPosition(const CanonicalIndex &index,
                                              Operation *operation) {
  auto found = index.eventOperationPositions.find(operation);
  if (found == index.eventOperationPositions.end())
    return std::nullopt;
  return found->second;
}

int64_t canonicalEventCount(const CanonicalIndex &index) {
  return static_cast<int64_t>(index.eventOperationPositions.size());
}

namespace {

/// One encoding walk over a verified container body. The walk is
/// three passes over the two geometries: number the spine events
/// (≤ order), normalize and number the transformers (claim graph),
/// then emit all three sections with references resolved to positions.
class Encoder {
public:
  llvm::Expected<JValue> encode(Operation *container, StringRef policy,
                                DictionaryAttr kappa, DictionaryAttr vocab,
                                DictionaryAttr routes,
                                llvm::ArrayRef<int64_t> segments) {
    if (llvm::Error err = checkStrings({policy}))
      return std::move(err);
    Block &body = container->getRegion(0).front();
    this->routes = routes;
    indexReduceLabels(body);

    // Pass 1: spine events in ≤ order. The public event index is the one
    // operation-level authority shared by encoding, projection, and
    // composition. The value maps key dependency, input, terminal-selection,
    // and material references for the later encoding passes.
    CanonicalIndex eventIndex = canonicalEventIndex(body);
    eventOperationPositions = std::move(eventIndex.eventOperationPositions);
    valEvent = std::move(eventIndex.eventPositions);
    checkPosition = std::move(eventIndex.checkPositions);
    for (Operation &op : body) {
      if (auto bind = dyn_cast<pir::BindOp>(op)) {
        int64_t position = valEvent.lookup(bind.getVal());
        if (!bindPos.insert({bind.getLabel(), position}).second)
          dupLabels.insert(("bind:" + bind.getLabel()).str());
      } else if (auto slot = dyn_cast<pir::SlotOp>(op)) {
        int64_t position = valEvent.lookup(slot.getVal());
        if (!slotPos.insert({slot.getLabel(), position}).second)
          dupLabels.insert(("slot:" + slot.getLabel()).str());
      } else if (auto chal = dyn_cast<pir::ChalOp>(op)) {
        int64_t position = valEvent.lookup(chal.getVal());
        if (!chalPos.insert({chal.getLabel(), position}).second)
          dupLabels.insert(("chal:" + chal.getLabel()).str());
      } else if (auto check = dyn_cast<pir::CheckOp>(op)) {
        checkEvent[check.getLabel()] =
            checkPosition.lookup(check.getOperation());
      } else if (auto verify = dyn_cast<pir::ArtifactVerifyOp>(op)) {
        int64_t position = valEvent.lookup(verify.getOut());
        if (!slotPos.insert({verify.getLabel(), position}).second)
          dupLabels.insert(("artifact_verify:" + verify.getLabel()).str());
      }
    }
    if (routes)
      if (auto witnesses = dyn_cast_or_null<ArrayAttr>(routes.get("witnesses")))
        for (auto [index, entry] : llvm::enumerate(witnesses))
          if (auto pair = dyn_cast<ArrayAttr>(entry))
            if (pair.size() == 2)
              if (auto label = dyn_cast<StringAttr>(pair[0]))
                witnessIndex[label.getValue()] = static_cast<int64_t>(index);

    // Pass 2: transformers. Kernel C and R are sets, so authored
    // order is normalized away on BOTH tails: sources sort by content
    // (profile, then canonical anchor bytes — exact-content ties keep
    // authored order, a named limitation for duplicated sources);
    // reduces are normalized topologically below. Claim positions are
    // production order over the normalized sequence.
    SmallVector<pir::InstantiateOp> sources;
    SmallVector<pir::ReduceOp> reduces;
    for (Operation &op : body) {
      if (auto source = dyn_cast<pir::InstantiateOp>(op))
        sources.push_back(source);
      else if (auto reduce = dyn_cast<pir::ReduceOp>(op))
        reduces.push_back(reduce);
    }
    struct SourceRow {
      std::string key;
      pir::InstantiateOp op;
      JValue anchors;
    };
    SmallVector<SourceRow> sourceRows;
    for (pir::InstantiateOp source : sources) {
      StringRef profile =
          cast<pir::ClaimType>(source.getClaim().getType()).getProfile();
      if (llvm::Error err = checkStrings({profile}))
        return std::move(err);
      auto anchors = attributeToCanonicalJson(source.getAnchors());
      if (!anchors)
        return anchors.takeError();
      auto key = canonicalSourceClaimKey(profile, *anchors);
      if (!key)
        return key.takeError();
      // The anchor JSON rides along: the row emitted below is built
      // from the exact value the sort key serialized, one conversion.
      sourceRows.push_back({std::move(*key), source, std::move(*anchors)});
    }
    llvm::stable_sort(sourceRows, [](const SourceRow &a, const SourceRow &b) {
      return a.key < b.key;
    });
    // Two sources with identical content would be ordered by the order
    // they were authored in, and their claim positions would follow —
    // so one protocol could take two identities depending on how it
    // was written. The canonical form is a complete invariant only if
    // that cannot happen, and the container already refuses duplicate
    // descriptor bytes one level up, so this refuses rather than
    // breaking the tie. An author who wants two claims about the same
    // relation distinguishes them by anchor.
    for (size_t index = 1; index < sourceRows.size(); ++index)
      if (sourceRows[index].key == sourceRows[index - 1].key)
        return llvm::createStringError(
            "[zkc-E172] two sources have identical profile and anchors, so "
            "their claim positions would depend on authored order");
    for (SourceRow &row : sourceRows) {
      claimPos[row.op.getClaim()] = claimCount++;
      transformerCount++;
    }
    if (llvm::Error err = normalizeReduces(reduces))
      return std::move(err);

    // Pass 3: emit. Sources then reduces, both in normalized order;
    // then the spine events; then the sinks (normalized by the
    // producer position of the claim each routes).
    for (SourceRow &row : sourceRows)
      transformers.push_back(
          Array{"source",
                cast<pir::ClaimType>(row.op.getClaim().getType()).getProfile(),
                std::move(row.anchors)});
    for (pir::ReduceOp reduce : normalizedReduces) {
      auto row = encodeReduce(reduce);
      if (!row)
        return row.takeError();
      transformers.push_back(std::move(*row));
    }
    for (Operation &op : body)
      if (llvm::Error err = encodeEvent(&op))
        return std::move(err);
    if (llvm::Error err = encodeMaterialBindings(body))
      return std::move(err);
    if (llvm::Error err = encodeSinks(body))
      return std::move(err);

    llvm::json::Object kappaJson;
    if (kappa) {
      auto json = attributeToCanonicalJson(kappa);
      if (!json)
        return json.takeError();
      kappaJson = std::move(*json->getAsObject());
    }
    // The resolved-vocabulary table is identity content (kernel.md
    // §8): without it the body's citations name registry entries
    // whose content the id would not pin — a shadow entry could
    // survive. The seal stamps the table; anything unstamped has no
    // canonical identity. Checked here at assembly, after the walk,
    // so out-of-domain content is still named at its own field first.
    if (!vocab)
      return llvm::createStringError(
          "container carries no resolved-vocabulary table: the seal "
          "stamps cited semantic-vocabulary content digests "
          "before anything is encoded");
    // The table is a closed set: five sections always, and two more that
    // appear exactly when something cites them. Anything else in it
    // would ride into identity unseen by any judgment (the judges
    // verify only the known sections), so reject an unknown section
    // here at the identity function itself, fail-closed like every
    // other out-of-domain shape. Construction profiles stay because kappa
    // determines transcript bytes; no section names a security analysis,
    // because an analysis is derived about a sealed protocol rather than
    // carried inside it.
    size_t expected = 5;
    if (vocab.getNamed("hole_contracts"))
      ++expected;
    if (vocab.getNamed("value_profiles"))
      ++expected;
    if (vocab.size() != expected)
      return llvm::createStringError(
          "resolved-vocabulary table must contain exactly claim_profiles, "
          "check_contracts, reduction_contracts, terminal_rules, "
          "and construction_profiles, plus hole_contracts only when routes "
          "cite hole contracts and value_profiles only when a value names a "
          "profile");
    for (NamedAttribute section : vocab) {
      StringRef name = section.getName().getValue();
      if (name != "claim_profiles" && name != "check_contracts" &&
          name != "reduction_contracts" && name != "terminal_rules" &&
          name != "construction_profiles" && name != "hole_contracts" &&
          name != "value_profiles")
        return llvm::createStringError(
            "resolved-vocabulary table has an unknown section '" + name.str() +
            "': only claim_profiles, check_contracts, reduction_contracts, "
            "terminal_rules, construction_profiles, hole_contracts, and "
            "value_profiles are identity content");
      if (!isa<DictionaryAttr>(section.getValue()))
        return llvm::createStringError("resolved-vocabulary section '" +
                                       name.str() + "' must be a dictionary");
    }
    auto vocabJson = attributeToCanonicalJson(vocab);
    if (!vocabJson)
      return vocabJson.takeError();
    // The segment decomposition is identity-bearing, so a spelling the
    // battery would refuse must not reach an id: starts are strictly
    // increasing event positions strictly inside the spine. Mirrors the
    // seal-time judgment so the pure-identity path fails closed too.
    size_t bodyEventCount = events.size();
    {
      int64_t previous = 0;
      for (int64_t start : segments) {
        if (start <= previous || start >= static_cast<int64_t>(bodyEventCount))
          return llvm::createStringError(
              "segment start " + std::to_string(start) +
              " is not a strictly increasing event position inside a spine "
              "of " +
              std::to_string(bodyEventCount) + " event(s)");
        previous = start;
      }
    }
    llvm::json::Object doc{{"policy", policy},
                           {"kappa", std::move(kappaJson)},
                           {"vocab", std::move(*vocabJson)},
                           {"transformers", std::move(transformers)},
                           {"events", std::move(events)},
                           {"material_bindings", std::move(materialBindings)},
                           {"sinks", std::move(sinks)}};
    // The segment decomposition is judgment-bearing (the
    // statement-binding default is judged per segment, kernel.md
    // §5.3) and therefore identity-bearing — emitted additively: a
    // one-segment artifact encodes exactly as before.
    if (!segments.empty()) {
      llvm::json::Array starts;
      for (int64_t start : segments)
        starts.push_back(start);
      doc["segments"] = std::move(starts);
    }
    // Construction routes are declared protocol content and enter
    // identity additively: a protocol without routes emits no section
    // and keeps its exact bytes (docs/spec/carrier.md §6).
    if (routes) {
      auto routesJson = encodeRoutes();
      if (!routesJson)
        return routesJson.takeError();
      doc["routes"] = std::move(*routesJson);
    }
    return JValue(std::move(doc));
  }

private:
  /// Normalizes one authored route reference to its canonical,
  /// label-free form: events by position, witnesses by ordinal,
  /// constants by kappa name, hole outputs by (instance, index).
  llvm::Expected<JValue> normalizeRouteRef(StringRef text) {
    auto resolveEvent = [&](const llvm::StringMap<int64_t> &positions,
                            StringRef tag,
                            StringRef name) -> llvm::Expected<JValue> {
      if (dupLabels.contains((tag + ":" + name).str()))
        return llvm::createStringError("route reference '" + tag.str() + ":" +
                                       name.str() +
                                       "' names an ambiguous label");
      auto it = positions.find(name);
      if (it == positions.end())
        return llvm::createStringError("route reference '" + tag.str() + ":" +
                                       name.str() + "' does not resolve");
      return JValue(Array{"event", it->second});
    };
    StringRef rest = text;
    if (rest.consume_front("bind:"))
      return resolveEvent(bindPos, "bind", rest);
    if (rest.consume_front("slot:"))
      return resolveEvent(slotPos, "slot", rest);
    if (rest.consume_front("chal:"))
      return resolveEvent(chalPos, "chal", rest);
    if (rest.consume_front("const:")) {
      if (llvm::Error err = checkStrings({rest}))
        return std::move(err);
      return JValue(Array{"const", rest});
    }
    if (rest.consume_front("witness:")) {
      auto it = witnessIndex.find(rest);
      if (it == witnessIndex.end())
        return llvm::createStringError(
            "route reference 'witness:" + rest.str() +
            "' names an undeclared payload");
      return JValue(Array{"witness", it->second});
    }
    size_t dot = rest.rfind('.');
    unsigned output = 0;
    if (dot == StringRef::npos || dot == 0 ||
        rest.substr(dot + 1).getAsInteger(10, output))
      return llvm::createStringError("'" + rest.str() +
                                     "' is not a route reference");
    StringRef instance = rest.substr(0, dot);
    if (llvm::Error err = checkStrings({instance}))
      return std::move(err);
    return JValue(Array{"hole", instance, static_cast<int64_t>(output)});
  }

  /// The canonical routes section: witness payload classes in declared
  /// order (labels are prover-endpoint ABI, not identity), instances
  /// keyed by their declared names with normalized inputs.
  llvm::Expected<JValue> encodeRoutes() {
    Array witnesses;
    if (auto list = dyn_cast_or_null<ArrayAttr>(routes.get("witnesses")))
      for (Attribute entry : list) {
        auto pair = dyn_cast<ArrayAttr>(entry);
        auto cls = pair && pair.size() == 2 ? dyn_cast<StringAttr>(pair[1])
                                            : StringAttr();
        if (!cls)
          return llvm::createStringError(
              "routes witnesses must be [label, class] string pairs");
        if (llvm::Error err = checkStrings({cls.getValue()}))
          return std::move(err);
        witnesses.push_back(cls.getValue());
      }
    auto instances = dyn_cast_or_null<DictionaryAttr>(routes.get("instances"));
    if (!instances)
      return llvm::createStringError("routes carries no instances section");
    llvm::json::Object instancesJson;
    for (NamedAttribute entry : instances) {
      StringRef name = entry.getName().getValue();
      auto body = dyn_cast<DictionaryAttr>(entry.getValue());
      auto contract = body ? dyn_cast_or_null<StringAttr>(body.get("contract"))
                           : StringAttr();
      auto inputs =
          body ? dyn_cast_or_null<ArrayAttr>(body.get("inputs")) : ArrayAttr();
      if (!contract || !inputs)
        return llvm::createStringError("route instance '" + name.str() +
                                       "' needs contract and inputs");
      if (llvm::Error err = checkStrings({name, contract.getValue()}))
        return std::move(err);
      Array inputsJson;
      for (Attribute input : inputs) {
        auto text = dyn_cast<StringAttr>(input);
        if (!text)
          return llvm::createStringError("route instance '" + name.str() +
                                         "' input is not a string");
        auto normalized = normalizeRouteRef(text.getValue());
        if (!normalized)
          return normalized.takeError();
        inputsJson.push_back(std::move(*normalized));
      }
      llvm::json::Object instanceJson{{"contract", contract.getValue()},
                                      {"inputs", std::move(inputsJson)}};
      if (auto params = dyn_cast_or_null<DictionaryAttr>(body.get("params"));
          params && !params.empty()) {
        auto paramsJson = attributeToCanonicalJson(params);
        if (!paramsJson)
          return paramsJson.takeError();
        instanceJson["params"] = std::move(*paramsJson);
      }
      instancesJson[name] = std::move(instanceJson);
    }
    return JValue(llvm::json::Object{{"instances", std::move(instancesJson)},
                                     {"witnesses", std::move(witnesses)}});
  }
  /// Kahn's algorithm with the complete canonical reduce row as its
  /// content tie-break: a reduce is emitted after every reduce producing a
  /// claim it consumes, and independent ready reductions compare by
  /// (contract, ordered consumed claim positions,
  /// dependency event positions, output profiles, parameters, authored output
  /// anchors, role-sorted selected check event positions). Exact-content ties
  /// alone keep authored order. Omitting any semantic field would let two
  /// independent, semantically distinct reductions retain carrier order in
  /// identity; sorting consumed claims would erase a contract-defined input
  /// order. A key is computable exactly when its last consumed claim is
  /// positioned and never changes after, so the ready set is an ordered set
  /// with keys computed once — O(n log n + edges) on the hot path of every
  /// seal and id.
  llvm::Error normalizeReduces(ArrayRef<pir::ReduceOp> reduces) {
    struct ReadyKey {
      std::string contract;
      SmallVector<int64_t> consumed;
      SmallVector<int64_t> deps;
      SmallVector<std::string> profiles;
      std::string params;
      std::string anchors;
      SmallVector<std::pair<std::string, int64_t>> checks;
      size_t authored; // unique: makes the order total, ties stable
      bool operator<(const ReadyKey &o) const {
        if (contract != o.contract)
          return contract < o.contract;
        if (consumed != o.consumed)
          return std::lexicographical_compare(consumed.begin(), consumed.end(),
                                              o.consumed.begin(),
                                              o.consumed.end());
        if (deps != o.deps)
          return std::lexicographical_compare(deps.begin(), deps.end(),
                                              o.deps.begin(), o.deps.end());
        if (profiles != o.profiles)
          return std::lexicographical_compare(profiles.begin(), profiles.end(),
                                              o.profiles.begin(),
                                              o.profiles.end());
        if (params != o.params)
          return params < o.params;
        if (anchors != o.anchors)
          return anchors < o.anchors;
        if (checks != o.checks)
          return std::lexicographical_compare(checks.begin(), checks.end(),
                                              o.checks.begin(), o.checks.end());
        return authored < o.authored;
      }
    };
    // Wire consumers: which reduces wait on a claim, and how many of
    // each reduce's consumed claims are still unpositioned.
    llvm::DenseMap<Value, SmallVector<size_t>> waiters;
    SmallVector<unsigned> missing(reduces.size(), 0);
    for (size_t i = 0; i < reduces.size(); ++i) {
      pir::ReduceOp reduce = reduces[i];
      for (Value claim : reduce.getClaims())
        if (!claimPos.contains(claim)) {
          waiters[claim].push_back(i);
          ++missing[i];
        }
    }
    auto makeKey = [&](size_t i) -> llvm::Expected<ReadyKey> {
      pir::ReduceOp reduce = reduces[i];
      ReadyKey key;
      key.contract = reduce.getContract().str();
      for (Value claim : reduce.getClaims())
        key.consumed.push_back(claimPos.lookup(claim));
      for (Value dep : reduce.getDeps())
        key.deps.push_back(valEvent.lookup(dep));
      for (Value out : reduce.getOuts())
        key.profiles.push_back(
            cast<pir::ClaimType>(out.getType()).getProfile().str());

      auto params = encodeReduceParams(reduce);
      if (!params)
        return params.takeError();
      auto paramsBytes = canonicalJsonBytes(*params);
      if (!paramsBytes)
        return paramsBytes.takeError();
      key.params = std::move(*paramsBytes);

      auto anchors = encodeReduceAnchors(reduce);
      if (!anchors)
        return anchors.takeError();
      auto anchorBytes = canonicalJsonBytes(JValue(std::move(*anchors)));
      if (!anchorBytes)
        return anchorBytes.takeError();
      key.anchors = std::move(*anchorBytes);

      auto checks = reduceCheckPositions(reduce);
      if (!checks)
        return checks.takeError();
      key.checks = std::move(*checks);
      key.authored = i;
      return key;
    };
    std::set<ReadyKey> ready;
    for (size_t i = 0; i < reduces.size(); ++i) {
      if (missing[i] != 0)
        continue;
      auto key = makeKey(i);
      if (!key)
        return key.takeError();
      ready.insert(std::move(*key));
    }
    size_t emitted = 0;
    while (!ready.empty()) {
      size_t i = ready.begin()->authored;
      ready.erase(ready.begin());
      pir::ReduceOp reduce = reduces[i];
      reduceTransformer[reduce.getOperation()] = transformerCount++;
      normalizedReduces.push_back(reduce);
      ++emitted;
      for (Value out : reduce.getOuts()) {
        claimPos[out] = claimCount++;
        auto waiting = waiters.find(out);
        if (waiting == waiters.end())
          continue;
        for (size_t waiter : waiting->second)
          if (--missing[waiter] == 0) {
            auto key = makeKey(waiter);
            if (!key)
              return key.takeError();
            ready.insert(std::move(*key));
          }
      }
    }
    if (emitted != reduces.size())
      return llvm::createStringError(
          "reduction claim flow is not acyclic (container verifier "
          "should have rejected this)");
    return llvm::Error::success();
  }

  using CheckPosition = std::pair<std::string, int64_t>;

  llvm::Expected<SmallVector<CheckPosition>>
  reduceCheckPositions(pir::ReduceOp reduce) const {
    SmallVector<CheckPosition> selected;
    for (NamedAttribute named : reduce.getChecks()) {
      StringRef role = named.getName().getValue();
      auto label = dyn_cast<StringAttr>(named.getValue());
      if (!label)
        return llvm::createStringError(
            "reduce check mapping values must be strings");
      if (llvm::Error err = checkStrings({role, label.getValue()}))
        return std::move(err);
      auto position = checkEvent.find(label.getValue());
      if (position == checkEvent.end())
        return llvm::createStringError("reduce selects an unknown check");
      selected.emplace_back(role.str(), position->second);
    }
    llvm::sort(selected, [](const CheckPosition &a, const CheckPosition &b) {
      return a.first < b.first;
    });
    return selected;
  }

  static llvm::Expected<JValue> encodeReduceParams(pir::ReduceOp reduce) {
    if (!reduce.getParams())
      return JValue(llvm::json::Object{});
    return attributeToCanonicalJson(*reduce.getParams());
  }

  static llvm::Expected<Array> encodeReduceAnchors(pir::ReduceOp reduce) {
    Array anchors;
    auto authoredAnchors = reduce.getOutAnchors();
    if (authoredAnchors && authoredAnchors->size() != reduce.getOuts().size())
      return llvm::createStringError(
          "reduce out_anchors arity does not match its result count");
    for (size_t i = 0; i < reduce.getOuts().size(); ++i) {
      Attribute anchorAttr =
          authoredAnchors ? (*authoredAnchors)[i] : Attribute();
      if (!anchorAttr) {
        anchors.push_back(llvm::json::Object{});
        continue;
      }
      auto dictionary = dyn_cast<DictionaryAttr>(anchorAttr);
      if (!dictionary)
        return llvm::createStringError(
            "each reduce output anchor entry must be a dictionary");
      auto json = attributeToCanonicalJson(dictionary);
      if (!json)
        return json.takeError();
      anchors.push_back(std::move(*json));
    }
    return anchors;
  }

  llvm::Expected<JValue> encodeReduce(pir::ReduceOp reduce) {
    // The resolved vocabulary table is the sole digest authority for reduction
    // contracts. The operation carries only the id; a parallel per-operation
    // digest would be duplicate authority that could disagree.
    if (llvm::Error err = checkStrings({reduce.getContract()}))
      return std::move(err);
    Array consumed;
    for (Value claim : reduce.getClaims())
      consumed.push_back(claimPos.lookup(claim));
    Array deps;
    for (Value dep : reduce.getDeps())
      deps.push_back(valEvent.lookup(dep));
    Array produced;
    for (Value out : reduce.getOuts()) {
      StringRef profile = cast<pir::ClaimType>(out.getType()).getProfile();
      if (llvm::Error err = checkStrings({profile}))
        return std::move(err);
      produced.push_back(profile);
    }
    auto params = encodeReduceParams(reduce);
    if (!params)
      return params.takeError();
    auto anchors = encodeReduceAnchors(reduce);
    if (!anchors)
      return anchors.takeError();
    auto checks = reduceCheckPositions(reduce);
    if (!checks)
      return checks.takeError();
    Array selectedChecks;
    for (const auto &[role, position] : *checks)
      selectedChecks.push_back(Array{role, position});

    // The contract's content digest lives once in vocab.reduction_contracts.
    return JValue(Array{"reduce", reduce.getContract(), std::move(consumed),
                        std::move(deps), std::move(produced),
                        std::move(*params), std::move(*anchors),
                        std::move(selectedChecks)});
  }

  /// The sink kinds, spelled once: encodeEvent skips exactly what
  /// encodeSinks collects.
  static bool isSinkOp(Operation *op) {
    return isa<pir::DischargeOp, pir::ExportOp, pir::AssumeOp, pir::ResidualOp>(
        op);
  }

  /// A contract role's occupant is encoded the same way whoever fills it:
  /// the owning transformer's position, the role, and the occurrence index.
  llvm::Expected<JValue> encodeMembership(std::optional<pir::Membership> m) {
    if (!m)
      return JValue(nullptr);
    if (llvm::Error err = checkStrings({m->role}))
      return std::move(err);
    // Fail closed like every other encoder path: a dangling instance must
    // never alias onto transformer position 0.
    pir::ReduceOp owner = reduceByLabel.lookup(m->instance);
    if (!owner)
      return llvm::createStringError(
          "membership instance does not resolve to a reduce");
    return JValue(Array{reduceTransformer.lookup(owner.getOperation()),
                        m->role, m->idx});
  }

  llvm::Error encodeEvent(Operation *op) {
    if (auto bind = dyn_cast<pir::BindOp>(op)) {
      if (llvm::Error err = checkStrings(
              {bind.getPayloadClass(), bind.getValue().value_or("")}))
        return err;
      JValue value = nullptr;
      if (bind.getValue())
        value = *bind.getValue();
      // A profiled binding is its own event family, exactly as a profiled
      // slot is: it carries the profile name where the scalar family carries
      // a payload class, and its membership beside it, so no row outside the
      // protocols that use one moves (docs/spec/carrier.md §6).
      if (bind.getProfiled()) {
        auto membership = encodeMembership(bind.getMembership());
        if (!membership)
          return membership.takeError();
        events.push_back(Array{"bind_profiled", bind.getPayloadClass(),
                               stringifyStage(bind.getStage()),
                               std::move(value), std::move(*membership)});
      } else {
        events.push_back(Array{"bind", bind.getPayloadClass(),
                               stringifyStage(bind.getStage()),
                               std::move(value)});
      }
    } else if (auto slot = dyn_cast<pir::SlotOp>(op)) {
      if (llvm::Error err = checkStrings({slot.getPayloadClass()}))
        return err;
      auto membership = encodeMembership(slot.getMembership());
      if (!membership)
        return membership.takeError();
      // A counted slot is its own event family, and so is a profiled one:
      // the scalar family's rows keep their exact historical encoding, so
      // no identity outside the new protocols moves (docs/spec/carrier.md
      // §6's additive discipline). The families are distinguished by head
      // rather than by arity, because the optional route below is already
      // pushed additively and two optional tails would collide.
      // The profiled family carries no count, so a counted one would encode
      // as a scalar commitment. The op verifier refuses that shape at parse,
      // and this refuses it again: the encoder is fail-closed on its own
      // input, because it is the identity function and not a second reader
      // of someone else's guarantee.
      if (slot.getProfiled() && slot.getCount() != "1")
        return llvm::createStringError(
            "a profiled slot carries one commitment and cannot be counted");
      Array slotRow =
          slot.getProfiled()
              ? Array{"slot_profiled", slot.getPayloadClass(),
                      slot.getUnabsorbed() ? 0 : 1, std::move(*membership)}
          : slot.getCount() == "1"
              ? Array{"slot", slot.getPayloadClass(),
                      slot.getUnabsorbed() ? 0 : 1, std::move(*membership)}
              : Array{"slot_vec", slot.getPayloadClass(), slot.getCount(),
                      slot.getUnabsorbed() ? 0 : 1, std::move(*membership)};
      // The construction-route binding is identity content, emitted
      // additively with its references normalized to positions, so an
      // unbound slot encodes exactly as before and renaming stays
      // id-stable (docs/spec/carrier.md §6).
      if (auto binding = slot.getBinding()) {
        auto normalized = normalizeRouteRef(*binding);
        if (!normalized)
          return normalized.takeError();
        slotRow.push_back(std::move(*normalized));
      }
      events.push_back(std::move(slotRow));
    } else if (auto chal = dyn_cast<pir::ChalOp>(op)) {
      if (llvm::Error err = checkStrings(
              {chal.getPayloadClass(), chal.getDomain(), chal.getSpace()}))
        return err;
      // P_req is a set of event references (kernel.md §1.5): sorted
      // positions are its canonical spelling, so authored dep order
      // never perturbs the id. Duplicates cannot reach here — the
      // container rejects them (zkc-E154).
      SmallVector<int64_t> depPos;
      for (Value dep : chal.getDeps())
        depPos.push_back(valEvent.lookup(dep));
      llvm::sort(depPos);
      Array deps(depPos);
      Array event{"chal", chal.getPayloadClass(), chal.getDomain(),
                  chal.getSpace(), std::move(deps)};
      // χ mode axis M is a trailing section, present only for a vector
      // challenge — a scalar challenge encodes exactly as before, so no
      // pre-FRI golden moves (docs/spec/carrier.md §6, using the same
      // additive-section discipline as earlier format extensions).
      if (auto mode = chal.getMode()) {
        Array modeArray;
        for (const std::string &field : *mode) {
          if (llvm::Error err = checkStrings({field}))
            return err;
          modeArray.push_back(field);
        }
        event.push_back(std::move(modeArray));
      }
      events.push_back(std::move(event));
    } else if (auto verify = dyn_cast<pir::ArtifactVerifyOp>(op)) {
      // Every fact endpoints.md §3.1 binds is identity content: two parents
      // that verify different children, under different verifier semantics,
      // keys, statements, protocols, or relation contracts are different
      // protocols, and a digest that did not separate them would let one
      // stand in for the other.
      llvm::StringRef abi = verify.getAbi().value_or(llvm::StringRef());
      if (llvm::Error err = checkStrings(
              {verify.getChild(), verify.getEndpoint(), verify.getSemantics(),
               verify.getKey(), verify.getStatement(), verify.getProtocol(),
               verify.getRelationContract(), verify.getRoute(), abi}))
        return err;
      Array slots;
      if (auto declared = verify.getProofSlots())
        for (Attribute slot : *declared) {
          auto label = dyn_cast<StringAttr>(slot);
          if (!label)
            return llvm::createStringError(
                "an artifact verification proof slot is not a label");
          if (llvm::Error err = checkStrings({label.getValue()}))
            return err;
          // Slot labels normalize to canonical event positions, like every
          // other label the encoder emits: renaming a slot must not move
          // the identity.  Fail closed rather than defaulting: a label that
          // resolves to nothing must never alias onto event position 0,
          // which would give two different protocols one identity.
          auto proofSlot = slotPos.find(label.getValue());
          if (proofSlot == slotPos.end())
            return llvm::createStringError(
                "an artifact verification names a proof slot that resolves "
                "to no event");
          slots.push_back(proofSlot->second);
        }
      events.push_back(Array{"artifact_verify", verify.getChild(),
                             verify.getEndpoint(), verify.getSemantics(),
                             verify.getKey(), verify.getStatement(),
                             verify.getProtocol(),
                             verify.getRelationContract(), verify.getRoute(),
                             verify.getUnabsorbed() ? 0 : 1,
                             abi.empty() ? JValue(nullptr) : JValue(abi),
                             std::move(slots)});
    } else if (auto check = dyn_cast<pir::CheckOp>(op)) {
      if (llvm::Error err = checkStrings({check.getContract()}))
        return err;
      Array inputs;
      for (Value input : check.getInputs())
        inputs.push_back(valEvent.lookup(input));
      JValue params = llvm::json::Object{};
      if (auto declared = check.getParams()) {
        auto json = attributeToCanonicalJson(*declared);
        if (!json)
          return json.takeError();
        params = std::move(*json);
      }
      JValue semanticArgs = llvm::json::Object{};
      if (auto declared = check.getSemanticArgs()) {
        auto json = attributeToCanonicalJson(*declared);
        if (!json)
          return json.takeError();
        semanticArgs = std::move(*json);
      }
      JValue expr = nullptr;
      if (check.getExpr()) {
        auto json = attributeToCanonicalJson(*check.getExpr());
        if (!json)
          return json.takeError();
        expr = std::move(*json);
      }
      events.push_back(Array{"check", check.getContract(), std::move(inputs),
                             std::move(params), std::move(semanticArgs),
                             std::move(expr)});
    } else if (!isSinkOp(op) &&
               !isa<pir::BeginOp, pir::EndOp, pir::InstantiateOp, pir::ReduceOp,
                    pir::MaterialBindOp>(op)) {
      // Fail closed: begin/end are the structural frame and the claim
      // graph encodes in its own sections, but a member kind outside
      // that whitelist must never be silently skipped — dropping
      // content from the walk would give two distinct protocols one
      // id, the worst failure this encoder can have (kernel.md 8).
      // Unreachable today (the container verifier closes the member
      // set); it exists so the next member kind fails loudly.
      return llvm::createStringError("operation '" +
                                     op->getName().getStringRef() +
                                     "' has no canonical encoding");
    }
    return llvm::Error::success();
  }

  llvm::Error encodeMaterialBindings(Block &body) {
    SmallVector<std::pair<int64_t, std::string>> rows;
    std::set<int64_t> endpoints;
    std::set<std::string> semanticRefs;
    for (pir::MaterialBindOp binding : body.getOps<pir::MaterialBindOp>()) {
      auto endpoint = valEvent.find(binding.getValue());
      if (endpoint == valEvent.end())
        return llvm::createStringError(
            "material binding value has no canonical event position");
      if (!zkc::encoding::isSha256Ref(binding.getSemanticRef()))
        return llvm::createStringError(
            llvm::Twine("material binding semantic reference ") +
            zkc::encoding::kSha256RefMessage);
      if (llvm::Error err = checkStrings({binding.getSemanticRef()}))
        return err;
      if (!endpoints.insert(endpoint->second).second)
        return llvm::createStringError(
            "one canonical value endpoint has multiple material bindings");
      std::string semanticRef = binding.getSemanticRef().str();
      if (!semanticRefs.insert(semanticRef).second)
        return llvm::createStringError(
            "one semantic material reference has multiple value endpoints");
      rows.emplace_back(endpoint->second, std::move(semanticRef));
    }
    llvm::sort(rows);
    for (auto &[endpoint, semanticRef] : rows)
      materialBindings.push_back(Array{endpoint, semanticRef});
    return llvm::Error::success();
  }

  llvm::Error encodeSinks(Block &body) {
    // Normalize by the producer position of the routed claim
    // (carrier.md §6): a permutable sink block gives one id.
    SmallVector<Operation *> sinkOps;
    for (Operation &op : body)
      if (isSinkOp(&op))
        sinkOps.push_back(&op);
    llvm::stable_sort(sinkOps, [&](Operation *a, Operation *b) {
      return claimPos.lookup(a->getOperand(0)) <
             claimPos.lookup(b->getOperand(0));
    });
    auto encodeRouted = [&](StringRef kind, Value claim,
                            StringRef route) -> llvm::Error {
      if (route.empty())
        return llvm::createStringError(
            "terminal route reference must not be empty");
      if (llvm::Error err = checkStrings({route}))
        return err;
      sinks.push_back(Array{kind, claimPos.lookup(claim), route});
      return llvm::Error::success();
    };
    for (Operation *op : sinkOps) {
      if (auto discharge = dyn_cast<pir::DischargeOp>(op)) {
        if (llvm::Error err = checkStrings({discharge.getRule()}))
          return err;
        llvm::json::Object selectedChecks;
        for (NamedAttribute named : discharge.getChecks()) {
          StringRef role = named.getName().getValue();
          auto label = dyn_cast<StringAttr>(named.getValue());
          if (!label)
            return llvm::createStringError(
                "discharge check mapping values must be strings");
          if (llvm::Error err = checkStrings({role}))
            return err;
          auto position = checkEvent.find(label.getValue());
          if (position == checkEvent.end())
            return llvm::createStringError(
                "discharge selects an unknown check");
          selectedChecks[role] = position->second;
        }
        sinks.push_back(Array{"discharge",
                              claimPos.lookup(discharge.getClaim()),
                              discharge.getRule(), std::move(selectedChecks)});
      } else if (auto exp = dyn_cast<pir::ExportOp>(op)) {
        if (llvm::Error err =
                encodeRouted("export", exp.getClaim(), exp.getRoute()))
          return err;
      } else if (auto asm_ = dyn_cast<pir::AssumeOp>(op)) {
        if (llvm::Error err =
                encodeRouted("assume", asm_.getClaim(), asm_.getRoute()))
          return err;
      } else if (auto res = dyn_cast<pir::ResidualOp>(op)) {
        if (llvm::Error err =
                encodeRouted("residual", res.getClaim(), res.getRoute()))
          return err;
      }
    }
    return llvm::Error::success();
  }

  /// Membership resolves a reduce label to a transformer position; the
  /// label map is built before encoding events.
  void indexReduceLabels(Block &body) {
    for (Operation &op : body)
      if (auto reduce = dyn_cast<pir::ReduceOp>(op))
        reduceByLabel[reduce.getLabel()] = reduce;
  }

  Array transformers, events, materialBindings, sinks;
  int64_t claimCount = 0, transformerCount = 0;
  llvm::DenseMap<Operation *, int64_t> eventOperationPositions;
  llvm::DenseMap<Value, int64_t> valEvent; // event-producing value → pos
  llvm::DenseMap<Operation *, int64_t> checkPosition;
  llvm::DenseMap<Value, int64_t> claimPos; // claim value → claim pos
  llvm::StringMap<int64_t> checkEvent;     // check label → event pos
  llvm::DenseMap<Operation *, int64_t> reduceTransformer;
  llvm::StringMap<pir::ReduceOp> reduceByLabel;
  SmallVector<pir::ReduceOp> normalizedReduces;
  // Route normalization state: authored labels resolve to positions
  // (events) and ordinals (witness payloads); an ambiguous referenced
  // label is refused, never guessed.
  DictionaryAttr routes;
  llvm::StringMap<int64_t> bindPos, slotPos, chalPos, witnessIndex;
  llvm::StringSet<> dupLabels;

public:
  /// Harvest of the position spaces this walk computed, for consumers
  /// that need the same numbering the encoding wrote
  /// (zkc::encoding::canonicalIndex). Call after encode().
  void harvestPositions(CanonicalIndex &index) {
    index.eventOperationPositions = std::move(eventOperationPositions);
    index.eventPositions = std::move(valEvent);
    index.checkPositions = std::move(checkPosition);
    index.transformerPositions = std::move(reduceTransformer);
    index.claimPositions = std::move(claimPos);
  }
};

} // namespace

/// The container facts both identity entry points unpack — one
/// spelling, so the two walks can never read a container differently.
struct ContainerFacts {
  StringRef policy;
  DictionaryAttr kappa, vocab, routes;
  SmallVector<int64_t> segments;
};

static llvm::Expected<ContainerFacts> unpackContainer(Operation *container) {
  ContainerFacts facts;
  if (auto protocol = dyn_cast<pir::ProtocolOp>(container)) {
    facts.policy = protocol.getPolicy();
    facts.kappa = protocol.getKappa().value_or(DictionaryAttr());
    facts.vocab = protocol.getVocab().value_or(DictionaryAttr());
    facts.routes = protocol.getRoutes().value_or(DictionaryAttr());
    if (auto starts = protocol.getSegments())
      facts.segments.assign(starts->begin(), starts->end());
  } else if (auto sealed = dyn_cast<pir::SealedOp>(container)) {
    facts.policy = sealed.getPolicy();
    facts.kappa = sealed.getKappa().value_or(DictionaryAttr());
    facts.vocab = sealed.getVocab().value_or(DictionaryAttr());
    facts.routes = sealed.getRoutes().value_or(DictionaryAttr());
    if (auto starts = sealed.getSegments())
      facts.segments.assign(starts->begin(), starts->end());
  } else {
    return llvm::createStringError("not a protocol container");
  }
  return facts;
}

llvm::Expected<std::string> encodeCanonical(Operation *container) {
  auto facts = unpackContainer(container);
  if (!facts)
    return facts.takeError();
  auto json = Encoder().encode(container, facts->policy, facts->kappa,
                               facts->vocab, facts->routes, facts->segments);
  if (!json)
    return json.takeError();
  return canonicalJsonBytes(*json);
}

llvm::Expected<CanonicalIndex> canonicalIndex(Operation *container) {
  auto facts = unpackContainer(container);
  if (!facts)
    return facts.takeError();
  // The numbering is a product of the identity walk itself — running
  // the encoder is what guarantees a position here is a position in
  // the sealed encoding (and that the container has one at all).
  Encoder encoder;
  auto json = encoder.encode(container, facts->policy, facts->kappa,
                             facts->vocab, facts->routes, facts->segments);
  if (!json)
    return json.takeError();
  CanonicalIndex index;
  encoder.harvestPositions(index);

  // Claim descriptors: content-derived — profile plus producer
  // anchors, position-free so a transform's multiset correspondence
  // survives transformer insertion; the position rides beside the
  // digest as `claim_index`.
  auto add = [&](Value claim, StringRef profile,
                 llvm::Expected<JValue> anchors) -> llvm::Error {
    if (!anchors)
      return anchors.takeError();
    if (llvm::Error err = checkStrings({profile}))
      return err;
    JValue descriptor = Array{profile, std::move(*anchors)};
    auto digest = taggedSha256Ref("zkc/claim\n", descriptor);
    if (!digest)
      return digest.takeError();
    index.claimDescriptors[claim] = std::move(*digest);
    return llvm::Error::success();
  };
  for (Operation &op : container->getRegion(0).front()) {
    if (auto source = dyn_cast<pir::InstantiateOp>(op)) {
      if (llvm::Error err = add(
              source.getClaim(),
              cast<pir::ClaimType>(source.getClaim().getType()).getProfile(),
              attributeToCanonicalJson(source.getAnchors())))
        return std::move(err);
    } else if (auto reduce = dyn_cast<pir::ReduceOp>(op)) {
      auto outAnchors = reduce.getOutAnchors();
      for (auto [i, out] : llvm::enumerate(reduce.getOuts())) {
        Attribute anchorsAttr = outAnchors ? (*outAnchors)[i] : Attribute();
        auto anchors =
            anchorsAttr ? attributeToCanonicalJson(anchorsAttr)
                        : llvm::Expected<JValue>(JValue(llvm::json::Object{}));
        if (llvm::Error err =
                add(out, cast<pir::ClaimType>(out.getType()).getProfile(),
                    std::move(anchors)))
          return std::move(err);
      }
    }
  }
  return index;
}

namespace {

/// The OIR program walk: rows in block order, operands by reference.
/// With `eraseProvenance` the walk produces the semantic document
/// instead: the PIR source citation is dropped and every row's src
/// position list is erased, so the digest depends only on what the
/// endpoint does — not on which protocol events it was projected from.
class OirEncoder {
public:
  explicit OirEncoder(bool eraseProvenance = false)
      : eraseProvenance(eraseProvenance) {}

  llvm::Expected<JValue> encode(zkc::oir::ArtifactOp artifact) {
    if (llvm::Error err =
            checkStrings({artifact.getEndpointKind(), artifact.getSource()}))
      return std::move(err);
    auto program = *artifact.getBody().getOps<zkc::oir::ProgramOp>().begin();
    Block &body = program.getBody().front();
    int64_t index = 0;
    for (Operation &op : body) {
      opIndex[&op] = index++;
      auto row =
          llvm::TypeSwitch<Operation *, llvm::Expected<JValue>>(&op)
              .Case<zkc::oir::TranscriptInitOp>(
                  [&](auto op) -> llvm::Expected<JValue> {
                    if (llvm::Error err =
                            checkStrings({op.getSponge(), op.getIv()}))
                      return std::move(err);
                    return ok(Array{"init", op.getSponge(), op.getIv()});
                  })
              .Case<zkc::oir::AbsorbOp>([&](auto op) {
                return ok(Array{"absorb", ref(op.getSponge()),
                                ref(op.getValue()), srcOf(op)});
              })
              .Case<zkc::oir::SqueezeOp>(
                  [&](auto op) -> llvm::Expected<JValue> {
                    if (llvm::Error err = checkStrings(
                            {op.getLabel(), op.getPayloadClass(), op.getCount(),
                             op.getDomain(), op.getRule(), op.getSpace()}))
                      return std::move(err);
                    return ok(Array{"squeeze", ref(op.getSponge()),
                                    op.getLabel(), op.getPayloadClass(),
                                    op.getCount(), op.getDomain(), op.getRule(),
                                    op.getSpace(), srcOf(op)});
                  })
              .Case<zkc::oir::ReadOp>([&](auto op) -> llvm::Expected<JValue> {
                if (llvm::Error err = checkStrings(
                        {op.getLabel(), op.getPayloadClass(), op.getCount()}))
                  return std::move(err);
                // Counted reads are their own row family so the scalar
                // family keeps its exact historical encoding
                // (docs/spec/carrier.md §6.2).
                if (op.getCount() != "1")
                  return ok(Array{"read_vec", ref(op.getStream()),
                                  op.getLabel(), op.getPayloadClass(),
                                  op.getCount(), srcOf(op)});
                return ok(Array{"read", ref(op.getStream()), op.getLabel(),
                                op.getPayloadClass(), srcOf(op)});
              })
              .Case<zkc::oir::ConstantOp>(
                  [&](auto op) -> llvm::Expected<JValue> {
                    if (llvm::Error err =
                            checkStrings({op.getValue(), op.getPayloadClass()}))
                      return std::move(err);
                    return ok(Array{"const", op.getValue(),
                                    op.getPayloadClass(), srcOf(op)});
                  })
              .Case<zkc::oir::CheckCallOp>(
                  [&](auto op) -> llvm::Expected<JValue> {
                    if (llvm::Error err =
                            checkStrings({op.getLabel(), op.getKind(),
                                          op.getContractDigest()}))
                      return std::move(err);
                    Array inputs;
                    for (Value input : op.getInputs())
                      inputs.push_back(ref(input));
                    auto params = attributeToCanonicalJson(op.getParams());
                    if (!params)
                      return params.takeError();
                    return JValue(Array{"check_call", std::move(inputs),
                                        op.getLabel(), op.getKind(),
                                        op.getContractDigest(),
                                        std::move(*params), srcOf(op)});
                  })
              .Case<zkc::oir::GExpOp, zkc::oir::GMulOp, zkc::oir::FAddOp,
                    zkc::oir::FMulOp>([&](Operation *op) {
                return ok(Array{op->getName().stripDialect(),
                                ref(op->getOperand(0)), ref(op->getOperand(1)),
                                srcOf(op)});
              })
              .Case<zkc::oir::FNegOp>([&](auto op) {
                return ok(Array{"f_neg", ref(op.getOperand()), srcOf(op)});
              })
              .Case<zkc::oir::AssertEqOp>(
                  [&](auto op) -> llvm::Expected<JValue> {
                    if (llvm::Error err = checkStrings({op.getLabel()}))
                      return std::move(err);
                    return ok(Array{"assert_eq", ref(op.getLhs()),
                                    ref(op.getRhs()), op.getLabel(),
                                    srcOf(op)});
                  })
              .Case<zkc::oir::ExpectEndOp>([&](auto op) {
                return ok(Array{"expect_end", ref(op.getStream())});
              })
              .Case<zkc::oir::DecideOp>([&](auto op) {
                return ok(Array{"decide", ref(op.getSponge())});
              })
              // The prover family (docs/spec/carrier.md §6.1):
              // additive rows, admitted per endpoint kind by the
              // container verifier before encoding is attempted.
              .Case<zkc::oir::WriteOp>(
                  [&](zkc::oir::WriteOp op) -> llvm::Expected<JValue> {
                    if (llvm::Error err = checkStrings({op.getLabel(),
                                                        op.getPayloadClass(),
                                                        op.getCount()}))
                      return std::move(err);
                    if (op.getCount() != "1")
                      return ok(Array{"write_vec", ref(op.getStream()),
                                      ref(op.getValue()), op.getLabel(),
                                      op.getPayloadClass(), op.getCount(),
                                      srcOf(op)});
                    return ok(Array{"write", ref(op.getStream()),
                                    ref(op.getValue()), op.getLabel(),
                                    op.getPayloadClass(), srcOf(op)});
                  })
              .Case<zkc::oir::HoleCallOp>([&](zkc::oir::HoleCallOp op)
                                              -> llvm::Expected<JValue> {
                if (llvm::Error err = checkStrings(
                        {op.getLabel(), op.getKind(), op.getContractDigest()}))
                  return std::move(err);
                Array operands;
                for (Value input : op.getInputs())
                  operands.push_back(ref(input));
                Array results;
                ArrayAttr resultCounts = op.getResultCounts();
                for (auto [index, output] : llvm::enumerate(op.getOutputs())) {
                  Type type = output.getType();
                  StringRef count =
                      index < resultCounts.size()
                          ? cast<StringAttr>(resultCounts[index]).getValue()
                          : StringRef("1");
                  if (auto val = dyn_cast<zkc::oir::ValType>(type)) {
                    if (llvm::Error err = checkStrings({val.getValueClass()}))
                      return std::move(err);
                    // A counted result carries its count additively;
                    // scalar results keep their exact historical
                    // encoding (docs/spec/carrier.md §6.2).
                    if (count != "1")
                      results.push_back(
                          Array{"val", val.getValueClass(), count});
                    else
                      results.push_back(Array{"val", val.getValueClass()});
                  } else if (auto handle =
                                 dyn_cast<zkc::oir::HandleType>(type)) {
                    if (llvm::Error err =
                            checkStrings({handle.getHandleClass()}))
                      return std::move(err);
                    results.push_back(Array{"handle", handle.getHandleClass()});
                  } else {
                    results.push_back(Array{"sponge"});
                  }
                }
                auto params = attributeToCanonicalJson(op.getParams());
                if (!params)
                  return params.takeError();
                auto semantic =
                    attributeToCanonicalJson(op.getSemanticParams());
                if (!semantic)
                  return semantic.takeError();
                return ok(Array{"hole_call", std::move(operands),
                                std::move(results), op.getLabel(), op.getKind(),
                                op.getContractDigest(), std::move(*params),
                                std::move(*semantic)});
              })
              .Case<zkc::oir::EndStreamOp>([&](auto op) {
                return ok(Array{"end_stream", ref(op.getStream())});
              })
              .Case<zkc::oir::FinishOp>([&](auto op) {
                return ok(Array{"finish", ref(op.getSponge())});
              })
              .Default([](Operation *op) -> llvm::Expected<JValue> {
                return llvm::createStringError(
                    "operation has no canonical OIR encoding: " +
                    op->getName().getStringRef());
              });
      if (!row)
        return row.takeError();
      rows.push_back(std::move(*row));
    }
    // Sequenced checks: an llvm::Expected must be examined before the
    // next one is created, or an early error aborts a checked build.
    auto labels = attributeToCanonicalJson(program.getStatementLabels());
    if (!labels)
      return labels.takeError();
    auto digests = attributeToCanonicalJson(program.getParamDigests());
    if (!digests)
      return digests.takeError();
    llvm::json::Object codecs;
    if (auto baked = program.getCodecs()) {
      auto json = attributeToCanonicalJson(*baked);
      if (!json)
        return json.takeError();
      codecs = std::move(*json->getAsObject());
    }
    // The complete entry signature is identity content: two endpoints
    // whose arguments differ in class are different ABIs even when every
    // row agrees, so the classes enter the preimage in argument order.
    Array entry;
    for (BlockArgument argument : body.getArguments()) {
      Type type = argument.getType();
      if (auto val = dyn_cast<zkc::oir::ValType>(type)) {
        if (llvm::Error err = checkStrings({val.getValueClass()}))
          return std::move(err);
        entry.push_back(Array{"val", val.getValueClass()});
      } else if (auto handle = dyn_cast<zkc::oir::HandleType>(type)) {
        if (llvm::Error err = checkStrings({handle.getHandleClass()}))
          return std::move(err);
        entry.push_back(Array{"handle", handle.getHandleClass()});
      } else {
        entry.push_back(Array{"stream"});
      }
    }
    llvm::json::Object doc{{"endpoint", artifact.getEndpointKind()},
                           {"codecs", std::move(codecs)},
                           {"entry", std::move(entry)},
                           {"statement_labels", std::move(*labels)},
                           {"param_digests", std::move(*digests)},
                           {"program", std::move(rows)}};
    if (!eraseProvenance)
      doc["source"] = artifact.getSource();
    // Prover-endpoint ABI and realization records are identity content
    // on prover documents, never present on verifier documents — the
    // container verifier enforces presence, the encoder fails closed.
    bool prover =
        artifact.getEndpointKind() == zkc::oir::kEndpointProverSkeleton;
    if (prover != static_cast<bool>(program.getWitnessLabelsAttr()) ||
        prover != static_cast<bool>(program.getCounterpartyAttr()))
      return llvm::createStringError(
          "witness_labels and counterparty are present exactly on "
          "prover_skeleton programs");
    if (prover) {
      auto witnessLabels =
          attributeToCanonicalJson(program.getWitnessLabelsAttr());
      if (!witnessLabels)
        return witnessLabels.takeError();
      doc["witness_labels"] = std::move(*witnessLabels);
      auto counterparty =
          attributeToCanonicalJson(program.getCounterpartyAttr());
      if (!counterparty)
        return counterparty.takeError();
      doc["counterparty"] = std::move(*counterparty);
    }
    return JValue(std::move(doc));
  }

private:
  llvm::Expected<JValue> ok(Array row) { return JValue(std::move(row)); }

  JValue ref(Value value) {
    if (auto arg = dyn_cast<BlockArgument>(value))
      return Array{"a", static_cast<int64_t>(arg.getArgNumber())};
    auto result = cast<OpResult>(value);
    return Array{"r", opIndex.lookup(result.getOwner()),
                 static_cast<int64_t>(result.getResultNumber())};
  }

  JValue srcOf(Operation *op) {
    Array positions;
    if (!eraseProvenance)
      if (auto src = op->getAttrOfType<ArrayAttr>("src"))
        for (Attribute p : src)
          positions.push_back(cast<IntegerAttr>(p).getValue().getSExtValue());
    return JValue(std::move(positions));
  }

  Array rows;
  llvm::DenseMap<Operation *, int64_t> opIndex;
  bool eraseProvenance;
};

} // namespace

llvm::Expected<std::string> encodeOirCanonical(Operation *artifactOp) {
  auto artifact = dyn_cast<zkc::oir::ArtifactOp>(artifactOp);
  if (!artifact)
    return llvm::createStringError("not an oir.artifact");
  auto json = OirEncoder().encode(artifact);
  if (!json)
    return json.takeError();
  std::string bytes;
  llvm::raw_string_ostream os(bytes);
  if (llvm::Error err = writeCanonicalJson(*json, os))
    return std::move(err);
  return bytes;
}

// Identity is domain-separated (kernel.md §8): the hash input starts
// with a fixed ASCII tag per artifact kind, so no zkc id can be
// reinterpreted across kinds or as another system's digest of the
// same bytes.

llvm::Expected<std::string> computeOirId(Operation *artifact) {
  auto bytes = encodeOirCanonical(artifact);
  if (!bytes)
    return bytes.takeError();
  llvm::SHA256 hasher;
  hasher.update(llvm::StringRef("zkc/oir\n"));
  hasher.update(*bytes);
  return llvm::toHex(hasher.final(), /*LowerCase=*/true);
}

llvm::Expected<std::string> computeOirSemanticId(Operation *artifactOp) {
  auto artifact = dyn_cast<zkc::oir::ArtifactOp>(artifactOp);
  if (!artifact)
    return llvm::createStringError("not an oir.artifact");
  auto json = OirEncoder(/*eraseProvenance=*/true).encode(artifact);
  if (!json)
    return json.takeError();
  std::string bytes;
  llvm::raw_string_ostream os(bytes);
  if (llvm::Error err = writeCanonicalJson(*json, os))
    return std::move(err);
  llvm::SHA256 hasher;
  hasher.update(llvm::StringRef("zkc/oir-semantic\n"));
  hasher.update(bytes);
  return llvm::toHex(hasher.final(), /*LowerCase=*/true);
}

llvm::Error validateOirIdentity(Operation *artifactOp) {
  auto artifact = dyn_cast<zkc::oir::ArtifactOp>(artifactOp);
  if (!artifact)
    return llvm::createStringError("not an oir.artifact");
  auto computed = computeOirId(artifact);
  if (!computed)
    return computed.takeError();
  if (*computed != artifact.getId())
    return llvm::createStringError(
        "[zkc-E170] stored OIR artifact id does not match its canonical "
        "identity (stored '" +
        artifact.getId() + "', computed '" + *computed + "')");
  return llvm::Error::success();
}

llvm::Expected<std::string> computeId(Operation *container) {
  auto bytes = encodeCanonical(container);
  if (!bytes)
    return bytes.takeError();
  llvm::SHA256 hasher;
  hasher.update(llvm::StringRef("zkc/pir\n"));
  hasher.update(*bytes);
  return llvm::toHex(hasher.final(), /*LowerCase=*/true);
}

llvm::Error validatePirIdentity(Operation *containerOp) {
  auto sealed = dyn_cast<zkc::pir::SealedOp>(containerOp);
  if (!sealed)
    return llvm::createStringError("not a pir.sealed artifact");
  auto computed = computeId(sealed);
  if (!computed)
    return computed.takeError();
  if (*computed != sealed.getId())
    return llvm::createStringError(
        "[zkc-E171] stored PIR artifact id does not match its canonical "
        "identity (stored '" +
        sealed.getId() + "', computed '" + *computed + "')");
  return llvm::Error::success();
}

} // namespace encoding
} // namespace zkc
