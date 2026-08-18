//===- SealBattery.cpp - the seal battery -----------------------*- C++ -*-===//
// Semantic halves of the seal judgment (kernel.md §7), shared by the
// seal pass and by every consumer that must make the attestation its
// own — the recheck pass at a load boundary. The container
// verifier has already accepted the structure by the time this runs,
// so the walk here reads a well-formed spine and a linear claim graph
// and asks only the semantic questions: absorption, policy, profile
// coverage, vocabulary resolution, and typed terminal closure.
// Diagnostics accumulate — an author sees every obligation a protocol
// misses, not the first.
//===----------------------------------------------------------------------===//

#include "zkc/Semantics/SealBattery.h"

#include "zkc/Dialect/Pir/KappaView.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Encoding/CanonicalEncoder.h"
#include "zkc/Encoding/EncodingDomain.h"
#include "zkc/Registry/ConstructionProfileRegistry.h"
#include "zkc/Registry/ProtocolVocabulary.h"
#include "zkc/Semantics/ClosureLedger.h"
#include "zkc/Semantics/ProtocolFacts.h"
#include "zkc/Semantics/ReductionClosure.h"
#include "zkc/Semantics/TerminalClosure.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/TypeSwitch.h"
#include "llvm/Support/ErrorHandling.h"

using namespace mlir;

zkc::pir::ProtocolVocabularyCitations zkc::pir::collectCitedProtocolVocabulary(
    Block &body, const zkc::registry::ProtocolVocabulary &protocolVocabulary) {
  ProtocolVocabularyCitations citations;
  for (Operation &op : body) {
    for (Value value : op.getOperands())
      if (auto claim = dyn_cast<zkc::pir::ClaimType>(value.getType()))
        citations.claimProfiles.push_back(claim.getProfile());
    for (Value value : op.getResults())
      if (auto claim = dyn_cast<zkc::pir::ClaimType>(value.getType()))
        citations.claimProfiles.push_back(claim.getProfile());
    if (auto check = dyn_cast<zkc::pir::CheckOp>(&op))
      citations.checkContracts.push_back(check.getContract());
    else if (auto reduce = dyn_cast<zkc::pir::ReduceOp>(&op))
      citations.reductionContracts.push_back(reduce.getContract());
    else if (auto discharge = dyn_cast<zkc::pir::DischargeOp>(&op))
      citations.terminalRules.push_back(discharge.getRule());
  }

  // Terminal rules cite profiles, optional producer contracts, and check
  // contracts. Reduction contracts in turn cite every consumed and produced
  // profile. The vocabulary loader has already admitted these references, so
  // one staged expansion computes the complete transitive closure.
  for (StringRef id : citations.terminalRules)
    if (const auto *rule = protocolVocabulary.lookupRule(id)) {
      citations.claimProfiles.push_back(rule->claimProfile);
      if (rule->producer)
        citations.reductionContracts.push_back(rule->producer->contract);
      for (const auto &[role, contract] : rule->checks) {
        (void)role;
        citations.checkContracts.push_back(contract);
      }
    }
  for (StringRef id : citations.reductionContracts)
    if (const auto *contract = protocolVocabulary.lookupReductionContract(id)) {
      for (const auto &pattern : contract->consumes)
        citations.claimProfiles.push_back(pattern.profile);
      for (const auto &output : contract->outputs)
        citations.claimProfiles.push_back(output.profile);
      for (const auto &[role, slot] : contract->checks) {
        (void)role;
        citations.checkContracts.push_back(slot.contract);
      }
    }

  auto normalize = [](auto &ids) {
    llvm::sort(ids);
    ids.erase(llvm::unique(ids), ids.end());
  };
  normalize(citations.claimProfiles);
  normalize(citations.checkContracts);
  normalize(citations.reductionContracts);
  normalize(citations.terminalRules);
  return citations;
}

namespace {

using zkc::registry::ConstructionProfileRegistry;
using zkc::registry::ProtocolVocabulary;
using zkc::registry::ReductionContract;

/// The permitted-sink set of each SealPolicy mode
/// (docs/spec/vocabularies.md §8). Discharge is always permitted; the
/// mode names which non-proof route may remain.
static std::optional<llvm::StringSet<>> permittedSinks(StringRef policy) {
  llvm::StringSet<> sinks;
  sinks.insert("discharge");
  if (policy == "closed_proof")
    return sinks;
  if (policy == "residual_artifact") {
    sinks.insert("residual");
    return sinks;
  }
  if (policy == "host_exporting_artifact") {
    sinks.insert("export");
    return sinks;
  }
  if (policy == "assumption_allowed_artifact") {
    sinks.insert("assume");
    return sinks;
  }
  if (policy == "analysis_only_artifact") {
    sinks.insert("export");
    sinks.insert("assume");
    sinks.insert("residual");
    return sinks;
  }
  return std::nullopt;
}

// The canonical encoding domain (kernel.md §3, item 4): printable-ASCII
// strings (zkc::encoding::inEncodingDomain) and signed-64-bit
// integers. Enforcing it at seal — with the oracle rejecting
// identically — is what makes cross-implementation byte parity an
// argument instead of an escaper hand-match: on the accepted domain
// the two encoders have no interesting cases left to disagree on.
using zkc::encoding::inEncodingDomain;

static bool inIntegerDomain(IntegerAttr attr) {
  return zkc::encoding::inIntegerDomain(attr.getValue(),
                                        attr.getType().isUnsignedInteger());
}

/// The seal battery, shared by the seal and recheck passes: the
/// semantic halves of WF, LIN, BIND, and COV_obl over one container
/// body (kernel.md §7). The COV_obl half is obligation derivability
/// (kernel.md §6.1): every semantic event must derive one projection
/// obligation from its already-encoded facts, so the judgment fails
/// exactly where a derivation input is missing — an unresolved codec
/// (zkc-E221), an unresolved or under-fed check kind
/// (zkc-E222/E223), an expr outside the grammar (zkc-E226), a
/// malformed vector mode — and the obligation table itself stays a
/// derived view (deriveObligations). Verdict-only; the callers own
/// stamping, identity, and artifact construction. One battery judges
/// one container — construct a fresh one per protocol.
class SealBattery {
public:
  SealBattery(const ProtocolVocabulary &protocolVocabulary,
              const ConstructionProfileRegistry *profiles, bool recheck)
      : vocabulary(protocolVocabulary), profiles(profiles), recheck(recheck) {}

  /// The full battery over one container body. Seal calls it to
  /// reject out-of-form input before stamping an identity; recheck
  /// calls it to re-judge a loaded sealed artifact (the consumer
  /// contract's second leg, boundaries.md §0), where the single
  /// resolved-vocabulary table must match the loaded authorities.
  LogicalResult run(Operation *container, std::optional<DictionaryAttr> kappa,
                    std::optional<DictionaryAttr> vocab,
                    std::optional<llvm::ArrayRef<int64_t>> segments,
                    StringRef sealPolicy) {
    policy = sealPolicy;
    subjectKappa = kappa;
    Block &body = container->getRegion(0).front();
    facts = zkc::semantics::ProtocolFacts::compute(body);
    canonicalEvents = zkc::encoding::canonicalEventIndex(body);
    checkEncodingDomain(container, kappa, body);
    checkPolicy(container);
    checkKappa(container, kappa);
    checkProfiles(container, kappa);
    checkSegments(container, segments);
    checkDomains(body);
    if (recheck)
      checkVocab(container, vocab, body);
    checkSpine(body);
    zkc::semantics::ClosureLedger closureLedger;
    if (failed(zkc::semantics::verifyReductionClosure(container, vocabulary,
                                                      closureLedger)))
      ok = false;
    if (failed(zkc::semantics::verifyTerminalClosure(container, vocabulary,
                                                     closureLedger)))
      ok = false;
    for (Operation &operation : body)
      if (auto binding = dyn_cast<zkc::pir::MaterialBindOp>(operation);
          binding &&
          !closureLedger.usedMaterialBindings.contains(binding.getOperation()))
        error(binding) << "[zkc-E328] material binding is not consumed by "
                          "reduction or terminal closure";
    return success(ok);
  }

private:
  /// The authorities the battery reads. The vocabulary is resolved at the
  /// ingress boundary before any battery runs; the profile registry is
  /// genuinely optional (absent when kappa consumes no sponge or codec).
  const ProtocolVocabulary &vocabulary;
  const ConstructionProfileRegistry *profiles;
  /// Recheck additionally holds the single sealed vocabulary table to all
  /// loaded digest authorities.
  const bool recheck;

  /// The one failure latch: emitting a diagnostic IS the verdict, so
  /// the two cannot drift apart. Diagnostics accumulate; `ok` decides.
  bool ok = true;

  // Facts one battery stage establishes for the stages after it.
  StringRef policy;
  std::optional<DictionaryAttr> subjectKappa;
  llvm::StringSet<> sinks;
  /// The route names this artifact's routed sinks carry. A bounded
  /// artifact verification must name one of them: endpoints.md §3.1 makes
  /// the parent route surface the place a child's assumptions, exports and
  /// residuals are lifted to, so a route no sink mentions has lifted
  /// nothing.
  llvm::StringSet<> routeSurface;
  /// The proof-slot labels this artifact declares, by canonical event
  /// position, for the artifact verification events that name the slots a
  /// child verifier consumes. The position is kept because a verification
  /// may only name material that has already entered the stream.
  llvm::StringMap<int64_t> slotLabels;
  DictionaryAttr codecs;
  DictionaryAttr constants;
  zkc::pir::ChalOp firstChal;
  /// Later-segment start positions (event numbering), validated by
  /// checkSegments; empty = one segment.
  SmallVector<int64_t> segmentStarts;
  Operation *firstUnabsorbed = nullptr;
  // Shared carrier facts remain judgment-free. This battery decides whether
  // collisions or missing structure are admissible; the index never does.
  zkc::semantics::ProtocolFacts facts;
  zkc::encoding::CanonicalIndex canonicalEvents;

  InFlightDiagnostic error(Operation *op) {
    ok = false;
    return op->emitOpError();
  }

  /// WF encoding-domain fact for one identity-bearing string.
  void domain(Operation *op, StringRef what, StringRef value) {
    if (!inEncodingDomain(value))
      error(op) << "[zkc-E228] " << what
                << " leaves the canonical encoding domain "
                   "(printable ASCII)";
  }

  /// Recursive domain check over identity-bearing attributes (kappa,
  /// params, expr trees): every string printable ASCII, every integer
  /// signed-64-bit, dictionary keys included; any other attribute kind
  /// has no canonical encoding and fails here rather than at the
  /// encoder, where attribution is gone.
  void checkAttrDomain(Attribute attr, Operation *op, StringRef what,
                       unsigned depth = 0) {
    auto bad = [&](StringRef why) {
      error(op) << "[zkc-E228] " << what
                << " leaves the canonical encoding domain (" << why << ")";
    };
    // Depth-bounded for the same totality reason as verifyExpr: a
    // hostile nesting depth exhausts this counter, never the stack.
    if (depth > zkc::encoding::kMaxAttrDepth) {
      bad("nesting exceeds the canonical depth bound");
      return;
    }
    if (auto s = dyn_cast<StringAttr>(attr)) {
      if (!inEncodingDomain(s.getValue()))
        bad("printable ASCII");
      return;
    }
    if (isa<BoolAttr>(attr)) {
      // Rejected before the integer case on purpose: a BoolAttr IS an
      // i1 IntegerAttr, and letting it through would give one
      // semantics two byte spellings (`false` aliases index 0 in expr
      // references while encoding differently). The domain enumerates
      // strings and signed-64-bit integers only (kernel.md §3, item 4).
      bad("no boolean encoding");
      return;
    }
    if (auto i = dyn_cast<IntegerAttr>(attr)) {
      if (!inIntegerDomain(i))
        bad("signed 64-bit integer");
      return;
    }
    if (auto arr = dyn_cast<ArrayAttr>(attr)) {
      // Positional paths keep repeated violations distinguishable —
      // identical diagnostics at one location fold under test
      // verification, which would make the per-element walk
      // untestable.
      for (auto [i, member] : llvm::enumerate(arr))
        checkAttrDomain(member, op, (what + "[" + llvm::Twine(i) + "]").str(),
                        depth + 1);
      return;
    }
    if (auto dict = dyn_cast<DictionaryAttr>(attr)) {
      for (NamedAttribute named : dict) {
        if (!inEncodingDomain(named.getName().getValue()))
          bad("printable ASCII");
        checkAttrDomain(named.getValue(), op, what, depth + 1);
      }
      return;
    }
    bad("no canonical attribute kind");
  }

  /// The transparent-check interior (kernel.md §1.2): an inert tree of
  /// ["in", k] / ["const", name] / [op, subtree...] with "eq" at the
  /// root only. There is deliberately no statement reference — binds
  /// produce vals, so statement values reach checks as SSA inputs and
  /// are therefore always absorbed. The per-subtree early return is
  /// load-bearing: a broken tree is not descended further.
  LogicalResult verifyExpr(zkc::pir::CheckOp op, ArrayAttr expr,
                           bool root = true, unsigned depth = 0) {
    auto err = [&](const llvm::Twine &what) {
      error(op) << "[zkc-E226] " << what;
      return failure();
    };
    // Depth-bounded so the judgment is total on hostile nesting
    // (kernel §3: WF is decidable structure checking) — the bound
    // exhausts a counter, never the stack.
    if (depth > zkc::encoding::kMaxAttrDepth)
      return err("expr nesting exceeds the canonical depth bound");
    if (expr.empty())
      return err("empty expr node");
    auto head = dyn_cast<StringAttr>(expr[0]);
    if (!head)
      return err("expr node head must be a string");
    StringRef tag = head.getValue();
    // The root gate runs before the leaf cases return: a bare
    // reference at the root would be a predicate that asserts
    // nothing — a no-op check able to discharge a claim.
    if (root && (tag == "in" || tag == "const"))
      return err("expr root must be 'eq': a transparent check "
                 "declares an equation");
    if (tag == "in") {
      auto index =
          expr.size() == 2 ? dyn_cast<IntegerAttr>(expr[1]) : IntegerAttr();
      if (!index || !inIntegerDomain(index) ||
          index.getValue().getSExtValue() < 0 ||
          index.getValue().getSExtValue() >=
              static_cast<int64_t>(op.getInputs().size()))
        return err("expr input reference out of range");
      return success();
    }
    if (tag == "const") {
      auto name =
          expr.size() == 2 ? dyn_cast<StringAttr>(expr[1]) : StringAttr();
      if (!name || !constants || !constants.getNamed(name.getValue()))
        return err("expr constant does not resolve in kappa.constants");
      return success();
    }
    bool isEq = tag == "eq";
    bool isAlgebra = tag == "g_exp" || tag == "g_mul" || tag == "f_add" ||
                     tag == "f_mul" || tag == "f_neg";
    if (!isEq && !isAlgebra)
      return err("unknown expr operation '" + tag + "'");
    if (isEq != root)
      return err(root ? "expr root must be 'eq': a transparent check "
                        "declares an equation"
                      : "'eq' is permitted at the expr root only");
    size_t arity = tag == "f_neg" ? 1 : 2;
    if (expr.size() != arity + 1)
      return err("'" + tag + "' takes " + llvm::Twine(arity) + " subtrees");
    for (Attribute sub : llvm::drop_begin(expr)) {
      auto subtree = dyn_cast<ArrayAttr>(sub);
      if (!subtree)
        return err("expr subtree must be an array");
      if (failed(verifyExpr(op, subtree, /*root=*/false, depth + 1)))
        return failure();
    }
    return success();
  }

  /// Descriptor-profile conformance (kernel.md §1.3): every claim producer
  /// carries exactly the anchors admitted by its profile.
  void anchorsComplete(Operation *op, StringRef profile,
                       DictionaryAttr anchors) {
    const auto *info = vocabulary.lookupProfile(profile);
    if (!info) {
      error(op) << "[zkc-E247] unknown claim profile '" << profile << "'";
      return;
    }
    SmallVector<StringRef> actual;
    if (anchors)
      for (NamedAttribute named : anchors)
        actual.push_back(named.getName().getValue());
    SmallVector<StringRef> expected;
    for (const std::string &name : info->anchors)
      expected.push_back(name);
    llvm::sort(actual);
    llvm::sort(expected);
    if (actual != expected)
      error(op) << "[zkc-E247] claim profile '" << profile
                << "' requires exactly its admitted anchor set";
  }

  /// WF encoding domain (kernel.md §3, item 4): every identity-bearing string
  /// and attribute is checked before anything else consumes it. `protocol_name`
  /// is not identity-bearing, but it is the human-readable subject handle and
  /// therefore must inhabit the same deterministic string domain.
  void checkEncodingDomain(Operation *container,
                           std::optional<DictionaryAttr> kappa, Block &body) {
    if (auto protocol = dyn_cast<zkc::pir::ProtocolOp>(container))
      domain(protocol, "protocol_name", protocol.getProtocolName());
    else if (auto sealed = dyn_cast<zkc::pir::SealedOp>(container))
      domain(sealed, "protocol_name", sealed.getProtocolName());
    if (kappa)
      checkAttrDomain(*kappa, container, "kappa");
    for (Operation &op : body) {
      llvm::TypeSwitch<Operation *>(&op)
          .Case<zkc::pir::InstantiateOp>([&](zkc::pir::InstantiateOp op) {
            domain(op, "label", op.getLabel());
            StringRef profile =
                cast<zkc::pir::ClaimType>(op.getClaim().getType()).getProfile();
            domain(op, "claim profile", profile);
            checkAttrDomain(op.getAnchors(), op, "anchors");
            anchorsComplete(op, profile, op.getAnchors());
          })
          .Case<zkc::pir::BindOp>([&](zkc::pir::BindOp op) {
            domain(op, "label", op.getLabel());
            domain(op, "payload class", op.getPayloadClass());
            if (op.getValue())
              domain(op, "value", *op.getValue());
          })
          .Case<zkc::pir::SlotOp>([&](zkc::pir::SlotOp op) {
            domain(op, "label", op.getLabel());
            domain(op, "payload class", op.getPayloadClass());
          })
          .Case<zkc::pir::ChalOp>([&](zkc::pir::ChalOp op) {
            domain(op, "label", op.getLabel());
            domain(op, "payload class", op.getPayloadClass());
            domain(op, "domain id", op.getDomain());
          })
          .Case<zkc::pir::CheckOp>([&](zkc::pir::CheckOp op) {
            domain(op, "label", op.getLabel());
            domain(op, "contract", op.getContract());
            if (op.getParams())
              checkAttrDomain(*op.getParams(), op, "params");
            if (op.getSemanticArgs())
              checkAttrDomain(*op.getSemanticArgs(), op, "semantic_args");
            if (op.getExpr())
              checkAttrDomain(*op.getExpr(), op, "expr");
          })
          .Case<zkc::pir::ReduceOp>([&](zkc::pir::ReduceOp op) {
            domain(op, "label", op.getLabel());
            domain(op, "reduction contract", op.getContract());
            checkAttrDomain(op.getChecks(), op, "checks");
            for (Value out : op.getOuts())
              domain(op, "claim profile",
                     cast<zkc::pir::ClaimType>(out.getType()).getProfile());
            if (op.getParams())
              checkAttrDomain(*op.getParams(), op, "params");
            if (op.getOutAnchors())
              checkAttrDomain(*op.getOutAnchors(), op, "anchors");
          })
          .Case<zkc::pir::MaterialBindOp>([&](zkc::pir::MaterialBindOp op) {
            domain(op, "semantic reference", op.getSemanticRef());
          })
          .Case<zkc::pir::DischargeOp>([&](zkc::pir::DischargeOp op) {
            domain(op, "terminal rule", op.getRule());
            checkAttrDomain(op.getChecks(), op, "checks");
          })
          .Case<zkc::pir::ExportOp, zkc::pir::AssumeOp, zkc::pir::ResidualOp>(
              [&](auto op) { domain(op, "route", op.getRoute()); })
          .Case<zkc::pir::ArtifactVerifyOp>(
              [&](zkc::pir::ArtifactVerifyOp op) {
                // Every fact endpoints.md §3.1 binds is identity-bearing:
                // the child, its endpoint kind and verifier semantics, the
                // key and statement it decides under, its protocol and
                // relation contract, and the parent route. All of them
                // reach the canonical encoding, so all of them are
                // admitted to the encoding domain here.
                domain(op, "child artifact", op.getChild());
                domain(op, "child endpoint kind", op.getEndpoint());
                domain(op, "verifier semantics", op.getSemantics());
                domain(op, "verifier key", op.getKey());
                domain(op, "child statement", op.getStatement());
                domain(op, "child protocol", op.getProtocol());
                domain(op, "child relation contract",
                       op.getRelationContract());
                domain(op, "route", op.getRoute());
                if (op.getAbi())
                  domain(op, "child artifact ABI", *op.getAbi());
                if (auto slots = op.getProofSlots())
                  checkAttrDomain(*slots, op, "proof_slots");
              })
          .Case<zkc::pir::BeginOp, zkc::pir::EndOp>([](auto) {
            // Structural frame; no identity-bearing fields.
          })
          .Default([&](Operation *op) {
            // Fail closed: a member kind this walk was not taught
            // would seal identity-bearing fields undomained. Today the
            // container verifier (zkc-E131) admits only the kinds
            // enumerated above, so this is unreachable — it exists so
            // the next member kind fails loudly here instead of
            // sealing unvalidated.
            error(op) << "operation has no seal domain rule; its fields "
                         "cannot be admitted to the encoding domain "
                         "(kernel.md 3.4)";
          });
    }
  }

  /// LIN policy: which terminal routes may this artifact carry.
  void checkPolicy(Operation *container) {
    auto permitted = permittedSinks(policy);
    if (!permitted) {
      // Continue with an empty permitted set so every non-proof
      // route also gets its own zkc-E201 — the author sees the whole
      // obligation, not the first.
      error(container) << "[zkc-E224] unknown seal policy '" << policy << "'";
      return;
    }
    sinks = std::move(*permitted);
  }

  /// WF profile: the codec map — and a closed, *typed* axis set. An
  /// unknown axis would seal into identity unvalidated; the
  /// vocabulary grows additively, never silently
  /// (docs/spec/vocabularies.md §1). A wrong-typed axis is an error
  /// too, never a skip: the malformed value would otherwise flow
  /// into identity and surface downstream as a misattributed
  /// diagnostic (a codec lookup or projection-axis failure).
  void checkKappa(Operation *container, std::optional<DictionaryAttr> kappa) {
    if (!kappa)
      return;
    for (NamedAttribute axis : *kappa) {
      StringRef name = axis.getName().getValue();
      if (name != "codecs" && name != "sponge" && name != "iv" &&
          name != "constants")
        error(container) << "[zkc-E225] unknown kappa axis '" << name << "'";
    }
    if (auto entry = kappa->getNamed("codecs")) {
      codecs = dyn_cast<DictionaryAttr>(entry->getValue());
      if (!codecs)
        error(container) << "[zkc-E225] kappa axis 'codecs' must be a "
                            "dictionary of payload class to codec";
    }
    for (StringRef axis : {"sponge", "iv"})
      if (auto entry = kappa->getNamed(axis))
        if (!isa<StringAttr>(entry->getValue()))
          error(container) << "[zkc-E225] kappa axis '" << axis
                           << "' must be a string";
    if (auto entry = kappa->getNamed("constants")) {
      constants = dyn_cast<DictionaryAttr>(entry->getValue());
      if (!constants)
        error(container) << "[zkc-E225] kappa axis 'constants' must be a "
                            "dictionary";
      else
        for (NamedAttribute constant : constants) {
          auto spec = dyn_cast<DictionaryAttr>(constant.getValue());
          if (!spec || !spec.getNamed("class") || !spec.getNamed("value"))
            error(container) << "[zkc-E225] kappa constant '"
                             << constant.getName().getValue()
                             << "' must be a {class, value} dictionary";
        }
    }
  }

  /// The unconditional content pin of consumed construction-profile
  /// entries (kernel.md §8): every codec kappa routes a payload class
  /// through, and the named sponge, must resolve in the construction-
  /// profile registry — their decode widths and squeeze shapes are
  /// transcript bytes and proof ABI, identity-bearing whether or not
  /// any later analysis reads them, so the seal refuses what it cannot
  /// pin.
  void checkProfiles(Operation *container,
                     std::optional<DictionaryAttr> kappa) {
    StringRef spongeName = zkc::pir::kappaSpongeName(kappa);
    auto codecNames = zkc::pir::kappaConsumedCodecNames(kappa);
    if (spongeName.empty() && codecNames.empty())
      return;
    if (!profiles) {
      error(container) << "[zkc-E229] kappa consumes construction-profile "
                          "entries and no construction-profile registry "
                          "was given: their content cannot be pinned";
      return;
    }
    if (!spongeName.empty() && !profiles->lookup(spongeName))
      error(container) << "[zkc-E229] kappa sponge '" << spongeName
                       << "' is not in the construction-profile registry";
    for (StringRef codecName : codecNames)
      if (!profiles->lookupCodec(codecName))
        error(container) << "[zkc-E229] kappa codec '" << codecName
                         << "' is not in the construction-profile "
                            "registry";
  }

  /// Challenge domains must be pairwise distinct within a container:
  /// the transcript hash namespaces each squeeze by its domain, so two
  /// challenges sharing a domain squeeze from the same framing and the
  /// Binding Lemma's injectivity fails (kernel.md §5.4). link composes
  /// two sealed faces into one transcript, so this is also the point
  /// where a cross-face domain collision is caught — the composite is
  /// re-sealed, and face-prefixing is trusted for disjointness only
  /// insofar as it survives this judgment (boundaries.md §3).
  void checkDomains(Block &body) {
    llvm::StringMap<zkc::pir::ChalOp> seen;
    for (Operation &op : body)
      if (auto chal = dyn_cast<zkc::pir::ChalOp>(&op)) {
        auto [it, inserted] = seen.try_emplace(chal.getDomain(), chal);
        if (!inserted)
          error(chal)
              << "[zkc-E216] challenge domain '" << chal.getDomain()
              << "' is already used by another challenge in this "
                 "container: challenge domains must be pairwise distinct";
      }
  }

  /// The segment decomposition (kernel.md §5.3): later-segment start
  /// positions in event numbering — strictly increasing, inside the
  /// spine. Judgment-bearing (the statement-binding default is judged
  /// per segment), so a malformed decomposition fails the seal, never
  /// degrades to the single-segment reading.
  void checkSegments(Operation *container,
                     std::optional<llvm::ArrayRef<int64_t>> segments) {
    if (!segments || segments->empty())
      return;
    int64_t eventCount = zkc::encoding::canonicalEventCount(canonicalEvents);
    int64_t previous = 0;
    for (int64_t start : *segments) {
      if (start <= previous || start >= eventCount) {
        error(container)
            << "[zkc-E215] segment starts must be strictly increasing "
               "event positions inside the spine (got "
            << start << " over " << eventCount << " event(s))";
        return;
      }
      previous = start;
    }
    segmentStarts.assign(segments->begin(), segments->end());
  }

  void requireCodec(Operation *op, StringRef payloadClass) {
    if (!codecs || !codecs.getNamed(payloadClass))
      error(op) << "[zkc-E221] payload class '" << payloadClass
                << "' has no codec in kappa.codecs";
  }

  /// Recheck only: the single sealed vocabulary table must be the exact cited
  /// subset of every loaded authority. No operation-local digest participates.
  void checkVocab(Operation *container, std::optional<DictionaryAttr> vocab,
                  Block &body) {
    zkc::pir::verifyResolvedVocab(body, subjectKappa, vocab, vocabulary,
                                  profiles, [&](const llvm::Twine &message) {
                                    error(container)
                                        << "[zkc-E248] " << message;
                                  });
  }

  /// The LIN/BIND walk over the spine: absorption discipline, policy
  /// routes, check-kind resolution — and the collection pass for the
  /// per-reduce battery. Duplicate (instance, role, idx) triples are
  /// caught during collection — one spelling per occurrence.
  void checkSpine(Block &body) {
    for (Operation &op : body)
      llvm::TypeSwitch<Operation *>(&op)
          .Case<zkc::pir::ExportOp, zkc::pir::AssumeOp, zkc::pir::ResidualOp>(
              [&](auto routed) { routeSurface.insert(routed.getRoute()); })
          .Case<zkc::pir::SlotOp>([&](zkc::pir::SlotOp slot) {
            if (auto position = zkc::encoding::canonicalEventPosition(
                    canonicalEvents, slot.getOperation()))
              slotLabels[slot.getLabel()] = *position;
          })
          .Default([](Operation *) {});

    size_t nextSegment = 0;
    auto collectMembership = [&](Operation *op,
                                 std::optional<zkc::pir::Membership> m) {
      if (!m)
        return;
      auto occurrences =
          facts.membershipOccurrences(m->instance, m->role, m->idx);
      if (occurrences.size() > 1 && occurrences.front() != op)
        error(op) << "[zkc-E244] duplicate occurrence: instance '"
                  << m->instance << "' role '" << m->role << "' idx " << m->idx
                  << " is already bound";
    };

    for (Operation &op : body) {
      if (auto eventPos =
              zkc::encoding::canonicalEventPosition(canonicalEvents, &op)) {
        // Crossing into the next segment resets the statement-binding
        // default's scope (kernel.md §5.3): each segment's bindings
        // precede that segment's own first challenge. The Frozen-Heart
        // default (firstUnabsorbed) deliberately stays global.
        if (nextSegment < segmentStarts.size() &&
            *eventPos == segmentStarts[nextSegment]) {
          ++nextSegment;
          firstChal = nullptr;
        }
      }
      if (auto member = dyn_cast<zkc::pir::ProtocolMemberOpInterface>(&op))
        collectMembership(&op, member.getMembership());
      llvm::TypeSwitch<Operation *>(&op)
          .Case<zkc::pir::BindOp>([&](zkc::pir::BindOp op) {
            requireCodec(op, op.getPayloadClass());
            // A seal-stage binding is a constant and must say which; an
            // instance-stage binding is a runtime input and must not.
            bool sealStage = op.getStage() == zkc::pir::Stage::Seal;
            if (sealStage != op.getValue().has_value())
              error(op) << "[zkc-E227] " << (sealStage ? "seal" : "instance")
                        << "-stage binding must "
                        << (sealStage ? "carry" : "not carry")
                        << " an explicit value";
            // The statement-binding default (kernel.md §5.3): the FS
            // theorems hash the statement under every challenge, so
            // every public binding precedes the first one. A scoped
            // relaxation would be a cited row; none is seeded.
            // INVARIANT: requirement generation (kernel.md §5.2)
            // delegates its statement-bindings component entirely to
            // this default — any relaxation admitted here must land
            // together with a per-reduce statement check, or schema
            // challenges silently lose a third of their generated
            // requirements.
            if (firstChal)
              error(op) << "[zkc-E214] statement binding '" << op.getLabel()
                        << "' follows challenge '" << firstChal.getLabel()
                        << "': every public binding precedes its "
                           "segment's first challenge";
          })
          .Case<zkc::pir::SlotOp>([&](zkc::pir::SlotOp op) {
            requireCodec(op, op.getPayloadClass());
            if (op.getUnabsorbed() && !firstUnabsorbed)
              firstUnabsorbed = op;
          })
          .Case<zkc::pir::ChalOp>([&](zkc::pir::ChalOp op) {
            requireCodec(op, op.getPayloadClass());
            if (!firstChal)
              firstChal = op;
            // BIND: prefix satisfaction is precedence (SSA) plus
            // absorption (kernel.md §5.1).
            for (Value dep : op.getDeps()) {
              auto slot = dep.getDefiningOp<zkc::pir::SlotOp>();
              if (slot && slot.getUnabsorbed())
                error(op) << "[zkc-E211] dependency '" << slot.getLabel()
                          << "' is unabsorbed: a challenge cannot bind "
                             "material outside the transcript";
            }
            // The generalized Frozen-Heart condition (kernel.md §5.3).
            if (firstUnabsorbed)
              error(firstUnabsorbed)
                  << "[zkc-E212] unabsorbed slot precedes challenge '"
                  << op.getLabel()
                  << "': pre-challenge unabsorbed prover material is the "
                     "generalized Frozen-Heart condition";
          })
          .Case<zkc::pir::CheckOp>([&](zkc::pir::CheckOp op) {
            // COV_obl at the check event needs a resolved contract and mode.
            // Exact parameter, semantic-role, and operand-layout matching is
            // reconstructed by TerminalClosureOK below.
            const auto *info = vocabulary.lookupCheckContract(op.getContract());
            if (!info) {
              error(op) << "[zkc-E222] unknown check contract '"
                        << op.getContract() << "'";
              return;
            }
            if (info->isTransparent() != op.getExpr().has_value()) {
              error(op) << "[zkc-E226] "
                        << (info->isTransparent()
                                ? "transparent check contract requires an expr"
                                : "opaque check contract cannot carry an expr");
              return;
            }
            if (op.getExpr()) {
              (void)verifyExpr(op, *op.getExpr());
            }
          })
          .Case<zkc::pir::ArtifactVerifyOp>(
              [&](zkc::pir::ArtifactVerifyOp op) {
                // A proof slot the child verifier consumes must be a slot
                // of this artifact, and it must already have entered the
                // stream. Left unchecked, the encoder has nothing to
                // resolve the label to, and a label naming nothing would
                // have to either alias onto an event position -- giving two
                // different protocols one identity -- or fail with no
                // diagnostic an author can act on.
                //
                // Each opening below starts with its own words rather than
                // a shared prefix. The allocation lint digests the opening
                // of every emission site to catch a condition that moves
                // between identifiers, and two conditions phrased alike
                // would be invisible to it.
                std::optional<int64_t> here =
                    zkc::encoding::canonicalEventPosition(canonicalEvents,
                                                          op.getOperation());
                if (!here)
                  error(op) << "[zkc-E164] unresolved proof slot: artifact "
                               "verification '"
                            << op.getLabel()
                            << "' has no canonical event position, so no "
                               "slot can be ordered against it";
                if (auto slots = op.getProofSlots())
                  for (Attribute entry : *slots)
                    if (auto label = dyn_cast<StringAttr>(entry)) {
                      auto slot = slotLabels.find(label.getValue());
                      if (slot == slotLabels.end()) {
                        error(op) << "[zkc-E164] unresolved proof slot '"
                                  << label.getValue()
                                  << "': artifact verification '"
                                  << op.getLabel()
                                  << "' names it, and it is not a slot of "
                                     "this artifact";
                        continue;
                      }
                      // The spine is a total order and an event reads what
                      // precedes it. A verification naming material that
                      // arrives later would have the child consume a proof
                      // that is not in the stream yet, which is not a shape
                      // any projection could realize.
                      if (here && slot->second > *here)
                        error(op) << "[zkc-E165] out-of-order proof slot '"
                                  << label.getValue()
                                  << "': artifact verification '"
                                  << op.getLabel()
                                  << "' names it, and it follows the "
                                     "verification on the spine";
                    }
                // endpoints.md §3.1: child assumptions, exports, residuals,
                // and carried obligations may not disappear at the boundary;
                // they are discharged by the child-verifier semantics or
                // lifted into the parent-visible route surface. The carrier
                // cannot read the child, so what it enforces is that the
                // parent names a route at all and that the name is one the
                // artifact's own route surface carries -- a verification
                // whose route no sink mentions has lifted nothing.
                if (!routeSurface.contains(op.getRoute()))
                  error(op) << "[zkc-E163] artifact verification '"
                            << op.getLabel() << "' routes through '"
                            << op.getRoute()
                            << "', which no sink of this artifact names: a "
                               "child's assumptions and residuals are lifted "
                               "into the parent route surface, never dropped "
                               "at the boundary";
              })
          .Case<zkc::pir::ReduceOp>([](zkc::pir::ReduceOp) {})
          .Case<zkc::pir::DischargeOp>([&](zkc::pir::DischargeOp op) {
            // TerminalClosureOK resolves the rule, exact role map, selected
            // contracts, and every semantic attachment.
            (void)op;
          })
          .Case<zkc::pir::ExportOp, zkc::pir::AssumeOp, zkc::pir::ResidualOp>(
              [&](Operation *op) {
                StringRef kind = op->getName().stripDialect();
                if (!sinks.contains(kind))
                  error(op)
                      << "[zkc-E201] terminal route '" << kind
                      << "' is not permitted under policy '" << policy << "'";
              })
          .Case<zkc::pir::InstantiateOp, zkc::pir::MaterialBindOp,
                zkc::pir::BeginOp, zkc::pir::EndOp>([](auto) {
            // Instantiate is judged by the anchor gate in the domain
            // walk above; material bindings by TerminalClosureOK;
            // begin/end are the structural frame.
          })
          .Default([&](Operation *op) {
            // Fail closed: a member kind with no battery rule must
            // never seal — a missing case here would be a judgment
            // silently skipped. Unreachable today (the container
            // verifier, zkc-E131, closes the member set); it exists
            // so the next member kind fails loudly.
            error(op) << "operation has no seal battery rule; the "
                         "WF/LIN/BIND obligations for this member kind are "
                         "not defined (kernel.md 7)";
          });
    }
  }
};

} // namespace

llvm::ArrayRef<zkc::pir::DischargeKindRow> zkc::pir::dischargeKindTable() {
  // The single definition of the closed discharge-kind table
  // (kernel.md §6.1), each kind beside both endpoint-effect family sets
  // licensed to realize it (kernel.md §6.2). A verifier-side transparent
  // check licenses its whole lowered algebra — the assert plus the interior
  // ops the equation lowers to. Check obligations are counterparty rows on the
  // prover endpoint and therefore license no local op family there. Scalar and
  // vector challenge capabilities both license one counted squeeze;
  // multiplicity remains an exact property on that endpoint effect rather than
  // being unrolled. Growing the table is a kernel change, never a local
  // convenience.
  static const llvm::StringRef constAbsorb[] = {"const", "absorb"};
  static const llvm::StringRef argAbsorb[] = {"absorb"};
  static const llvm::StringRef verifierReadAbsorb[] = {"read", "absorb"};
  static const llvm::StringRef verifierRead[] = {"read"};
  static const llvm::StringRef proverReadAbsorb[] = {"write", "absorb"};
  static const llvm::StringRef proverRead[] = {"write"};
  static const llvm::StringRef squeeze[] = {"squeeze"};
  static const llvm::StringRef assertEq[] = {
      "assert_eq", "const", "f_neg", "f_add", "f_mul", "g_exp", "g_mul"};
  static const llvm::StringRef checkCall[] = {"check_call"};
  static const llvm::ArrayRef<llvm::StringRef> noLocalFamily;
  static const DischargeKindRow table[] = {
      {"const+absorb", constAbsorb, constAbsorb},
      {"arg+absorb", argAbsorb, argAbsorb},
      {"read+absorb", verifierReadAbsorb, proverReadAbsorb},
      {"read", verifierRead, proverRead},
      {"squeeze.scalar", squeeze, squeeze},
      {"squeeze.vector", squeeze, squeeze},
      {"assert_eq", assertEq, noLocalFamily},
      {"check_call", checkCall, noLocalFamily},
  };
  return table;
}

const zkc::pir::DischargeKindRow *
zkc::pir::findDischargeKind(llvm::StringRef name) {
  for (const DischargeKindRow &row : dischargeKindTable())
    if (row.name == name)
      return &row;
  return nullptr;
}

llvm::SmallVector<zkc::pir::ProjectionObligation> zkc::pir::deriveObligations(
    Block &body, const zkc::encoding::CanonicalIndex &canonicalEvents) {
  // One obligation per event, a pure function of the event's
  // already-encoded facts; every discharge name is a row of the
  // closed table above, looked up so a renamed or removed row cannot
  // leave a stale literal here.
  llvm::SmallVector<ProjectionObligation> table;
  for (Operation &op : body) {
    auto eventRef = zkc::encoding::canonicalEventPosition(canonicalEvents, &op);
    if (!eventRef)
      continue;
    StringRef discharge =
        llvm::TypeSwitch<Operation *, StringRef>(&op)
            .Case<zkc::pir::BindOp>([](zkc::pir::BindOp op) -> StringRef {
              return op.getStage() == zkc::pir::Stage::Seal ? "const+absorb"
                                                            : "arg+absorb";
            })
            .Case<zkc::pir::SlotOp>([](zkc::pir::SlotOp op) -> StringRef {
              return op.getUnabsorbed() ? "read" : "read+absorb";
            })
            .Case<zkc::pir::ChalOp>([](zkc::pir::ChalOp op) -> StringRef {
              return op.getMode() ? "squeeze.vector" : "squeeze.scalar";
            })
            .Case<zkc::pir::CheckOp>([](zkc::pir::CheckOp op) -> StringRef {
              return op.getExpr() ? "assert_eq" : "check_call";
            })
            .Default([](Operation *) -> StringRef {
              llvm_unreachable(
                  "canonical event kind has no obligation derivation");
            });
    const DischargeKindRow *row = findDischargeKind(discharge);
    assert(row && "event discharge outside the closed table");
    table.push_back({*eventRef, row->name});
  }
  llvm::sort(table, [](const ProjectionObligation &left,
                       const ProjectionObligation &right) {
    return left.eventRef < right.eventRef;
  });
  assert(static_cast<int64_t>(table.size()) ==
             zkc::encoding::canonicalEventCount(canonicalEvents) &&
         "canonical event index and obligation derivation cover one set");
  for (auto [position, obligation] : llvm::enumerate(table))
    assert(obligation.eventRef == static_cast<int64_t>(position) &&
           "canonical event positions are contiguous");
  return table;
}

bool zkc::pir::verifyResolvedVocab(
    Block &body, std::optional<DictionaryAttr> kappa,
    std::optional<DictionaryAttr> vocab,
    const zkc::registry::ProtocolVocabulary &protocolVocabulary,
    const zkc::registry::ConstructionProfileRegistry *profiles,
    llvm::function_ref<void(const llvm::Twine &)> error) {
  bool ok = true;
  auto fail = [&](const llvm::Twine &message) {
    error(message);
    ok = false;
  };
  if (!vocab) {
    fail("carries no resolved-vocabulary table: the seal stamps cited "
         "content digests (kernel.md 8)");
    return ok;
  }

  // The five core sections are mandatory; hole_contracts appears
  // exactly when construction routes cite at least one contract, so a
  // protocol without routes keeps its exact table shape and bytes.
  static constexpr StringLiteral sections[] = {
      "claim_profiles", "check_contracts",       "reduction_contracts",
      "terminal_rules", "construction_profiles", "hole_contracts"};
  bool hasHoleSection = vocab->getNamed("hole_contracts").has_value();
  if (vocab->size() != (hasHoleSection ? 6u : 5u))
    fail("resolved-vocabulary table must contain exactly claim_profiles, "
         "check_contracts, reduction_contracts, terminal_rules, "
         "and construction_profiles, plus hole_contracts only when routes "
         "cite hole contracts");
  for (NamedAttribute section : *vocab) {
    StringRef name = section.getName().getValue();
    if (!llvm::is_contained(sections, name))
      fail("resolved-vocabulary table has an unknown section '" + name + "'");
    if (!isa<DictionaryAttr>(section.getValue()))
      fail("resolved-vocabulary section '" + name + "' must be a dictionary");
  }

  auto verifySection =
      [&](StringRef section, ArrayRef<StringRef> cited,
          llvm::function_ref<std::optional<StringRef>(StringRef)>
              loadedDigest) {
        auto named = vocab->getNamed(section);
        auto dict = named ? dyn_cast<DictionaryAttr>(named->getValue())
                          : DictionaryAttr();
        if (!dict) {
          fail("resolved-vocabulary table has no '" + section + "' section");
          return;
        }
        llvm::StringSet<> citedSet;
        for (StringRef id : cited)
          citedSet.insert(id);
        for (NamedAttribute entry : dict)
          if (!citedSet.contains(entry.getName().getValue()))
            fail("vocabulary section '" + section + "' stamps a digest for '" +
                 entry.getName().getValue() + "', which this body never cites");
        for (StringRef id : cited) {
          auto entry = dict.getNamed(id);
          auto digest =
              entry ? dyn_cast<StringAttr>(entry->getValue()) : StringAttr();
          if (!digest) {
            fail("cited id '" + id +
                 "' has no stamped digest in vocabulary section '" + section +
                 "'");
            continue;
          }
          std::optional<StringRef> loaded = loadedDigest(id);
          if (!loaded) {
            fail("cited id '" + id + "' in section '" + section +
                 "' is not in the loaded authority");
            continue;
          }
          if (digest.getValue() != *loaded)
            fail("'" + id +
                 "' content digest does not match the loaded registry: the "
                 "artifact was sealed against different vocabulary semantics");
        }
      };

  ProtocolVocabularyCitations protocolCitations =
      zkc::pir::collectCitedProtocolVocabulary(body, protocolVocabulary);
  verifySection("claim_profiles", protocolCitations.claimProfiles,
                [&](StringRef id) -> std::optional<StringRef> {
                  const auto *entry = protocolVocabulary.lookupProfile(id);
                  return entry
                             ? std::optional<StringRef>(entry->contentDigest())
                             : std::nullopt;
                });
  verifySection("check_contracts", protocolCitations.checkContracts,
                [&](StringRef id) -> std::optional<StringRef> {
                  const auto *entry =
                      protocolVocabulary.lookupCheckContract(id);
                  return entry
                             ? std::optional<StringRef>(entry->contentDigest())
                             : std::nullopt;
                });
  verifySection("reduction_contracts", protocolCitations.reductionContracts,
                [&](StringRef id) -> std::optional<StringRef> {
                  const auto *entry =
                      protocolVocabulary.lookupReductionContract(id);
                  return entry
                             ? std::optional<StringRef>(entry->contentDigest())
                             : std::nullopt;
                });
  verifySection("terminal_rules", protocolCitations.terminalRules,
                [&](StringRef id) -> std::optional<StringRef> {
                  const auto *entry = protocolVocabulary.lookupRule(id);
                  return entry
                             ? std::optional<StringRef>(entry->contentDigest())
                             : std::nullopt;
                });

  // Construction entries remain a separate lifecycle, but every consumed
  // sponge and codec is pinned in this one artifact-level digest table.
  StringRef spongeName = zkc::pir::kappaSpongeName(kappa);
  auto codecNames = zkc::pir::kappaConsumedCodecNames(kappa);
  SmallVector<std::string> constructionStorage;
  if (!spongeName.empty())
    constructionStorage.push_back(("sponge:" + spongeName).str());
  for (StringRef codecName : codecNames)
    constructionStorage.push_back(("codec:" + codecName).str());
  llvm::sort(constructionStorage);
  constructionStorage.erase(llvm::unique(constructionStorage),
                            constructionStorage.end());
  SmallVector<StringRef> citedConstruction;
  for (const std::string &name : constructionStorage)
    citedConstruction.push_back(name);
  verifySection("construction_profiles", citedConstruction,
                [&](StringRef name) -> std::optional<StringRef> {
                  if (!profiles)
                    return std::nullopt;
                  if (name.consume_front("sponge:")) {
                    const auto *sponge = profiles->lookup(name);
                    return sponge ? std::optional<StringRef>(sponge->digest)
                                  : std::nullopt;
                  }
                  if (name.consume_front("codec:")) {
                    const auto *codec = profiles->lookupCodec(name);
                    return codec ? std::optional<StringRef>(codec->digest)
                                 : std::nullopt;
                  }
                  return std::nullopt;
                });

  // Hole contracts are cited by the construction routes riding on the
  // container, not by body ops; the same exact-citation discipline
  // applies to the sixth section when it exists.
  SmallVector<StringRef> citedHoles;
  if (Operation *container = body.getParentOp())
    if (auto routes = container->getAttrOfType<DictionaryAttr>("routes"))
      if (auto instances =
              dyn_cast_or_null<DictionaryAttr>(routes.get("instances"))) {
        llvm::StringSet<> seenHole;
        for (NamedAttribute instance : instances)
          if (auto instanceBody = dyn_cast<DictionaryAttr>(instance.getValue()))
            if (auto id =
                    dyn_cast_or_null<StringAttr>(instanceBody.get("contract")))
              if (seenHole.insert(id.getValue()).second)
                citedHoles.push_back(id.getValue());
      }
  if (hasHoleSection != !citedHoles.empty())
    fail("resolved-vocabulary table carries hole_contracts exactly when "
         "routes cite hole contracts");
  if (hasHoleSection || !citedHoles.empty())
    verifySection(
        "hole_contracts", citedHoles,
        [&](StringRef id) -> std::optional<StringRef> {
          const auto *entry = protocolVocabulary.lookupHoleContract(id);
          return entry ? std::optional<StringRef>(entry->contentDigest())
                       : std::nullopt;
        });
  return ok;
}

LogicalResult zkc::pir::runSealBattery(
    Operation *container, std::optional<DictionaryAttr> kappa,
    std::optional<DictionaryAttr> vocab,
    std::optional<llvm::ArrayRef<int64_t>> segments, llvm::StringRef policy,
    bool recheck, const zkc::registry::ProtocolVocabulary &protocolVocabulary,
    const zkc::registry::ConstructionProfileRegistry *profiles) {
  SealBattery battery(protocolVocabulary, profiles, recheck);
  return battery.run(container, kappa, vocab, segments, policy);
}
