# Native FRI/IOR End-to-End Validation Plan

> **Kind:** Temporary protocol-validation work contract
> **State:** Executed for one finite early-terminated profile; broader
> protocol-family closure remains open
> **Authority:** None. This page fixes the scope and method of one research
> package. It does not define target semantics, establish protocol support,
> discharge a theorem, or authorize normative cutover.
> **Baseline:** Candidate redesign at outer-repository commit
> `ae9a99f51d2e5fe41c53b8e9894ff6a4506bbe6a`.
> **Disposition:** Absorb accepted semantic conclusions and retained evidence
> into their exact owners, preserve rejected alternatives only when their
> rationale remains useful, and delete this page before cutover.

## 1. Central question

Can the candidate semantic architecture represent a source-faithful native
FRI interactive-oracle protocol through authenticated query openings, without
moving semantic authority into an evaluator, codec, Merkle implementation,
backend, report, or opaque extension?

The package is allowed to answer `no`. A decisive obstruction is a successful
research result when it identifies the exact boundary that must change.

The work is not constrained to fitting the current candidate. If the protocol
requires a better treatment of interaction, logical oracles, commitments,
challenge interpretation, strategy state, relations, quantitative analysis,
identity, or authority, the package must compare alternatives and may propose
an explicit reopening.

## 2. One long end-to-end unit

This is one continuous validation package, not a preliminary survey followed
by an assumed implementation. It includes:

1. primary-source and implementation-profile selection;
2. source-faithful protocol reconstruction;
3. current specification and implementation correspondence;
4. independently derived semantic anatomy;
5. alternative architecture generation and comparison;
6. a complete typed constructive encoding;
7. an executable finite witness with positive and negative cases;
8. cross-domain convergence across Foundation, PIR, Fiat--Shamir, Relations,
   Analysis, Compiler consumers, and the bounded endpoint seam;
9. explicit model-change proposals where required;
10. replay, independent reconstruction, and final classification; and
11. absorption or deferral recommendations.

Research, design, implementation, and falsification are therefore all in
scope. Passing the current model is not assumed, and producing an executable
witness is not allowed to hide a failed semantic boundary.

## 3. Protocol boundary in scope

The selected source profile must be rich enough to cover the following path:

```text
public instance and code/domain parameters
    -> fixed initial logical oracle
    -> verifier folding challenges
    -> folded prover oracles
    -> terminal material and residual condition
    -> optional work augmentation: work seed, nonce, and predicate
    -> query randomness
    -> query positions with multiplicity
    -> values and authentication openings
    -> root/path authentication
    -> fold-consistency and terminal checks
    -> Accept, Reject, Abort, or exact residual
```

The package must distinguish four levels rather than conflating them:

1. **Native IOP/IOPP semantics:** verifier access to logical oracles and the
   source protocol's own query and decision structure.
2. **Commitment compilation:** roots, salts, paths, leaf grouping, query
   deduplication, and authentication supplied by an exact commitment profile.
3. **Grinding augmentation:** an explicit prior work-seed challenge, nonce
   publication, predicate, placement, and work accounting when the selected
   profile adds grinding that is absent from native FRI.
4. **Fiat--Shamir interpretation:** statement- and context-bound derivation of
   interaction coins and final query randomness under an exact transcript,
   framing, sampler, and random-oracle or sponge profile.

The selected finite profile may compose these levels, but their subjects,
assumptions, identities, failures, and conclusions must remain recoverable.

## 4. Required research

Research begins from primary sources and exact official implementation
artifacts where they materially determine protocol shape.

At minimum, reconstruct and compare:

- original FRI as an interactive oracle proof of proximity;
- the BCS-style transformation from public-coin IOPs to noninteractive
  arguments with vector commitments;
- modern analyses of FRI Fiat--Shamir, state restoration, grinding, and
  concrete loss;
- at least two real implementation profiles that make different choices for
  leaf layout, cap/root representation, extension-field values, query
  deduplication, openings, salting, grinding, or transcript state; and
- one implementation-agnostic idealization that is not copied from the current zkc model or
  either implementation.

Every external claim records its exact source, version or retrieval date,
the proposition it supports, the assumptions it requires, and the limit of
the analogy to zkc. Implementation convention is not promoted into protocol
semantics merely because multiple libraries share it.

The reserved cold holdout protocols remain unopened. This package may derive
general requirements from the selected native FRI sources, but it must not
optimize the model against withheld cases.

## 5. Reconstruction obligations

The source dossier must account for:

- statement, witness, public parameters, domain parameters, and setup;
- prover strategy state and non-anticipating reads;
- verifier state, public coins, derived coins, and adaptive query choice;
- every logical oracle, its author, lifetime, domain, codomain, and visibility;
- when an oracle becomes fixed relative to each later challenge;
- commitment roots, leaves, caps, salts, paths, and authentication checks;
- query draws as occurrences, including repeated positions;
- deduplicated proof material without erasing draw multiplicity;
- folding maps, extension-field operations, terminal representations, and
  residual claims;
- all rejection and abort paths;
- direct interaction, commitment compilation, and Fiat--Shamir as distinct
  constructions;
- relation grounding and the boundary to an outer AIR or computation claim;
- theorem premises and quantitative loss without claiming theorem truth; and
- exact semantic omissions and residual trust.

The prior grinding fixture is evidence only for its exact finite residual. It
must not supply the native oracle, authentication, fold, degree, or terminal
semantics required here.

## 6. Design-space requirement

For every material obstruction, compare the meaningful members of this
portfolio:

1. preserve the current design and provide the missing source-faithful
   inhabitant;
2. complete the current design with owner-local typed definitions or laws;
3. structurally redesign the affected subject, lifecycle, authority, or
   construction boundary; and
4. introduce a capability-expanding abstraction when it simplifies at least
   two materially distinct mechanisms or preserves important future option
   value.

At least the following architecture choices must be evaluated rather than
silently assumed:

- logical oracle as a native Core effect, a typed message family, or a
  separately owned subject related to Core;
- commitment/opening as protocol semantics, a checked compilation, or an
  endpoint realization;
- query draws and opened positions as one object or related distinct objects;
- Fresh IOP, committed interactive protocol, and Fiat--Shamir argument as one
  subject, mapped subjects, or a shared skeleton with separate realizations;
- transcript as a prefix log, a typed state machine, or an abstract challenge
  interpretation with profile-owned state;
- terminal low-degree material as acceptance, a residual claim, or a
  reduction target;
- FRI-specific vocabulary versus reusable oracle/query/opening interfaces;
- semantic identity of logical oracles versus representation identity of
  committed trees and proof packages; and
- theorem applicability as structural admission, an Analysis proposition, or
  a composition of independently checked premises.

The preferred model must state what becomes possible, what becomes harder,
what remains outside v0, and what would reverse the decision.

## 7. Constructive encoding

Before executable work is counted, produce a complete typed object graph for
one exact finite profile. It must expose:

- all semantic subjects and occurrence identities;
- actors, visibility, causality, strategy reads, and ownership;
- interaction phases and every challenge request;
- logical-oracle declarations, writes, queries, and returned values;
- commitment compilation and authenticated-opening correspondence;
- codecs, framing, samplers, hash or sponge operations, domains, and bounds;
- Fresh and Fiat--Shamir constructions where both are claimed;
- relation instances, witness or private-input boundaries, and grounding;
- terminal result or residual claim;
- Analysis questions and theorem-premise records;
- all required local admissions, validation records, and consumer
  capabilities; and
- explicit unsupported or deferred surfaces.

Opaque callbacks, universal values, evaluator-authored success, post-hoc
identity equality, and proof bytes that erase semantic structure do not count
as an encoding.

## 8. Executable witness

The finite witness must be independently reconstructible from frozen public
source material. It may use a deliberately small field, domain, degree, and
query count when either the reduction from the selected source profile is
exact and recorded, or the package defines one exact internal finite profile,
records every source delta, and makes no theorem or source-correspondence claim
for that profile.

The executable package must contain:

- frozen public inputs and a separate, explicitly declassified owner-generation
  lane whose values populate private semantic roles;
- a source ledger with content digests and versioned provenance;
- one deterministic reference execution for reproducibility;
- exact semantic and validation identities;
- a complete positive trace to the claimed terminal or residual;
- non-authoring replay from public inputs;
- bounded evaluation and resource-exhaustion behavior;
- separately implemented reconstruction where it provides real diversity;
- a compact machine-readable report; and
- tests for every named refusal.

The evaluator may compute the selected finite protocol, but it may not define
what success means after seeing the produced values. Acceptance and residual
conditions must be fixed by the source-derived semantic profile before
execution.

## 9. Mandatory negative pressure

Negative cases must remain well formed until their intended first refusal.
The suite covers at least:

- missing, delayed, reordered, duplicated, or substituted statement binding;
- a logical oracle authored after a challenge that must depend on it;
- a commitment root omitted from protected challenge state;
- challenge namespace, framing, codec, sampler, or domain mismatch;
- prover reads of future verifier randomness;
- query randomness sampled before terminal commitment;
- draw multiplicity erased by deduplicated openings;
- value, index, leaf, cap, root, salt, or authentication-path substitution;
- valid paths attached to the wrong query occurrence;
- fold-domain, extension-field, or terminal-representation mismatch;
- an authenticated opening that does not establish fold consistency;
- a fold-consistent trace that does not establish the terminal degree claim;
- an outer relation claim inferred from FRI proximity alone;
- grinding placed after the randomness it purports to protect;
- unsupported algorithms, profiles, regimes, or commitment parameters;
- lossy bridges mislabeled as embeddings or isomorphisms;
- stale validation, wrong-profile reuse, and identifier-as-capability errors;
- evaluation, proof-size, depth, byte, node, or work-budget exhaustion; and
- self-authored positive evidence or an input-shape-guaranteed checker.

Additional mutations are required whenever candidate comparison exposes a new
first boundary.

## 10. Cross-domain convergence

The result is reviewed across every affected owner:

- **Foundation:** canonical values, algorithms, profiles, identities, bounds,
  failures, and capability minting;
- **PIR:** interaction, oracle effects, challenges, execution, composition,
  and Fresh/Fiat--Shamir constructions;
- **Relations:** statement grounding, residual claims, lossy bridges, and
  outer-relation non-implication;
- **Analysis:** adversary and oracle models, theorem applicability,
  state-restoration or rewinding premises, and quantitative loss;
- **Compiler:** only decisions actually required to choose or validate a
  commitment or realization profile;
- **OIR seam:** source-relative projection pressure without activating a full
  endpoint or realization architecture; and
- **Evidence:** replay and observation claims without semantic backflow.

If two domains require incompatible assumptions, reopen the shared boundary.
Do not repair one page locally while leaving the contradiction elsewhere.

## 11. Evidence strength and classification

The intended result is executable falsification for one finite profile. Its
strongest permitted positive claim is:

> One source-grounded finite native FRI/IOR profile, including its commitment
> declaration and one-run validation receipt plus its admitted Fiat--Shamir
> construction, inhabited the candidate model and reproduced its named
> positive and negative boundaries under the frozen evaluator and resource
> contracts.

It does not establish general FRI support, protocol soundness, theorem truth,
ROM or QROM security, implementation conformance, performance, or support for
all oracle protocols.

The final primary classification is exactly one of:

- native;
- owner-local profile or module;
- conservative extension;
- modeling workaround;
- semantic loss;
- fundamental obstruction;
- intentional v0 boundary; or
- undetermined.

Local mechanisms may receive separate subordinate classifications, but they
must not blur the case-level result.

## 12. Gates

The package closes only when all applicable gates pass or a retained failure
decisively explains why they cannot pass.

| Gate | Required result |
|---|---|
| Source fidelity | Exact source/profile selection, provenance, anatomy, and explicit deductions versus conventions |
| Design-space coverage | Current model and serious completion, redesign, and capability alternatives compared at equal resolution |
| Semantic closure | Complete typed subjects, identities, authority, lifecycle, failures, bounds, and non-claims |
| Protocol closure | Logical-oracle, query, opening, authentication, fold, terminal, and residual boundaries are all explicit |
| Construction closure | Native execution and generally admitted Fiat--Shamir construction are checked at their respective scopes; commitment and grinding declarations have separate validation-bound one-run receipts |
| Relations closure | Statement, residual, and outer-relation grounding are exact; loss and non-implications are visible |
| Analysis closure | Exact questions and premises are representable without claiming theorem truth |
| Executable pressure | Frozen positive case and named negative mutations replay under bounded resources |
| Independent reconstruction | A separate path reproduces the public classification without importing producer conclusions |
| Regression | Existing semantic witnesses and applicable repository checks remain green or have explicit reopening records |
| Convergence | Every affected owner accepts one coherent boundary or records the unresolved contradiction |
| Absorption | Accepted changes, retained evidence, open questions, and deletion targets have exact destinations |

### 12.1 Observed disposition

The executed finite case is a **conservative semantic extension**. One
early-terminated logical-oracle FRI profile inhabits separate native,
commitment-compiled, work-augmented, Fresh, and Fiat--Shamir subjects. The
producer and separately coded replay agree on selected exact positive
public-execution facts. Two named late negatives reach their expected producer
boundaries. Owner-local construction-validation and Relations operations pass
under their own validation-bound live receipts. The commitment and grinding
receipts concern one concrete execution and do not generally admit either
construction; these are distinct evidence lanes rather than one shared
correspondence result. The package forms Analysis questions but does not answer
them.

This result preserves the central factorization. It does not close exact
classical FRI correspondence or protocol-family support. Cross-family source
pressure identifies verifier-derived oracle access as a real missing
capability, but `DerivedOracle`/`QueryPlan` remains a candidate rather than an
accepted design. Static pre-authentication elaboration is the leading next
test; runtime query expansion would reopen Core execution, receipts,
composition, and authentication.

The remaining absorption work is therefore intentionally split:

- retain the finite executable package as bounded falsification evidence;
- carry the logical-access, origin, construction, identity, Relations, and
  Analysis requirements into their eventual durable owners only after review;
- construct the exact three-fold scalar-terminal control before claiming
  classical FRI correspondence; and
- resolve static derived-query elaboration, face-map capability transport,
  DEEP-ALI total quotient semantics, and STIR collision semantics before
  promoting the cross-family seam.

## 13. Checkpoints and interruption rule

The work proceeds continuously through the following semantic checkpoints:

1. source and implementation-profile selection;
2. complete source anatomy and current-model reconstruction;
3. candidate portfolio and independently derived object graphs;
4. provisional architecture decision with reversal conditions;
5. executable finite witness and negative suite;
6. independent replay and cross-domain reconciliation; and
7. final classification, absorption proposal, and remaining portfolio handoff.

An external review may arrive during any checkpoint. Finish the smallest
currently atomic read, experiment, or edit, then pause at a clean checkpoint.
Classify whether the review:

- leaves the work unchanged;
- requires a local amendment and replay;
- reopens a shared boundary but preserves the source reconstruction; or
- invalidates the selected object graph and requires a new candidate pass.

Do not merge concurrent conclusions by chronology. Reconcile them against the
same source facts, invariants, and affected owners.

## 14. Explicit non-goals

This package does not attempt to:

- specify a complete STARK, AIR, trace commitment, constraint system, or outer
  computation proof;
- prove FRI soundness, proximity, knowledge, or zero knowledge;
- define a universal polynomial-commitment interface;
- complete Sumcheck, GKR, KZG, folding, recursion, or the remaining protocol
  portfolio;
- inspect or optimize against reserved cold holdout protocols;
- activate a full OIR, realization, endpoint, or deployment architecture;
- preserve compatibility with the current implementation at the expense of a
  better semantic model; or
- infer generality from one executable finite case.

These exclusions bound the package; they do not prevent reopening a shared v0
decision when native FRI/IOR supplies concrete evidence that the decision is
wrong.

## 15. Exact classical follow-up disposition

The requested exact follow-up is now executable without replacing the earlier
order-16 early-stop case. It adds the Goldilocks order-64 three-fold control,
one exact structural logical-Oracle-to-committed-Core construction, Fresh and
strong-Fiat--Shamir execution over one committed Core, and a separately coded
public verifier. The construction checker owns stable static maps and live
process-local authority; its portable receipt validates one concrete
source/target pair only.

Relations and Analysis pressure found two deliberate promotion boundaries.
The current Relations instrument grounds initial G0 from a declassified full
trace, so a durable result first needs a PIR-owned purpose-specific
confidential Oracle view and live capability. The Analysis instrument forms
questions and checks non-vacuous arithmetic but establishes no theorem truth,
applicability, or property. General FRI/IOR, BCS, derived-oracle, commitment
security, and outer-relation claims remain outside this follow-up.
