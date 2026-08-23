# R1 Invariant Ledger

> **Document kind:** Temporary cross-domain requirement ledger
> **Document state:** Active
> **Owner:** `project`, routing each invariant to its semantic owner
> **Authority:** None. These are recovered requirements and falsification
> targets, not a selected representation or normative specification.
> **Source:** The independently adjudicated findings in
> [review-adjudication.md](review-adjudication.md).
> **Disposition:** Resolve each item through R2--R4, absorb it into one durable
> owner or an explicit extension boundary, then delete this ledger.

## 1. How to use this ledger

An invariant constrains every viable candidate without prescribing its data
structure. A candidate does not satisfy an invariant by repeating its name: it
must identify the owner, formation and checking law, positive inhabitant,
well-formed negative mutation, resource behavior, and downstream consumer.

`Required` means every viable v0 candidate must close the item. `Preserve`
means the current target has an important semantic hypothesis that remains the
leading candidate, although its representation and even its final retention
remain subject to the stated executable revalidation. It is not a universal,
solution-independent law. `OpenScope` means R2/R3 must first decide what v0
promises.

## 2. Foundation and identity invariants

| ID | State | Invariant | Acceptance pressure and owner |
|---|---|---|---|
| F-01 | `Required` | **Regime closure.** Every semantic regime has exact identity derivation, meaning, support, equality, and compatibility rules. A first-class acquired regime additionally needs authentication, admission, and lifecycle laws; a static regime needs an exact version/change law, not a fictitious runtime rotation path. | Two independent implementations must derive the same identity/support result and reject an unsupported or ambiguously interpreted regime. Foundation owns only the common mechanism; each domain owns regime content and whether the static or first-class lane applies. |
| F-02 | `Required` | **Canonical boundary-value closure.** Every value that crosses identity, transport, equality, or execution boundaries is domain-indexed and has decidable membership, unique canonical bytes/equality, decode rejection, and substitution rules. | A noncanonical encoding, wrong domain, or ambiguous equality must fail before the affected boundary. Project owns the cross-domain condition; exact domains own membership, bytes, and equality; Foundation owns only a common mechanism that passes extraction. |
| F-03 | `Required` | **Algorithm closure.** Every identity-bearing algorithm has an exact kind-indexed ABI, canonical preimage or referenced contract, deterministic transition/evaluation semantics, and named failure behavior. | Round-trip a real codec/sampler/bridge; reject wrong arity, domain, state, or result. Shared envelope only if extraction proves identity; semantics remain domain-owned. |
| F-04 | `Required` | **Totality has evidence.** A totality claim names the proposition, evaluator, domain, resource model, evidence form, checker/trust root, and identity effect. | A mere declaration cannot establish totality. Include a malformed, partial, or exhausted evaluator case. |
| F-05 | `Required` | **Bounded identity work.** Identity preimages and admission-derived work are profile-bounded, certificate-bounded, or terminate with a nonsemantic checker/resource failure. | Measure stored bytes, peak derived structure, memory, and work on real and adversarial guards. No divergent semantic verdict. |
| F-06 | `Required` | **Identity-field justification.** A field or collection order enters identity only if it changes an authorized observation, creates a necessary stable reference namespace, or enforces a stated domain-separation invariant. | Remove or justify one semantically inert permutation/field; demonstrate the consumer or attack boundary for every retained one. Domain owner plus identity specification. |
| F-07 | `Preserve` | **Acyclic self-binding.** A self-derived value has an exact construction whose identity dependencies are acyclic and whose post-ID interpretation is unique; no evidence or policy can reintroduce a hash cycle. | Independently evaluate the current `BindConstructionSelfId` inhabitant and at least one equally exact alternative if available; reject premature resolution and recursive regime/policy roots. |
| F-08 | `Required` | **Kind-safe ABI algebra.** Algorithm, capability, proof/interface, relation bridge, and endpoint ABIs carry enough kind information and explicit compatibility judgments to reject cross-kind substitution. | Every bare “exact ABI” reference must route to one schema owner. Either disjoint schemas or one dependently indexed algebra may satisfy the requirement. |

## 3. Protocol, transcript, and execution invariants

| ID | State | Invariant | Acceptance pressure and owner |
|---|---|---|---|
| P-01 | `Required` | **Complete instance binding.** Every Statement occurrence in a challenge's declared scope has explicit canonical, typed, injective influence on the challenge state before that challenge, with exact scope, ordering, and multiplicity rules. | Omit, substitute, reorder where order is semantic, delay, or use the wrong codec for one Statement occurrence; duplicate only where the selected profile forbids it. PIR invocation and FS construction. |
| P-02 | `Required` | **Derived transcript obligation.** Required challenge sources follow from statement purpose, proof/round/oracle role, and exact contracts, not solely from an authored Transcript observation bit. | A required Proof message changed to Wire-only rejects, while a declared irrelevant application message remains admissible. PIR and exact round/oracle contracts. |
| P-03 | `Required` | **Exact prefix closure.** Every active required source precedes the challenge and appears in the exact active ordered prefix with its declared occurrence/multiplicity rule. | Reproduce the semantic boundaries behind E211, E212, and E214 without importing their current representation by fiat. Namespace collision and reuse are tested under P-07. PIR. |
| P-04 | `Required` | **Explicit relaxation.** Omitting a normally required source is legal only under a named theorem/profile with exact assumptions, scope, and quantitative consequence. | A weak/static profile cannot be consumed as strong/adaptive FS. PIR marks structure; Analysis owns applicability and loss. |
| P-05 | `Required` | **Public-coin eligibility.** Every verifier action in the transformed proof interaction is a deterministic function of public history and explicit PublicEnvironment randomness; no verifier-private value or hidden state influences a prover-visible move. | Introduce a verifier-private invocation value, private sample, hidden state dependency, or unlinked stochastic verifier move and require admission to reject it. PIR Core/FS admission. |
| P-06 | `OpenScope` | **Declared FS strength.** If `FiatShamir` denotes structurally strong FS, every proof-interaction verifier message must be challenge-derived, publicly reconstructible, or explicitly outside the transformed interaction. If it denotes a generic transcript-derived interpretation, strong-FS eligibility must be a separate checked result. | Encode a deterministic nonchallenge verifier message and decide which result admits or rejects it; no message silently disappears under either interpretation. PIR. |
| P-07 | `Required` | **Unambiguous challenge derivation.** The squeeze/sample ABI includes a collision-free, composition-safe occurrence namespace and a full `(state, conditional inputs) -> (state', value or named failure)` relation. It need not be one globally unique authored string. | Ambiguous/reused occurrence namespace, wrong state transition, and grinding/rejection failure mutations, including the semantic boundary behind E216. PIR FS construction. |
| P-08 | `Required` | **Causal prover generation.** A prover move depends only on its visible past, private inputs/witness, prior private state/randomness, advice, and permitted oracle responses. | A commitment depending on a future challenge is not strategy-generated even if a whole serialized trace replays. PIR exposes decision points/history/legal moves; Analysis owns strategy classes. |
| P-09 | `Required` | **Causal reproducibility and auditability.** Strategy execution exposes enough authenticated history to reproduce or independently audit the induced outcome distribution under the same invocation and randomness. | A paired online/replay semantics or one evaluator that emits a checked trace may satisfy the requirement; exercise honest and malicious strategies and reject a clairvoyant trace as non-generated. PIR/Analysis seam. |
| P-10 | `Required` | **Typed claim routing.** Claim production, reduction inputs/outputs and side inputs, and check operands satisfy explicit contract/parameter/domain equations. | Wrong claim contract, parameter order/domain, reduction output, or check input rejects. PIR. |
| P-11 | `Required` | **View adequacy is checked.** A source-owned finite view covers the exact consumer-owned read closure, with defined missing, extra, selector, and equality behavior. | Remove one required fact, add a forbidden authoritative mirror, or request an unknown question. Source domain plus consumer. |
| P-12 | `Preserve` | **Checked Fresh/FS factorization.** Fresh and FS Protocols are connected by an explicit checked construction that closes all interpretation-specific obligations. Sharing one admitted Core is the current favored hypothesis, not part of the invariant itself. | Compare a genuine same-Core FRI pair with a related-distinct-Core or bisimulation-style challenger and apply negative construction mutations. PIR. |

## 4. Relations invariants

| ID | State | Invariant | Acceptance pressure and owner |
|---|---|---|---|
| R-01 | `Required` | **Correspondence-regime reachability.** Every operation that requires an admitted regime has a constructible static or first-class regime path, exact authority, and cold replay. | Reconstruct the regime and every dependency from persistent inputs; reject a substituted regime. Foundation mechanism plus Relations specialization. |
| R-02 | `Required` | **Closed artifact-fact algebra.** Fact schemas, typed facts, field references, selectors, absence/multiplicity, equality, and profile/adapter compatibility are formed and canonically encoded. | Interpret one real R1CS/AIR-style artifact and reject wrong-schema selectors and ambiguous fields. Relations. |
| R-03 | `Required` | **Explicit grounding equations.** Committed-object grounding names every typed left/right operand, source, equality relation, evaluation order, and failure fact. | One affirmative real object plus wrong commitment, material, selector, position, and equation mutations. Relations; Analysis owns later cryptographic faithfulness. |
| R-04 | `Preserve` | **Lossless bridge laws are explicit.** Whole-domain semantic equivalence is a total bijection with both inverse laws. A lossless embedding is injective, has an exact image predicate, and is invertible on that image. Neither may be represented as a lossy projection. | Round-trip a full equivalence in both directions, round-trip an embedding on its image, and reject a lossy mapping presented as either. Relations. |
| R-05 | `Required` | **Every retained lossy projection is separate and priced.** A directional identity/transcript-material projection names authenticated source meaning, source and target domains, canonical algorithm, collision relation/game, any preimage premise, exact occurrences, and a quantitative loss transform. | Model the current 256-to-216-bit anchor case with a grounded reduction or deliberately eliminate it, for example by retaining a full digest. Relations owns projection meaning, PIR owns absorb occurrences, and Analysis owns the game and loss. |
| R-06 | `Required` | **Relation-facing witness surface.** PIR explicitly distinguishes relation Witness occurrences from confidential Context, ProtocolValue, and internal obligation outputs. | A protocol-private nonwitness input must not force a Relations witness port; an exported derived witness must be expressible. PIR defines surface; Relations compares it. |
| R-07 | `Required` | **Result correspondence has a direction.** Structural result references, relation acceptance, Protocol acceptance, soundness direction, completeness direction, and full equivalence are distinct judgments. | A structural binding cannot be consumed as behavioral equivalence. Relations/PIR, with universal theorems in Analysis. |
| R-08 | `Required` | **Binding questions retain meaningful negatives.** Admission, structural correspondence, instance correspondence, grounding, and behavioral correspondence do not duplicate the same predicate under stronger names. | For every affirmative result, exhibit a well-formed admitted operand that can produce its declared Negative, or derive the fact internally instead. Relations. |

## 5. Analysis and Compiler invariants

| ID | State | Invariant | Acceptance pressure and owner |
|---|---|---|---|
| A-01 | `Required` | **Theorem grounding.** A property result names its exact game/experiment, causal strategy class, model/oracles, resource regime, assumptions, theorem or checked derivation, correspondence premises, and loss. | Instantiate at least one real FS theorem and reject an assumption/model mismatch. Analysis. |
| A-02 | `Required` | **Quantitative-loss completeness.** Every approximation, projection, reduction, composition, or transform loss has an exact occurrence/accounting source and enters one typed ledger. | The anchor projection and one FS/composition loss must be recomputed without hidden terms. Analysis. |
| A-03 | `Preserve` | **Property-family separation.** Soundness does not imply round-by-round soundness, ROM does not imply QROM, and HVZK does not imply malicious-verifier ZK without an exact checked transport. | Wrong-family or wrong-model capability use rejects. Analysis. |
| A-04 | `Preserve` | **Cost meaning precedes optimization.** The producer owns raw observation meaning and completeness; Evidence owns provenance, procedure, environment, samples, and uncertainty; Analysis owns derived cost judgments and inference; Compiler owns comparison under explicit objectives and comparators. | A measured estimate cannot masquerade as exact semantic cost, incomplete observations cannot acquire false completeness, and missing objective data cannot become an implicit score. |
| A-05 | `Required` | **Primary-source traceability.** Source-specific cryptographic notions and theorem instances have maintained primary citations, exact versions, scope, and non-transferable assumptions. | A cold reader can recover the theorem statement and see why its hypotheses match; citation alone never grants authority. Analysis/project related work. |

## 6. Cross-domain and process invariants

| ID | State | Invariant | Acceptance pressure and owner |
|---|---|---|---|
| X-01 | `Required` | **Nonvacuous semantic relations.** Every semantic affirmative/negative relation states the exact postcondition and admits a meaningful well-formed negative. Deterministic derivation or conformance checks may instead report typed mismatch, malformed input, or invalid evidence. | Do not manufacture a semantic Negative by corrupting a deterministic constructor's only canonical output; test the declared failure class at each relation boundary. |
| X-02 | `Required` | **Derived evidence remains derived.** Canonical maps, prefixes, endpoint obligations, and indexes are recomputed or accepted only through an independently checked certificate/proof or authenticated derived cache; they are never elevated into authored semantic truth unless they carry distinct choice. | Two independent routes reproduce or validate the same derived object; mutation is detected without turning the cache or certificate into the semantic owner. |
| X-03 | `Required` | **Outcome and failure separation.** Semantic Negative, unsupported question, malformed input, missing dependency, resource exhaustion, and checker failure remain distinct and cannot be cached or consumed interchangeably. | Exercise one case of each at a real boundary. Foundation envelope plus domain owners. |
| X-04 | `Required` | **Durable semantic closure.** A durable page depends only on durable owners or explicit inactive extension boundaries; temporary notes never supply a required type or law at cutover. | Delete or hide the notes tree and re-run link, symbol-owner, and clean-room reconstruction checks. Project governance. |
| X-05 | `Required` | **Executable inhabitance before selection.** No target contract is selected until at least one real positive inhabitant and its named negative mutations execute in an independent model, oracle twin, or dialect prototype. | Each selection names its concrete witness in the applicable stage plan; later families must be materially different, not renamed synthetic schedules. Project method. |
| X-06 | `Required` | **Independent gate evidence.** A closing gate freezes inputs, distinguishes author and falsifier roles, permits a failed artifact, and records exact reopening conditions. | External validator can rebut an adjudication without accepting its proposed repair. Project method. |
| X-07 | `Required` | **One semantic owner after convergence.** Temporary targets, matrices, and narratives are absorbed or deleted; shared mechanisms are defined once without moving domain meaning into Foundation. | Shadow-definition scan, manifest closure, and cold-reader reconstruction after R5. Project governance. |

## 7. Open scope and representation decisions

These are not invariants and must not be resolved by whichever patch is
shortest.

| Decision | Alternatives that remain live | Required pressure before selection |
|---|---|---|
| Statement scope | Initial/global only; dynamic/adaptive introduction; both with explicit scopes | FRI grinding plus Sigma/sequential-composition witnesses |
| Meaning of `FiatShamir` | Structurally strong only; generic transcript-derived interpretation plus a separate strong-FS result | Restate current negative boundaries and instantiate one theorem |
| Fresh/FS Core relationship | Identical admitted Core; related distinct cores with a checked map; bisimulation or projection relation | FRI grinding witness with equivalent Fresh/FS observations and discriminating negative mutations |
| Oracle layer | Finite ordinary messages; first-class oracle publication/query; separate IOR subject linked to Core | Sumcheck/FRI/ArkLib correspondence and BCS mutation |
| Repetition and recursion | Finite unrolling; bounded recurrence; verifier-descent/import subject; dynamic schedule | Grinding, parallel repetition, recursive imported verification |
| Regime representation | Allocated opaque roots; content-addressed descriptors; per-domain semantic modules | Independent implementation and regime-rotation experiment |
| Algorithm representation | Shared strongly normalizing calculus; per-kind DSLs; content-addressed contract-only v0 | Real codec, sampler, bridge, and grounding implementations |
| Guard representation | Bounded ROBDD; canonical syntax plus certificates; derived ROBDD witness | Real/adversarial node and work measurements |
| Schedule identity | Total schedule in Core identity; partial-order semantics with a canonical execution policy; explicit scheduler subject | Two linear extensions with equal and observably different behavior |
| MLIR/canonical split | MLIR semantic carrier; MLIR workbench over neutral bytes; hybrid token-plus-canonical reference | Round-trip, invalid-structure, rewrite, and identity tests |
| Composition context | Full lineage in challenges; smaller semantic domain ID; provenance excluded | Concrete replay threat or interoperability counterexample |
| Plan closure | Rename structural coverage; split open/closed Plan; require total supplier disposition | FRI plan with real holes and downstream closure |
| Interface collections | Keyed canonical maps/sets; explicitly observable order | Permutation and stable-reference tests |
| Correspondence regime | Static versioned specification constant; first-class admitted subject | Cold replay and authority-cycle analysis |
| Result semantics | Structural reference only; directional acceptance relation; full checked equivalence where decidable | Real relation/Protocol pair and Analysis theorem boundary |

## 8. R1 gate

R1 is internally complete when every adjudicated finding maps to this ledger,
a rebuttal, or an explicit current-system finding, and the independent
validation brief has been issued. The first cold pass failed the gate and
required material corrections to this ledger; its outcome is recorded in
[validation-outcome.md](validation-outcome.md). No item here authorizes durable
rewrites. R2 begins only after a fresh follow-up falsifier validates the amended
record or its further material corrections are incorporated and rechecked.
