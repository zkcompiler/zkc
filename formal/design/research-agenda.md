# Formal research and external theorem agenda

This agenda records required proof work, unsettled design questions and optional
research separately; it does not make every promising theorem a prerequisite.
Current capability is recorded in [support](../SUPPORT.md).

Section 1 records the required questions and their accepted scoped answers.
They are implemented through maintained source, interpretation, endpoint,
fixed-object/checking and ordinary Sumcheck clients. Proposed stronger
extensions in Sections 3–4 are not claims of completed proofs. A new wrapper or
name around an existing theorem is not a new research result.

A future value-sensitive analysis extension has a concrete task:
produce branch facts beyond the current value-insensitive phase summaries, with
a sound transfer theorem and an invalid-guard control.

The complete-zkVM target needs a bounded machine execution contract, adequacy of
distinct encodings of that same contract, and evaluation-claim, memory/lookup and
AIR/FRI compositions. Protocol experiments and MLIR design inform each other
before the relevant dialect APIs freeze.

The [cubic example](../Examples/OpeningReduction/README.md) adds arbitrary-round
virtual-product execution, explicit opening obligations and a same-experiment
terminal-error theorem. Remaining work is concrete: a second memory-log encoding of the same machine,
field/limb adequacy, a real opening-proof/provider experiment and retained MLIR
representations. Avoid maintaining two common table APIs merely because both
experiments independently defined one; consolidate when the next client fixes
the needed layout and terminal distinctions.

## 1. Required semantic connections

### Interpretation and construction

**Question.** Can one actual structured round source support distinct execution
constructions while retaining its source, phase and observation obligations?

Promote the existing interpretation composition/fusion laws. For a translation
`T` and meanings `I` and `J`, establish the appropriate instance of
`denote_J(T p) ~ denote_I(p)` under explicit operation laws. Here `~` names the
chosen complete outcome/state/event relation, not an unspecified equality.
Keep this logical lowering relation distinct from a security reduction between
different challenge experiments.

Instantiate Fresh and one canonical framed FS interpretation with independently
specified reference executions. The FS state includes statement/context,
ordered messages, challenge locations, encoding/domain separation and actual
oracle state. An operation may elaborate to several lower-level operations.
Prove phase, return and public operation bounds for the resulting process;
retain malformed input, rejection and exhausted-resource outcomes.

**Theory used:** algebraic effects and models satisfying operation equations;
interpreter composition as in Interaction Trees; indexed syntax and substitution.
The ITree paper motivates the method, not a claim that zkc has its coinductive
semantics. [1, 2]

**Exit:** one source, two actual constructions, source/reference correspondence
and consumed admission laws. A generic FS security theorem is not this exit.

### Local endpoint adequacy

**Question.** Does the supplied role implementation use only its permitted
information, rather than merely fit a globally legal schedule?

Define allowed view and related private memory for each role. Relate actual
elaboration or decisions under two bindings with equal allowed views and
related local memory. Deterministic actions must be related; randomized actions
need a specified coupling or distribution relation under their actual random
state. Quantify over changes in hidden inputs, including captured values.

Prove this law for two roles of the same round fragment and connect their
composition to the global driver under a specified delivery discipline. Invalid
hidden captures and future challenges must invalidate the premises. Distinguish
local implementability from global conformance, cryptographic noninterference
and distributed deadlock freedom.

**Theory used:** choreography projection/session types, relational noninterference
and logical relations. A full projection algorithm is not necessary for supplied
endpoints. The session-projection literature explains why global syntax alone
does not establish realizability. [3]

**Exit:** a maintained locality contract, actual two-role proof and a meaningful
counterexample; no general asynchronous network semantics is promised.

### Logical objects and law-restricted transformations

**Question.** Can a substantive algorithm change preserve one fixed object and
its complete source-visible behavior under checkable requirements?

For a fixed binding `b`, define `object(b)` before adaptive queries. For each
permitted query sequence, prove recomputation and materialization answer for
that same object. In particular, do not use
`for every query, there exists some object fitting its answer` as fixation.
Keep commitment binding separate from logical object identity.

Choose typed field-valued factors with ordered variables and actual caller
operands. Join forward fact soundness, backward demand, dependency-sensitive
preparation and outcome-specific frame laws to an actual transformed source.
Allow internal caches to differ under a relation while preserving the declared
observable result, guards and failure behavior. Explain any observation that
permits an implementation difference; do not erase a logical request merely
because its computation was cached.

Extend source-relative checking to accept a finite rule derivation under a
specific lawful interpretation and relation. The direct equality checker stays
valid as a special case. Negative cases cover missing algebra laws, stale
versions, wrong variable order, moved guards and failed-call mutation.

**Theory used:** abstract interpretation, semantic frames, relational program
logic, data refinement and translation validation. A Galois connection is useful
where a best abstraction is claimed; a proved concretization/transfer condition
can suffice for a deliberately incomplete analysis. [4, 5]

**Exit:** a substantive checked Lean source change plus one contrasting existing
Boolean/view or correlated-service client using the shared law. No native pass
or physical buffer proof is required at this stage.

### Probability, resources and property transport

**Question.** Do the maintained state and observation abstractions suffice for
the actual security experiment and allowed adversarial behavior?

Preserve existing joint initialization, persistent state, conditional mass and
correlated setup results during migration. A sample's marginal distribution
does not justify independent reuse. A stopped local attempt may leave consumed
resources for its enclosing controller; an outer stop has no resumed suffix.
Migration must retain the exact observer, event order and conditioning event.

For each security adapter, identify a map from every admitted target adversary
to an admitted source adversary, respecting its information and query bounds.
If related experiments have corresponding bad events, prove their probability
relation. For an approximate simulation, a typical target is
`Pr[bad_target] ≤ Pr[bad_source] + δ`, with `δ` supplied by a stated coupling or
event-distance bound. Equality of a single honest run does not supply this map.
Call-count bounds do not by themselves supply oracle-query or computation bounds.

**Theory used:** relational probability/couplings, game-based reductions,
resource-sensitive state reasoning and contextual observations. Use VCVio and
Mathlib at the optional/property boundaries; keep their types out of the small
execution foundation. Do not introduce a universal probabilistic logic merely
to rename existing sufficient lemmas.

**Exit:** preserved existing correlation/disclosure consumers and an explicit
property-transfer theorem for the selected actual source transformation.
Broader approximate composition is pursued only if this instance needs it.

### Source-bound Sumcheck companion

**Question.** Does the whole actual source prove the intended statement, and does
its selected transformation preserve the relevant property?

Retain the [selected scope](../../docs/roadmap.md#4-the-security-companion):
a public round count, finite field, fixed polynomial of per-variable degree at
most two, claimed Boolean sum, actual messages and terminal evaluation. Prove
ordinary completeness and soundness against the specified arbitrary provers.
Derive the applicable accumulated error from conditional round bounds; expose
field-size and sampling premises rather than substituting a tiny-field test.

Connect a meaningful changed source/verifier to those same definitions. A
prover-only rewrite has a different obligation from a verifier rewrite. Use
existing scalar root bounds and ArkLib types where they fit. Missing stronger
knowledge-soundness results must not be silently assumed to prove ordinary
soundness; prove the scoped result locally if needed.

**Exit:** complete parameterized source-to-terminal theorem plus transformation
transport, audited without proof holes. Full ZK, extraction, FS soundness and
native code correctness remain different claims.

The scoped ordinary companion is now implemented in
[Sumcheck](../Zkc/Protocols/Sumcheck/Security.lean) and its
[checked evaluation integration](../Zkc/Protocols/Sumcheck/Optimization.lean).
The proof follows the standard conditional-round argument [10]: a false boundary
sum makes the difference polynomial nonzero; Mathlib bounds its roots by two;
independent product-tape averaging accumulates the error. The pointwise proof
quantifies over arbitrary adaptive messages. It neither assumes honest messages
nor uses ArkLib's admitted stronger knowledge results. `UniformTape.average_eq_sum`
identifies the recursive average with a normalized sum over complete tapes.

The residual polynomial is a proof device. The typed verifier retains the original
polynomial and evaluates it once at its complete delivered point. Thus proving
soundness by restriction does not prescribe materializing residual coefficients
in the verifier implementation. The existing factor materialization proof and
this protocol proof share the fixed polynomial definition without forcing the
same operational algorithm. General PMF/approximate couplings are unnecessary
for this exact finite experiment; they remain relevant to later distributions
and reductions. The completed source/endpoint connections and their scoped
review evidence are recorded in [support](../SUPPORT.md).

## 2. Consolidation obligations

| Area | What to check explicitly | Required disposition |
|---|---|---|
| Dependent/indexed source | Scope, substitutions, actual captures, finite encodings, elaboration uniqueness | Preserve constructor laws and connect needed domain operations |
| Specialization and disclosure | Public parameters versus private inputs; joint observation of selected code, evidence, publication and protocol history | Preserve the stated disclosure policy; separate observations cannot justify a joint privacy claim |
| Modules and state | Allocation identity, aliases, read/write footprints, preparation validity versus current readiness | Existing laws migrate with actual consumers; missing concrete premises stay visible |
| Relations and continuation | Statement/witness relation, residual, terminal acceptance, source-bound authorization and consumed target | Preserve both successful and failed-arm behavior; do not infer completeness from soundness |
| Realization | Heterogeneous logical values, final state, errors, observers and progress assumptions | Logical contracts established; differential validation with each native slice; optional Rust/backend proofs |
| Evidence and checking | Actual source/candidate, context, law suppliers, declaration audit coverage | No unchecked caller assertion is promoted to a proof; optional namespaces get their own audits |
| Packaging | Semantic dependency direction, meaningful names, external package isolation | No active Compat or numbered API; no build/test/doc dependency on retired scratch files |

A theory may be examined and deliberately not adopted; a capability is not
required to expose every theory it rests on.

## 3. External libraries and theorem boundaries

The installed pins are ArkLib `3f3f045dd295834c262bd6f0d9dfdfee07cc8e76`
and VCVio `7607103730459b127e2218fb36f5f13c2d65c038` on Lean 4.33.1.
These are assessments of selected declarations at those pins, not upstream HEAD
or whole-project certification.

| Selected external surface | Observed status | Action and ownership |
|---|---|---|
| ArkLib `OracleReduction/FiatShamir/Basic.lean` transformation definitions | Actual prover/verifier/reduction and statement/message-dependent oracle queries | Reuse in an optional adapter; zkc proves its own source, encoding, result/failure and query correspondence |
| Same file, `fiatShamir_completeness` | Proof ends in `sorry` | Audit the exact proposition before adopting it; prove a needed scoped instance locally or retain an explicit missing-proof parameter |
| Same file, state-restoration (knowledge) soundness to FS | TODO rather than a proved transfer theorem | Separate upstream/general research task; specify adversary, oracle, reduction and quantitative bound before committing an adapter |
| ArkLib duplex-sponge construction/security files | Selected state operations and security development incomplete | Compare construction contracts now; do not claim duplex security or require its full completion for this baseline |
| VCVio `FiatShamir/Sigma/Security.lean`: `euf_cma_to_nma`, `euf_nma_bound`, `euf_cma_bound` | Fresh audit of installed declarations reaches only standard Lean axioms | Available for a matching Sigma-signature application; first discharge source adequacy, special soundness, HVZK/predictability and query-bound premises |
| VCVio `FiatShamir/WithAbort/Security.lean` | Placeholder proof and explicit warning about invalid signed-error parameters; additional probabilistic premises need review | Do not freeze the present statement as an interface. Repair the theorem design before using it; upstream is the natural home for a general result |
| ArkLib Sumcheck security dependencies | Stronger selected single-round knowledge statements contain admissions | Inspect the exact dependency cone; reuse sound definitions/math and prove the required ordinary scoped result without those admissions |

VCVio's cited Sigma result concerns FS **signature unforgeability**, not arbitrary
multi-round SNARK soundness, duplex instantiation or QROM. ArkLib's oracle
reductions provide a useful protocol-specific model, not an automatic embedding
of every zkc interaction. [6, 7]

For every imported claim, retain this small record: exact pin and declaration,
statement and quantified experiment, transitive axioms, adapter theorem,
premise producers, scope and update trigger. Distinguish:

- A cryptographic assumption such as a named hardness premise.
- A theorem whose mathematical proof is missing.
- A proved theorem whose hypotheses zkc has not discharged.
- Trusted native realization of a proved logical contract.

These must not share an undifferentiated “trusted” status. A conditional Lean
theorem can take `externalLaw : RequiredLaw` as an explicit proof parameter.
Without a proof of `RequiredLaw`, there is no closed instantiation of the final
security claim. Do not use a global axiom or `sorry` to manufacture that proof.
Lean's transitive axiom inspection supports this distinction. [8]

For a small necessary mathematical bridge, prove it in the optional integration
and consider later upstreaming. For a large general crypto result, track it
separately and prefer upstream reuse. A source/observation/encoding mismatch in
zkc remains zkc's responsibility. An upstream update triggers an exact consumer
re-audit, not automatic promotion of all pending claims.

## 4. Larger research opportunities

These questions are worth retaining without making them completion conditions.
Each needs a literature comparison before any novelty claim.

| Question / possible result | Why it matters | First decisive study and boundary |
|---|---|---|
| Compositional security transport through lawful protocol interpretations | Reuse security arguments across source transformations and staged constructions | Prove one actual strategy/observer/query-preserving adapter, then compose two. Compare with probabilistic relational logics and game reductions; operational fusion alone is insufficient |
| A verified FS construction interface spanning canonical framing and duplex state | Separate protocol-local reasoning from transcript implementation and encoding | State exact lazy-oracle/canonical-framing correspondence first. Compare query topology with duplex and existing indifferentiability reductions; do not infer cryptographic equivalence from matching honest transcripts |
| Security-aware demand and preparation analysis | Optimize shared computation while preserving correlated randomness and joint disclosure | Reuse one analysis on field factors and a correlated service; produce a precise no-reuse counterexample. A generic theorem or a demonstrated unavoidable distinction is the result |
| Automatic locality checking or endpoint projection | Detect protocol descriptions that require unavailable information before compilation | Construct a finite source fragment with a sound decision procedure and an unprojectable example; decide later whether completeness, asynchronous queues or richer session types are worth the cost |
| Costed refinement and proof-directed algorithm search | Spend compilation time searching representation/algorithm alternatives while checking results cheaply | Prove cost recurrences for recomputation/materialization and validate a real choice. E-graphs or solvers may propose candidates; soundness and profitability are separate |
| Retry and partial-delivery probability semantics | Cover abort protocols and stateful setup without resetting consumed correlation | Instantiate the existing finite-prefix controller and conditional mass laws with an actual producer, sampler and publication contract. Unbounded expected-time, almost-sure termination and infinite observations still need additional probability semantics |
| Cross-library protocol adequacy | Connect reusable zkc source meanings to ArkLib/VCVio without redoing every protocol proof | Derive a nontrivial parameterized adapter, including hostile inputs and terminal behavior. A finite matching table alone is insufficient |

Additional follow-ups are identified but not required work:

- [Invocation-selected families](../../docs/spec/profiles/source/families.md)
  now have actual-ingress and role-knowledge contracts, plus compact counted
  Lean templates. Native runtime-symbolic counts require coordinated carrier
  admission, capacity checks and exact provenance. Broader variable-port or
  variable-topology templates need their own projection/instantiation laws;
  later distributed choices still need delivery, merging or proved segmentation.

- A concrete controller probability proof should use `Iteration.evaluateM` (or
  an explicitly equivalent finite experiment), retain the reached joint state,
  and derive the pending-mass recurrence before applying `retry_tail`. The
  persistent-bit countermodel rules out replacing this with a marginal retry
  rate. A projected state used repeatedly needs a justified quotient transition;
  one-step pushforward is insufficient. A compiler-facing family consumer also
  supplies actual post-ingress phase/resource readiness, stored-source binding,
  and permitted local selectors. `SelectsReady` and `selected_ready` now provide
  the domain-wide postcondition/admission bridge, and `run_proc` exposes finite
  ingress to existing sequencing laws; the adapter still proves their premises
  for its actual resources and transport. These are concrete consumer obligations, not
  reasons to add another universal admission framework.

- A compact CFG analysis certificate should handle distinct path facts without
  copying continuations exponentially. The current equal-transfer sharing law
  removes needless duplication but is not that general complexity result.
- A two-path Merkle client should bind both roots/coordinates and inconsistent
  redundant openings before testing shared-node preparation. The current
  single-path source/fold connection supplies its algorithmic starting point.
- A complete MPC-view protocol needs actual view construction, selected opening,
  challenge-dependent disclosure and its terminal experiment. Historical family
  studies and correlated-service laws do not supply that connection automatically.
- A recurrence-security application should connect each delivered residual
  instance to the final relation. The inactive bounded-loop client establishes
  control/execution behavior, not recursive-proof soundness.

Full separation-logic machinery, UC-style contextual security, coinductive
interaction, QROM, recursive proof composition and verified native toolchains
remain candidates. None has been exhaustively researched or implemented here.
Revisit one when a concrete claim cannot be expressed or a required proof fails
under the present model. Generic placeholders are not evidence of coverage.

## 5. Stopping

Differential testing supplies practical Lean to MLIR and Rust correspondence, as
the [assurance policy](../../docs/assurance.md#6-implementation-correspondence-policy)
states. A missing native proof does not reopen the finite semantic foundation or
block native delivery. A discovered mismatch requires identifying whether the
source contract, logical reference, implementation or test relation needs repair.

Section 1 plus the preservation in Section 2 is the required work. Section 3
supplies external evidence and pending stronger claims; Section 4 is an optional
backlog. An optional item is promoted only with the affected capability, missing
law, minimal experiment and expected deliverable identified.

A counterexample can justify changing a definition, strengthening a hypothesis,
or narrowing an unsupported claim. It must not be hidden as a rename. Once a
required statement, actual client, premise producers and negative cases are
closed, that unit stays closed without new evidence.

## References

1. Gordon D. Plotkin and Matija Pretnar. [Handling Algebraic Effects](https://homepages.inf.ed.ac.uk/gdp/publications/handling-algebraic-effects.pdf). LMCS 9(4:23), 2013, 1–36. Models satisfying equations and handler correctness.
2. Li-yao Xia et al. [Interaction Trees: Representing Recursive and Impure Programs in Coq](https://www.cis.upenn.edu/~stevez/papers/XZHH%2B20.pdf). PACMPL 4(POPL), Article 51, 2020, 32 pages. Interpretation and compiler-correctness methodology; a richer coinductive setting than the selected core.
3. Elaine Li, Felix Stutz, Thomas Wies and Damien Zufferey. [Complete Multiparty Session Type Projection with Automata](https://cs.nyu.edu/wies/publ/cav23_mst.pdf). CAV 2023, LNCS 13966, 350–373. Use the authors' corrected version; no PSPACE-hardness claim is relied upon.
4. Nick Benton. [Simple Relational Correctness Proofs for Static Analyses and Program Transformations](https://nickbenton.name/correctnesspopl2004.pdf). POPL 2004, 14–25. Relating analyses to actual transformation correctness.
5. Patrick Cousot and Radhia Cousot. [Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs by Construction or Approximation of Fixpoints](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml). POPL 1977, 238–252.
6. ArkLib. [Oracle reductions blueprint](https://verified-zkevm.github.io/ArkLib/blueprint/chap-oracle_reductions.html) and [pinned FS source](https://github.com/Verified-zkEVM/ArkLib/blob/3f3f045dd295834c262bd6f0d9dfdfee07cc8e76/ArkLib/OracleReduction/FiatShamir/Basic.lean). The live blueprint aids interpretation; the pinned local source owns this audit's findings.
7. VCVio. [Pinned Sigma security source](https://github.com/Verified-zkEVM/VCVio/blob/7607103730459b127e2218fb36f5f13c2d65c038/VCVio/CryptoFoundations/FiatShamir/Sigma/Security.lean) and [with-abort source](https://github.com/Verified-zkEVM/VCVio/blob/7607103730459b127e2218fb36f5f13c2d65c038/VCVio/CryptoFoundations/FiatShamir/WithAbort/Security.lean). Findings above use the installed exact-pin source and selected compiled declarations.
8. Lean Language Reference. [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/), accessed 2026-09-09. Statement meaning, transitive axioms and independent proof rechecking are distinct validation questions.
9. Merlin. [Transcript operations](https://merlin.cool/transcript/ops.html). Concrete framing/operation reference for construction review; documentation is not a cryptographic proof of a zkc adapter.

10. Justin Thaler. [Interactive proofs, polynomial extensions and Sumcheck lecture notes](https://people.cs.georgetown.edu/jthaler/extensionsandsumcheck.pdf), Sections 2–3, accessed 2026-09-10. Standard ordinary-soundness argument and the distinction between per-variable and total degree.
