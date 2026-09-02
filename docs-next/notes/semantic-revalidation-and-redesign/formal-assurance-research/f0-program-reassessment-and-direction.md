# F0 Program Reassessment and Proposed Direction

> **Kind:** Temporary independent reassessment of the formal-assurance
> research program after F0-V2B2D1
> **State:** Assessment complete at reading and replay resolution; the
> proposed next step is a recommendation awaiting the design lane's decision
> **Authority:** None. This note changes no target semantics, profile
> identity, evaluator, Analysis judgment, or roadmap priority.
> **Observed:** 2026-09-03 at branch `docs/semantic-redesign`, HEAD
> `b70ee60`, clean worktree.
> **Method:** Reconstructed the program from its index and every package
> record, read the target text it repairs (`docs-next/pir/interactive-core.md`
> Sections 6.4, 7.2, 9--13, 15), reread the D1 runner, typed model, and cold
> model, replayed the D1 gate (42/42 frozen findings), validated the checks
> manifest (57 checks, six tiers), and compared the program against the
> parallel Fiat--Shamir assurance package on branch
> `codex/fs-assurance-pre-freeze` and the 2026-08-28 independent peer review.

## 1. Questions this note answers

The handoff asked five questions: what the central unresolved problem is,
which prior conclusions are robust and which are provisional, whether the
current decomposition is right, which alternative directions deserve serious
consideration, and which research step would provide the most information
next. Sections 3 through 7 answer them in that order. Section 2 records the
state the answers rest on.

## 2. State reconstruction

### 2.1 What exists

| Layer | Result | Evidence kind |
|---|---|---|
| F0 architecture pass | Q0--Q10 claim lattice; Candidates P/A/S/C/R at equal resolution; provisional A/S/C selection; staged F1/F2 entry contracts | paper analysis, primary-source ledger, one VCVio module build and axiom probe |
| F1-R0 | two-layer package class discriminates the F0 mutation set | 18 cases; Python and no-crate Rust checkers sharing no parser or canonical encoder |
| F1-R1A/R1B | exact target Interaction profile reconstructed; one finite Schnorr Core and Fresh Protocol admitted under the written ten-stage law | 10 and 27 cases; offline evaluator for one constructor fiber |
| F1-R1C0 | published profile lacks the promised view-schema catalog, nested body grammars, law bindings, and authority-envelope bodies | 13-case source audit; `CannotAnswer` |
| F0-V1, V2A, V2B0, V2B1 | in-place repair topology fits the publication mechanism; one generic Record/Variant/Sequence/Atom schema algebra; displays cannot be compiled verbatim; normalized six-view bodies validated on the R1B slice | 18, 40, 18, 63 findings |
| F0-V2B2A/B2B | 79-case constructor census; constructor-complete schemas with 302 inhabitants over 914 branch requirements | 44 and 65 findings |
| F0-V2B2C0/C1A | canonical-byte immutable owner admission; exact value codec | 22 and 22 findings |
| F0-V2B2C1B1--B5B2 | 21/21 constructor-isolation families project through typed and cold paths | 39, 44, 61, 69, 38, 58, 62 findings |
| F0-V2B2D1 | integrated static graph over five carriers; 14/14 node cases, 4/4 classes; four directed refusals; five owner-substitution refusals | 42 findings, replayed today |

Twenty executable packages carry this lane, about 49,500 lines of Python,
twenty entries in the `research-checkpoint` tier. All but the first F0 pass
were committed on 2026-09-02 between 07:24 and 23:12.

### 2.2 What is verified from the target text

The following are confirmed by reading `interactive-core.md`, not only by the
package records:

- Section 13.1 promises a closed `PIRViewSchemaCatalog`; the Interaction
  manifest publishes no such catalog kind. `PIRReference` appears as an atomic
  boundary with no definition. Section 13.2 bodies carry prose fields such as
  `exact producer edges` and `run_record_schema`. The R1C0 finding stands.
- Section 6.4 says every required check "has occurred and is true" at an
  active terminal while terminal selection is by guard alone; no rule connects
  the guard to the check result, and "accepting-path required reduction" has
  no field in `TerminalDecl`. The B5A semantic gap stands.
- Section 11 assigns `Publish(activity)` to an "Oracle publication output"
  and names a "public Query index" among sinks. For a `LogicalAccess`
  publication there is no output node, and the Query sink may be read as the
  index producer alone. The two D1 wording obligations stand. Since Section
  9.1 makes `LogicalAccessFixed` a public observation, D1's choice to place
  `Publish` on the publication effect node is the reading consistent with the
  rest of the page.

### 2.3 What the D1 evidence is, precisely

The D1 record is accurate but two properties deserve plain statement because
a reader can over-read "admits" and "independent".

The typed path recognizes exactly five Core bodies. `_scenario_for_domain`
re-encodes each fixture and matches the candidate's domain bytes against
them, and `_validate_integrated_shape` requires decoded equality with the
fixture. Admission therefore consists of profile, module, algorithm, and
contract closure authentication plus the graph law on known bodies. It is not
a general evaluator of the ten admission stages over arbitrary input, and the
record's phrase "five exact carriers only" should be read that literally.

The cold path shares more with the typed path than the word "independent"
suggests. Both load `evaluation/k1-executable-foundations/reference_model.py`
as separate module instances, so the constitutional datum encoder and decoder
are one implementation. Both compile the same `schema-source.json`. The cold
path decodes bytes that the typed path's fixtures encoded. What is genuinely
separate is the Core table parser, module and algorithm closure
reconstruction, graph derivation, class assignment, sink selection, and view
encoding. Dual-path agreement therefore excludes graph and projection
implementation errors; it does not exclude a shared K1 encoding defect or a
shared misreading of the target text. The only pair in this lane with a
separately implemented canonical encoder is F1-R0's Python and Rust checkers.
The publication evaluator's `independent.py` also reimplements the encoder,
but the D1 cold path does not use it.

### 2.4 Related work on this machine that the program does not cite

Branch `codex/fs-assurance-pre-freeze` (worktree `~/code/zkc-fs-assurance`,
commit `616405f`, 2026-09-01) holds a complete Fiat--Shamir assurance package
with its own ten-layer lattice L1--L10, an attack-to-obligation matrix, a
proposed reusable Analysis FS profile family, a Stage 4B entry contract, and
a 33-control executable instrument. It forked from `808ec2d` and was
fast-forwarded to `a1585b2`; it is not an ancestor of this branch. No file in
this lane, in `evaluation/`, or in `checks/` references it, and it does not
reference this lane. Both programs independently select an owner-separated
assurance chain and reject a kernel-style authority. Their lattices overlap
without coinciding: F0 has Q1 source reification and Q2 provider
correspondence, which the FS lattice lacks; the FS lattice has L2 Statement
correspondence and splits F0's Q5/Q6 into encoding, transition binding,
sampler, oracle-process, and source-property layers. Two proposed Analysis
families with overlapping slots now exist on two branches.

Two private lanes exist in detached worktrees: a causal QROM extraction
theory study (`~/code/qrom-causal-theory`, 2026-09-02) and a post-quantum
Analysis study (`~/code/zkc-pq`, 2026-08-31 to 2026-09-02). They are
consumers of the QROM variant of any assurance lattice and are not blockers
for this lane.

## 3. The central unresolved problem

The program began with the question of whether a formal subject really
corresponds to the zkc subject that produced it. It found that the source side
of that correspondence, the owner views a formal consumer would read, was not
independently determinate, and it has since spent every executable package
making the source side exact. The provider side has one theorem probe and no
correspondence attempt.

The central unresolved problem is therefore this: **no evidence yet exists
that any exact source object, however canonical, admits a provider
interpretation whose correspondence can be checked.** The A/S/C selection
survives only if two reversal conditions from the candidate matrix stay
false: that a theorem-relevant observation can always be selected through an
owner view, and that provider adapters need no shared universal calculus.
Nothing has tested either, because nothing has tried to build a provider term
from an admitted zkc subject. The six views carry graphs, coordinates, and
law references. A VCVio interpretation needs a step relation over
`CoreState`, the denotation of each check and guard algorithm as a function,
the challenge domain's sampling semantics, the relation predicate, and a map
from the eleven-way outcome partition into the provider's failure layer. The
views name these facts by declaration reference; they do not carry them. The
likely first provider-side finding is that the formal source closure is
larger than the six views and includes the exact-used semantic-module
declaration bodies and portable algorithm preimages. That finding decides what
F0-V2C must publish, so it should arrive before F0-V2C, not after a
sixteen-profile rotation.

A second problem sits beside it. B5A found a genuine hole in the Terminal law
and B5B1/B5B2 selected a repair that changes the Core grammar: it removes
`ClaimDisposition`, adds `required_applied_reductions`, and turns three
sequences into sets. Every Core with a terminal rotates. F0's own non-change
list says `InteractiveCore` fields and occurrence order need no change, and
the lane's authority line says it changes nothing. The repair is correct in
shape and is the strongest single finding of the lane, but it is a
main-design reopening under the v0 design program's Section 14 protocol, and
no reopening record exists. A side lane cannot carry it to publication.

## 4. Robust and provisional conclusions

| Conclusion | Standing | Why |
|---|---|---|
| Source admission, reification, provider correspondence, environment authentication, theorem truth, applicability, property, transition, and realization are separate judgments | robust | reached independently by F0, by the FS lane, and by the peer review's proposition/basis/validation/capability split; matches the current `docs/formalization.md` nonclaims |
| A formally verified verifier and an authored `covers` receipt do not establish subject correspondence | robust | both lanes; primary-source method comparison; the current receipt code checks environment facts only |
| A proof-assistant-native semantic center is not justified for v0 | robust at architecture resolution | rejected on authority, identity, and migration grounds by F0 and, for the IOR-shaped variant, by the peer review; still a named reversal option |
| The published Interaction profile does not determine the six views | robust | 13/13 audit and direct reading of Section 13 |
| The Terminal law has an unauthored guard/check entailment gap and an ownerless required-reduction phrase | robust as a finding | direct reading of Sections 6.4 and 10; B5A oracle counterexample |
| The two Section 11 wording ambiguities | robust | direct reading; D1's resolutions are consistent with Section 9.1 |
| The A/S/C composition | provisional | survived paper scenarios and source-side falsifiers only; no Q2 attempt |
| The generic schema algebra and normalized six-view bodies | provisional | one coherent candidate validated by dual-path agreement with a shared encoder and shared schema source; not yet read by any consumer |
| Complete-view-first issuance with partial closure deferred | provisional | a proof-ordering choice, adequately argued |
| Placing the Q1/Q2 family in Analysis | provisional | unexercised; the FS lane proposes a sibling family in the same owner |
| The Terminal repair body | provisional and identity-bearing | needs a main-lane decision; alternative of conjoining checks into selection was refused for a stated reason but not exercised |
| D1's structural FS eligibility on the integrated carrier | bounded evidence | five bodies; structural, not cryptographic |

## 5. Is the decomposition right

The vertical decomposition is right. Separating the claim lattice from the
owner map, the candidate matrix, the scenarios, and the entry contracts is
what let R1C0 stop at an absent premise instead of inventing one, and it is
what makes the Terminal finding legible.

The execution decomposition is one-sided. Since R1C0 the program has walked
depth-first down the source side: publication topology, schema algebra,
body audit, bounded grammar, census, complete schema, admission substrate,
codec, twenty-one isolation families, integrated graph, and next runtime
receipts, migration, read closure, package integration, live binding, and
only then any provider work. Every step was locally justified and each closed
a real gap, but the horizon before the first provider-side signal is now
seven gates long, and the entire source-side design could be wrong in a way
only the provider side can show.

Four smaller defects in the decomposition:

1. **D2 is defined twice.** The census inventory defines the
   `fresh-runtime-oracle-receipts` family as a schema obligation on
   `ExecutionView`: the completed-record description with every receipt
   branch and exact arity. The D1 handoff defines D2 as executing Fresh runs,
   producing receipts, and replaying them. These are different packages with
   different costs. K2's witness already executes and replays Fresh runs on a
   witness-local profile, so the second reading largely re-derives an
   operational semantics in zkc-internal form that a provider spike would
   need in provider-facing form.
2. **The lane has drifted from formal assurance into PIR specification.**
   Most of its output is owner-view grammar and a Core-grammar repair. That
   work is valuable and belongs to PIR, but it should be routed and reviewed
   as PIR work under the main lane, where the peer review has already asked
   for one generic owner-view mechanism and a consolidation pass. The generic
   algebra selected in F0-V2A answers that request; the twenty per-slice
   packages are the mass it warned about, and the lifecycle catalog already
   marks them for removal once the selected source is absorbed.
3. **Two assurance lattices exist on two branches.** Absorbing either into
   `docs-next/analysis/` before reconciling them would reproduce the drift the
   design program is trying to eliminate.
4. **Evidence independence is overstated by one word.** "Independent" in the
   B2C/B2D records means separately structured code over a shared encoder and
   shared schema source. That is a useful translation-validation boundary, and
   the records' non-claims are correct, but a reader should not equate it with
   the F1-R0 pair.

## 6. Alternatives that deserve serious consideration

| Direction | What it would establish | Main cost or risk |
|---|---|---|
| **A. Provider-observable audit first** (Section 7) | whether the six views plus Protocol and module closure are provider-adequate for one admitted subject; the exact list of missing observables, if any; a first test of two A/S/C reversal conditions | one package; no proof; Schnorr alone cannot exercise the shared-challenge discriminator |
| B. Migration first (F0-V2C) | unblocks R1C, R1D, and F1-I; publishes the Terminal repair | rotates the frozen candidate's sixteen-profile cone on a side lane's authority before the provider side is tested; a second rotation if A later finds a missing observable |
| C. D2 as indexed | closes B2D | ambiguous scope; overlaps K2's existing execution and replay; low provider information |
| D. Reconcile the two lattices and hand the Terminal finding to the main lane | one vocabulary before absorption; a proper reopening record | documentation only; needed regardless of A, B, or C |
| E. Family versus instance for applicability | how a family-typed VCVio or ArkLib theorem binds to an instance `CoreId`; the indexed-core-elaboration experiment already supplies a checked instance map | not first; belongs on the Q5 entry contract |

Option B is what the index proposes after D2. Option A is what the evidence
recommends, because it is the only option that can falsify the design before
the design is frozen into profile identities.

## 7. Proposed next step: F2-O0 provider-observable audit

The step mirrors R1C0 on the other side of the bridge: stop at the first
absent premise, name it exactly, and do not invent it.

**Subject.** The F1-R1B admitted finite Schnorr Core and Fresh Protocol under
the frozen Interaction profile, taken as exact bytes through the existing
cold decoder. The D1 integrated baseline is a stretch subject, not required.

**Provider.** VCVio at the revision pinned in `f0-source-ledger.md`. The
checkout at that revision with the built `Examples.Schnorr.SigmaProtocol`
module already exists on this machine under the F0 sources directory, with
Lean `v4.33.1`.

**Untrusted generator.** From the decoded Core and Protocol, emit two
artifacts: a Lean file that states one `OracleComp`-shaped interaction with
one construct per source occurrence, and a machine-readable ledger that maps
every emitted construct to exactly one source coordinate or to a typed
`NoSourceCoordinate(reason)` entry. The generator may read any bytes it likes;
its output carries no authority.

**Checks.**

1. The emitted file elaborates under the pinned toolchain and manifest; the
   reported axiom closure is recorded. This is a Q3-class environment fact
   only.
2. An independent Python checker, sharing no code with the generator, verifies
   that the ledger is total over the occurrence schedule and injective over
   source coordinates, and enumerates every `NoSourceCoordinate` entry with
   its reason. Those entries are the result: they name the observables a
   provider needs that no owner view carries.
3. Mutations: alias two equal-valued coordinates, drop the response producer,
   replace the Fresh challenge by a constant, omit the Reject terminal. Each
   must produce a named ledger failure, not merely a Lean error.

**Expected outcome classes.** `Affirmative/F2O0-A-OBSERVABLES-CLOSED` if
the six views plus the Protocol body suffice; otherwise
`CannotAnswer/F2O0-C-MISSING-OPERATIONAL-OBSERVABLE` carrying the exact list.
The prediction recorded here is the second class, with at least these
entries: the check algorithm's denotation, the challenge domain's sampling
law, and the relation predicate, all of which are reachable only through
semantic-module and Relations bodies that the six views reference but do not
contain. Either outcome is decisive for what F0-V2C publishes.

**Non-claims.** The package establishes no Q2 correspondence, no theorem
applicability, no property, no security result, and no target change. The
shared-challenge discriminator remains an F2-O1 obligation because Schnorr
cannot express it.

**Alongside it, before any migration:**

- one reconciliation table mapping Q0--Q10, L1--L10, and the current
  `docs/formalization.md` bridge chain, choosing one vocabulary for
  `docs-next/analysis/` absorption; and
- one reopening record for the Terminal contract under the v0 design program's
  Section 14 protocol, naming the affected conclusion, the B5A counterexample,
  the dependent profiles, and the decision gate. F0-V2C should carry the view
  grammar and the Terminal repair together, after that record exists and
  after F2-O0 reports.

D2 should then be scoped by F2-O0's result. If the provider needs an
operational trace object, D2 becomes the owner-side definition of that object
and is worth doing exactly once, in the provider-facing form. If it does not,
the census's schema-only reading of D2 suffices.

## 8. Disposition of the two D1 wording obligations

Both are owner-local wording fixes for F0-V2C and need no new mechanism:

- Section 11 should state that a `LogicalAccess` publication effect node uses
  `Publish(activity)`, so the fixation marker classifies as `PublicHistory`
  and cannot collapse into a static fact; and
- `PCSinks` should enumerate both the public Query activity and effect
  observation and the index producer, so two conforming implementations
  cannot serialize different sink sets.

## 9. Non-claims

This note is a reading of research records and one replayed gate. It proves
nothing about the target, the provider, or any theorem. It does not select a
wire format, authorize migration, change any profile, or reorder the main
lane. Its recommendation is a proposal for the design lane's decision.
