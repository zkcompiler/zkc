# F0-V2C Decision Inputs: Formal Source Closure and the Open Sub-Decisions

> **Kind:** Temporary main-lane synthesis of the F2-O0, M0, Q3-A, and
> reconciliation results into the decisions F0-V2C must take
> **State:** Decided. On 2026-09-03 the user took all eight decisions in
> Section 10 as recommended. The migration may now be drafted as exact
> owner text on the research branch under those decisions; pushing and
> pull-request landing remain the user's gates
> **Authority:** None. This note changes no owner page, profile, identity,
> evaluator, or judgment.
> **Inputs:** `f2o0-provider-observable-audit.md`,
> `m0-mechanized-kernel-feasibility.md`,
> `q3a-formalization-receipt-assurance-audit.md`,
> `f0-assurance-lattice-reconciliation.md`,
> `../terminal-contract-reopening-2026-09-03.md`, and the candidate matrix's
> reversal conditions in `f0-candidate-matrix.md` Section 11.

## 1. What changed since the architecture pass

The A/S/C selection rested on the assumption that every theorem-relevant
observation can be selected through an owner view. F2-O0 tested that on the
smallest admitted subject and found it false for four operational
observables when "owner view" means the six normalized views alone: the
Check's denotation, the terminal guard's denotation, the Fresh challenge's
sampling law, and the map from the Core's verdict and run-outcome partition
into a provider's result type. The views carry algorithm identities, nominal
law references, and verdict cases; they do not carry functions, distributions,
or an outcome lattice.

This is not a defect in the views. The views were specified to add no fact
absent from the admitted owner body, and the missing facts are not Core facts.
Two live in Foundation (portable-algorithm denotation under the evaluation
contract), one is disclaimed by PIR on purpose (distribution truth, Sections
5.2 and 12.1 of `interactive-core.md`), and one has never had an owner (the
outcome map). The reversal condition therefore fires against the *reading*
"package = views", and is repaired by a different closure definition rather
than by a different architecture.

## 2. The formal source closure

**Proposed definition.** The formal source closure of an admitted Fresh or FS
Protocol is:

1. the exact Protocol and Core bodies and their authenticated dependency
   closure as Core admission already authenticates them: the exact-used
   semantic-module declarations, the portable-algorithm preimages named by
   Checks, guards, derived values, and module effects, and their evaluation
   contracts;
2. the six normalized owner views, which select and coordinate those facts;
3. one Analysis-owned law binding for each nominal `pir.public-coin-law` and
   `pir.challenge-domain` declaration the subject uses (Section 4); and
4. the owner-defined abstract outcome partition carried by the ExecutionView
   (Section 5).

Item 1 is already what the D1 cold path authenticates before it projects
anything, so the definition adds no new authority; it makes explicit that a
consumer of the views must also hold the preimages the views name. Item 2 is
unchanged. Items 3 and 4 are the two genuine additions and are decided below.

**Consequence for Q1 and Q2.** A portable source package carries items 1, 2,
and 4 and the *coordinates* of item 3; the Analysis binding itself is a Q5
premise, not package content. A provider interpretation needs, beyond the
package, a denotation of the K1 term calculus into the provider's functions
with its own checked correspondence. M0 has transcribed the K1 datum encoding;
the term calculus is the natural M2, and until it exists the Check and guard
denotations are trusted-adapter residuals in any Q2 result.

## 3. Sub-decision A: algorithm denotations

| Option | Description | Cost | Disposition |
|---|---|---|---|
| A1 | inline algorithm bodies into the views | duplicates Foundation preimages inside PIR bodies; view sizes explode; violates the rule that a view adds no fact absent from the owner body | reject |
| A2 | views keep identities; the closure definition (Section 2 item 1) obliges every consumer to hold the authenticated preimages; the package carries them | no owner change beyond one sentence in Section 13; consistent with D1's cold path today | **recommend** |
| A3 | a new "algorithm read" view kind | a seventh view whose only content is Foundation data; a second owner for Foundation facts | reject |

Wording obligation for V2C under A2: Section 13.1's closure law says a leaf
"closes to ... referenced semantic dependency"; it should state that a
referenced algorithm or module identity closes to its authenticated preimage
in the Core's dependency closure, which the reader must hold, and that the
view itself never carries the preimage.

## 4. Sub-decision B: the sampling law

| Option | Description | Cost | Disposition |
|---|---|---|---|
| B1 | give `pir.public-coin-law` declarations a denotational body in PIR | contradicts Sections 5.2 and 12.1, which make distribution truth an Analysis or evidence obligation; would let a Core assert a distribution it cannot check | reject |
| B2 | keep the nominal declaration as the exact hook; Analysis binds it to a distribution model as a named Q5 premise, retained in every Q6 hypothesis set that uses it | no PIR change; the premise is visible in the judgment; matches how the provider's completeness theorem fixes a uniform draw as a hypothesis | **recommend** |
| B3 | treat the law as an opaque atom and let each provider theorem's hypothesis carry it silently | the assumption disappears from zkc's own record | reject |

Under B2 the F2-P applicability question binds three things by name: the
`pir.public-coin-law` coordinate, the Analysis distribution model, and the
provider's sampling hypothesis. The reconciliation note already places this
in the Fiat--Shamir family's premise catalog as the sampler premise; the Fresh
case is its trivial instance.

## 5. Sub-decision C: the outcome partition

| Option | Description | Cost | Disposition |
|---|---|---|---|
| C1 | PIR defines one abstract outcome partition in the ExecutionView: `Accepted`, `Rejected`, `Aborted`, `InterpretationFailed(profile schema)`, `StrategyStopped`, and `OperationalNoncompletion` outside the record; provider-specific carriers (a Boolean, an option layer) are per-provider maps in Analysis over that partition | one owner-defined sum, provider-neutral; every failure lane visible | **recommend** |
| C2 | per-provider maps only, defined in Analysis | each provider invents its own reading of `Abort` and noncompletion; the F2-O entry contract's requirement that every failure branch be in the relation cannot be checked once | reject |
| C3 | collapse to accept/reject in PIR | erases the distinctions the outcome partition exists to keep | reject |

C1 is the input the D2 lane was asked to realize: the completed-record schema
carries the record sum, and the abstract partition is the ExecutionView's
statement of what a run can end as. The Terminal repair makes the accept case
derivable from the required Check, so a provider's `verify` follows from the
Check under C1 plus Block 1.

## 6. What V2C publishes, on the current evidence

1. the Terminal contract repair (Block 1) and its OIR consequence (Block 4);
2. the normalized six-view grammar and the `pir.static-view-schema` catalog
   (Block 2);
3. the closure sentence of Section 3 and the outcome partition of Section 5,
   both as Section 13 text and one ExecutionView field;
4. the five wording fixes: LogicalAccess publication effect uses
   `Publish(activity)`; `PCSinks` enumerates the public Query activity/effect
   observation and the index producer; the transfer paragraph names the node
   that carries each transfer; "first failed dependency" is fixed as lattice
   priority or positional order (D1 and M0 agree on the five carriers, so
   either is consistent with the goldens; lattice priority is what the
   implementations do); and the Foundation byte bound is confirmed as
   "reaching a bound is allowed", with the K1 model moved to the prose.

The second-round lanes filled the slots as follows.

- **gates-green.** K3-E is green again: the finite Analysis subject
  authenticates through K1's build-once/check-many prepared-context seam and
  the recorded profile counts were stale; the query-plan instrument now
  propagates site-argument answer taint and checks a path-to-occurrence map, so
  the two confirmed defects refuse with regression fixtures. No owner page
  changed. The precondition "all gates green" holds at the integrated head.
- **M1.** Edge construction from an admitted Core reproduces all five D1 graph
  tables in Lean; decoder canonicity and class-fold order independence are
  proved on `propext` and `Quot.sound`; the K1 byte bound is now the prose
  reading in the Python model with an exact-bound oracle case. Five Section 11
  wording items remain: three transfer coordinates, the public-Query sink
  coordinates, and Challenge failure precedence. Item 4 above absorbs them.
- **F2-O1.** On the integrated carrier the discriminating mutations all
  refuse from Challenge facts the views do carry, so the shared-challenge and
  ordering discipline survives the provider side. The 56 operational gaps
  split into two kinds. Most are *source-boundary* gaps: D1 issues only the
  `PublicCoinView` for the integrated carrier, so the other five views were
  never derived for it; that is an evidence obligation on the migration's
  fixtures, not a semantic gap. The rest extend F2-O0's classes: module-effect
  denotation for the three decision classes, Oracle carrier representation for
  the three modes, and the same distribution, denotation, and outcome-map gaps.
  Module denotations fall under sub-decision A (the authenticated module
  declaration bodies are part of the closure); Oracle carriers are a Q2 design
  question (a provider must model a confidential carrier as a typed unknown
  behind a handler), not a V2C item.
- **D2.** The Fresh completed-record schema is representable and reconstructs
  through two paths for all five carriers, with zero runs. It leaves five
  owner-text choices, all of which belong in this migration: where the
  LogicalAccess fixation marker lives in the `Published` receipt; whether
  occurrence receipts run through the active terminal; the exact body of
  `PartialRunRecord`; whether `StrategyStopped` is a lane of the record sum or
  stays diagnostic; and the field name `run_record_schema`. Recommendation:
  take D2's candidate readings for the first three, keep `StrategyStopped`
  outside `CompletedProtocolRecord` as the page says while adding it as a lane
  of the *abstract outcome partition* of Section 5 (so providers see it
  without PIR calling it a completed record), and keep the target's field name.
- **F0-V3.** The eight Fiat--Shamir family view bodies are 37 exact, 40 prose,
  and 20 undefined fields; a bounded normalized grammar compiles and derives
  from the K2 and duplex witnesses; eleven owner obligations are named.
  Recommendation: the FS profiles are inside the freeze scope, so their view
  catalogs enter the same migration, authored from F0-V3's candidate under the
  same generic algebra, rather than being excluded from the frozen view
  surface; the alternative, freezing FS construction semantics while leaving
  its views declared but indeterminate, would repeat the R1C0 defect for the
  family that motivates the whole assurance program.

## 7. Two decisions that are not V2C

**Property premises.** The relation predicate, witness type, Prover private
state, and honest strategy are Relations and Plan bindings, not view content.
They are assigned to the Relations-and-Plan binding lane and enter F1-R1D,
not the migration.

**The identity pin.** Profile identity is today computed over the bytes of
marked prose fragments. M0 shows the kernel can be transcribed into formal
definitions at low cost, which reopens whether identity should be pinned to
formal text. Options at equal resolution:

| Option | Description | Disposition |
|---|---|---|
| P1 | pin identity to formal definitions before V2C | blocks the migration on M1 and a term-calculus transcription; one rotation but a long delay |
| P2 | keep prose-fragment identity for V2C; transcribe the frozen kernel afterwards under the rule that a transcription discrepancy is a named reopening; decide the pin when the transcription covers admission, execution, and FS construction | one rotation now, a possible second later, explicitly budgeted | **recommend** |
| P3 | never pin to formal text; treat transcriptions as conformance evidence only | leaves the drift class that R1C0, B5A, D1, and M0 found in place | reject |

P2 keeps the direction without holding the freeze hostage to mechanization.

## 8. Freeze scope

The freeze claim covers a dependency-closed set of activated contracts, not a
list of pages. A contract is activated when a frozen consumer reads it: the
Foundation values and identity; the Interaction Core, its admission, PCGraph,
Fresh execution and replay, and the static views a frozen Analysis question
selects; the invocation-issued public setup view, whose entries are the
invocation-determined bindings of Section 13.4 of the Interaction page and
whose `run_established` sequence names the rest, because the kernel property
source consumes it; the source-authority bodies of every
profile that issues a view, since a frozen read holds their preimages; the
canonical-framed construction, its four views, its execution and replay, and
the same-Core check; the Relations four-role boundary; and the Analysis outcome
and proposition discipline with the named-premise intake. Activation is
transitive: a contract a frozen consumer's read closure reaches is inside the
claim even when no page names it as a kernel, and the pre-freeze deep review
(`pre-freeze-deep-review-2026-09-04.md`) is the control that the activated set
has one well-typed, representable meaning end to end.

The surfaces the peer review listed as unexercised, the compiler trilogy, the
Analysis family-transport lane, the lossy Relations lane, the endpoint receipt
catalogs, and the Interface completion presentation, are frozen as declared
but unexercised and are not part of the claim that later consumers rely on;
an unexercised surface is excluded by saying so, never by leaving a formable
contract unstated. This is the "deliberately smaller v0" of the peer review's
Section 9.C, stated as scope rather than as deletion; consolidation can follow
the freeze.

## 10. Decisions requested (taken 2026-09-03, all as recommended)

1. Sub-decision A: adopt A2 (views keep identities; the closure obliges the
   consumer to hold the authenticated algorithm and module preimages).
2. Sub-decision B: adopt B2 (nominal coin law stays the hook; Analysis binds a
   distribution as a named Q5 premise).
3. Sub-decision C: adopt C1 (one PIR-owned abstract outcome partition in the
   ExecutionView; provider carriers mapped in Analysis), with
   `StrategyStopped` as a partition lane but not a completed record.
4. D2's five owner choices as recommended above.
5. Section 11 wording: fix the five M1 items and the two D1 items by the
   readings D1 and M1 implement (lattice priority; `Publish(activity)` on the
   LogicalAccess publication effect; named transfer nodes; both public-Query
   sink coordinates).
6. F0-V3: author the FS-family view catalogs in the same migration.
7. Identity pin: P2 (prose-fragment identity for this migration; transcription
   discrepancies are named reopenings; the pin is decided after the
   transcription covers admission, execution, and FS construction).
8. Freeze scope as in Section 8.

With these eight decisions the migration candidate of Block 7 can be refreshed
into exact owner text, both publication compilers rerun, old-profile refusal
controls retained, and the holdout and independent freeze review scheduled.
The identity-rotating publication itself remains the user's gate.

## 11. Consistency review against the Fiat--Shamir and Relations kernels

The recommendations above were checked, by reading rather than by a package,
against `docs-next/pir/fiat-shamir.md` Sections 5, 7, 9, 10, 11, and 12 and
`docs-next/relations/relation-model.md` Section 7.2. No conflict was found;
three recommendations gain a precise qualification.

1. **Sub-decision C is profile-qualified.** The abstract outcome partition's
   `InterpretationFailed` arm exists exactly for Protocols whose profile
   declares an interpretation-failure schema: the canonical-framed family's
   `FiatShamirSamplingFailure` with its `FSSamplingFailureReceipt` (Section
   5.1, Section 9.2), and no arm for Fresh or for the duplex family. Section
   9.2 also fixes that every other K1 noncompletion class "produces no
   semantic Protocol outcome", so `OperationalNoncompletion` is a partition
   lane visible to providers and never a record variant, and Section 9.4 keeps
   strategy search exhaustion an operational `Stop`. The partition therefore
   has five lanes over a Fresh Protocol and six over a canonical-framed one,
   and D2's schema-form record sum stays exactly the page's
   `CompletedProtocolRecord`.
2. **Sub-decision B splits by interpretation.** For a Fresh challenge the
   nominal `pir.public-coin-law` coordinate is the hook and the distribution is
   an Analysis-bound premise. For a Fiat--Shamir challenge the value is fixed
   operationally by Section 7: squeeze, exact-length check, state advance,
   `rule.accept`, `rule.decode`, retry up to `maximum_draws`. There is nothing
   for Analysis to bind on the PIR side; the provider-facing premises are the
   family catalog's sampler adequacy (one of the four affirmative forms, with
   the exhaustion term explicit) and oracle-process correspondence. B2 should
   say so, or a reader will look for a Fresh-style law binding that FS
   challenges do not have.
3. **The Terminal repair and Fiat--Shamir agree, and the repair closes a case
   the FS page already relies on.** Section 5.2's base requirements read prior
   guard outcomes and publications and are indifferent to the terminal body;
   `CheckFSConstruction` item 7 demands identical Core bodies on both sides,
   which the repair preserves because it changes the shared Core once;
   constructions are Core-scoped through `CoreHeaderAtom(CoreId)`, so the
   measured sixteen-profile cone already contains both FS profiles. Section
   9.4 states that an invalid grinding value "makes the ordinary check false"
   and expects an authored non-accepting branch; under the old text that state
   was the unspecified guard-true/check-false case, and under the repair the
   Accept guard carries the Check as a must-fact, so the false Check falls to
   the fallback terminal as the page assumes.
4. **The closure definition respects the Relations attachment cut.**
   Section 7.2 makes `ProtocolRelationBinding` depend only on the exact
   `ProtocolId` and its relation Interfaces and forbids any PIR
   back-reference. The formal source closure of Section 2 therefore stays a
   PIR-plus-Foundation object; a property question adds the Relations roots
   (binding, definition, model, instance) as separate package roots, which is
   the question-relative package design and exactly what the Relations--Plan
   coupling audit found: destination coordinate families exist, and the
   Schnorr subject has selected none of them.
5. **The LogicalAccess wording fix is what the FS page already says.**
   Section 11 calls the publication frame "only a typed fixation marker" and
   Section 5.2 item 6 requires "the exact logical-access fixation marker" in
   the required prefix, matching `Publish(activity)` on the publication effect
   node and the control-aware influence cone D1 implements.
6. **One F0-V3 obligation has its answer in Section 10.1.**
   `CheckedFSConstruction` has no semantic ID and its result reference is an
   owner-local, nonserializable object, so the `FSConstructionView` body cannot
   carry `result_ref` as bytes. The body-safe replacement F0-V3 asks for is the
   result schema plus the source and target Protocol, shared Core, and
   construction identities that Section 13 already lists; the reference stays
   live authority outside the body.

## 9. Non-claims

This note selects nothing. It records options, costs, and recommendations for
the design lane and the user, with slots for the five lanes still running. It
establishes no correspondence, theorem, or property, and it does not
authorize the migration it describes.
