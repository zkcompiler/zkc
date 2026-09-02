# F0-V2C Decision Inputs: Formal Source Closure and the Open Sub-Decisions

> **Kind:** Temporary main-lane synthesis of the F2-O0, M0, Q3-A, and
> reconciliation results into the decisions F0-V2C must take
> **State:** Options compared at equal resolution; recommendations recorded;
> nothing selected. Inputs from D2, F0-V3, F2-O1, M1, and the gates-green
> lane are still outstanding and have marked slots below
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

Slots for outstanding lanes: D2 supplies the completed-record schema and may
adjust item 3; F0-V3 decides whether the FS-family view catalogs enter the
same migration or are explicitly excluded from the frozen view surface; F2-O1
may add operational gaps for joint and shared Challenges, Oracles, and module
effects; M1 may turn a Section 11 wording item into a law defect; the
gates-green lane must be green before any of this is applied.

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

The freeze claim should cover the load-bearing kernel only: Foundation values
and identity, the Interaction Core and admission, PCGraph, Fresh execution and
replay, the canonical-framed construction and same-Core check, the Relations
four-role boundary, and the Analysis outcome and proposition discipline. The
satellite surfaces the peer review listed as unexercised, the compiler
trilogy, the Analysis family-transport lane, the lossy Relations lane, and
the endpoint receipt catalogs, are frozen as declared but unexercised and are
not part of the claim that later consumers rely on. This is the "deliberately
smaller v0" of the peer review's Section 9.C, stated as scope rather than as
deletion; consolidation can follow the freeze.

## 9. Non-claims

This note selects nothing. It records options, costs, and recommendations for
the design lane and the user, with slots for the five lanes still running. It
establishes no correspondence, theorem, or property, and it does not
authorize the migration it describes.
