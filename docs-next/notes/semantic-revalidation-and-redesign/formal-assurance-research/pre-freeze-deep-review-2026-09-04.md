# Pre-freeze deep review — 2026-09-04

> **Kind:** Independent adversarial review; non-authoritative research note.
> **Reviewed source:** `20074d1c6c12c1ac7ef700f23c2e204a46b24329`, the local
> `docs/analysis-premise-intake` head at clone creation.
> **Disposition:** Do not publish this tree as an exact first frozen semantic
> contract yet. The blockers below are representability and cross-contract
> defects, not demands for a security proof or a completed compiler.
> **Change boundary:** This note changes no owner text, manifest, publication,
> checked finding, implementation, or authority. Nothing was committed.

## 1. Method and claim boundary

I read the requested owner pages in the requested order, then the PIR and
Analysis manifests, research index, migration record, decision inputs, decision
review packet, and both reopening records. I subsequently followed specific
dependencies into Foundation, the refreeze rehearsal, and the relevant checker
sources. All line numbers below refer to the reviewed commit, not a moving
branch. Paths are repository-relative.

The main method was **adversarial contract composition**, not another replay of
the Terminal proof: take a producer's admitted input domain, its exact output
schema, the consumer's selected fields, and the body compiler selected by its
manifest, and ask whether they can all hold simultaneously. I used small
paper countermodels and a read-only Python instrument. That instrument checks
Foundation size/encoding controls, explicit source joins, existing source-pin
drift, and an in-memory publication mutation. It does not implement PIR
admission, prove either paper Core admitted, or establish protocol security.

I also reran six existing check IDs. Results are recorded in the handoff;
passing a check is not promoted beyond its declared scope. In particular, I
did not rerun the half-hour Analysis closure suite, Lean builds, or the external
provider proofs. No external paper's theorem was audited in this review.

Definitions used here:

- **Defect:** two binding statements disagree, or a required construction
  cannot inhabit its stated type.
- **Underdetermination:** the admissible cases require an unstated selection or
  an unstated support/refusal boundary.
- **Design disagreement:** the rule is clear, but its cost or acceptance
  criterion should be changed.
- **Non-claim:** an explicitly withheld result; its absence is not a defect.

The findings are new questions relative to the packet's enumerated review
questions. This is not a claim that nobody has ever noticed them in an
uninspected task or private discussion.

## 2. Findings at a glance

| Code | Classification | Finding | Freeze consequence |
|---|---|---|---|
| PFDR-01 | Defect | Mandatory FS Interface failure presentation has an unformable K1 type | Repair or explicitly exclude canonical-framed Interface support |
| PFDR-02 | Defect | Authority-ID constructors omit the variant required by their profile compiler | Repair before freezing these identity contracts |
| PFDR-03 | Underdetermination / representational defect | Construction-wide FS view has singleton fields for heterogeneous challenge rules | Repair the kernel FS view contract |
| PFDR-04 | Defect | Two incompatible definitions of `InfluenceAtom`; the view cannot use the required header atom | Repair the kernel FS view contract |
| PFDR-05 | Defect, with adjacent underdeterminations | Analysis asks for a deliberately non-body `result_ref` and unmapped legacy field aliases | Repair the cross-owner source catalog |
| PFDR-06 | Underdetermination | Invocation-only setup issuance includes values produced later by a strategy | State the exact support boundary or change the operation |
| PFDR-07 | Defect | Family-premise source constructor receives a subject ID where it requires a declaration reference | Repair the transport declaration, or explicitly defer its activation |
| PFDR-08 | Design disagreement | Prose-pin reversal test measures hashing, not semantic determinacy or churn | Keep P2 provisionally, replace its acceptance/reversal test |

PFDR-03 through PFDR-05 directly contradict an unqualified claim that the
load-bearing source-view contracts are already exact. Calling Interface or
family transport unexercised limits the claims for PFDR-01 and PFDR-07; it
does not turn contradictory declarations into well-defined ones.

## 3. PFDR-01 — No canonical-framed Interface can meet the mandatory draws type

**Classification:** Defect. High confidence. This is a type-formation problem,
not a long-run or resource-exhaustion example.

**Exact sources:**

- `docs-next/pir/interfaces-and-plans.md`, §3.5, lines 514–522: every
  canonical-framed FS Interface has the interpretation-failure completion
  entry with all six coordinates.
- Same section, lines 528–548: `FSFailureDraws` has exact type
  `RootSeq<FSDrawReceiptPresentationType, 2^20>`; the codec type must equal it.
- `docs-next/foundation/executable-foundations.md`, Appendix A.2,
  lines 2405–2418 and 2435–2464: sequence capacity is at most `2^14`, and the
  complete worst-case value must also fit the constitutional bounds.
- Interface §3.6, lines 578–591: admission checks codec formation and total
  completion payloads.

**Smallest argument:** Choose any one-shot, one-challenge canonical-framed
construction. Even though its exhaustion lane is unreachable, §3.5 requires
the failure completion entry and its exact draws type. The capacity `2^20`
already violates K1's constructor-local bound. No actual million-element
receipt is needed. Shrinking the constant merely to `2^14` is not sufficient:
even `Seq(Unit,2^14)` has `1 + 2^14` nodes. The eight-field draw record costs
more than Unit.

The executable control admitted `Seq(Unit,1)` with maximum encoded size 18,
rejected `Seq(Unit,16384)` for the worst-case node bound, and rejected
`Seq(Unit,1048576)` for the sequence bound. Substituting Unit is deliberately
weaker than the actual required record. This proves the bound obstruction,
not the admissibility of a complete Interface fixture.

**Proposed change:** Derive a construction-specific presentation type from its
challenge rules and receipt types, then perform full K1 `Worst` admission.
Specify an exact unsupported/refused Interface boundary when that presentation
cannot fit. Alternatively define a separately owned, bounded/chunked external
presentation with its preservation contract. Do not omit an otherwise required
failure coordinate just because a sample run never reaches it, or raise a
Foundation limit implicitly.

**Identity effect:** Changes inside the Interface fragment rotate
`pir.interface-plan` and its import dependents, Interface/Plan IDs, and their
source-authority artifacts. Core and FS construction meaning need not change;
their upstream IDs need not rotate. Raising Foundation bounds would have a
much broader effect and is not the recommended repair.

**Reversal condition:** Exhibit a K1-admitted type with the exact current
`RootSeq<...,2^20>` schema and unchanged constitutional rules, or an existing
owner clause exempting canonical-framed Interfaces from this mandatory entry.
One small receipt or a passing FS executor does not meet that condition.

## 4. PFDR-02 — The profile compiler and the ID constructor hash different bodies

**Classification:** Defect. High confidence. The generic Foundation constructor
does not insert an owner-specific family tag.

**Exact sources:**

- `docs-next/pir/interactive-core.md`, §13.3, lines 2911–2930: the Interaction
  `pir.source-*` compiler is a closed variant; confidential initial-Oracle
  payloads, requirements, and closures use arm 1.
- Same page, §13.6, lines 3438–3455: their named ID constructors pass the bare
  family-local bodies to `ProfiledSemanticId`.
- `docs-next/pir/interfaces-and-plans.md`, §3.7, lines 709–719, versus §5.2,
  lines 1831–1844: the same discrepancy for confidential Plan witnesses.
- `docs-next/pir/endpoint-projection-views.md`, §3.1, lines 459–508: all four
  supplement IDs pass bare records, while their designated subject compilers
  require arm 0.
- `docs-next/foundation/executable-foundations.md`, §3.2, “Exact
  semantic-language profiles,” lines 528–537: `ProfiledSemanticId` wraps the
  supplied `domain_body` with the profile ID; it does not recompile that body
  through a family dispatcher.

**Smallest counterexample:** Let `R` be a valid family-local payload record.
The explicit confidential constructor supplies `R`; the profile subject
compiler supplies `V(1,R)`. For the supplement the two candidates are `R`
and `V(0,R)`. These are different canonical preimages. A strict consumer of
the profile compiler rejects the bare-record result; a producer following the
named constructor emits it. This is disagreement before any theorem or live
capability is involved.

The small Foundation encoding control used `R{0:N(0)}`: its encoding is
35 bytes, while either variant-wrapped encoding is 52 bytes; all three byte
strings differ. That small record is an encoding witness, **not** an admitted
authority payload. The argument applies to arbitrary valid family-local
records. No hash-collision assumption is needed to establish preimage
disagreement.

**Proposed change:** Make every named ID constructor call its selected
profile's outer family compiler explicitly. The static-view constructors at
Interactive Core §13.3, lines 2897–2908 already demonstrate the intended form.
Audit all four source-authority kinds across every family, including the
one-arm cases. Adding a second implicit wrapper in Foundation would break the
already explicitly wrapped cases.

**Identity effect:** Family artifact IDs computed by the bare-record route
change. Repairing the marked Interaction, Interface, and endpoint text also
rotates those profiles and their import dependents. Because Interaction
profile identity changes, dependent Core/Protocol IDs rotate even though this
repair need not change their execution rules or domain-body fields. The OIR
endpoint-graph schema need not change.

**Reversal condition:** Provide an existing exact rule under which
`ProfiledSemanticId(B,p,R)` automatically dispatches and produces
`ProfiledSemanticId(B,p,V(i,R))`, while also explaining why the explicit
static-view wrapper is not doubled. The current Foundation equation rules
that reading out.

## 5. PFDR-03 — One transition view cannot select two different challenge rules

**Classification:** Underdetermination if an unstated selection is intended;
representational defect if the view is meant to carry every admitted rule.
High confidence in the obstruction; the complete counterexample was reasoned
on paper, not submitted to an arbitrary-Core admission implementation.

**Exact sources:** `docs-next/pir/fiat-shamir.md`, §3.2, lines 208–239 and 242:
rules have per-challenge draw bounds, acceptance algorithms, and decoder
result types. §3.3, lines 300–318: the construction contains a total sequence
over every Core challenge. §13, lines 1315–1336: the view has one
`acceptance_abi`, one `decoder_abi`, and one `draw_bounds` record, followed by
only `(challenge_ref,position)` pairs. Lines 1412–1416 scope the view to the
construction, not to a selected challenge.

**Smallest countermodel:** A root scope, two unconditional independent
challenges, and one unconditional terminal, with no claim obligation. Give
`c0` Boolean output and `c1` `RootNat(2)` output. Both decoders can be total
constant algorithms with empty failure rows. For additional pressure choose
different admitted draw lengths/bounds, for example `(1,1)` and `(2,3)`,
under a sufficiently large admitted transcript byte type. No rule in §3.2 or
§3.3 requires homogeneity. Even with equal lengths and bounds, the two exact
decoder ABIs disagree in result type.

Which `decoder_abi` does the construction-wide view contain? Choosing the
first or last differs; a union changes the exact ABI; duplicating the view
requires a challenge coordinate the view key lacks. Recovering the other rule
from the complete construction preimage can help a consumer, but does not
define the singleton field it is required to issue.

The existing runtime witness has one rule: its view projector explicitly
selects `construction.challenge_rules[0]` in
`evaluation/formal-source-fs-runtime-f0v3c/views.py`, `construction_views`,
lines 171–192. Agreement on that witness cannot adjudicate the two-rule case.
This is precisely the
packet §2, line 30 reversal condition: a family field two producers could fill
differently.

**Proposed change:** Use a challenge-indexed table containing the exact
acceptance ABI, decoder ABI, and draw bounds for every challenge. Derive its
domain and order from `challenge_rules`; retain shared laws once. The duplex
page already uses a per-challenge `squeeze_and_decoder_map` (§11.3,
lines 1076–1096). Alternatively state an explicit homogeneous/single-rule
support restriction, but that is a real narrowing, not a clarification.

**Identity effect:** Canonical-framed profile, construction/FS Protocol IDs,
its view manifests, and dependent profiles/subjects rotate. Interaction and
duplex profiles need not change. Adding a challenge parameter to the view
coordinate instead would additionally change the common coordinate contract.

**Reversal condition:** Point to an existing admission restriction forcing
every rule's ABI and bounds to be identical, or derive one current view body
for the countermodel without selecting, dropping, or changing a rule.

## 6. PFDR-04 — `InfluenceAtom` means both an exact tagged coordinate and a different record

**Classification:** Defect. High confidence. This is not a demand that the
transcript state be injective or cryptographically binding.

**Exact sources:** `docs-next/pir/fiat-shamir.md`, §5.1, lines 585–610,
defines a 14-arm `InfluenceAtom`; lines 635–676 map actual transition inputs
to those atoms. Appendix A, lines 1872–1891, supplies the exact variant
bodies. §5.2, lines 689–705 and 728–740, requires headers, scope paths,
bindings, and ordered transition atoms. But §13, lines 1293–1307,
redefines the same name as a record containing an `OccurrenceRef`, a nonempty
sequence of `OccurrenceKind`, and `required: MetaBoolean`; lines 1360–1364
describe the view as carrying the required or merely framed atoms.

**Smallest counterexample:** The first active challenge requires
`CoreHeaderAtom(CoreId)` before any occurrence. That is an arm-0 ID-bearing
atom under §5.1/Appendix A, not a record with an occurrence reference. There
is no header `OccurrenceKind` or canonical invented occurrence ordinal.
Likewise two public bindings at one opening have different `BindingRef`s,
which the §13 record cannot name. This problem exists before heterogeneous
challenges or sophisticated protocols enter the picture.

**Proposed change:** Keep the exact existing atom algebra and make the view
contain explicitly typed entries such as `(atom: InfluenceAtom, required)`
with a stated static/symbolic projection law. If an occurrence-only summary
was intended, give it a different name, state what it omits, and specify how
its fields are derived; do not call it the exact required-influence sequence.
The source closure retaining headers elsewhere does not resolve this
same-name, different-body contradiction.

**Identity effect:** Canonical-framed profile and downstream identity cone
rotate; no new Core constructor is required. Reusing the §5/Appendix-A atom
definition need not alter runtime framing, whereas changing that definition
would also alter transition/prefix identities and requires separate review.

**Reversal condition:** Exhibit a unique, source-specified encoding of the
required header and binding atoms in the current §13 record without synthetic
occurrence IDs, dropped coordinates, or a second meaning of `InfluenceAtom`.

## 7. PFDR-05 — The Analysis read catalog requests a field PIR expressly excludes

**Classification:** Defect for `result_ref`; underdetermination for the
unmapped legacy aliases. High confidence in the former. A lexical mismatch
alone is not treated as a semantic counterexample.

**Exact sources:**

- `docs-next/analysis/cryptographic-properties.md`, §3, lines 734–750:
  selected names abbreviate exact ordinal paths into the closed owner schema.
- Same section, lines 884–891: `FSConstructionView` selects `result_ref`
  as well as the nine actual body fields.
- `docs-next/pir/fiat-shamir.md`, §13, lines 1338–1351 and 1365–1369:
  the result body has no `result_ref`; the owner-local result reference is
  explicitly not a body field. Lines 1417–1419 keep it in the live result
  coordinate.
- `docs-next/pir/interactive-core.md`, §13.1, lines 2299–2303: a field path
  must reach an actual atomic body leaf; absent fields are malformed.
- `docs-next/analysis/analysis-model.md`, §2.1, lines 594–603: exact owner
  field projection rejects absent paths.

**Smallest counterexample:** Request the published AFK additional source slot
for an otherwise supported checked FS construction. There is no ordinal body
path for the requested live `result_ref`. Treating it as an alias for an
existing semantic ID does not preserve its meaning: a live result reference
is neither `result_schema` nor `transcript_construction_id`. Moving it into
the bytes would violate PIR's deliberate authority boundary. Thus the exact
read list cannot be formed literally as written.

Adjacent stale selections are useful diagnostic evidence, not independent
security findings: `scope_openings` versus `PublicBindingViewBody.scopes`
(Analysis lines 783–787; Core lines 2438–2453), and
`initialize_algorithm_and_contract` versus a construction with an
`initial_state` and `initialization_schedule_law` but no initialize algorithm
(Analysis lines 856–864; FS lines 1271–1285). The page permits expository
aliases, but supplies no exact path map for these changed meanings. FS's own
execution view still names `exact_frame_schedule_coordinates` and
`challenge_decoding_coordinates` at lines 1520–1523 rather than its newly
declared `frame_schedule` and `challenge_coordinates`.

**Proposed change:** Re-author and type-check the consumer catalog against the
actual owner schema. Keep result identity/live authority in the coordinate
and invocation; remove it from the body-leaf selection. Publish exact alias
to ordinal-path mappings where aliases are retained, including whether an
alias selects one leaf or a subtree. Add a cross-owner join test that resolves
every catalog selection, rather than checking each page's field inventory
separately. Do not weaken absent-field refusal.

**Identity effect:** Repairing the Analysis catalog rotates the cryptographic
property profile and its transport/source-validation descendants, semantic
read manifests, questions, and dependent supports. Correcting the FS execution
aliases also rotates the canonical-framed cone. Neither change requires
adding a serializable checked-result ID or weakening capability freshness.

**Reversal condition:** Show the exact current body ordinal for `result_ref`
and its canonical type, consistent with the explicit non-body rule, or an
existing catalog rule that removes it before leaf resolution without changing
the requested read. A host-side surrogate is not such a rule.

## 8. PFDR-06 — An invocation quotient is asked to contain future strategy values

**Classification:** Underdetermination of the supported issuance domain; an
impossible positive projection if the advertised quotient covers every
admitted binding. Medium-high confidence. I do **not** infer that admission
promises every downstream operation must succeed.

**Exact sources:** `docs-next/pir/interactive-core.md`, §4.2,
lines 506–537: a `ValueRef` may name an occurrence output. §4.3,
lines 548–565: any such public value can be a `SessionContext` or
`PublicParameter`; no invocation-only restriction is stated. §4.4,
lines 584–599: a child opens after its binding values become available.
§13.4, lines 2951–2969 and 2992–3013: issuance takes an admitted Protocol and
CoreInvocation, not a run or strategy, yet entries cover every and only
SessionContext/PublicParameter binding with its canonical value, and the view
contains no prover output.

**Smallest paper countermodel:**

```text
scope 0: Initially
o0 in scope 0: Always, ProverMessage(RootBool)
scope 1: child of 0, opens BeforeOccurrence(o1)
b0 in scope 1: SessionContext, OccurrenceOutput(o0,0)
o1 in scope 1: Always, terminal Accept, no claim/check/reduction obligations
```

There are no invocation inputs, so both legal strategies receive the same
invocation. One supplies false at `o0`; the other supplies true. Scope 1 can
open in both executions, but the required value of `b0` differs. No function
of the supplied invocation and Protocol determines it. Rejecting this
specific setup projection is a reasonable design; the exact eligibility law
and rejection category need to say so. This does not justify rejecting the
underlying Core or pretending the binding is invocation-fixed.

This surface is not wholly peripheral: `cryptographic-properties.md`, §3,
lines 571–587 and 790–797, consumes the issued setup values and requires the
complete binding sequence.
`docs-next/analysis/profiles/cryptographic-property.json`, `expected_imports`
at lines 7–13 and `definitions[0].dependencies` at lines 82–88, imports
`public-setup` and its body compiler. A static Schnorr setup may be an eligible
subset, but that subset must be explicit.

**Proposed change:** Define an invocation-determined setup projection domain:
every included binding's transitive value dependency must be available from
the allowed invocation/constant sources, with no occurrence/strategy source;
also state the exclusion law needed for the claimed Statement/private-input
quotient invariance. Refuse or return `Unsupported` outside that named domain,
without changing Core binding semantics. If runtime-produced setup is needed,
provide a separate boundary/run-issued view with explicit authority and
fixedness premises, not an implicit run inside this operation.

**Identity effect:** The narrower issuance law rotates `pir.public-setup` and
its import-dependent profiles and setup-derived subjects. Core and Protocol
domain bodies and upstream IDs can remain unchanged. Restricting public
bindings globally instead would rotate Interaction and is a materially
different, more disruptive choice.

**Reversal condition:** Show a current Core or public-setup rule that excludes
the example by an exact, named condition, or derive `b0` solely from the
operation's actual inputs for both strategies. Merely choosing an arbitrary
noncompletion branch does not specify the missing support boundary.

## 9. PFDR-07 — Family-premise provenance is passed at the wrong semantic kind

**Classification:** Defect in the declared transport constructor. High
confidence in the kind mismatch. It is not a claim that AFK transport is
currently operationally supported.

**Exact sources:** `docs-next/analysis/analysis-model.md`, §4.1,
lines 1483–1489: `AnalysisFamilyCoordinate` is a profile declaration reference
of kind `analysis.property-family`. Its “Exact Analysis body compiler”
subsection, lines 2190–2194, defines
`FamilyHypothesisSource(AnalysisFamilyCoordinate)`.
`docs-next/analysis/cryptographic-properties.md`, §7.3, lines 5902–5918 and
5929–5939: `F` is an `AnalysisAsymptoticProtocolFamilyDefinitionId`, and both
the sampler and oracle-process bindings pass `FamilyHypothesisSource(F)`.

**Smallest argument:** A semantic subject ID for one asymptotic protocol
family is not a profile-local/imported declaration reference for one property
family. The coordinate already includes `F`; its presence does not give it
the other type. These two calls require an unstated coercion or a changed
constructor signature. The instrument checked the exact declarations and the
two call sites; it did not form an authenticated transport subject.

**Proposed change:** If provenance means the property-family hypothesis
schema, pass its exact declaration coordinate; keep the specific `F` in the
already typed premise coordinate. If provenance is intentionally the exact
asymptotic subject, introduce a separately typed source arm for that meaning.
Do not overload “family” to mean both.

**Identity effect:** The first repair can remain in the transport profile and
rotates its premise/support IDs and source-validation child. Widening the
common source sum instead changes the Analysis kernel and its full dependent
cone. This choice should be made explicitly before encoding new frozen
vectors.

**Reversal condition:** Supply an existing exact coercion or definition making
the two kinds identical while preserving the declared canonical bodies.
A Python value accepted by an untyped helper is not that evidence.

## 10. PFDR-08 — Keep prose pinning provisionally, but reject its current reversal test

**Classification:** Design disagreement, not a hashing defect or proof that
the discipline must collapse after a year.

**Exact sources:** `decision-review-packet-2026-09-03.md`, §2, line 31,
would reverse P2 on disagreement about a fragment digest.
`f0-v2c-decision-inputs.md`, §7, lines 181–192, selects prose pinning pending
admission/execution/FS transcription. `docs-next/pir/profiles/README.md`,
§3, lines 88–95, makes every byte inside a selected prose fragment
identity-bearing; §6, lines 215–228, describes publication compiler agreement.

**Counterexample to the test, not to the hash:** Both publication compilers
agree on the current source despite PFDR-02's two subject-preimage equations
and PFDR-04's two meanings of an atom. Their agreement shows which bytes are
committed, not that those bytes admit one semantic interpretation. Thus the
packet's reversal condition would miss exactly the risk P2 is deferring.

**Churn measurement:** In memory only, I inserted
`<!-- editorial-only pre-freeze probe -->` immediately before the Interaction
kernel end marker. No rule or declaration selector changed. Both compilers
agreed before and after; 16 of 18 profile digests rotated, with only
`oir-endpoint-graph` and `analysis-kernel` stable. This is intended behavior
under the present rule, not an attack on its implementation. Existing fresh
clone failures also show the operational cost: one five-line FS insertion
invalidated four pinned field locations and the Analysis review's FS source
digest without changing those four field lists.

**Proposed change:** Retain P2 rather than block on a whole mechanized
compiler, but require (1) one exact producer/consumer schema and body-dispatch
contract for each activated surface, (2) a two-implementer determinacy
obligation with adversarial cross-field cases, (3) an explicit identity cone
and revalidation policy for editorial versus semantic changes, and (4) stable
versioned source artifacts and resolvable old preimages. Put commentary
outside identity-bearing fragments where practical. Do not introduce
after-the-fact whitespace/comment normalization into the current format.

**Identity effect:** Changing the review criterion in research/release policy
does not itself rotate a profile. Moving commentary out of an already pinned
fragment, changing fragment partitioning, or selecting a formal-law preimage
does rotate the affected profiles; changing extraction/compiler interpretation
requires a new explicit format under the publication README §7,
lines 237–239. Exact-subject support must never be silently carried across
those rotations merely because a change was called editorial.

**Reversal condition:** Keep the current criterion only if it is explicitly
limited to publication-byte integrity and a separate enforceable semantic
determinacy gate covers the examples above. For a stronger churn claim,
demonstrate representative independent edits and refreezes with maintained old
preimages, explain which proofs/support can be reused, and measure that cost.
The one-comment experiment cannot predict a year's maintenance effort.

## 11. Decisions I would retain, decisions I would change

I would retain A2 (views plus authenticated preimages), B2 (distribution
premises stay outside Core), C1 (PIR's own outcome distinctions), first-active
Terminals, the explicit required-check/reduction/claim sets, and fail-closed
`Unknown`. The counterexamples here do not show those choices wrong.
PFDR-03/04 reverse the assertion that the selected FS catalogs are already
complete, not the decision to give FS exact owner views. PFDR-08 changes P2's
review criterion, not its provisional use of prose identity.

For the requested protocol pressures, my reasoning is structural rather than
a claim of implementing a particular published protocol:

- A folding or recursive-verification script that uses both a field challenge
  and an index/Boolean challenge immediately reaches PFDR-03. The needed
  repair is per-challenge data, not a new general protocol calculus.
- A batched-opening or lookup script with several public bindings and guard
  or query frames reaches PFDR-04's exact-coordinate problem. A list of
  occurrence kinds is not a substitute for binding/query/frame identities.
- Recursive composition can legitimately establish a child scope's context
  from an earlier public message. PFDR-06 argues for a separate eligibility
  boundary for invocation-fixed setup, not a global prohibition on that Core.
- I found no new argument that the finite instance-only Core must become a
  family generator, or that syntactic `GuardImplies` must become a theorem
  prover. A useful next pressure case is a single admitted mixed-challenge,
  multi-binding script carried all the way through Interface, owner reads,
  Analysis premise formation, and an exact outcome-preserving provider map.
  This is a proposed discriminating case, not another claim that five protocol
  names amount to end-to-end coverage.

The freeze scope should be a dependency-closed set of **activated contracts**,
not only a list of pages. Decision inputs §8, lines 196–205, properly disclaims
unexercised family transport and endpoint receipt catalogs. But a kernel
property source already consumes public-setup issuance, and exact authority
bodies occur in the Interaction profile itself. Their needed subset is
load-bearing. Conversely Interface execution is not a prerequisite for every
abstract PIR claim: PFDR-01 can be deferred only by honestly excluding that
Interface support, not by claiming the abstract FS executor is broken.

## 12. Outcomes, providers, assumptions, and non-findings

The “eight lanes” are not the Protocol outcome sum. Analysis has eight
qualified attempt-failure branches (`analysis-model.md`, §6,
lines 3996–4004), besides affirmative/negative judgments. PIR has five
profile-qualified outcome lanes for Fresh/duplex and six for canonical-framed
FS; only completed records inhabit its completed-record sum. Provider
`Image`/`Unmodelled` is a third distinction. These must not be put in one
untyped table.

The current text explicitly refuses to map operational noncompletion to
Boolean rejection; a whole-partition claim requires its completion premise
(`cryptographic-properties.md`, §3.2, lines 2276–2282 and 2603–2621).
Genuine nontermination is missing subdistribution mass, not a second returned
outcome (`analysis-model.md`, §3.3, lines 1335–1356). Those clauses defeat the
simple “missing run was counted as reject” criticism. They do not by
themselves prove measure-preserving theorem transport.

A hostile paper reviewer should next demand a **typed, event-and-measure
preserving transport argument**, not just a lane-name correspondence. For
example, normalizing a subdistribution with half its mass accepted and half
missing turns acceptance mass `1/2` into conditional probability `1`; a map
on accepted/rejected names cannot justify that normalization. The existing
completion, process-correspondence, quantifier, and sampler premises must
exclude or explicitly account for such a move. I did not find a demonstrated
admitted transport that performs this illicit normalization, so I report it
as an adversarial obligation, not a proved soundness defect.

Other explicit non-claims respected by this review:

- Lean results about the Terminal abstraction are not a full implementation
  theorem. None of my findings refutes those proofs.
- A finite provider table for additive `Z/3Z` Schnorr, including one-shot and
  retrying FS variants, does not establish arbitrary-protocol correspondence
  or ROM/QROM security.
- The provider declaration remains unpublished; a provider-map premise
  cannot be formed from a name alone. That known hold is not rediscovered as
  a new defect.
- Host-side Analysis dispatcher and adequacy-evaluator surrogates are
  explicitly disclosed at `analysis-model.md` lines 1472–1481 and
  `cryptographic-properties.md` lines 772–777. I do not call their
  incompleteness a hidden implementation claim. They also cannot resolve the
  contradictory exact contracts in PFDR-05 or PFDR-07.
- A publication check failing on deliberately old identities is expected
  until authorized publication. It is not permission to regenerate the table.
- Replay does not recreate causal-generation authority; the owner explicitly
  says so. No replay-to-honesty implication is assumed here.

The most immediate paper attack is therefore not “you have not proved
security.” It is: **your exact-language claim precedes a cross-owner
well-typedness and representability check.** Even a deliberately small kernel
needs a unique body and a defined projection for every case it claims to
support. Repeatedly hashing a contradictory source cannot establish that.

## 13. Small-instrument results and reproducibility

The read-only instrument is in scratch space at
`/tmp/zkc-pre-freeze-probes-2026-09-04-lDox7P/probe.py`.
SHA-256:
`a52eeb2397c7c22279b09ff83a223efd8c8a904ecd1f47339e74b7cd34a3e7c3`.
It imports the two publication compilers and the existing Foundation encoder;
therefore those parts are bounded checks using existing machinery, **not** a
third independent Foundation implementation. The source-join and paper
arguments do not rely on treating checker agreement as semantic truth.

```sh
UV_NO_SYNC=1 UV_OFFLINE=1 \
UV_CACHE_DIR=/tmp/zkc-pre-freeze-deep-review-2026-09-04-J3JaDN/.uv-cache \
python3 -B /tmp/zkc-pre-freeze-probes-2026-09-04-lDox7P/probe.py \
  /tmp/zkc-pre-freeze-deep-review-2026-09-04-J3JaDN
```

It exited 0 in 0.438 seconds. Summary:

| Control | Observed result |
|---|---|
| `Seq(Unit,1)` | Admitted; maximum 18 bytes |
| `Seq(Unit,2^14)` | Refused by worst-case node bound |
| `Seq(Unit,2^20)` | Refused by sequence capacity bound |
| `R`, `V(0,R)`, `V(1,R)` encoding witness | Three unequal byte strings; lengths 35, 52, 52 |
| `InfluenceAtom` definitions | Variant at line 588; incompatible record at line 1293 |
| Literal read aliases | `scope_openings`, `initialize_algorithm_and_contract`, `result_ref` absent from their selected records; alias caveat retained |
| Family source calls | Two `FamilyHypothesisSource(F)` calls against a declaration-reference argument type |
| Analysis review source drift | Only `docs-next/pir/fiat-shamir.md` differs from its frozen source digest |
| FS field audit drift | Four canonical view starts each moved by +5 lines; all four field-name lists are unchanged |
| In-memory editorial mutation | Both compilers agree; 16 profile digests rotate, two remain stable; owner bytes on disk unchanged |

For reproduction after scratch cleanup, the essential executable controls need
only the reviewed source and this compact driver. Run it with `python3 -B`
from that checkout. I also executed this embedded driver: exit 0, 0.414
seconds, matching the bounds, encoding lengths, and sixteen-profile rotation
above. It deliberately tests encodings, bounds, and the editorial cone, not
complete PIR admission or a semantic parser for the Markdown:

```python
import importlib.util
import sys
from pathlib import Path

root = Path.cwd()

def load(name, file):
    spec = importlib.util.spec_from_file_location(name, root / file)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module

p = load("review_pub", "evaluation/semantic-profile-publication/reference_model.py")
q = load("review_cold", "evaluation/semantic-profile-publication/independent.py")
k = p.k1
for cap in (1, 2**14, 2**20):
    try:
        print(cap, k.maximum_encoded_size(k.SeqSchema(k.UNIT_VALUE, cap)))
    except k.CanonicalError as error:
        print(cap, type(error).__name__, str(error))
r = k.DatumRecord(((0, k.Nat(0)),))
encoded = [k.encode_datum(x) for x in (r, k.DatumVariant(0, r), k.DatumVariant(1, r))]
assert len(set(encoded)) == 3
print("body lengths", [len(x) for x in encoded])
before = p.identity_table(p.compile_repository())
assert before == q.identity_table(q.compile_repository())
path = "docs-next/pir/interactive-core.md"
original = (root / path).read_bytes()
marker = b"<!-- zkc-profile-source:interaction-kernel:end -->"
assert original.count(marker) == 1
override = {path: original.replace(
    marker, b"<!-- editorial-only pre-freeze probe -->\n\n" + marker)}
after = p.identity_table(p.compile_repository(page_overrides=override))
assert after == q.identity_table(q.compile_repository(page_overrides=override))
print("rotated", [x for x in before["profiles"] if
    before["profiles"][x]["profile_digest"] != after["profiles"][x]["profile_digest"]])
assert (root / path).read_bytes() == original
```

## Handoff

### Workspace and authorization

- Fresh local shared-object clone:
  `/tmp/zkc-pre-freeze-deep-review-2026-09-04-J3JaDN`.
- Own branch: `codex/pre-freeze-deep-review-2026-09-04`.
- Reviewed commit: `20074d1c6c12c1ac7ef700f23c2e204a46b24329`.
- The clone uses Git's local shared object store; retain the source checkout
  while using this scratch clone. No remote fetch was needed.
- The only intended repository change is this uncommitted note. Check logs
  are ignored files under the clone's `target/checks/`; the instrument is in
  separate `/tmp` scratch space. No owner pages, manifests, expected findings,
  private registers, or publication tables were edited. No commit, push, or
  pull request was made.

### Commands and check results

The first batch ran offline with a clone-local UV cache:

```sh
UV_NO_SYNC=1 UV_OFFLINE=1 \
UV_CACHE_DIR=/tmp/zkc-pre-freeze-deep-review-2026-09-04-J3JaDN/.uv-cache \
python3 -B checks/run.py run \
  --check research.migration-text-review \
  --check research.analysis-premise-text-review \
  --check research.owner-view-fs-family-determinacy \
  --check research.holdout-readjudication \
  --check research.profile-publication --keep-going
```

Controller result:
`target/checks/20260903T211720Z/result.json`, 20.491 seconds, exit 1.
Its UTC directory date is September 3; this review's local date is September 4
in Asia/Seoul.

| Check | Result | Interpretation |
|---|---|---|
| `research.profile-publication` | Fail, 3.420 s | The six legacy upstream comparisons and old published table fail; direct/cold candidate reconstruction agrees. Expected publication hold. |
| `research.migration-text-review` | Fail, 1.062 s | Its rotation-cone assertion still requires `analysis-kernel` stable; the stacked Analysis migration changes that profile. |
| `research.analysis-premise-text-review` | Fail, 15.841 s | Aggregate and finding classifications pass their comparisons; the frozen FS page digest then fails. |
| `research.holdout-readjudication` | Pass, 0.043 s | Frozen holdout findings reproduced; a passing expected-result test is not universal support. |
| `research.owner-view-fs-family-determinacy` | Fail, 0.047 s | Four canonical view body-line pins are each five lines stale; field lists are unchanged. |

The FS runtime check was separately invoked under the same offline settings:

```sh
python3 -B checks/run.py run --check research.fs-runtime --keep-going
```

It passed: 389.088 seconds for the check, 389.113 seconds for the controller,
exit 0; result `target/checks/20260903T212010Z/result.json`. This reproduces
the finite runtime's expected findings, not arbitrary-Core support or security.
Across the six selected IDs, two passed and four failed for the reasons above.
The custom probe command and its exact results are in §13. Read-only
inspection additionally used
`git status`, `git log`, `git rev-parse`, `git ls-files`, `rg`, `nl`, `sed`,
`jq`, and `sha256sum`. The fresh branch was created with `git clone --shared
--branch docs/analysis-premise-intake` followed by `git switch -c`.

Final hygiene checks: `git diff --no-index --check /dev/null` against this
note reported no whitespace errors; `git diff --exit-code HEAD` showed no
tracked-file edits; `git status --short` showed only this untracked note.
The source checkout remained clean and its requested branch head still
matched the reviewed commit. The scratch instrument's SHA-256 was rechecked.

I did not update stale pins, reinterpret these failures as new semantic
counterexamples, or run the expensive closure/release-freeze tier. No live
Lean/provider build or compiler/backend test is claimed.

### Where the prompt was wrong or needed qualification

1. `.claude/CLAUDE.md` is not tracked at the requested branch head and was
   absent from the fresh clone. I read the source checkout's local copy as
   workflow guidance; it is not part of the frozen review subject. The
   explicit no-commit/no-push request overrides its ordinary handoff defaults.
2. The requested stacked branch exists and is the correct superset. However,
   the history of seven/four review rounds is not a green current-head test
   result: three of the selected review/audit checks are stale as detailed
   above. The prompt did not promise they were green; this distinction matters
   before treating previous closure summaries as this tree's evidence.
3. The older PIR-only rehearsal's “17 rotate, Analysis kernel stable” is not
   the identity delta of the full stacked Analysis migration. The kernel
   manifest here is revision 1. Publication is still intentionally held.
4. “Eight lanes” needs an owner qualification: eight Analysis attempt failures
   are not eight PIR run outcomes. Fresh/duplex have five PIR lanes and
   canonical-framed FS has six; provider images are yet another typed layer.
5. The pre-existing fixture claim-binding and provider-declaration holds were
   not repaired or recounted as novel findings. The reviewed frozen subjects
   are finite research evidence, not finished implementations of the protocol
   families mentioned in the prompt.

### Publication verdict

I would not publish this exact tree as the first frozen semantic version. First
repair the incompatible authority-body constructors, make canonical-framed
views represent heterogeneous challenges and the actual influence-atom
algebra, and reconcile Analysis reads with the owner bodies they select;
define the public-setup issuance domain, and either repair the unformable FS
Interface and family-source constructor or explicitly exclude their activation
from the release contract. Then add cross-contract counterexample controls,
refresh the stale current-head checks, reconstruct the identity cone, and run
the authorized publication/refreeze gates. This does not require a security
proof, a universal provider theorem, or finishing the compiler: it requires
that the deliberately limited contract being frozen have one well-typed,
representable meaning.
