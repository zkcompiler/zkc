# Mixed-Challenge, Multi-Binding End-to-End Pressure

> **State:** `CannotAnswer/F0V4-C-END-TO-END-COMPOSITION`; the bounded PIR
> composition is executable, while four exact Analysis inputs are not formable
> from current owner text and evidence
> **Authority:** None. This record changes no owner page, profile manifest,
> publication table, or semantic identity.
> **Executable evidence:**
> [`evaluation/formal-source-end-to-end-pressure-f0v4`](../../../../evaluation/formal-source-end-to-end-pressure-f0v4/README.md)

## 1. Exact question and answer

does one admitted Core with heterogeneous challenges and several public
bindings compose through every activated contract without an owner
underdetermination?

Not completely. One exact finite subject composes through Core and Protocol
admission, canonical-framed construction admission, the owner checker
equation, ten static owner views, both public-setup variants, Interface
admission, Fresh and Fiat--Shamir execution, independent replay, and the
package-local outcome map. Analysis premise formation stops at four separate
boundaries:

1. the active Analysis requirement grammar has no named-premise case;
2. no exact Boolean Fresh-distribution premise is supplied;
3. the available relation and Plan premise fixture names another Core and
   requires rebind; and
4. no provider declaration has been published.

Those absences are not converted into affirmatives. The 28 frozen findings are
21 `Affirmative`, two expected `Refused`, and five `CannotAnswer`, including
the aggregate.

## 2. The discriminating subject

The baseline Core uses the finite additive `Z/3Z` carrier and one Boolean
constant. It has one root scope and one child scope opening before occurrence
1. At that opening it emits two public bindings in owner order:

| Binding | Class | Baseline value | Run-established variant value |
|---:|---|---|---|
| 0 | Statement | public input 0 | public input 0 |
| 1 | SessionContext | public input 0 | occurrence 0 output 0 |

The occurrence schedule is exact:

```text
0  Prover message: seed
1  guarded deterministic Verifier message
2  unguarded deterministic Verifier message: both sampling predicates read it
3  independent Boolean challenge
4  independent RootNat(2) challenge
5  Prover message: commitment
6  Prover message: response
7  finite Schnorr-style Check
8  guarded Accept terminal
9  unconditional Reject terminal
```

The accepting terminal requires the Check and is guarded by the conjunction of
the Boolean challenge and the Check result. The unconditional Reject is the
first-active fallback. The guarded verifier message is intentionally not used
as a later operand; occurrence 2 supplies the static public condition so
availability and `GuardImplies` remain exact.

The challenges use two distinct nominal-domain and Fresh-law coordinates.
Their canonical-framed rules both consume `(bytes, Z/3Z-condition)` but decode
to different result types. The Boolean rule requests 8 bytes and permits one
draw; the `RootNat(2)` rule requests 8 bytes and permits two draws. They are
independent rather than one joint group: a joint group would require a common
value type under the current owner contract and would make this heterogeneous
subject inadmissible before reaching the intended composition pressure.

## 3. Admission and exact owner views

The package forms the Core through the current owner compiler, authenticates
its exact-used semantic modules, portable algorithms, and evaluation contract
in one ledger, round-trips the complete body, and verifies the ten ordered
admission boundaries. The graph accepts both challenge conditions as
structurally public. The Fresh Protocol is separately reauthenticated against
the exact retained Core closure and evaluator identity.

The canonical-framed construction authenticates the exact two-profile closure,
its common algorithms, evaluation contracts, application declaration,
sampling-failure declaration, and two challenge-rule algorithms in one
ledger. It verifies all eleven ordered admission boundaries, including full
view derivation and the static envelope: 2 rules, at most 16 frames, 19
transition calls, 929 frame octets, 1,861 namespace octets, and 13,562
cumulative framed, namespace, and squeezed octets. Its identifier is
recomputed from the owner body equation. The Fiat--Shamir Protocol names that
construction and the same Core and is cold-reauthenticated under the retained
evaluator identity. The checked construction has total occurrence, value, and
challenge maps, verifies all seven same-Core requirements, and recomputes its
checker contract through the complete owner equation including the result
schema. These exact admission vectors are frozen under the five findings from
`F0V4-A-CORE-ADMISSION` through `F0V4-A-CHECKED-SAME-CORE`.

The owner projectors issue all six Interaction views:

- `PublicBindingView`;
- `StrategyDecisionView`;
- `PublicCoinView`;
- `EffectView`;
- `ClaimReductionView`; and
- the Fresh `ExecutionView`.

They also issue all four canonical-framed views and the corresponding
Fiat--Shamir `ExecutionView`. The package resolves every ordinal subtree that
the Analysis source catalog selects against those exact bodies. Thirteen read
slots close; the complete selected-field vector and every body digest are
frozen under `F0V4-A-ANALYSIS-READ-JOIN`. This establishes only that the
issued owner bodies contain the selected reads. It does not establish the
premises those reads are meant to support.

## 4. Public setup and fixed setup

`interactive-core.md` Section 13.4, lines 3041--3071, partitions
SessionContext and PublicParameter bindings by whether their values are
invocation-determined. The Statement does not enter either sequence.

For the baseline, both Fresh and Fiat--Shamir views place binding 1 in
`entries`; their entry sequences are byte-identical and
`run_established = []`. The Schnorr-style fixed-setup projection therefore
forms.

For the variant, both views instead have `entries = []` and
`run_established = [1]`. The setup view itself still forms, but
`cryptographic-properties.md` lines 561--572 requires the fixed-setup entry
sequences to contain exactly every SessionContext/PublicParameter binding.
Formation consequently refuses with
`F0V4-R-FIXED-SETUP-RUN-ESTABLISHED`. It does not fill the context from a run
or silently weaken fixed setup.

## 5. Interface admission and its discriminator

The positive Interface is formed from the exact canonical body in
`interfaces-and-plans.md` Section 3. It has:

- one total assignment from public input 0 to slot 0;
- Statement binding 0 represented by `SuppliesInvocation(0)`;
- seven exactly used codecs and 13 exactly closed slots;
- one ExternalApplication transport for every formable owner transport target,
  occurrences 0 through 6;
- one completion entry for each of the two Core terminals; and
- one canonical interpretation-failure entry with the domain payload,
  challenge, prefix receipt count, prefix state, and final state.

Admission checks all eight ordered items at lines 600--614 and succeeds with
`F0V4-A-INTERFACE-ADMISSION`.

The negative Interface removes only occurrence 2's transport. Both challenge
sampling predicates consume that occurrence value, so the replay-input rule at
lines 537--559 requires it to be presented to `ExternalApplication`. Admission
refuses at ordered item 6 with `F0V4-R-INTERFACE-REPLAY-INPUT`; the checker does
not continue to the resulting slot-use defect at item 7 and thereby hide the
decisive cause.

## 6. Exhaustive execution and independent replay

The Fresh path executes every combination of 81 invocation/strategy cases and
the six independent challenge pairs `(false|true, 0|1|2)`. Its 486 runs yield
81 Accepted and 405 Rejected records. The independent replay implementation
reconstructs all 486 outcomes and receipts exactly.

The canonical-framed path executes all 81 invocation/strategy cases through
the generalized portable runtime library. It yields 21 Accepted, 42 Rejected,
and 18 InterpretationFailed records; independent replay agrees on all 81. No
run reaches Aborted, StrategyStopped, or OperationalNoncompletion in either
finite corpus.

For one interpretation failure at statement 0, seed 1, commitment 0, response
0, the Interface presentation carries exactly the five owner completion
coordinates plus occurrence 2's sampling operand. Replay rederives the draw
receipts from those values and obtains the frozen failure record. Nine changes
to unpresented later commitment/response values do not affect it. This is
`F0V4-A-SAMPLING-FAILURE-PRESENTATION`; it is not authority created by replay.

## 7. Exact Analysis boundary

The package derives this ordered premise requirement sequence without claiming
that the owner can currently admit it:

| Slot | Kind | Exact source status |
|---|---|---|
| `challenge-law-0` | Fresh public-coin distribution | Boolean `pir.public-coin-law` leaf; no matching exact-coordinate premise fixture |
| `challenge-law-1` | Fresh public-coin distribution | `RootNat(2)` `pir.public-coin-law` leaf; one proposal fixture coordinate matches |
| `outcome-carrier` | provider outcome-carrier map | exact Fiat--Shamir Protocol outcome partition; no provider declaration |
| `relation-predicate` | relation predicate | proposal fixture for another Core; rebind required |
| `witness-type` | witness type | proposal fixture for another Core; rebind required |
| `prover-private-state` | Prover private state | proposal fixture for another Core; rebind required |
| `honest-commit` | honest commitment step | proposal fixture for another Core; rebind required |
| `honest-respond` | honest response step | proposal fixture for another Core; rebind required |

The two Fresh-law leaves are distinct and exact, which supports
`F0V4-A-FRESH-LAW-COORDINATES`. The second coordinate's match and the five
available relation/Plan coordinates support only
`F0V4-A-RELATION-PLAN-COORDINATES`: the source record is a proposal fixture,
and its Core identity differs from this subject's Core identity.

The owner text then fails to determine an admitted premise object.
`analysis-model.md` lines 2246--2261 lists only hypothesis-node,
affirmative-judgment-capability, and exact-quantified-witness requirements; it
has no named-premise requirement. `cryptographic-properties.md` lines
968--973 says the Fresh distribution remains an explicit premise, but the
exact Boolean instance is absent. The relation/Plan fixture names another Core
at line 5 and marks the five relevant entries `RebindRequired` at lines
154--259. Finally, the carrier decision record says `Authority: None` at line
7, while `cryptographic-properties.md` proceeds from Section 3.1 at line 1299
to Section 4 at line 2167 without a provider declaration or provider
outcome-map body. The four resulting `CannotAnswer` findings remain
independent.

## 8. Finite outcome-preserving map

PIR owns the six canonical-framed outcome lanes at
`interactive-core.md` lines 2032--2063 and forbids a consumer from relabeling
one lane as another. The package evaluates this total finite candidate:

```text
Accepted                  -> Image(true)
Rejected                  -> Image(false)
Aborted                   -> Unmodelled
InterpretationFailed      -> Unmodelled
StrategyStopped           -> Unmodelled
OperationalNoncompletion  -> Unmodelled
```

Under uniform mass on the 81 executed cases, the Accepted and transported
`true` events each have mass `21/81 = 7/27`; Rejected and transported `false`
each have mass `42/81 = 14/27`; the four unmodelled lanes jointly have mass
`18/81 = 2/9`. The transport retains the original denominator. In particular,
it does not condition on the 63 modelled outcomes and inflate acceptance to
`21/63 = 1/3`.

That arithmetic gives `F0V4-A-SIX-LANE-PROVIDER-MAP` and
`F0V4-A-MEASURE-PRESERVATION` only as finite package-local evidence. Because
the provider declaration and owner premise constructor are absent,
`F0V4-C-PROVIDER-DECLARATION` remains and no Analysis judgment forms.

## 9. Proposed delta

Nothing below has been applied. Each change requires the named owner and an
authorized identity refreeze.

### 9.1 Named-premise intake

**Owner page and section.** `docs-next/analysis/analysis-model.md`, Section
4.1, at the `AnalysisPremiseRequirement` grammar on lines 2246--2261.

**Exact change.** Add one closed `NamedPremiseRequirement` variant whose body
contains an exact slot symbol, one closed premise kind, and one typed owner
coordinate. Add authenticated named-premise bodies and exact bindings; derive
the required key set from the question; return `CannotAnswer` for a missing
key/source, `Refused` for a wrong kind or coordinate, and `Malformed` for an
extra, duplicate, or noncanonical key. Carry the exact named-premise ID set
through goals, hypothesis contexts, support instantiations, and judgments.

**Identity effect.** The marked Analysis kernel source and kernel profile
rotate. Every dependent question, goal, premise, support, and judgment identity
rotates. No PIR Core, Protocol, construction, Interface, or owner-view identity
changes.

**Evidence.** `F0V4-C-NAMED-PREMISE-OWNER-CONTRACT`; the exact eight-slot
sequence and its digest in the frozen report.

**Reversal condition.** Do not add this grammar if the Analysis owner selects
an existing requirement variant and publishes an exact, equally fail-closed
encoding of all eight slots through it. Merely storing names in prose or in a
research fixture does not satisfy the condition.

**Nonclaims.** The grammar would admit assumptions as assumptions. It would
not prove a premise, theorem, property, or provider correspondence.

### 9.2 Per-challenge Fresh distribution premise

**Owner page and section.** `docs-next/analysis/cryptographic-properties.md`,
Section 3, immediately after the explicit Fresh-distribution requirement at
lines 968--973.

**Exact change.** Define a Fresh distribution requirement for every selected
challenge as the tuple of exact Protocol and Core identities, `ChallengeRef`,
the `PublicCoinView` path to `challenges[ChallengeRef].fresh_law`, that exact
`pir.public-coin-law` declaration reference, challenge value type, and the
bound distribution/hypothesis. Require one exact binding for each selected
Fresh challenge and no others. Publish a Boolean-law binding for this subject
only after its distribution and independence hypothesis is supplied and
checked; do not copy the three-element-law fixture into that slot.

**Identity effect.** The cryptographic-property profile and each dependent
premise, question, support, and judgment rotate. The two PIR Fresh-law
declaration coordinates and all PIR subject identities remain unchanged.

**Evidence.** `F0V4-A-FRESH-LAW-COORDINATES` and
`F0V4-C-BOOLEAN-FRESH-PREMISE`; challenge refs 0 and 1 resolve to distinct
nominal law coordinates, while only ref 1 has a matching proposal fixture.

**Reversal condition.** Omit the challenge-qualified tuple only if the owner
proves that its smaller law coordinate uniquely fixes value type,
distribution, correlation obligations, and Protocol applicability. If the
Boolean challenge is removed from the target subject, retire rather than
default its requirement.

**Nonclaims.** A supplied uniform-law premise would remain an assumption. It
would not establish that an implementation samples it or that Fiat--Shamir
preserves it.

### 9.3 Provider map and measure clause

**Owner page and section.** `docs-next/analysis/cryptographic-properties.md`,
new Section 3.2 after the currently present Section 3.1; shared carrier grammar
belongs in `docs-next/analysis/analysis-model.md` under the named-premise body
introduced above.

**Exact change.** Define
`ProviderLaneImage<T> = Image(CanonicalValue<T>) | Unmodelled` and a total
provider outcome-carrier body containing the exact provider declaration, exact
Protocol outcome-partition coordinate, closed carrier, and a map from every
profile-qualified PIR lane to `ProviderLaneImage`. A declaration must name the
provider artifact/source identity, toolchain identity, carrier, and producible
outcomes. Add the measure law over the unmodified run distribution: the mass
of each provider event equals the mass of its exact preimage under the lane
map; `Unmodelled` mass remains in the measure, and neither conditioning nor
renormalization is permitted. For the Boolean event `true` in this subject,
the required equation is exactly `mu(true) = mu(Accepted)`.

**Identity effect.** The Analysis kernel rotates for the shared grammar; the
cryptographic-property profile rotates for the declaration and measure law.
Provider-map premises and every consuming support/judgment rotate. PIR's
six-lane partition and this Core, Protocol, and view identity cone do not.

**Evidence.** `F0V4-C-PROVIDER-DECLARATION`,
`F0V4-A-SIX-LANE-PROVIDER-MAP`, and `F0V4-A-MEASURE-PRESERVATION`; exact masses
are `7/27`, `14/27`, and `2/9` with denominator 81 retained.

**Reversal condition.** Withdraw this shape if the selected provider publishes
a richer carrier that models all six lanes, or if the Analysis owner requires
every provider to model every lane. In the latter case this Boolean provider
is inapplicable; unmodelled lanes must not be coerced to `false`.

**Nonclaims.** The finite table is not a provider declaration, provider
execution, correspondence theorem, completeness premise, or security
transport. The proposed measure clause does not prove the source distribution
or a theorem about it.

### 9.4 Required evidence rebind, not an owner-page edit

The relation/Plan hold does not expose an underdetermined owner grammar. Build
and admit the relation definition, interface, instance,
Protocol-relation bindings, Prover Plans, witness bindings, and grounding
results against this exact Core and its two Protocols. Then bind the five
relation/Plan requirements to those new owner IDs. The current proposal
fixture's IDs must remain `RebindRequired`, not be repinned onto this subject.

This creates new Relations/PIR subject identities and rotates dependent
Analysis subjects and judgments; it need not rotate any owner profile. Its
gate is `F0V4-C-RELATION-PLAN-REBIND`. Reverse the work if the target property
does not consume these five roles, and then remove the requirements explicitly
rather than filling them with unrelated fixture evidence. Even a successful
rebind would not establish relation truth or honest-prover behavior.

## 10. Nonclaims

The result is finite construction, owner-view, execution, replay, and
arithmetic evidence for two exact Cores. It is not owner adoption or
publication, a general admission or runtime implementation, arbitrary
heterogeneous-challenge support, provider correspondence, relation truth,
theorem applicability, protocol soundness, Fiat--Shamir security, a
random-oracle or concrete-hash model, compiler/backend correspondence, or
production evidence.

The four `CannotAnswer` inputs are not semantic defects hidden as pin drift.
The two deliberate refusals are expected semantic consequences of the current
owner contracts. A passing frozen check preserves these classifications; it
does not make the aggregate affirmative.

## Handoff

### Files changed

- Added `evaluation/formal-source-end-to-end-pressure-f0v4/README.md`,
  `expected-findings.json`, `model.py`, and `run.py`.
- Added this note at
  `docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/mixed-challenge-multi-binding-end-to-end-pressure.md`.
- Registered the package in `checks/manifest.json`,
  `evaluation/lifecycle.json`, and `evaluation/README.md`; advanced the exact
  count pins in `checks/tests/test_evaluation_lifecycle.py` to 61 research
  checks, 63 packages, and 35 active-source entries.
- Generalized the portable canonical-framed libraries in
  `evaluation/formal-source-fs-runtime-f0v3c/executor.py`, `model.py`,
  `replay.py`, and `views.py`. The original fixture and its frozen semantics
  are retained.
- Added pure projection entry points in
  `evaluation/formal-source-integrated-graph-f0v2b2d1/model.py` and
  `evaluation/formal-source-integrated-views-f0v2b2d3/model.py`. Refreshed only
  the resulting source digest in the latter package's
  `expected-findings.json`; all semantic vectors were unchanged.
- No owner page, owner profile manifest, publication table, private ledger,
  primary checkout, or real repository Git index was edited.

### Commands and outcomes

- `python3 -B checks/run.py validate`: exit 0, wall 0.05 s; 78 checks, six
  tiers, manifest digest
  `65a7597232bd603fbb4d67b1694fd854f94771bf94e82df82b1de81360ef4ecc`.
- With `GIT_INDEX_FILE=.cache/f0v4-index`, clone-local object storage and
  alternates, `UV_NO_SYNC=1`, `UV_OFFLINE=1`, and
  `UV_CACHE_DIR=.cache/uv`,
  `python3 -B checks/run.py run --check research.formal-source-end-to-end-pressure`:
  exit 0, wall 168.45 s (check 168.395 s), result
  `target/checks/20260904T154514Z/result.json`.
- With the same alternate index,
  `python3 -B -m unittest checks.tests.test_evaluation_lifecycle -v`: exit 0,
  wall 0.08 s; four tests passed.
- With the same alternate index and offline uv environment,
  `python3 -B checks/run.py run --tier developer`: exit 0, wall 1.96 s; all
  nine checks passed, result `target/checks/20260904T154811Z/result.json`.
- `python3 -B checks/run.py run --check research.owner-view-integrated-pcgraph`:
  exit 0, runner elapsed 3.765 s. The first combined successor regression then
  exited 1 after 8.419 s because the intentional helper extraction changed one
  authenticated source digest. This was source-pin drift only. After refreshing
  that exact pin,
  `python3 -B checks/run.py run --check research.owner-view-integrated-projections`
  exited 0, wall 4.79 s (check 4.729 s).
- `python3 -B checks/run.py run --check research.formal-source-fs-runtime`:
  exit 0, wall 65.78 s (check 65.716 s), preserving the portable suite's
  original frozen report.
- The focused presented-value replay mutation probe exited 0 in 4.88 s, and
  the setup-view/admission variant probe exited 0 in 5.00 s.
- `git diff --check`: exit 0. The alternate index listed exactly the 16 files
  above as modified or added.

Development reds were retained rather than disguised: the first focused run
exited 1 after check time 165.716 s because of the authored field-name typo
`construction.state_type`; changing it to the owner field
`construction.transcript_state_type` repaired that transcription defect. The
integrated-view regression red was the source-pin drift described above. A
developer run against the deliberately untouched real index exited 1 in 0.54 s
because lifecycle and public-tree checks correctly saw the new package and note
as untracked; this was the expected semantic consequence of the required
read-only-index lane, and the specified alternate-index run passed.

### Aggregate outcome

`CannotAnswer/F0V4-C-END-TO-END-COMPOSITION`: executable composition closes,
but named-premise formation, one Fresh distribution premise, exact-subject
relation/Plan evidence, and the provider declaration do not.

The frozen report contains 28 findings: 21 `Affirmative`, two `Refused`, and
five `CannotAnswer` including the aggregate. The separately declared provider
hold is `CannotAnswer/F0V4-C-PROVIDER-DECLARATION`; the aggregate is not
silently promoted around it or the other three evidence holds.

### Surprises and where the brief was wrong

- `AGENTS.md` is absent from this clone. The requested read-only source copy
  was used as workflow guidance.
- The brief names a provider measure-preservation clause in
  `cryptographic-properties.md` Section 3.2. At migration head `1ce298cb`, that
  page moves from Section 3.1 at line 1299 to Section 4 at line 2167. It has no
  provider-map body or provider-lane-map measure-preservation clause. Generic
  Analysis distribution profiles do have separate probability/measure-law
  fields; this record does not claim that all measure grammar is absent.
- The brief anticipates a separately declared provider hold, but the live
  Analysis grammar also lacks named-premise intake, the available premise
  fixture lacks the Boolean law, and its relation/Plan coordinates belong to a
  different Core. The aggregate therefore cannot be affirmative under the
  brief's own missing-evidence rule.
- A heterogeneous Boolean/`RootNat(2)` joint challenge group is not admitted
  by the current common-value-type rule. The final subject uses two independent
  Fresh challenges, preserving the requested heterogeneity without inventing
  an owner exception.
- The Interface grammar has no Check or Terminal transport target. The package
  therefore transports every formable target (occurrences 0 through 6), carries
  terminals through completion entries, and does not invent transports for the
  literal remainder of the ten-occurrence schedule.

### Nonclaims

No commit, push, pull request, profile publication, semantic refreeze, owner
adoption, provider run, theorem proof, security result, or implementation
correspondence is claimed. Main may commit the complete working tree with the
requested subject after reviewing this handoff.
