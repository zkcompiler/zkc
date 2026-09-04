# Mixed-challenge, multi-binding end-to-end pressure

This package asks exactly one question:

> does one admitted Core with heterogeneous challenges and several public
> bindings compose through every activated contract without an owner
> underdetermination?

Run it from the repository root:

```sh
python3 -B evaluation/formal-source-end-to-end-pressure-f0v4/run.py --check
```

The frozen aggregate is
`Affirmative/F0V4-A-END-TO-END-COMPOSITION`: 29 findings comprise 24 bounded
affirmatives, two deliberate refusals, and three separately declared
`CannotAnswer` holds. The aggregate says that every determined stage composes
modulo exactly those holds. It does not say that a complete Analysis goal,
support, or judgment formed.

## Exact subject

The invocation-determined subject is one finite additive `Z/3Z` script with
ten occurrences:

| Occurrence | Effect | Relevant property |
|---:|---|---|
| 0 | Prover message | seed; also the run-established variant's context value |
| 1 | deterministic Verifier message | guarded |
| 2 | deterministic Verifier message | unguarded operand of both sampling predicates |
| 3 | Fresh Boolean challenge | independent; canonical draw bound `(8, 1)` |
| 4 | Fresh `RootNat(2)` challenge | independent; canonical draw bound `(8, 2)` |
| 5 | Prover message | commitment |
| 6 | Prover message | response |
| 7 | Check | finite Schnorr-style equation |
| 8 | Accept terminal | active only when the Boolean challenge and Check are true |
| 9 | Reject terminal | unconditional first-active fallback |

At scope opening 1, binding 0 is a Statement over public input 0 and binding
1 is SessionContext over the same invocation input. The second Core differs
only in binding 1, which instead names occurrence 0 output 0. The two
challenge declarations have distinct value types, nominal domains, and
Fresh-law coordinates. Their canonical-framed rules also have different
decoder result types and maximum-draw bounds.

The package authenticates the Core and Fresh Protocol against one retained
closure and verifies all ten ordered Core-admission boundaries. It verifies all
eleven construction-admission boundaries, reauthenticates the Fiat--Shamir
Protocol, and checks all seven same-Core requirements under the
checker-contract identity recomputed by the owner equation. The derived static
construction envelope is 2 rules, at most 16 frames, 19 transition calls, 929
frame octets, 1,861 namespace octets, and 13,562 cumulative framed, namespace,
and squeezed octets. Exact identities, admission vectors, bounds, body hashes,
source-page hashes, and view hashes are frozen in `expected-findings.json`.

## Views, setup, and Interface

All six Interaction static views and all four canonical-framed construction
views form. The package joins every field selected by the Analysis read
catalog against those issued bodies: 13 read slots close, including both
Protocol-qualified execution views.

The public-setup partition is exact:

| Core variant | `entries` for Fresh and Fiat--Shamir | `run_established` | fixed-setup formation |
|---|---|---|---|
| invocation-determined context | binding 1 | empty | `Affirmative/F0V4-A-FIXED-SETUP-FORMATION` |
| occurrence-output context | empty | binding 1 | `Refused/F0V4-R-FIXED-SETUP-RUN-ESTABLISHED` |

The Statement is absent from both sequences by owner construction. Fresh and
Fiat--Shamir setup entry bytes agree within each variant. The second variant
is a valid Core and has a valid setup view; only the Analysis fixed-setup
formation refuses because it requires an empty `run_established` sequence.

The admitted Interface has one total public-input assignment, exact Statement
coverage, seven codecs, 13 external slots, transport entries for every
value-producing occurrence 0 through 6, both terminal completion entries,
and the canonical interpretation-failure completion entry with all five
payload coordinates. Its transports cover every formable owner transport
target, occurrences 0 through 6; Check and Terminal are not transport-target
constructors. A neighboring Interface omits occurrence 2's
ExternalApplication transport. It is refused at admission item 6 with
`F0V4-R-INTERFACE-REPLAY-INPUT`, before slot-closure checking can mask the
replay-input defect.

## Exhaustive execution and replay

The Fresh runner enumerates all 81 invocation/strategy cases and all six
Boolean-by-`Z/3Z` challenge pairs. The canonical-framed runner enumerates the
same 81 invocation/strategy cases. Execution and independently implemented
replay agree on every run:

| Interpretation | Runs | Accepted | Rejected | Interpretation failed | Replay matches |
|---|---:|---:|---:|---:|---:|
| Fresh | 486 | 81 | 405 | 0 | 486 |
| canonical-framed Fiat--Shamir | 81 | 21 | 42 | 18 | 81 |

The Fiat--Shamir executor and replay are imported from the existing portable
runtime package; this package supplies a generalized heterogeneous challenge
suite instead of copying their semantics. One sampling exhaustion is also
replayed from the Interface-presented domain payload, challenge, prefix
receipt count, prefix state, final state, and occurrence 2 operand. Its draw
sequence is rederived rather than trusted as presentation data; nine mutations
of later, unpresented commitment/response values leave that replay unchanged.

## Analysis boundary

The Analysis owner text now defines the ten premise kinds, typed
coordinates, body and scope laws, exact requirement keys, fail-closed intake,
and downstream premise-ID propagation. The package therefore replaces the
named-premise owner hold it carried before that text existed with
`Affirmative/F0V4-A-NAMED-PREMISE-OWNER-CONTRACT`.

The pressure question candidate carries eight canonically sorted
requirements: one Fresh distribution requirement for each of the two exact
`pir.public-coin-law` leaves, one provider outcome-carrier requirement, and
five relation/Plan requirements. The current executable Analysis model forms
the existing uniform three-element distribution profile and binds it to the
`RootNat(2)` law leaf. The resulting profile and premise IDs are frozen.

Three holds remain:

| Missing input | Frozen result | Exact boundary |
|---|---|---|
| exact uniform Boolean distribution profile | `CannotAnswer/F0V4-C-BOOLEAN-DISTRIBUTION-PROFILE` | `cryptographic-properties.md` Section 3, lines 321--369 defines a singular challenge model and lines 2543--2551 refer to that model's uniform law, but the section declares no `AnalysisDistributionProfileId` body for this Boolean leaf |
| relation and Plan evidence for this exact Core | `CannotAnswer/F0V4-C-RELATION-PLAN-REBIND` | `analysis-premise-intake-probe/fixture.json` line 5 names another Core; its five typed coordinates remain rebind-only controls |
| published provider declaration | `CannotAnswer/F0V4-C-PROVIDER-DECLARATION` | `cryptographic-properties.md` lines 2619--2622 forbid provider-premise formation until the profile publishes the declaration; the supporting carrier record still has `Authority: None` |

Only the three-element premise is supplied to the full intake. The other seven
bindings are absent, so intake returns
`CannotAnswer/F0V2D2-C-MISSING-BINDING-KEY`. Each of the five stale
relation/Plan controls separately returns
`Refused/F0V2D2-R-REBIND-REQUIRED-SCOPE`. The first unformed downstream stage
is `analysis.goal`; consequently no hypothesis context, proposition, support
instantiation, or judgment record is assigned an ID. This exact fail-closed
boundary is the positive finding
`Affirmative/F0V4-A-NAMED-PREMISE-INTAKE-BOUNDARY`.

Relative to the package's earlier freeze, before the Analysis named-premise
text, the named-premise owner finding changes
from `CannotAnswer` to `Affirmative`, the Boolean hold is narrowed from an
unspecified missing premise to the exact missing distribution-profile
declaration, the relation/Plan and provider holds remain, and the aggregate
changes to `Affirmative` under the rule that those holds are reported
separately. One intake-boundary finding is added, increasing the finding count
from 28 to 29.

The successful Fresh-law and relation/Plan coordinate findings say only that
the owner leaves and stale candidate coordinates were reconstructed exactly.
They do not turn evidence for another subject into owner premise authority.

At the finite arithmetic level, the package evaluates the six-lane map

```text
Accepted                  -> Image(true)
Rejected                  -> Image(false)
Aborted                   -> Unmodelled
InterpretationFailed      -> Unmodelled
StrategyStopped           -> Unmodelled
OperationalNoncompletion  -> Unmodelled
```

over the uniform 81-case Fiat--Shamir distribution. Accepted and transported
`true` mass are both `7/27`; Rejected and transported `false` mass are both
`14/27`; unmodelled mass is `2/9`. No mass is discarded or renormalized. These
are package-local finite calculations, not a formed Analysis premise or a
provider correspondence result.

## What a passing check establishes

A pass means that the exact frozen subject still composes through the listed
PIR admissions, owner projections, setup partition, Interface checks,
execution, replay, finite map arithmetic, and the now-active named-premise
grammar. It also establishes the exact three-element premise identity and the
fail-closed intake stop. The aggregate is affirmative only modulo the three
separately reported holds; the check does not form or establish the missing
premises or any downstream Analysis judgment.

This package does not establish owner publication, a general Core or Interface
implementation, arbitrary-protocol execution, provider correspondence,
relation truth, theorem applicability, protocol soundness, Fiat--Shamir
security, a random-oracle or concrete-hash assumption, compiler/backend
correspondence, or production readiness.
