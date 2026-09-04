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
`CannotAnswer/F0V4-C-END-TO-END-COMPOSITION`: 28 findings comprise 21 bounded
affirmatives, two deliberate refusals, and five `CannotAnswer` findings
including the aggregate. The executable PIR path composes. Analysis premise
formation does not, because the current owner text and exact-subject evidence
do not determine four required inputs.

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

The exact ordered requirement sequence has eight entries: two Fresh
distribution coordinates, one provider outcome-carrier coordinate, and five
relation/Plan coordinates. Formation stops for four independent reasons:

| Missing input | Frozen result | Exact boundary |
|---|---|---|
| first-class named-premise formation | `CannotAnswer/F0V4-C-NAMED-PREMISE-OWNER-CONTRACT` | `analysis-model.md` lines 2246--2261 has only three non-named requirement variants |
| Boolean Fresh distribution evidence | `CannotAnswer/F0V4-C-BOOLEAN-FRESH-PREMISE` | `cryptographic-properties.md` lines 968--973 requires the law as an explicit premise; the available fixture matches only the `RootNat(2)` law coordinate |
| relation and Plan evidence for this exact Core | `CannotAnswer/F0V4-C-RELATION-PLAN-REBIND` | `analysis-premise-intake-probe/fixture.json` line 5 names another Core; lines 154--259 mark all five relevant coordinates `RebindRequired` |
| published provider declaration | `CannotAnswer/F0V4-C-PROVIDER-DECLARATION` | the carrier decision record has `Authority: None` at line 7; `cryptographic-properties.md` goes from Section 3.1 at line 1299 to Section 4 at line 2167 without the requested provider section |

The successful Fresh-law and relation/Plan coordinate findings say only that
the leaves and candidate fixture coordinates were reconstructed exactly. They
do not turn proposal data for another subject into owner premise authority.

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
execution, replay, and finite map arithmetic, and that the four Analysis holds
remain classified at their exact source/evidence boundaries. It does not turn
the `CannotAnswer` aggregate affirmative.

This package does not establish owner publication, a general Core or Interface
implementation, arbitrary-protocol execution, provider correspondence,
relation truth, theorem applicability, protocol soundness, Fiat--Shamir
security, a random-oracle or concrete-hash assumption, compiler/backend
correspondence, or production readiness.
