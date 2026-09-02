# F2-O0 provider-observable audit

This package asks one bounded question on the provider side of the formal
bridge: does the exact admitted finite Schnorr Core and Fresh Protocol, as
exposed by its six normalized owner views, carry every observable that a
VCVio-shaped operational interpretation needs, or exactly which observables
are missing? It mirrors the F1-R1C0 method: stop at the first absent premise,
name it exactly, and never invent it.

Run from the repository root:

```sh
python3 -B evaluation/formal-provider-observables-f2o0/run.py --check
```

`--check` needs only the Python standard library and the repository. It
regenerates the Lean file and the ledger, requires them to equal the committed
fixtures byte for byte, runs the independent checker on the baseline and on
every mutation, verifies that the committed elaboration receipt is bound to the
committed generated file by SHA-256, and compares the 45 findings with
[`expected-findings.json`](expected-findings.json).

```sh
python3 -B evaluation/formal-provider-observables-f2o0/run.py --elaborate
```

`--elaborate` additionally runs `lake env lean` on the generated file inside
the pinned VCVio checkout (`ZKC_F2O0_VCVIO_CHECKOUT` or `--checkout`
overrides the default path) and rewrites
[`elaboration-receipt.json`](elaboration-receipt.json) before the ordinary
check. A missing checkout is reported as
`Unsupported/F2O0-U-PROVIDER-ENVIRONMENT`; it is never a silent pass, and the
`--check` output records the same classification under `live_elaboration`.

The frozen result is `CannotAnswer/F2O0-C-MISSING-OPERATIONAL-OBSERVABLE`.

## Subject, provider, and coordinate universe

The subject is the F1-R1B admitted Core
`zkcidv0:pir.interactive-core:33f9d34a…` and Fresh Protocol
`zkcidv0:pir.protocol:5ef61d48…`, reached only through the F0-V2B1 owner
derivation. The coordinate universe is the 329 active leaves of the six
normalized owner views, in B1's coordinate encoding (view, exact path,
boundary). The generator reads the views through B1's reference path; the
checker reads them through B1's clean-room path and treats the result as its
owner-side oracle.

The provider is VCVio at revision `de0a3108140e3e04a7ebf0075aa110b459ee6e8a`
under Lean `v4.33.1`. The generated file imports
`VCVio.CryptoFoundations.SigmaProtocol`, states the interaction in `ProbComp`,
and binds the `ChallengeVerifyProtocol` shape that the pinned completeness
theorem is stated over.

## What the generator emits

[`generator.py`](generator.py) is untrusted. It emits
[`generated/Schnorr.lean`](generated/Schnorr.lean) and
[`generated/ledger.json`](generated/ledger.json). Every construct line in the
Lean file ends with a marker `-- [f2o0:<id>]`, and the ledger maps each marker
to exactly one of:

- one source coordinate: the view leaf whose value determines the construct
  under a declared rendering rule, plus the further leaves consulted; or
- one typed `no_source_coordinate` entry with the observable's class, the
  exact reason no leaf determines it, what needs it, the leaves that merely
  name it, and where the fact actually lives.

The interaction has one step per Core occurrence in schedule order: two
Prover messages received from a strategy typed by the StrategyDecisionView,
one Fresh challenge bound from a public-coin law parameter, one Check applied
to its ordered inputs, and the guarded Accept and fallback Reject terminals.
Everything no view determines is left as a parameter of the interaction rather
than filled in from a semantic-module body, a portable-algorithm preimage, or a
Relations body.

The ledger states one premise and seven rendering rules. The premise is that
reading any leaf requires the decoders of the body compilers named in the B1
schema source (Foundation and PIR laws, not view leaves). Under that premise
the value types decode to root natural and Boolean types, which the rendering
rules carry as `Fin 3` and `Bool`.

## What the checker establishes

[`checker.py`](checker.py) shares no code with the generator. It checks, in a
fixed rule order with one stable code per rule:

| Rule | Code |
|---|---|
| ledger shape and subject binding | `F2O0-R-LEDGER-SHAPE` |
| every gap entry is typed | `F2O0-R-GAP-UNTYPED` |
| every construct has exactly one coordinate or one gap | `F2O0-R-CONSTRUCT-UNSOURCED` |
| every claimed, consulted, or naming coordinate is an active leaf | `F2O0-R-COORDINATE-UNKNOWN` |
| no two constructs claim one coordinate | `F2O0-R-COORDINATE-ALIAS` |
| a construct claims only a leaf whose boundary can determine its kind; denotations, distributions, relations, strategies, and outcome maps are gap-only | `F2O0-R-INVENTED-OBSERVABLE` |
| Lean markers and ledger agree once each at the recorded lines | `F2O0-R-MARKER-MISSING`, `-UNLEDGERED`, `-DUPLICATE`, `-LINE` |
| verdict constructors agree with the Terminal table | `F2O0-R-VERDICT-MISMATCH` |
| steps agree with the occurrence effect table | `F2O0-R-EFFECT-MISMATCH` |
| every Terminal has a verdict and a step | `F2O0-R-TERMINAL-UNCOVERED` |
| every occurrence has a step | `F2O0-R-OCCURRENCE-UNCOVERED` |
| steps appear in schedule order | `F2O0-R-SCHEDULE-ORDER` |
| the Challenge step is a sample from a declared law parameter | `F2O0-R-CHALLENGE-NOT-FRESH` |

A ledger that passes every rule yields the audit result: the enumerated gaps.
The aggregate is `Affirmative/F2O0-A-OBSERVABLES-CLOSED` only when no
operational gap remains; otherwise it is
`CannotAnswer/F2O0-C-MISSING-OPERATIONAL-OBSERVABLE`.

## Result

The baseline ledger has 37 constructs: 28 claim distinct coordinates and nine
are gaps.

| Missing observable | Class | Where the fact lives |
|---|---|---|
| Check denotation (`check.0.denotation`) | operational | the K1 portable-algorithm preimage `finite_schnorr_algorithm` in `evaluation/formal-source-target-core-f1r1b/reference_model.py`, evaluated by the K1 evaluator under Foundation Sections 5 and 7.2; the views carry only its identity, contract, inputs, and output type |
| Terminal guard denotation (`guard.4.denotation`) | operational | the `boolean_identity_algorithm` preimage; the views carry one opaque guard body and no statement that guard truth equals Check truth |
| Fresh sampling law (`challenge.0.law`) | operational | nominal `pir.public-coin-law` and `pir.challenge-domain` bodies in the semantic module; `interactive-core.md` Sections 5.2 and 12.1 make distribution truth an Analysis/evidence obligation; the provider's `PerfectlyComplete` fixes a uniform draw |
| Outcome-partition map (`provider.verify`) | operational | `interactive-core.md` Sections 6.4, 12.3, 12.4 and Foundation Section 8 on the zkc side; `verify : Bool` and `OptionT` failure on the provider side; the views carry only the Accept and Reject cases and `interpretation_failure_schema = None` |
| Relation predicate, witness type | property premise | `docs-next/relations/relation-model.md`; nothing is bound for this subject |
| Prover private state, honest commit and respond | property premise | `interactive-core.md` Sections 9.2 and 12.3 and `interfaces-and-plans.md`; strategies are execution inputs, not Core observables |

Observables that turned out to be present: the message, challenge, and Check
output value types (under the codec premise), the Prover decision interface
(two decision points, seven guaranteed reads, legal move types), the Fresh
interpretation, and four of the six `ChallengeVerifyProtocol` type parameters
(statement, commitment, challenge, response).

Fourteen mutations each produce their named checker failure: aliasing two
equal-valued read coordinates, dropping or unsourcing the response producer,
replacing the Fresh challenge by a constant, omitting the Reject terminal,
claiming an out-of-range or cross-view coordinate, inventing the Check
denotation from its identifier leaf, unledgered and duplicated markers,
reordering the challenge after the response, an untyped gap, a swapped
verdict, and a mislabeled effect. Several of these still elaborate in Lean;
the checker, not the type checker, refuses them.

The committed receipt records exit status 0 in 2.4 s and an empty axiom
closure for `ZkcF2O0.interaction` and `ZkcF2O0.providerShape`.

## What a pass means and does not mean

A pass means: the committed Lean file and ledger are what the generator
produces from the admitted subject; the ledger is total over the schedule,
injective and valid over the 329-leaf universe, consistent with the Lean text,
and refuses the mutations; the enumerated gaps are exactly the frozen ones; and
the receipt is bound to the file.

It does not establish provider correspondence, theorem applicability, any
protocol or cryptographic property, any security result, or any target change.
The generated Lean file is untrusted output. The elaboration receipt is an
environment fact about one toolchain and one checkout. A sourced construct is a
coordinate claim under a declared rendering rule, not a proof of meaning. The
checker checks the ledger and the Lean text's structure, not the semantics of
the Lean term. Schnorr cannot exercise the shared-challenge discriminator; that
remains a later obligation.
