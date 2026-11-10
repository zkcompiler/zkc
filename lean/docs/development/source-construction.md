# Constructing quantitative source proofs

Import `Zkc.Tools.Protocol.Construction` and select a local quantitative interpretation.
The program is an existing typed `Region`; the tool emits an ordinary Lean proof about its
actual `RegionMeaning`. The [specification](../spec/source-construction.md) fixes the meaning.
No global default provider or second interpreter is installed.

The pinned toolchain marks `vcgen` experimental. Put
`set_option experimental.vcgen true` in the client module to acknowledge this and avoid its
warning, especially when the package treats warnings as errors.

## The author boundary

A definition law fixes the actual body, ordered operands, interpretation, returned/stopped
postconditions and mathematical premises. Mark an ordinary proved law `@[spec]` to make it
available to the constructor. Unfold only the definition being proved, then call
`construct_region`. Named child laws are applied to their actual arguments; their proofs
are not reconstructed at each call. Registering a name is discovery, never semantic authority.

For finite repetition, supply a typed value:

```lean
construct_region with_invariants [fun remaining accumulator =>
  potential remaining accumulator]
```

The initialization, preservation and terminal propositions remain obligations. The invariant
may depend on logical inputs, semantic state and remaining count. It is not a private frame or
cursor. A well-typed zero invariant cannot prove a nonzero requested bound. Missing structural
rules are reported separately from mathematics; the constructor does not give an unresolved
execution fold to the companion.

The model examples author typed source fixtures explicitly. Actual-source clients instead
import `Zkc.Tools.Verification.SourceConstruction`, use `import_source` on the native structured
export, and bind definitions with `bind_source_helper` or `bind_source_protocol`. The quotation
retains the exported source; ordinary kernel-checked admission produces the typed Region.
Bindings derive the actual body, signature and closure membership. Named installation rules
supply dependency framing, role substitution and input/output placement. Authors select the
intended definition and state its mathematical contract; they do not write a replacement body,
slot layout, source visitor or frame proof. Rendering remains a named trust boundary.

The current root evidence records are still explicit: the author states the intended request,
local operation law, provider installation, initial budget and terminal observation. Source
construction fills the structural bound, not the independent mathematical/security meaning.

## Proposition-valued readings

Import `Zkc.Tools.Protocol.Readings` to construct the charged, exact and cost readings of
the [weakest-precondition interfaces](../spec/weakest-preconditions.md). Select the reading
as a local instance and register the concrete transcript interface with the structural
normalization, so that each primitive call exposes its absorption:

```lean
noncomputable abbrev logic := chargedMonad absorb (boundedEscape charge) (boundedEscape_antitone charge)
attribute [local instance] logic
attribute [local construction_simp] absorb
```

The exact reading is `chargedMonad absorb exactEscape exactEscape_antitone`; the cost reading
is `costMonad absorb charge`. Assertions are written `⟨P⟩`, for example
`⦃fun _ => ⟨True⟩⦄ game ⦃fun out _ => ⟨out = false⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄`. No rule
is registered per interface or per judgment.

The author supplies:

- one bound per query site. Under a bounded judgment the remaining obligation is
  `Pr[∃ reply decoded from the raw answer whose continuation fails] ≤ charge`; it is usually
  a root-counting or binding lemma about the actual check. Under the exact judgment it is the
  continuation for every reply.
- the continuation obligations of receives: every recovered message, with the actual
  recovery equation as a hypothesis.
- a loop invariant through `construct_region with_invariants`, with its preservation and
  terminal conditions. A cost invariant is a budget on the remaining iterations.
- the endpoint assembly: `charged_of_triple` and `costBound_of_triple`, then
  `ZkcSecurity.FiatShamir.Typed.soundness_charged` with `certificate` and `certificate_doomed`, or
  `ZkcSecurity.Interactive.soundness_accepted`.

The remaining goals read as plain propositions over the quantified histories, messages and
replies; name them with `intro`. The constructor never supplies a probability bound or an
invariant.

### Structural equations and value types

Structural normalization (`construction_simp`) matches up to reducible unfolding. An
equation about the program whose left side spells a value type differently from the actual
program, for example `Nat` against a carrier `Carrier true` that unfolds to `Nat` only at
default transparency, does not fire as a structural simp lemma. Register such an equation as
a `@[spec]` equation instead: the constructor applies specification equations at the program
root with full unification. `Regressions.lean` shows both forms on the same program.

## Core definitions

Import `Zkc.Tools.Verification.CoreConstruction` to construct a reading of an imported
[core definition](../spec/core-language.md#readings-of-a-side). The program is the meaning of
the definition for a literal side, `package.definition.meaning model side inputs`, or the meaning
of a function.

```lean
register_core_entries sumcheck

noncomputable abbrev logic :
    WPMonad (Process (Effects M)) (Assert (Event M.Value)) (StopAssert (Event M.Value)) :=
  chargedMonad (interface .refused) (boundedEscape charge) (boundedEscape_antitone charge)
attribute [local instance] logic

@[spec] theorem round_wrong … :
    ⦃Wrong values arity rounds (remaining + 1) claim point⦄
      sumcheck.round.meaning M (Side.preimage [0, 1] verifier) (.cons () (.cons claim (.cons point .nil)))
    ⦃fun out => Wrong values arity rounds remaining (out.get (.there .here)) (out.get (.there (.there .here)));
      estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  open_core_definition
  construct_region
  …
```

The author writes:

- the reading: a local instance over `Zkc.Core.Transcript.interface secrets`, with a `Sampling`
  instance for the model when a probability is bounded. `interface .refused` serves a side
  that samples no secret, under both endpoints; a side that samples is read with `.fresh` under
  the exact reading. The model documentation states what each endpoint concludes.
- `open_core_definition` and `construct_region` for the definition being proved. A callee is
  never opened: the author states a law about its meaning, at the side the caller applies it
  at (`Side.preimage roleMap side`), registers it with `@[spec]`, and the constructor applies
  it at every `call` and `apply`. `register_core_entries package` makes the callee's meaning
  visible there.
- the laws of the model as hypotheses on named rows, the bound of each challenge site, and an
  invariant for each `repeat` and `loop` through `with_invariants`. The carried values of a
  `repeat` are one tuple; the invariant names them by position, `state.get (.there .here)`.
- the residual obligations. They name the received values, the replies and the model's rows
  applied to them. A model operation defined on a row, such as
  `add M a b := (M.pure (.of row) (.cons a (.cons b .nil))).get .here`, is definitionally the
  term in the obligation; `show` restates the obligation with the named operations.

The author writes no equation about the structure of a body. A law that a loop reuses states
the step of the loop's invariant: its ghost parameters, such as the rounds to go, are found by
unifying its postcondition with the invariant, so the postcondition must be the invariant's
shape. A fact about the state before a call that the postcondition needs must be part of that
shape; a law stated as a plain consequence leaves the two obligations of the rule of
consequence, which share no hypothesis.

| Client | Author input | Steps, build |
| --- | --- | --- |
| `Core.Schnorr` | none beyond the statement | 37 steps, 4.5 s |
| `Core.Sumcheck` | field laws and restricted multilinearity of the model, one root-counting lemma, the law of the final check, the doomed invariant and the budget | 6 + 41 + 38 + 41 + 36 steps, 21 s |
| `Core.Opening` | none beyond the statement | 78 steps, 12 s |
| `Core.Controls` | none beyond the statements | 57, 30 and 7 steps, 8 s |
| `Core.Regions` | two invariants on the length of the history | 6 s |

The previous import path took 424 steps and 29 s, with a raised heartbeat limit, for the
verifier of the Schnorr example. The steps here are one rule application for a pure row, for a
role outside the side and for an internal exchange, and a step followed by the primitive call
for an effect. The times are fresh elaboration of the test module with built dependencies.

## Complete clients and reusable inputs

All examples below are under `Zkc.Tests.Protocol.Construction`.

| Client | Author/library mathematics and configuration | Common construction supplies |
| --- | --- | --- |
| `AdaptiveSource` | Existing prediction bound, remaining-round invariant, honesty premise, fixed soundness/completeness requests | Nested finite loops, actual callback inputs, sequencing and complete upper/lower source bounds |
| `GuardedAdaptive` | Admission guard and honest admission premise | Selected execution and unreachable refusal behavior; reuse of the complete adaptive law |
| `StatefulOracle` | Word representation, checked decoder, acceptance formula and proximity premise | Two publications, sample, reply-dependent second position, actual read/decode calls and stop preservation |
| `OracleInstallation` | Audit-state projection and whole-outcome map law | Existing installation and upper/lower root assembly with the same source mathematics |
| `SharedChallengeSource` | Boolean recovery law, counter meaning and intended observation | Multi-result routing and two different query arguments using one named theorem |

The proposition-valued clients are under `Zkc.Tests.Protocol.Construction.Readings`:

| Client | Author/library mathematics | Endpoint |
| --- | --- | --- |
| `Sumcheck` | Multilinearity of the reference, one root-counting lemma per round, wrong-claim invariant and per-round budget | Fiat–Shamir `(queries + count) / \|F\|`; interactive `count / \|F\|` |
| `Extraction` | The same lemma; invariant "agreement implies the statement of the received handle" | Fiat–Shamir, at "accepted and the returned handle's statement fails": soundness for a prover-chosen statement sent in the clear (identity extractor), not extraction from a commitment |
| `ExactThreeMove` | None beyond the reached history and returned value | Exact characterization of every returning run; bounded evidence for every charge |
| `SetupOpening` | Root counting for the exponent equation at the setup secret | Interactive `(n + 1) / \|F\|` in the ideal algebraic game (representations fixed before the secret, no published reference string), randomized and fixed-message forms |
| `Controls` | Counterexamples and one total interface | Refuted acceptance, required stop, the refuted obligation of a forgetful invariant and unpaid query; refusal and failed decoding accepted as stops; every run returns over a total interface |

`Regressions` checks the nested-condition split, the equation-candidate filter, decided
conditions, the two registrations of a structural equation, premises decided by evaluation,
definitions registered for evaluation and instance parameters of a law.

`SharedChallengeSource` was held out until the constructor and rules were frozen. The first
reply recovers the shared private bit; the second query then accepts with probability one.
Both directions close on the existing initial distribution. Requiring both replies to accept
is a different, false request, and is explicitly rejected. Reusing a provider does not reset
its state or infer independent challenges.

The first author writes laws and the fixed evidence record. A second call of an installed
helper needs no new mathematical theorem. A new component author still supplies genuinely new
mathematics, representation/admissibility premises and operation meaning; the shared constructor
handles supported structural composition. An entirely new operation constructor needs a common
proved specification before this authoring guarantee applies.

## Actual-source clients

`Zkc.Tests.Verification.Construction` exercises the native
`compiler/test/fixtures/structured-source/actual-calls.zkc` and `scoped-control.zkc` exports.
The source-admission check regenerates and compares their literal quotations with the current
compiler output; checking an unrelated hand-authored Region cannot satisfy that gate.

| Client | Author input | Constructed connection |
| --- | --- | --- |
| `ActualCalls` | Difference formula over the selected field interpretation | The same named law at two actual calls with opposite operand order |
| `SharedServices` | Counter provider, shared state and history observation | Selected execution, two aliased or distinct handles, reached stop and ordered effects |
| `FiniteLoop` | Remaining-sequence invariant and replacement formula | Actual finite loop, captured replacement, arbitrary runtime count including zero |
| `AssociationControls` | Addition law for the changed dependency | Correct rebinding under unchanged lookup metadata and caller body |
| `SemanticControls` | Counterexamples to incorrect result/history requests | Kernel-checked rejection of stale dependencies, operand/handle swaps and ignored stops |
| `LawRequests` | Fixed actual-body proposition and a proved library law | Typed selection, direct proof, explicit wrong-law refusal and open required coverage |

The shared-state example uses integer carriers to isolate service behavior. It does not establish
a production field instance or protocol security. The generic arithmetic example quantifies over
the admitted domain model. Public source law/ghost syntax is not required for these Lean library
laws; its frontend formation and coverage remain a separate language task.

## Choices and module ordering

`Choices/Templates` defines the fixed scale type and parameterized mathematical obligations.
`Choices/Companions` imports these templates and supplies values and laws. `Choices/Assembly`
selects the value first, then resolves its instantiated propositions and applies the law to
the actual `AdaptiveSource.rounds`. Templates never import their companions or assembly.

The existing `zkc_companion` resolver checks each selected term against a fixed expected type.
A missing, ill-typed or explicitly invalid selection does not silently choose another meaning.
`report_construction_goals` preserves the actual proposition, complete local context and its
constant dependencies. Model-only diagnostics contain no fabricated native source identity.
Reports describe open authoring work; only checked proof/evidence assembly establishes a claim.

## Sharing and cost checks

Build `Zkc.Tests.Protocol.Construction.SharingAudit` in the protocol package. The audit checks
stored proof bodies, including owner-qualified auxiliary proofs. Flat call counts 1/2/4/8 must
contain exactly that many references to one helper theorem. Nested definitions must contain
two references to the preceding theorem. Counts 0/1/8/1024 must contain one reference to the
same parameterized finite-loop law. Both held-out source bounds must reference the query law
twice. Types and mere imports are not counted as proof applications.

The distinct-expression regression limits have headroom above measured values. Counting the
fully expanded expression tree instead gives much larger values, since repeated types and
source contexts lose sharing. Neither count alone measures kernel time or serialized size.
The audit does not assert an asymptotic complexity theorem.

After that build, measure fresh proof elaboration against cached dependencies:

```sh
python3 lean/checks/check_source_construction_cost.py \
  --records build/source-construction-cost --repetitions 3
```

The driver never builds dependencies. It records source hashes, actual commands, elapsed time,
peak RSS, the serialized `.olean` artifact group, named-theorem references, expanded and distinct
expression counts, elaboration time and synchronous declaration-check time. Three fresh kernel
rechecks of each stored proof are separate measurements. Setup/import time belongs only to the
whole-process measurement. A timeout or resource failure is an incomplete experiment.

These are warm-dependency measurements with fresh proof modules. The driver does not evict OS
caches or claim cold-start results. They establish a bounded regression baseline, not a speedup
over a different proof architecture. Proof sharing never discounts executed service calls.

## Scope and next boundary

The path covers quantitative and proposition-valued construction over model Regions, the
admitted Boolean-control original-source profile and imported core definitions at literal
sides. The proposition-valued readings are exercised on model verifiers and on the sides of
three imported core packages, of which the Sumcheck verifier reaches both endpoints. A core
side at a symbolic side, a partial row whose law is a hypothesis on the model, and `match` are
not covered. The laws of the Sumcheck client are hypotheses on the model; the model that
restricts a table by folding satisfies them, and at that model the bound has no hypothesis. The
opening client characterizes runs and states no binding property. The setup-shaped client is the ideal
algebraic interpretation: the group, the pairing, the algebraic adversary and the reduction
from the group game are not modelled.

The readings bound acceptance and do not show that an execution returns: refusal and failed
decoding are accepted stops (`Controls` exhibits both). Completeness over an interface that
admits every operation follows from an exact triple with false stop assertions
(`ZkcSecurity.Interactive.returns_of_exact`); an outcome-aware adequacy theorem for other
interfaces is not provided. The interactive endpoint's strategies see every earlier raw draw; a
secret setup value is a property of the strategy a statement instantiates, not of the
endpoint. Existing exact derivations remain appropriate for exact correspondence;
installed extraction and simulation laws retain their meanings. Multi-alternative protocol
variants are still explicitly refused by this formal profile.

Generated controllers next need one whole execution theorem covering phases, saved continuations,
captures, ordered answers, completion and capacity. Complete protocol applications then instantiate
that theorem and supply their mathematical reductions. These are separate acceptance boundaries;
actual-source installation alone does not establish a compiled Sumcheck or FRI security endpoint.
