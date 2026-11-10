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

## Complete clients and reusable inputs

All examples below are under `Zkc.Tests.Protocol.Construction`.

| Client | Author/library mathematics and configuration | Common construction supplies |
| --- | --- | --- |
| `AdaptiveSource` | Existing prediction bound, remaining-round invariant, honesty premise, fixed soundness/completeness requests | Nested finite loops, actual callback inputs, sequencing and complete upper/lower source bounds |
| `GuardedAdaptive` | Admission guard and honest admission premise | Selected execution and unreachable refusal behavior; reuse of the complete adaptive law |
| `StatefulOracle` | Word representation, checked decoder, acceptance formula and proximity premise | Two publications, sample, reply-dependent second position, actual read/decode calls and stop preservation |
| `OracleInstallation` | Audit-state projection and whole-outcome map law | Existing installation and upper/lower root assembly with the same source mathematics |
| `SharedChallengeSource` | Boolean recovery law, counter meaning and intended observation | Multi-result routing and two different query arguments using one named theorem |

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

The path covers quantitative construction over model Regions and the admitted Boolean-control
original-source profile. Existing exact derivations remain appropriate for exact correspondence;
installed extraction and simulation laws retain their meanings. Multi-alternative protocol
variants are still explicitly refused by this formal profile.

Generated controllers next need one whole execution theorem covering phases, saved continuations,
captures, ordered answers, completion and capacity. Complete protocol applications then instantiate
that theorem and supply their mathematical reductions. These are separate acceptance boundaries;
actual-source installation alone does not establish a compiled Sumcheck or FRI security endpoint.
