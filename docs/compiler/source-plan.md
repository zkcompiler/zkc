# Finite source and direct logical plan

The maintained source and checker component accepts finite typed source, checks a direct logical plan against an
independently retained request, and provides an example executable. It implements
the initial source-to-plan portion of the [roadmap](../roadmap.md). The
[native direct-plan route](../runtime/reference-execution.md) executes the actual
export in Rust under explicit native/backend trust.

## 1. Representation and meaning

The [typed program specification](../spec/language/programs.md),
[direct plan profile](../spec/profiles/compiler/direct-plan.md) and [common input specification](../spec/language/inputs.md)
own these contracts. This section describes the maintained direct reference
profile; its duplicate source/plan datatypes are not a mandatory compiler IR hierarchy.

[`Language`](../../formal/Zkc/Source/Program.lean) supplies type and operation
descriptors, argument/result signatures and a condition type. Generic contexts,
control, lowering and checking do not dispatch on protocol or field names.
An `Interpretation` supplies actual mathematical values and operation meanings;
each operation may denote an effectful `PIR.Proc`. A name does not establish purity.

The source has return, stop, operation binding, branch and public finite
iteration. References use typed de Bruijn positions: zero is the newest binding.
An operation's result is prepended to the context. A loop body receives its
accumulator followed by the enclosing context; its continuation receives the
final accumulator in that same position. There is no implicit loop-index input.
Both branches and the entire loop body must elaborate, including dormant code.

[`InputBinding`](../../formal/Zkc/Source/InputBinding.lean) keeps ordered
declarations separate from runtime values. It checks names, types, role access,
duplicates and every required slot before constructing the total environment.
Arguments and captures retain distinct metadata. It does not establish the
authenticity, secrecy or external provenance of a supplied value.

The direct [`Plan`](../../formal/Zkc/Compiler/Plan.lean) has its own typed
constructors and execution function. It carries logical values and ordered
control, without selecting buffers, allocation or native kernels. Its operation
dispatch uses the same mathematical interpretation as the source. A stopped
call retains its resulting state and events and skips the remaining continuation.

## 2. What is proved

The later [transformation interface](../../formal/Zkc/Compiler/Transformation.lean)
also checks a changed source under a selected
[execution refinement](../../formal/Zkc/Compiler/Refinement.lean).
[Horner](../../formal/Zkc/Compiler/Arithmetic/Horner.lean) is its first actual rule:
it expands quadratic evaluation into explicit additions and multiplications,
preserving input positions, public control and complete effectful continuations
under semiring laws. The candidate must equal the plan computed by that proved
rule from the actual source. Arbitrary operation meanings cannot inherit this law.
The native artifact format still selects the direct rule; a serialized
transformation consumer must bind its rule, certificate codec and interpretation.

| Law | Meaning |
|---|---|
| `Program.denote_rename` | Structural capture/variable renaming agrees with the corresponding environment map, through branches and loop regions |
| `Program.elaborate_erase` | Erasing any typed program and elaborating under its original context recovers that program |
| `Plan.decode_erase` | The analogous recovery law for a typed direct plan |
| `lower_correct` | Direct-plan execution equals source execution for every interpretation, handler, input environment and initial state |
| `CheckedPlan.decoded_unique` | The accepted typed plan is the plan decoded from the candidate body |
| `bindInputs_exact` | Successful binding reifies to the exact ordered supplied names, sorts and values |
| `CheckedPlan.calls_bounded` | The source bound limits actual checked-plan invocations, including a stopping call, under uniform operation bounds |
| `Program.denote_within` | A public interface-call bound follows from uniform bounds on the interpreted operations |

The preservation equality includes the outcome, stopped reason, final state and
ordered events. It is stronger than comparing successful returned values and
does not assume one particular secret input. It is a representation theorem;
this implementation claims no optimization or performance gain.

Intrinsic typing supplies local scope/type correctness. Interpretation into the
existing effect tree and induction supply compositional execution preservation.
Public call bounds use conservative branch maxima and the existing sequencing
and repetition laws. These are concrete applications of scoped/dependent
syntax, algebraic effects and compiler correctness; see the [theory map](../theory.md).
[Phase conformance](phase-admission.md) now has a separate checked analysis and
plan-preservation join. Cryptographic properties, arbitrary substitution and
native representation correspondence remain separate obligations.

## 3. Checking and the consumer boundary

[`Request`](../../formal/Zkc/Compiler/Artifact.lean) contains the retained source,
ordered input schema, role, result type, definition references and permitted
requirements. The producer supplies a `Candidate` containing the final body and
its metadata. The consumer must retain the request independently and resolve
its definitions to the chosen codecs, signatures and interpretation.

The current checker supports exactly:

- Format version `1`, semantics `finite-source-1`, no additional mandatory capabilities.
- Realization `direct-logical-plan` and rule `direct-lowering`.
- Equality of complete logical outcome/state/events for all inputs and handlers.
- Exact context/dependency matching and no introduced requirements.

An unapproved requirement is rejected. Even a permitted extra requirement is
currently unsupported: this direct rule has no premise-discharge mechanism and
introduces none. Unsupported claims, versions, rules, capabilities and generated
code cannot inherit a logical-plan result.

`CheckedArtifact` retains successful metadata checking, actual source elaboration
and `CheckedPlan` evidence. The lower-level checker compares the candidate with
the exact erased direct lowering; it does not yet recognize equivalent optimized
programs. Refusal to match is not a proof that another plan is incorrect.

Definition references identify the consumer's intended meanings. Merely matching
their strings does not prove an operation contract or backend implementation.
The example executable resolves one exact versioned vocabulary; it rejects a
changed definition even if both input files contain that changed reference.

## 4. External format

The [direct profile](../spec/profiles/compiler/direct-plan.md#format-parameters) owns the
exact grammar, version checks, decoder limits and diagnostics summarized here.
[`Source.Format`](../../formal/Zkc/Source/Format.lean) and
[`ArtifactFormat`](../../formal/Zkc/Compiler/ArtifactFormat.lean) implement tagged
JSON arrays with exact arity. Objects are not accepted as records, so duplicate
keys cannot override an obligation. The control grammar is:

```text
["return", index]
["stop", "reject" | "abort" | "exhausted" | "incomplete" | "refused"]
["apply", operation, [operand, ...], continuation]
["if", condition, yes, no]
["repeat", count, accumulatorType, initial, body, continuation]
```

Type and operation spellings come from the selected vocabulary. Naturals use
integer tokens decoded as nonnegative JSON values (including `-0` as zero);
decimal and scientific notation are rejected before
the JSON parser can expand exponents. Decoder policy limits numeric tokens to
1,024 digits. The example additionally limits files to 1 MiB and program depth
to 256. These are implementation capacities, not mathematical natural bounds.

A request envelope is `["zkc-request", format, semantics, context, permitted,
source]`. A candidate is `["zkc-plan", format, semantics, capabilities, realization,
rule, claim, context, requirements, body]`. Context is `[role, inputs, resultType,
dependencies]`; each input is `[name, type, access, kind]`. Access is `["shared"]`
or `["private", role]`, and kind is `"argument"` or `"capture"`. Definition
references are `[name, revision]`. Claim is `[relation, observation, scope]`.

The source and direct plan share this first control grammar, while typed
constructors and evaluators remain separate. This is an experimental logical
format, not the legacy artifact ABI or the future native-plan layout. There is
no hash identity or canonical-byte theorem; checking compares decoded data.

## 5. Implemented example and assurance

### Example capacity and input policy

The maintained example uses one MiB per file, control depth 256 and the
format's 1,024-digit numeric limit. Its file reader requires valid UTF-8 and
reports `invalid-utf8` for invalid byte sequences. Before logical execution,
it enforces work bound 100,000 using:

```text
work(return _) = work(stop _) = 1
work(apply _ _ next)          = 1 + work(next)
work(if _ yes no)             = 1 + max(work(yes), work(no))
work(repeat n _ _ body next)  = 1 + n * (1 + work(body)) + work(next).
```

The `execution-work-limit` and `unresolved-dependency` checks are example-tool
policies, separate from the generic artifact rule. The work measure counts
control evaluation; it does not bound arbitrary interpreted operation cost.

### Execution and evidence

[`SourcePlanExample`](../../formal/Examples/SourcePlan.lean) uses actual
`ZMod 5` and `ZMod 7` values, a natural accumulator, ordered private captures,
branching and a stateful record call. Its generic compiler requires no knowledge
of these operations. The executable reads external source and plan files,
checks them, binds the example's values and interprets the accepted logical plan.

With the loop enabled and initial counter one, it returns `(2, 4, 4)`, state
three and events `[1, 2, 3]`. Counter zero aborts on the first call with state
one and events `[0]`; disabling the loop rejects with unchanged state and no
events.

Lean checks the generic preservation and decoding propositions. The compiled
checker executes that proved decision procedure after parsing; its JSON output
is a runtime result, not a newly serialized kernel proof. The JSON parser, file
handling, Lean code generator/runtime and vocabulary resolution retain their
implementation trust. Runtime controls do not discharge those assumptions.
The [native checked-plan runtime](../runtime/reference-execution.md) connects to this
boundary. Its implementation checks do not establish native
value/state/resource correspondence; that remains a separate proof obligation.
