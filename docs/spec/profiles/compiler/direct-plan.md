# Direct logical plans

This profile realizes finite typed control using logical values. It defines a
reference evaluator and a source-relative checking rule, together with the
external request and candidate formats for that rule.

## Typed plans

Fix a [language](../../language/programs.md#language-signatures) `L`, context `Γ`
and result sort `τ`. A plan has one of these constructors:

| Plan | Premises |
|---|---|
| `yield v` | `v : Var Γ τ` |
| `stop r` | `r : Stop` |
| `execute o args next` | `args : Operands Γ (L.arguments o)`; `next : Plan (L.result o :: Γ) τ` |
| `select c yes no` | `c : Var Γ L.condition`; `yes, no : Plan Γ τ` |
| `loop n initial body next` | `n : Nat`; some sort `α`; `initial : Var Γ α`; `body : Plan (α :: Γ) α`; `next : Plan (α :: Γ) τ` |

References and operands have the common typed interpretation. A loop retains
the original enclosing environment, extends it by the current accumulator for
each body execution, and extends it by the final accumulator for the suffix.
There is no implicit loop-index slot or mutation of lexical captures.

## Evaluation

Fix an operation interpretation `M`, signature `Σ`, handler
`h : Handler Σ S E`, environment `η` and initial state `s`. Plan evaluation
has type `evaluatePlan M h q η s : Execution S E (M.Value τ)`. In its defining
equations below, `R q η s` abbreviates `evaluatePlan M h q η s` with `M, h`
fixed. For `f : A → S → Execution S E A`, define:

```text
loopRun f 0 a s       = (returned a, s, [])
loopRun f (n + 1) a s = follow (f a s) (fun b t => loopRun f n b t)
```

Evaluation uses [complete-result sequencing](../../core/execution.md#sequencing):

```text
R (yield v) η s = (returned (η v), s, [])
R (stop r) η s  = (stopped r, s, [])

R (execute o args q) η s =
  follow (run h (M.operation o (eval η args)) s)
    (fun a t => R q (η.push a) t)

R (select c p q) η s =
  if M.condition (η c) then R p η s else R q η s

R (loop n a p q) η s =
  follow (loopRun (fun x t => R p (η.push x) t) n (η a) s)
    (fun x t => R q (η.push x) t).
```

A stopped operation or iteration retains its state and event prefix and skips
the remaining computation. A zero-count loop executes only its suffix on the
initial accumulator. Plan evaluation does not perform implicit codec, storage
allocation or native kernel actions.

## Direct lowering

Direct lowering maps source constructors structurally:

```text
lower (ret v)                 = yield v
lower (stop r)                = stop r
lower (letOp o args q)        = execute o args (lower q)
lower (branch c p q)          = select c (lower p) (lower q)
lower (iterate n a body next) = loop n a (lower body) (lower next).
```

For every typed source `p`, interpretation `M`, handler `h`, environment `η`
and initial state `s`, lowering preserves the complete execution:

```text
evaluatePlan M h (lower p) η s = run h (⟦p⟧M η) s.
```

This equality requires the same actual meanings and operands on both sides.
It has no successful-return or pure-handler premise. It includes all stopped
outcomes, residual states and ordered events. Source and plan are distinct
subjects of the judgment; the common specification does not require other
realizations to maintain two isomorphic representations.

## Checked plans

Plan erasure maps `yield`, `stop`, `execute`, `select`, and `loop` to the
corresponding [raw control](../../language/programs.md#raw-formation), replacing
typed references by indices and retaining every descriptor, argument position,
count and accumulator sort. Typed plan decoding under `Γ, τ` follows the same
formation rules as the source, including both branch arms and a zero-count
loop body. It satisfies `decodePlan Γ τ (erase q) = ok q` for every typed plan.

A checked plan for retained typed source `p` and actual raw candidate `c`
contains:

```text
plan    : Plan Γ τ
decoded : decodePlan Γ τ c = ok plan
correct : ∀ Σ M S E h η s,
            evaluatePlan M h plan η s = run h (⟦p⟧M η) s.
```

All variables in `correct` have the compatible types from evaluation. The
candidate does not supply an alternative interpretation to justify itself.
Determinism of decoding ensures that any other plan decoded from this same
candidate under `Γ, τ` equals the retained plan.

The selected direct checker assumes decidable equality of sorts and operation
descriptors. It succeeds exactly when:

```text
c = erase (lower p).
```

On success it retains `lower p` and the preceding decoding and preservation
laws. A mismatch returns no checked plan. This rule does not decide semantic
equivalence: even an equivalent changed candidate needs a rule that establishes
its own preservation judgment.

The source's [uniform call bound](../../language/programs.md#structural-call-bounds)
transfers to the actual instrumented checked plan under the bound's operation
premises. With [phase admission](finite-phases.md#checked-phase-admission),
the same source, interpretation, summary laws, handler, environment and covered
initial phase also give call permission and the permitted returned phase.
Direct-plan checking alone does not supply those additional premises.

## Format parameters

The external format is parameterized by a consumer-selected language, a type
descriptor codec `CT`, an operation descriptor codec `CO`, and a natural
control-depth limit `d`. Each codec has functions:

```text
encode : X → Json
decode : Json → Except FormatError X.
```

For `CT`, `X = L.Ty`; for `CO`, `X = L.Op`. These are data interfaces, with
no inverse law implicit in the pair. A concrete vocabulary defines its
descriptors and decoding errors and supplies any claimed round-trip or native
resolution law. The selected consumer interpretation gives decoded descriptors
their meaning. The control format does not install new meanings from strings.

In the grammars below, quoted labels are exact JSON strings; `String` denotes a
JSON string; `Nat` denotes a JSON numeric value with nonnegative integer
mantissa and exponent zero. `Type` and `Op` denote JSON values accepted by
`CT.decode` and `CO.decode`. `List(X)` denotes a JSON array of zero or more
`X` values, preserving order and duplicates unless later validation rejects
them. Each displayed constructor array has exactly the displayed arity.
Only the selected vocabulary codecs can introduce additional descriptor shapes.

## Control grammar

The same external raw-control grammar is used for source and direct plan:

```text
Stop ::= "reject" | "abort" | "exhausted" | "incomplete" | "refused"

Control ::= ["return", Nat]
          | ["stop", Stop]
          | ["apply", Op, List(Nat), Control]
          | ["if", Nat, Control, Control]
          | ["repeat", Nat, Type, Nat, Control, Control].
```

The fields of `apply` are the operation, ordered operand indices and suffix.
The fields of `if` are the condition index, yes arm and no arm. The fields of
`repeat` are the count, accumulator sort, initial index, body and suffix.
Indices are zero-based in the constructor's actual context; decoding numbers
does not establish that those indices exist or have the required sorts.

At depth zero, decoding any control returns `depth-limit`. At depth `k + 1`,
the decoder checks the current array and decodes each child control at depth
`k`. Thus a terminal needs depth at least one; a parent needs one more than the
maximum depth of its children. Siblings each receive `k`, rather than sharing
a consumable counter. Envelope arrays and type/operation descriptor nesting
are not charged as control nodes; those codecs require their own capacity
policy where applicable.

*Example (informative).* `["repeat", 0, T, 0, ["return", 0], ["return", 0]]`
requires control depth at least two. It forms only if `T` decodes to the
accumulator sort and the initial reference is valid under the retained context.
The zero count does not excuse an invalid body.

## Envelope grammar

References, input declarations, contexts and claims have these exact shapes:

```text
Reference   ::= [String, String]
Access      ::= ["shared"] | ["private", String]
Kind        ::= "argument" | "capture"
Declaration ::= [String, Type, Access, Kind]
Context     ::= [String, List(Declaration), Type, List(Reference)]
Claim       ::= [String, String, String]

Request ::= ["zkc-request", 1, "finite-source-1",
             Context, List(Reference), Control]

Candidate ::= ["zkc-plan", Nat, String, List(String), String, String,
               Claim, Context, List(Reference), Control].
```

A reference is `(name, revision)`. A declaration is `(name, type, access,
kind)`. A context is `(role, orderedInputs, resultType, dependencies)`. A claim
is `(relation, observation, scope)`. The request's final fields are its
context, permitted requirements and retained raw source. The candidate's
fields, in order after its tag, are format version, semantic version,
mandatory capabilities, realization, rule, claim, context, requirements and
raw body.

No extra fields are ignored. The envelope contains declarations and source
descriptors, with no separate payload field for actual argument or capture
values. Runtime [input binding](../source/named-inputs.md#exact-ordered-binding)
is a distinct step. A vocabulary can still encode a specialized value in an
operation descriptor; any resulting disclosure is subject to the artifact's
[release contract](../../realization/artifacts.md#lifecycle-and-release).

The request decoder requires version `1` and semantics `finite-source-1`.
A well-typed mismatch of either is `invalid-shape`. The candidate decoder
retains its numeric version and string semantic version; unsupported values
are rejected subsequently by the metadata checker. This difference in stage
and diagnostic is part of this format.

## Context validity and accepted metadata

Context equality is structural equality after decoding. It includes input and
dependency list order, names, sorts, access, kind, role and result sort.
Dependency order is not normalized as a set. A valid context has:

- a nonempty role;
- nonempty, pairwise distinct input names;
- each input either shared or private to that exact role;
- pairwise distinct dependency names, with every name and revision nonempty.

The metadata checker applies the following tests in order, returning the first
listed error whose condition fails:

| Required condition | Error code |
|---|---|
| Candidate format is `1` | `unsupported-format-version` |
| Candidate semantics is `finite-source-1` | `unsupported-semantics-version` |
| Candidate capabilities are `[]` | `unsupported-capability` |
| Realization is `direct-logical-plan` | `unsupported-realization` |
| Rule is `direct-lowering` | `unsupported-rule` |
| Claim is `["equality", "logical-outcome-state-events", "all-inputs-and-handlers"]` | `unsupported-claim` |
| Candidate context equals retained request context | `context-mismatch` |
| Retained request context is valid | `invalid-context` |
| Every candidate requirement occurs in the request's permitted list | `unapproved-requirement` |
| Candidate requirements are `[]` | `unsupported-requirement` |

Reference membership compares both name and revision. A permitted requirement
is still unsupported by this rule. The permitted list itself is decoded but
is not subject to the context dependency checks: unused empty or repeated
references confer no authority and introduce no premise into an accepted
direct artifact. A later rule that consumes requirements must define its
disposition and validation rather than inherit a meaning from that unused list.

## Artifact checking and execution binding

After metadata succeeds, the checker elaborates the retained request's source
under the context's ordered input sorts and result sort. Any formation failure
at this stage becomes `malformed-source`. It then runs the direct checker on
that typed source and the actual candidate body. A mismatch is `unchecked-plan`,
including a candidate with invalid typed references. Candidate format decoding
has already occurred; this rule does not separately classify all candidate
typing failures.

Success retains the metadata equation, the elaborated source and its exact
elaboration equation, and a checked plan for the actual raw body. Admission
does not replace the consumer request with a producer copy. Execution uses the
retained checked object, resolved interpretation, actual bound inputs and
initial state under the [custody contract](../../realization/artifacts.md#exact-retained-content).

The profile introduces no cryptographic premise, provider resolver, native-code
claim or canonical byte identity. An implementation using native providers or
generated code supplies the corresponding realization and process contracts.
Adding a new rule, mandatory facility or realization requires an explicit
extension with its meanings and checking laws.

## Text parsing and limits

The text parser takes a natural byte limit `B`. It first refuses a string whose
UTF-8 encoding exceeds `B`. It then scans numeric spellings outside quoted
strings, respecting escaped characters inside strings. A consecutive run of
more than 1,024 decimal digits is `number-limit`. An `e`, `E` or `.` immediately
after a nonempty digit run is `expected-natural`. These checks precede JSON
parsing and apply throughout the document, including vocabulary descriptors.
They do not validate JSON by themselves. The subsequent JSON parser requires
one complete JSON value and maps its syntax failures to `invalid-json`.

Numeric fields are then checked against the `Nat` JSON-value definition above.
With this text boundary, integer spelling `-0` is accepted as zero after
parsing. Negative nonzero integers fail the natural check; fractional and
exponent spellings fail the earlier numeric scan, even if they denote an
integer. Leading-zero spelling `01` is invalid JSON. Whitespace and equivalent
JSON string escapes are not canonicalized to a prescribed byte representation.

The format errors are:

| Code | Meaning |
|---|---|
| `invalid-json` | Text fails the selected JSON parser after the preliminary checks |
| `invalid-shape` | Wrong array shape, tag, kind or well-typed request version |
| `expected-natural` | Disallowed numeric spelling or a non-natural JSON value at a natural field |
| `expected-string` | A string field contains another JSON kind |
| `unknown-type`, `unknown-operation` | Selected vocabulary decoding refuses a descriptor with that error |
| `unknown-stop` | The stop field is not one of the five specified strings |
| `byte-limit`, `depth-limit`, `number-limit` | The corresponding decoding capacity is exceeded |

Structured decoding processes fields and list entries in their displayed order,
propagating a child codec's error. Request decoding obtains both its numeric
version and semantic string before testing their supported values. The numeric
scanner can therefore reject text before a later grammar-specific diagnostic,
and a malformed version field need not receive a version-support error.

The mathematical grammar has unbounded naturals and finite syntax. Available
byte, control-depth, vocabulary-depth and execution-work capacity are distinct
implementation policies. In particular, a low control-depth limit is not a
bound on loop iterations or total interpreter work.

*Note (informative).* The [source-plan example's capacities](../../../compiler/source-plan.md#example-capacity-and-input-policy)
instantiate the resource policies separately from this format. Its file reader,
work measure and fixed invocation values are described there.

## Phase-certificate sidecar

The [finite phase analysis](finite-phases.md#certificates) can
receive a separately encoded certificate. Fix a phase codec `CP` and a
certificate depth limit `dc`. Its exact JSON grammar is:

```text
Certificate ::= ["terminal"]
              | ["next", Certificate]
              | ["branch", Certificate, Certificate]
              | ["loop", List(Phase), Certificate, Certificate]
              | ["bind", Certificate, Certificate].
```

Here `Phase` is a JSON value accepted by `CP.decode`. A loop contains its
invariant cover, body certificate and suffix certificate in that order. The
binding form contains the body and shared suffix certificates. It applies to
compact regions; a tree program rejects a binding certificate at that position.
The encoder preserves invariant list order and duplicates. At depth zero the
decoder returns `depth-limit`; at depth `k + 1` each child certificate is
decoded at `k`. Phase values use the phase codec's own domain and limits.
Unknown tags or arities are `invalid-shape`; phase-codec errors propagate.

The source, policy, entry cover and permitted return cover are supplied
separately. Decoding the sidecar establishes only certificate syntax. The
phase checker must accept it against those actual operands, and use additionally
requires the interpretation's policy realization and initial coverage laws.
The sidecar is not a field of version `1`, a new direct-lowering rule, or
evidence that the direct checker establishes phase admission by itself.

## Compact region profile

The separately selected `region-source-1` profile adds explicit computation
binding. It uses the same language, values, operation interpretations and
complete-execution semantics. It does not extend the accepted grammar of
`finite-source-1` or alter a previously issued request's meaning.

Its intrinsically typed source, `Region L Γ τ`, contains the five structured
source constructors and this additional constructor:

```text
bind body next : Region L Γ τ
  body : Region L Γ α
  next : Region L (α :: Γ) τ.
```

`body` receives the original environment. On normal return, `next` receives
that returned value followed by the original environment. Body-local values do
not escape implicitly. There is no initial value or loop accumulator. The
complete evaluation equation is:

```text
R (bind body next) η s =
  follow (R body η s) (fun value t => R next (η.push value) t).
```

A stopped body retains its actual post-state and event prefix and skips `next`.
The suffix is stored once regardless of the number of returning branches in
`body`. Capture renaming permits selection, reordering and aliasing subject to
the same typed-reference rules.

The exact external grammar `RegionControl` has the five `Control` constructors
with every child replaced by `RegionControl`, plus:

```text
RegionControl ::= ... | ["bind", Type, RegionControl, RegionControl].
```

The new fields are result sort, body and suffix. Both children consume one
control-depth level and are formed under the respective contexts above.
Malformed dormant bodies or suffixes fail formation even when execution would
stop before reaching them.

The request envelope substitutes `"region-source-1"` and `RegionControl` for
the old semantic version and body. The candidate envelope keeps its fields and
uses `RegionControl`; metadata checking requires exactly `"region-source-1"`.
All other metadata conditions, error precedence, text parsing and custody
requirements remain those specified above.

The direct region checker elaborates the retained source, requires its typed
erasure to equal the actual candidate body, and retains both decoding
equations. Source and candidate may share one typed carrier; no second
isomorphic mathematical plan type is required. The resulting theorem compares
complete execution for every interpretation, handler, environment and state.
An equivalent but syntactically changed candidate is still `unchecked-plan`.

Reference expansion maps `bind body next` to source sequencing of their
expansions. Its denotation equals the region's denotation. Expansion can
replicate suffixes, so compact decoding, checking and execution must operate on
the region directly. The expansion theorem provides a semantic bridge; it does
not prescribe compiler implementation or certificate size.

Under uniform per-operation call bounds, binding adds the body and suffix
bounds. Branch bounds take the maximum; public iteration multiplies its body
bound. These are semantic call bounds, separate from native allocation and
interpreter-work policies.

The phase-certificate grammar includes compact binding. The maintained checker
and its conformance/return-cover theorem traverse regions directly, sharing the
same algorithm with tree programs. Native transport, changed-candidate rules and
physical realization require their actual consumer connections. The installed
table consumer supplies local phase transport and the
[physical scalar/folding application](finite-phases.md#physical-scalar-application);
this does not extend the exact direct-lowering rule defined here.
The [implementation and design analysis](../../../compiler/regions.md) records
the broader remaining joins and the proof declarations.
