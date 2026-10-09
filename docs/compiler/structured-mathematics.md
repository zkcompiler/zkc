# Structured mathematics

This design is implemented for the closed subset specified in
[structured native mathematics](../spec/profiles/compiler/structured-mathematics.md).
That profile owns exact signatures, limits, codecs and checked compilation;
[status](../status.md#foundation-capability-map) records coverage and
the [roadmap](../roadmap.md) owns remaining work.

## One program, retained mathematical meaning

Keep one mutable mathematical program in MLIR SSA and the existing profiles:

```text
protocol    : mathematics + role interfaces + ordered actions + specifications
participant : retained mathematics + actual role-local values and actions
exec        : executable algorithms and representation bindings
physical    : selected kernels, storage, codecs and runtime contracts
```

Profiles constrain mixed-dialect programs; they are not four new dialects.
Projection selects participant components without erasing mathematical structure.
Math lowering happens after the analyses and transformations that need it.
Availability, degree, relation obligations and schedules are derived views of
this program. They do not own another independently editable expression graph.

Mathematical dependencies remain available for projection, analysis and
execution through MLIR operations and interfaces, alongside explicit received
values, stateful queries, stops and resource failures.
[Native proof compilation](native-proofs.md) consumes this structure to derive
transcripts. Algebraic security analyses and parallel execution require their
own consumers and correctness conditions.

| Owner | Responsibility in this extension |
|---|---|
| `algebra` | Scalar field/group meaning, canonical field literals, finite field-array formation and total arithmetic |
| `poly` | Formal polynomial constructors, ring recipes and observations, ordered axes, domains and degree transfer |
| `data` | Canonical index/dimension observations and copyable product/sum operations |
| Standard tensor types and selected operations | Static/dynamic immutable finite data; no implicit polynomial interpretation |
| `protocol` | Roles, sends/receives, queries, guards and actual component boundaries |
| `relation` and protocol binding machinery | Interpreted requirements and residuals associated with actual boundaries |
| `local` and `plan` | Executable algorithms, representation selection, state, storage and failure contracts |

The Data dialect owns total data operations. `protocol.repeat` owns
[structured iteration](../spec/profiles/compiler/structured-iteration.md),
including role availability and carried state. General finite data has no
implicit polynomial interpretation.

## Mathematical objects and finite data

Prefer named polynomial SSA over a declared field and ordered variables. The
carrier is `!poly.polynomial<"F", n>`, denoting
`F[X0, ..., X(n-1)]`. It is distinct from normalized concrete univariate objects and retains
explicit meaning and sharing, with no forced dense expansion.

The initial vocabulary is closed. These are semantic names, not parser syntax:

```text
constructors:
  constant(field, arity, scalar)
  from_coefficients(static_tensor)                    // univariate
  mle(static_field_array_of_length_2^arity)
  add(p, q), multiply(p, q)
  fix_prefix(p, ordered_point)
  sum_boolean_suffix(p, suffix_length)
  interpolate_on_domain(values, validated_static_domain) // univariate

observations:
  evaluate(p, point)
  evaluate_on_domain(p, validated_static_domain)        // univariate initially
  coefficients(p, static_length)                      // univariate, bounded
```

The maintained clients cover degree-two public-table Sumcheck and degree-three
[weighted R1CS Sumcheck](relation-composition.md) rounds and small
univariate coefficient/domain calculations. A generic carrier does not promise
every polynomial algorithm. Unknown or excessive required bounds reject the
selected lowering.

Static data has fully defined elements and constant in-bounds extraction.
Shape, field, arity and domain identity are checked separately. Axis `k` denotes `X_k`; a rank-one array flattens the
Boolean cube in the high-bit order defined by the polynomial specification. Coefficient order and all prefix/suffix orders
are explicit. Zero arity and degree-zero polynomials are admitted.
MLE and coefficient constructors require nonempty arrays; general data arrays
can be empty. Fixing every table axis yields a length-one array.

Degree upper bounds come from constructors: MLE contributes at most one per
variable, multiplication adds bounds, addition takes maxima, and fixing or
Boolean suffix summation removes axes without increasing the remaining bounds.
Bounds may exceed the actual degree after cancellation. An author annotation
alone cannot establish a bound for an opaque value.

A domain fixes explicit ordered points and cardinality. The initial
coset client supplies its points; generator/shift descriptors are deferred. Interpolation requires distinct points and returns the unique
polynomial below the domain-size degree bound. It cannot recover an arbitrary
formal polynomial from its domain evaluations.

| Expression | Preserved meaning |
|---|---|
| `mle(T)` | Formal multilinear extension of the ordered table |
| `mle(T) * mle(U)` | Formal product; generally not multilinear |
| `mle(pointwise_product(T,U))` | Interpolation of table products; can differ from the formal product away from the Boolean cube |
| `interpolate_on_domain(evaluate_on_domain(p,D),D)` | Reconstruction below the domain-size bound; not unconditionally identical to `p` |
| `evaluate(p,x)` | A field value; not an identity or degree certificate |

Polynomial values may flow through transparent acyclic helpers when preparation
inlines them and exposes their constructors and bounds. Protocol
entry/exchange values are concrete tensors or scalars. Opaque polynomial inputs,
unresolved polynomial calls and a universal polynomial runtime ABI are excluded.

### Representation alternatives

Named SSA preserves sharing in nested sums and products. Factorwise prefix
fixing remains opt-in; its effect on work and storage depends on the expression
and selected realization. Mathematical equality alone does not establish a
performance benefit or equal exhaustion behavior.

Builtin static tensors fit MLIR shape and SSA APIs. A distinct immutable
`field_array<F,N>` preserves shape through native boundaries. Existing dynamic
vectors supply reference packing; reusing private fixed vectors as public
arrays would conflate custody and wire contracts. One exchange remains one frame.

Dense coefficients, evaluations, shared factors and recomputation are execution
representations with interpretation contracts. A `VirtualPolynomial` style
factor representation can be selected later without becoming the universal
source type. Mathematical equality alone does not permit reordered effects or
establish the same failure under insufficient resources.

## Actual relations, residuals and terminal decisions

The implementation uses interpreted relation families and actual-instance
reduction contracts from the relation specification. An independent requirement
document and a selected C++ checker bind those requirements to the program. Actual bindings are derived from original ports and checked against
candidate SSA; candidate metadata cannot define their meaning.

The selected bindings identify:

- The independently fixed source requirement, actual entry inputs and roles.
- Each round's actual received coefficients, guard, query and next scalar.
- The actual returned subject, ordered challenge point and scalar.
- The residual-to-terminal input map and actual terminal decision output.

The public client returns the actual verifier-side tables `T@V, U@V` with its
point and scalar. The terminal receives those fields. A matching subject name
or type does not establish this connection. The requirement and terminal use
one admitted mathematical helper/body for the expression recipe; do not maintain
two mutable recipe graphs or accept an unchecked author hash as equivalence.

A specification reference creates neither communication nor witness visibility.
Private prover tables cannot be evaluated at the verifier through a binding.
A future private terminal instead needs a public commitment/oracle subject,
an existential witness relation and its own opening contract.

Prefer component boundary references over arbitrary interior SSA values.
Specification associations stay protected until checked transfer or explicit
erasure. Absence of runtime effects does not make a required binding disposable
by generic DCE.

### Reduction correspondence check

Use a closed structural recognizer for the selected verifier reduction and
terminal. Run it on participant form after admission and helper expansion,
before polynomial folding, with a fixed preceding pass set. Inspect actual
operands and action order, not just symbols or metadata:

1. The subjects, recipe, Boolean-cube arity and initial scalar match the source requirement.
2. Each round polynomial is built from that round's received coefficient payload.
3. Its guard compares `q_i(0) + q_i(1)` with the previous actual scalar.
4. The challenge comes from the declared query after the message and guard.
5. The next scalar is `q_i(r_i)` and the residual retains every actual challenge,
   in order, including the final one.
6. Returned subject/point/scalar fields connect to the terminal's actual inputs;
   its decision checks the required expression at that point against that scalar.
7. Every supplied independent requirement is checked against the retained source
   and the candidate. The check cannot discover requirements omitted from that
   independent document.

This is a selected analysis, not a Sumcheck instruction baked into generic IR.
An unsupported rewrite must be disabled for this checked path or have an explicit
preservation step. Reconsider named relation/terminal operations or preservation
certificates if legitimate transformations make structural recognition brittle.

For the verifier's true round polynomial `h_i`, a received `q_i`, and an actual
challenge `r_i`, the mathematical law on a passed guard is:

```text
Bad_i := passed_guard_i AND q_i != h_i formally AND q_i(r_i) = h_i(r_i)
S_(i+1) implies S_i or Bad_i
```

Here `S_i` says the current scalar equals the remaining Boolean sum of the
verifier's subject after its actual prefix. The terminal establishes `S_n`.
Composition uses the actual residuals and the union of exceptional events.
A quantitative probability bound additionally needs the declared degree and
challenge experiment. Query order alone does not establish uniform sampling.
Honest completeness separately requires a valid initial claim, agreeing role
inputs including that claim, faithful delivery, and the stated execution
availability and resource conditions.

The reduction recognizer checks the selected mathematical relation.
[Adjacent preservation checks](preservation.md) separately compare projection,
exec/physical lowering and emitted programs. The composed client uses
`protocol.apply` to connect reduction and terminal through SSA in one entry;
[static composition](relation-composition.md) owns that handoff. These native
checks do not establish a Lean refinement or cryptographic security theorem.

## Two clients and one useful transformation

### Public-table Sumcheck

Use the two-variable expression `f = mle(T)^2 + mle(T)*mle(U)`.
For each statically elaborated round, the prover fixes its delivered prefix,
sums the Boolean suffix and sends three coefficients. The verifier constructs
the received polynomial, guards its sum at zero/one, queries the challenge,
sends it to the prover and updates its scalar using that actual challenge.

The prover returns its received prefix, including the final challenge. The
verifier returns `(T@V, U@V, prefix_V, value_V)`. The composed entry applies the
terminal to exactly those returned fields and evaluates the same expression.
A stopped guard, a normally returned terminal `false`, a decode error and a
resource failure stay distinct.
This is a public reference reduction, not a private PCS protocol.

### Formal product and domain reconstruction

Construct two univariate polynomials from independent length-four coefficient
inputs. Return their formal product's seven coefficients, the four coefficients
reconstructed from a validated size-four domain, and both evaluations at a point
outside the domain. The two outputs can differ there. Include a low-degree
roundtrip as a positive control, not the only observable case. Native execution
uses an installed field and a domain validated for that field.

### Ordered fixing

Exercise factorwise prefix fixing with repeated factors preserved. Compare
actual work and storage with the existing specialized table evaluator using
the same algorithms and cache policy. If it already does the same work, record
no performance gain. Another executable representation needs a concrete consumer or measured benefit.

## Polynomial expression admission

This formal-polynomial subset admits flat expressions and static finite data. Retain the
[flat SSA decision](../rationale/mathematical-ir.md). Generic collection regions, `tensor.generate`, authored `linalg` and higher-order
polynomial functions remain outside this subset. Dynamic tensors and structured
control have their own [foundation contracts](../spec/profiles/compiler/structured-iteration.md). A universal `compute` wrapper or `at<T,A>` type is not
required by the selected subset.

Before any region mathematics is admitted, availability, helper summaries,
demand, cloning and lowering must share an external-value dependency query
covering operands and free body captures. Region bodies also need positive
totality and index/bounds rules. The current direct-operand interface is correct
only for its admitted flat scope.

The [decision checkpoints](../roadmap.md#extend-on-demonstrated-demand) name when
to reconsider these choices. They do not promise every deferred feature or
prevent a counterexample from reopening the design earlier.
