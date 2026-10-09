# Static native protocol composition

This profile extends [mathematical protocols](mathematical-protocols.md).
It retains `protocol → participant → exec → physical`. The additional operation
is a static component application, expanded before projection; it adds no runtime
call stack, bundle connector, or separately mutable relation graph.

## Application interface and meaning

```mlir
%result:4 = protocol.apply @reduction(%assignment, %weight, %zero, %random)
  {roles = ["Prover", "Checker"], site = "reduce"}
  : (tensor<4x!algebra.field<"bls12-381.fr">>,
     tensor<1x!algebra.field<"bls12-381.fr">>,
     !algebra.field<"bls12-381.fr">,
     !protocol.service_ref<"random.bls12-381.fr/1">)
  -> (tensor<4x!algebra.field<"bls12-381.fr">>,
      tensor<1x!algebra.field<"bls12-381.fr">>,
      !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
```

The callee is a `protocol.func` in the same `protocol.module`. Operand and result
types match its ordered signature exactly. `roles[i]` substitutes the callee's
ith declared role with a caller role. Substitution is total and injective.
Each operand supplies every substituted input component. Result availability is
exactly the substituted declared output set, even when an internal value has
more components. Shared availability never establishes equality of those
components.

All functions are verified independently, including dead calculations and
unreferenced definitions. Application admission uses those interfaces, without
mutating IR inside a verifier. An affine input counts as a use at the call.
Owner-local data retains its singleton owner. Service operands retain the
caller's entry reference and state; they cannot become component results.
Applied components cannot contain `protocol.statement`: those declarations bind
entry arguments and acceptance indices, which are not generally preserved by
substitution. The enclosing entry owns its statement binding.

Applications have effects and cannot be erased merely because their results
are unused. The symbol call graph must be acyclic, with combined application/helper depth
at most 64.
Before cloning, the compiler memoizes conservative expanded operation and storage bounds. The total over
all retained definitions, including inserted boundary restrictions, is bounded
by 100000. Expanded operand/result slots and role selectors are bounded by
1000000, and generated site text by 16 MiB, before cloning. Existing helper and
availability budgets additionally apply.
Applications and pure helper expansions are counted at every occurrence, not
once per callee. Helper inlining also shares a module-wide defensive budget.

Expansion uses MLIR symbol lookup and `IRMapping` on an owned candidate. Shared
inputs and outputs receive explicit `protocol.restrict_roles` boundaries.
Action owners, peers, nested substitutions and restrictions are renamed.
Services continue to refer to the same caller block argument. Pure helper
symbols are unchanged and expand afterwards. The expanded module is verified
before projection and simplification can erase restrictions.

A nested action site becomes `apply_<length>_<application-site>_<callee-site>`.
Length counts bytes; nesting applies the same rule recursively. This encoding
distinguishes `a`/`b_c` from `a_b`/`c`. Expanded sites above 4096 bytes or collisions
with authored sites refuse compilation. `CallSiteLoc` retains call provenance.
There is no runtime application event: traces contain the expanded action sites.

## Execution and failures

The resulting entry executes in the existing joint runtime. A guard stop or
failed receive prevents later terminal work. A returned terminal `false` is a
completed execution carrying false, not a stop. Decode failures, service errors,
host cancellation and resource exhaustion retain their existing outcomes and
cleanup behavior. A service budget covers prelude and component draws together;
composition does not reset service state or grant each call a fresh budget.
These are compiler/runtime contracts tested on generated programs, not a native
Lean refinement theorem.

## Checked reduction and terminal application

A [polynomial requirement](structured-mathematics.md#independent-reduction-requirements)
may additionally contain:

```json
"composition": {
  "entry": "main", "reduction_site": "reduce", "terminal_site": "decide"
}
```

The selected source entry has one Boolean result. Its suffix is exactly the
reduction application, terminal application and return. The two callee symbols
and sites match the independent requirement. Every terminal input is the actual
corresponding reduction result SSA value. The terminal's role is the substituted
reduction verifier; the sole decision result is returned unchanged and owned
only by that role. Swapping equal-typed subjects, points or scalars fails this
check. The generic entry prelude remains authoritative source code; the generic
family does not certify an arbitrary external relation.

The checker compares complete selected projection interfaces (including
statements and actions), dispatch definitions, relation declarations and authored
local definitions with the independently projected original. Candidate-only
supporting declarations are refused too. It also compares
each composed candidate participant with the original
entry's unsimplified expansion/projection, ignoring locations only. Separate
component checking retains its existing structural recipe/round checks. The
composed family deliberately refuses other candidate rewrites, even if they
might be equivalent. Checked compilation checks before optional simplification
or factor fixing, then binds the resulting bundle and post-check pass list.
Source expansion, projection and later lowerings remain trusted/tested; repeating
the same transformation is not an independent proof of that transformation.

The report binds bundle hashes for the reduction, terminal and composed entry,
regardless of which checked entry is selected for output. It allows the composed
entry to be compiled directly. Actual residual
handoff is then SSA within one entry. No host interpretation of a connector is
required. Separately executed companion bundles retain their explicit host
handoff obligation. Digests identify bytes; they do not authenticate a report.

## Independently specified R1CS client

`r1cs-sum-to-point/1` adds a mandatory `relation` containing canonical
`zkc.relation.r1cs` JSON and a mandatory composition requirement. It accepts the
exact source emitted by `authorR1CSSumcheck` for that independently supplied
relation, ignoring locations only. This pins matrix coefficients, ordered public
layout, relation identity, assignment construction, zero claim, weight draws,
component applications and decision provenance. Renamed or algebraically
rewritten source requires a future equivalence contract; it is not silently
accepted. The adapter itself remains trusted and differentially tested.

The authoring envelope is BLS12-381 Fr, at most 8 constraints, 128 columns and
1024 nonzero canonical matrix terms. Other fields and larger inputs refuse
before SSA construction. Ordinary compiler work limits still apply; authoring
admission is not a guarantee of executable lowering for every dense input.
Zero and one row use two rows; other row counts round up to a power of two.
Padding contributes zero constraints. Variable order is high-bit first.

For n padded rows and m = log2(n), the recipe is:

```text
z = [1, public outputs, public inputs, witness]
a = MLE(A z); b = MLE(B z); c = MLE(C z)
eq(tau, X) = product_i ((1-tau_i)(1-X_i) + tau_i X_i)
f(z,tau)(X) = eq(tau,X) * (a(X)*b(X) - c(X))
```

`main` takes all non-ONE assignment coordinates as field inputs available to
Prover and Checker, plus a Checker service port. Each role has its own input
components. It constructs `z`, samples m weight coordinates at Checker, sends
them to Prover, applies m degree-at-most-three Sumcheck rounds with claim zero,
and passes the actual residual to the Checker terminal. The same service supplies
weights and round challenges. The terminal recomputes f from assignment and
weight inputs; no precomputed row tables are terminal subjects. The statement
contains only public output/input components selected at Checker, in imported
layout order. Its external key is the canonical R1CS representation identity.
Witness availability at Checker is explicit; it is not a statement coordinate.

The cube sum equals the multilinear evaluation of the row residual vector at
tau. Nonzero residuals can cancel in an unweighted sum or at selected weights.
For example `(1,-1)` vanishes at tau = 1/2. Such runs are valid bad-event controls,
not evidence of deterministic R1CS decision. Randomness quality and probabilistic
soundness need a declared experiment and proof. This client claims neither
hiding, succinct verification, knowledge soundness nor circuit-to-R1CS adequacy.

The separate `evaluate` entry accepts an explicit assignment array and public
scalars. It returns padded A/B/C products, exact ONE/public binding, and exact
R1CS satisfaction. Tests compare it with the existing imported-relation evaluator
and independent integer field arithmetic, including invalid ONE/public prefixes.
