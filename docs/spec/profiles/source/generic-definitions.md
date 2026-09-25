# Generic requirements and type instantiation

This profile specifies constrained generic source, its native elaboration and
the mechanized static foundation. It extends
[resolved source definitions](definitions.md). Native execution has independent
backend admission and bounded original-source executable correspondence checks;
raw/native elaboration adequacy remains unproved.
The implementation decision is in
[the compiler carrier](../../../compiler/specialization.md).

## Requirement meaning

A static term is a root identity, an associated-member projection, or a pure
application of a resolved constructor to ordered static arguments:

```text
Term = root(name) | project(base, member) | apply(head, ordered_arguments).
Predicate = equal(left, right) | relation(name, ordered_arguments).
```

A model assigns an identity to every root, interprets associated members as
functions of identity, interprets each application head as a function of an
ordered identity list, and gives each named relation a predicate on ordered
identity lists. Application heads identify resolved pure constructors, never
runtime actions. A seal may be represented by a distinguished constructor whose
head identifies its qualified declaration and whose arguments include its
enclosing selection; this does not allocate a fresh identity on replay. Roots are not automatically distinct merely because their names
differ. Sorted parameter formation and installed nominal consistency are separate
obligations of the generic source/installation boundary.

The derivation rules are assumptions, equality reflexivity/symmetry/transitivity,
associated-member congruence, pure application congruence, argument-wise relation
transport, and explicitly
installed unary capability implications. No rule concludes a cryptographic
property just because an implementation advertises a matching capability name.
Application congruence requires the same head, equal arity, and one equality
premise for each ordered pair of children. It neither reorders nor drops
arguments, equates different heads by spelling similarity, infers injectivity,
nor asserts disequality of distinct terms. A nullary application is allowed and
is distinct syntax from a root with the same name. Sorted constructor formation,
qualified-head resolution, and coherent interpretation remain caller obligations.

For a public requirement list `Q` and body obligations `R`, declaration checking
requires a derivation of each element of `R` from `Q` and installed implication
rules. The direction is `Q entails R`. Checking the body under stronger facts
than the public promise does not validate that promise.

The executable checker replays shared certificate steps in order. Each premise
must reference an earlier established fact and the supplied conclusion must match
the actual inference. Successful replay constructs a proof of derivability.
Under any model satisfying the input assumptions and installed implications,
every accepted conclusion holds. An unanswered goal is unresolved, not false;
resource limits and missing implementations are not contradiction proofs.

This result is implemented in
[`Zkc.Source.Requirements`](../../../../formal/Zkc/Source/Requirements.lean).
It proves soundness of accepted derivations, not completeness of the native
search, consistency of arbitrary assumptions, or existence of a native instance.

## Requirement certificate carrier

The bounded replay interface accepts one request format and one certificate
format:

```text
["zkc.requirements/1", terms, assumptions, implications, goals]
["zkc.requirements-certificate/1", steps, answers]
```

Terms are `[null, name]` roots, `[parent_index, member]` projections and
`["apply", head, child_indices]` applications. Any other version name refuses.
Term indices refer only to earlier entries, including every ordered application
child. Exact duplicate terms refuse; repeated children within one application
are allowed. Heads, roots and members are nonempty UTF-8 strings of at most 256
bytes. There are at most 128 terms, 16 children per application, 1024 assumptions,
1024 goals, 128 unary implications, and 65536 certificate steps.

A predicate is `[name, argument_indices]`: `"="` requires exactly two arguments;
other nonempty names denote relations with at most 16 ordered arguments. Every
index must refer to a declared term. An implication is `[premise, conclusion]`,
where both names are nonempty, at most 256 bytes, and different from `"="`.
A step is `[conclusion, rule, premise_indices, declaration_index]`.
All premise indices must refer to earlier steps, including steps unused by any
goal. The rule checks are:

| Rule | Required premises and conclusion |
|---|---|
| `assumption` | No premises; conclusion equals the indexed input assumption |
| `reflexivity` | No premises; conclusion is `equal(a,a)` |
| `symmetry` | One premise `equal(b,a)` for conclusion `equal(a,b)` |
| `transitivity` | Ordered premises `equal(a,b)`, `equal(b,c)` for `equal(a,c)` |
| `projection` | One premise `equal(a,b)`; conclusion projects the same member from `a` and `b` |
| `application` | Same head and arity on both sides; exactly one ordered premise `equal(a_i,b_i)` per child pair, including zero for nullary applications |
| `transport` | Source relation followed by exactly one equality from each original argument to its corresponding conclusion argument; same relation name and arity |
| `implication` | One unary relation premise; indexed installed implication matches its name and the conclusion name, with the same argument |

Only `assumption` and `implication` use `declaration_index`; all other rules
require zero. A step has at most 17 premises. Every numeric index is a natural
at most 65536, further bounded by its referenced collection. Answers have exactly
one entry per goal: `null` means unresolved, otherwise an existing step must
conclude that exact goal. Malformed formation, wrong conclusions, invalid rule
shapes, extra/missing premises and forward/self references refuse the entire
certificate, even if all requested answers are unresolved. No checker trusts the
producer's search procedure.

Each checker replays this rule set independently of the producer. The
separate execution-bound claim contract/certificate service is unaffected by
this carrier.

The executable replay profile also bounds expanded work before interpreting the
indexed term DAG. A root has weight 1, a projection 1 plus its parent's weight,
and an application 1 plus the sum of its ordered children's weights, counting
repeated children each time. The sum of all declared term weights is at most
16384. A predicate costs 1 plus the sum of its argument weights. Assumptions and
goals together cost at most 262144; certificate conclusions together have the
same separate limit. Exceeding either bound returns `requirements-work-limit`
before recursive term comparison. These transport limits do not restrict the
mathematical derivation rules or interpret exhaustion as falsity.

## Typed instantiation

Given a source language `L` and a static type substitution `theta`, define
`L[theta]` by mapping its type vocabulary, operation argument/result types and
condition type. Operation identities remain the same. Structured instantiation
maps every variable and operand position and recursively maps regions, including
both branches, bounded iteration, sequential binding and explicit stopping.

The substitution need not be injective. Two generic parameters may select the
same domain without merging their value arguments or resource identities.

For a selected interpretation `M` of `L[theta]`, its pullback interprets each
original type through `theta` and each original operation using `M` on the mapped
arguments. This defines the source meaning independently of the transformed body.
The implemented theorem is:

```text
denote(instantiate(theta, body), M, env)
  = denote(body, pullback(theta, M), pullback(theta, env)).
```

Equality is at `PIR.Proc`; running either side under any common handler preserves
the complete outcome, post-state and events, including stopped executions. This
is a proof about the actual structural substitution algorithm, with no premise
asserting that the entire transformed body already denotes the desired result.
See [`Zkc.Source.TypeInstantiation`](../../../../formal/Zkc/Source/TypeInstantiation.lean).

Type substitution does not select or justify a new operation implementation.
Substituting associated operation meanings, interning/sharing native code,
preserving logical source origins, physical representation conversion and generic
portable parsing each require their own checked connection. Existing execution
relations supply the target obligations; these are not discharged by this theorem.

## Native definitions and configurations

The readable development frontend retains generic source before specialization:

```text
fn Fold<F: Field>(table: table:F, r: field:F) -> (table:F)
    requires (CommRing(F)) {
  [fold] (result) = poly.fold<F>(table, r);
  return (result);
}
configure Partial = Fold();
configure Direct = Partial(F = bls12-381.fr);
configure OtherLayout = Partial(F = bls12-381.fr)
    using (fold = "arkworks-msb/poly.fold");
```

`F: Field` declares the sort of a static identity. `CommRing(F)` is an algebraic
requirement, not a runtime field object. An operation has explicit static term
arguments and ordinary SSA operands. Empty static argument lists support helpers
such as `Both<>` with no cryptographic dependencies. Associated members retain
their own sorts: `G.Scalar`, `C.ValueField`, `C.PointField`,
`C.EvaluationField` and `T.ChallengeField` do not acquire generic equality merely
because the current finite installation uses the same field for them.

Formation checks every definition, including unused definitions. It checks
parameter/member sorts, installed predicate arities, SSA signatures, affine
operand use and `Q entails R`. The current executable body fragment is a sequence
of installed operations and acyclic local `apply` applications followed by a
return. Symbolic control regions and arbitrary user-declared capability predicates
are outside this authoring fragment; the typed theorem covers a richer language.

A generic application `apply [site] (outputs) = Helper<F>(inputs);` substitutes
ordered static terms into the target generic signature. A configuration target
uses the same rule for only its residual parameters, in base declaration order.
Fixed parameters become nominal constants, not caller arguments or invented
capabilities. Ground obligations are validated against the installed domains;
all residual obligations must follow from the caller's public requirements.
Operand and result equality obligations and affine consumption are checked by
the same inference discipline as primitive operations. The whole declaration
graph, including unused definitions and configuration-resolved edges, must be
acyclic and satisfy the bounded depth profile. Implementation choices at helper
application sites are refused; the target configuration owns its primitive
choices. See [canonical local expansion](../compiler/local-algorithms.md).

Configurations are immutable and acyclic. They may leave parameters unresolved
and inherit an earlier configuration, but cannot rebind an assigned parameter.
All configurations are checked, including unused ones: known nominal
contradictions and ineligible fixed implementations are errors. Requirements
depending on unresolved parameters remain pending. Equality closure must also
reject a contradiction derived through an unresolved term.

Demand from a protocol-local call requires complete bindings and closes over
nested helper applications. An ordinary closed function can also call a generic
definition or configuration with concrete residual identities. Elaboration emits
closed functions and operation bindings, preserving mathematical operation
boundaries and retaining local calls for explicit MLIR expansion. Equivalent
definition/static-binding/implementation selections share
code. Physical variants retain the same logical origin; different runtime calls
retain their own dynamic origins and resource views. An unused partial
configuration emits no executable function.

The retained interchange is:

```text
["zkc.library/1", generic_definitions, configurations, closed_common]
generic = ["generic_function", name, parameters, requirements, inputs, outputs, body]
configuration = ["configure", name, base, assignments, implementation_choices]
```

Elaboration produces the [closed explicit-binding `/1` carrier](operation-bindings.md), without
replacing the retained original source. Generic field constants denote natural
number casts: the source permits bounded canonical decimal naturals, while
closed elaboration reduces them modulo the selected field. This literal
elaboration needs its own source correspondence check; it is not proved by the
structural type-substitution theorem.
