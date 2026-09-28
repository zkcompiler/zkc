# Mathematical protocols

This profile defines a shared mathematical protocol before role placement.
Its values are typed and available at declared roles. Pure computations form
acyclic regions; messages, local services and control retain their order.
The [implementation status](../../../status.md) distinguishes this contract
and its Lean core from native compiler support.

## Subjects and formation

A module contains ordered nominal domain and operation declarations, static
parameters, typed wire schemas, capability signatures, relation definitions,
acyclic protocol definitions and an entry binding. Names resolve to typed,
definition-local ordinals. Source positions are optional debugging data.
An admitted module fixes its interpretation and dependency manifest.

```text
port       = (available role set, mathematical type)
body       = return(operands)
           | pure(region, captures, outputs, next)
           | local(site, owner, operation, capabilities, operands, outputs, next)
           | query(site, owner, capability, operands, output, next)
           | guard(site, owner, condition, next)
           | message(site, wire, sender, receiver, operand, shared output, next)
           | invoke(site, earlier definition, static arguments, role binding,
                    capability arguments, operands, outputs, next)
           | repeat(site, count, index, captures, initial, body, outputs, next)
           | stop(site, owner, reason)
region     = ordered typed pure nodes and output references
pure node  = operation(static arguments, attributes, operand references)
           | map(shape, captures, body)
           | fold(shape, captures, initial, body)
```

The order of pure nodes is a topological reference order, not a physical
schedule. References point to preceding bindings or explicit captures.
Reverse edges, interning tables and demand sets are derived data. Region
boundaries, typed captures, operations and outputs belong to the subject.
Pure map/fold bodies are structured and finite; a fold specifies its order.
Parallel reduction requires an associativity law for the selected operation.

| Constructor | Formation and availability | Open-role meaning |
|---|---|---|
| Return | Every operand covers every role required by its result port | Return that role's ordered result components |
| Pure | Typed operands; positive total-purity contract; result available at the intersection of operand role sets | Evaluate the registered function on that role's components |
| Closed pure constant | No operands; result available at all participating roles | Evaluate the same nullary interpretation |
| Local/sample/query | One owner; explicit capabilities and permission; operands available there | Issue the specified local action, bind its reply only there; other roles skip it |
| Message | Distinct participating sender/receiver; operand available at sender; wire type agrees | Sender sends and aliases its operand; receiver obtains a fresh arbitrary typed reply; others skip |
| Invoke | Earlier definition; checked static substitution; injective role map; argument and result port coverage; explicit capability aliases | Execute the independently interpreted callee under those bindings and a new invocation path |
| Repeat | Public finite count; invariant carried port types; checked initial/yield coverage; bounded public index | Execute the same body at each actual index with its role-local carried state and captures |
| Guard | Participating owner; available condition | Continue when true; owner stops with reject when false |
| Stop | Participating owner and reason | Owner issues its terminal stop action; a foreign terminal leaf has no continuation and is incomplete |

An owned operation may contain local conditional computation. General
effectful branch syntax is outside the version-1 encoding; this profile has
no global branch on a private role value. Unclassified operations
remain ordered opaque local operations. Multi-result ports remain ordered;
lowering to a single local result uses an explicitly interpreted product with
checked packing/projection, including the empty product.

## Role components and statements

A context entry is `(R, T)`. Its environment at role `r` supplies a value of
`T` when `r ∈ R`. It supplies no peer-private value. Availability expresses
permission to read, not equality across roles.

For `m = send P -> V x`, `m` has roles `{P,V}`. Its P component aliases
`x`; its V component is the fresh receive reply. Consequently, `f(m)` can be
written once and has two independently evaluated components. Substituting
the sender's `x` into the receiver's `f(m)` is invalid in an open-role view.
Effect sites retain an invocation/iteration path, so repeated syntax does not
merge message, sampling, query or stop occurrences.

The reference meaning evaluates every available pure node. Demand analysis
may later remove unused total work under a preservation law; demand is not
part of the source meaning. Public input binding additionally identifies a
common statement and its canonical input encoding. Merely making two inputs
available does not prove that they agree.

Honest joint meaning composes the independently defined roles, honest message
delivery, one common statement, identical pure interpretations and a selected
reference schedule. Each capability has one joint handler/state. Coincidence
of shared values is a property at jointly reached bindings under these
premises. Query results coincide only under the service's response law.
The open-role interpretation does not assume honest coincidence. A foreign
role skips a guard even when its owner rejects, and may continue or return;
at an explicit terminal stop its foreign leaf is incomplete. This asymmetry
is intentional. General joint correspondence must relate jointly reached
prefixes and readable bindings under a delivery schedule. It cannot assert
unconditional equality of all roles' terminal outcomes.

A relation is a pure predicate over explicit public and witness ports with
declared domain assumptions. A protocol binds those ports by reference.
Relation hypotheses may be used by a theorem that assumes them; they do not
make witnesses public or received messages honest.

## Purity and capability identity

A pure operation is a total deterministic function on **all admitted typed
arguments**, including hostile received components. Any precondition must
already follow from their admitted types/refinements. When embedded in an
existing effectful interpretation, the required law is
`operation(op,args) = Proc.done(eval(op,args))`.

Checked inverse, decoding, bounds access and dynamic degree checks remain
ordered when they can stop. Sampling, queries, messages and guards are
ordered effects. Absence of effect metadata is not evidence of purity.
Resource allocation, mutable caches and opaque handles have their own
realization contracts. Mathematical sharing alone grants no physical
copy/drop permission or unchanged resource failure behavior.

Capability ports are separate from mathematical values. They specify a
service identity, query/reply signature and permitted roles. Local/query
operations and calls pass references explicitly. Passing the same reference
twice preserves one state. Fresh allocation is an explicit setup effect;
calls never silently clone a service. Distinct resolved root identities select
distinct state components. Callee
parameters may alias one root; local parameter names alone imply no
distinctness. Independent randomness requires an initialization law.
Root resolution composes the entry binding with every call binding on the
actual invocation path. Laws requiring non-aliasing must establish distinct
roots for every relevant instance, including multiple uses of one callee.
Pure interning never merges or duplicates capability identities.

## Static shapes and indexed iteration

Static natural expressions are literals, scoped parameters, addition,
multiplication and `2^e`. Formation is checked under an admitted static
environment. Initial automatic equality uses polynomial normalization over
addition/multiplication, treating identical `2^e` terms as opaque atoms after
normalizing their exponents. Numerals are evaluated with checked resource
bounds. Other equalities require an explicit checked derivation or refusal.
Instantiation results and universally quantified family laws are distinct.

`repeat(count, ...)` binds `i : Fin count`, available to every participating
role, plus invariant carried ports and immutable captures. Iterations occur
in ascending index order. At count zero the initial state flows to the
continuation and no body or `Fin 0` value is evaluated. Public counts
must be bound and agreed before execution; version-1 interchange accepts them
through closed entry instantiation. Runtime-derived counts require an extension. Symbolic storage does not require
unrolling; consumers may request a separately bounded expansion.

Nominal fields and groups remain distinct. Polynomial types retain field,
arity and degree bounds. A Boolean table and its multilinear extension are
distinct from a general formal polynomial. Multiplication preserves formal
polynomial multiplication; the MLE of a pointwise product is generally a
different object. Finite-field function equality does not establish formal
polynomial or degree equality. See [polynomial meanings](../../domains/polynomials.md).

`Residual(F,n,d)` packages a prefix length `k ≤ n` and an `(n-k)`-variable
polynomial with its bounds. Its fixed outer type supports a loop carrying a
length-n challenge buffer and scalar claim. Round extraction at `i : Fin n`
returns a univariate polynomial bounded by `d`. A shrinking physical buffer
needs a simulation relation to this logical residual.

Every selected wire is canonical as a function of the mathematical message.
For bounded coefficients the schema records exactly `d+1` ascending
coefficients, with zero padding and canonical field encoding. This is a
different schema from normalized variable-length coefficient objects.
Hostile ingress checks the selected schema before admitting the type.
Virtual and materialized encoders must emit identical complete bytes under
their representation premises. Physical comparisons include sent bytes and
stop outcomes on the same admitted resource domain.

## Placement and formal correspondence

[Placement](../compiler/mathematical-placement.md) owns the candidate/witness
contract, inline pure regions and the separate outlining law.
[Subject encoding](../../../compiler/mathematical-format.md) fixes canonical
bytes and ordinal references. Native support remains separately reported.

Formal definitions, checked statements and unimplemented obligations are
reported in the [formal support map](../../../../formal/SUPPORT.md#shared-mathematical-protocols)
and [status](../../../status.md#mathematical-protocol-foundation).
