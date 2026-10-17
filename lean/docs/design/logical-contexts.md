# Logical contexts

A security theorem talks about mathematical objects: a polynomial, a claimed
sum, a witness. A protocol packs related runtime values into ports. Logical
contexts identify the objects independently of that packing, so the same
mathematical lemma applies when ports are reordered and when a component's
context is instantiated at an actual call.

## Carrier

`Zkc.Source.Structured.LogicalContext` defines a typed context of binders. A
binder's sort is a native type or a library sort, such as a multilinear table of
fixed arity, that has no native port. A library supplies a vocabulary: sort,
predicate and view codes, each with an identity made of its declaration and its
normalized static arguments, and a typed signature. An interpretation gives
each code one Lean meaning, so every use of one code, including source aliases,
reads one meaning.

Arguments are terms: a store key, an observation of an actual boundary
selector, a supplied native constant or a view. A key is a lexical binder or one
of the legacy selector-named `parameter`/`witness` slots; keys never read the
boundary and observations never read the store. An atom applies a predicate code
to ordered terms and holds when every term reads and the meaning holds.

Choosing a binder value supplies no quantifier, agreement, causality or
security assumption. The property consumer quantifies binders and states which
atoms it assumes or refutes.

## Substitution and transport

`LogicalInstantiation` substitutes a callee's keys at an actual checked
application: binders are renamed into the caller's context and the legacy slots
follow the existing `AssignmentInstantiation`. `LogicalTransport` moves terms
along a port map that keeps types, scopes and the number of roles. Binders do not move, so an
atom holds on a repacked subject exactly when it holds on the original at the
pulled-back boundary.

## The contract layer as an instance

`LogicalTranslation` covers the clause, residual and instantiation semantics:
`LogicalAssignments` is the selector-named view of a store, logical
instantiation projects to `AssignmentInstantiation.apply`, and every retained
clause lowers to an atom with the same truth. For an external terminal only the
reads are lowered; its experiment-authored meaning is applied unchanged and is
not translated. Retained relations keep their snapshot positions in this
translation.

## Exported metadata

`LogicalChecking` admits contexts in an export form that names binder sorts and
predicates by identity, binders by position and observations by direction, port
and role; the compiler does not emit this form. A
library resolution accepts a code only when its identity is exactly the
exported one. Unknown identities, unbound or wrongly sorted binders, observations
of the wrong type or scope and wrong argument counts are refused by name.

## Loop frames

An owner's boundary does not show what a repeat carries between iterations.
`LogicalFrames` adds loop frames: the masked state that enters one iteration of
one repeat occurrence at one participant, with the iteration index. A frame
term reads an owner binder, a carried slot, the index, a supplied constant or a
view; a frame invariant is a list of atoms over these terms, with the same
vocabulary and interpretation as boundary atoms. The loop never chooses or
changes a binder.

Execution records actions, not frames. A frame invariant is therefore
established by `Repeat.loop_frames`: an obligation on the actual masked
callback step, for every reply, gives the invariant at the frame the loop
reaches after any number of iterations. The export form names the repeat by its
site in the owner body, the observed participant by its local role and carried
slots by position. `checkFrame` refuses an unknown site, a slot of another type,
a slot outside the participant's scope, and a misplaced index by name.

`ZkcExamples.Structured.SumcheckFoldInvariant` states the prover's fold
invariant on the actual Reduce callback. The original table is one binder; the
prover's entries, remaining dimension, width and received point are carried
slots. At every frame, the entries represent the partial evaluation of the
original table at the received point, and their two half sums are the endpoints
of the correct round polynomial. The binder is the decoding of the prover's own
input table; this agreement is an explicit premise.

## Example

`ZkcExamples.Structured.SumcheckLogicalContext` expresses the Sumcheck residual
request with one table binder shared by the initial sum and the residual
evaluation; only the verifier's claim, point and value are observed. The same
atoms apply to the retained Reduction export and to an export whose root ports
are reordered. The security integration proves the `count / |F|` bound on both
roots with the unchanged `repeat_uniform_residual_soundness`.

## Limits

Sorts have static arities; a dependency on an observed value, such as the
remaining dimension of a folded table, stays inside a predicate's meaning.
Frames observe carried state only: actions inside an iteration are not frame
terms, and the process events carry no iteration coordinate. Identity keying of
opaque relations, native export and source syntax are not part of these
modules.
