# A body is a well-founded tree of calls, and a handler gives it meaning

A protocol computation denotes a [body](../spec/core/execution.md#bodies): it
returns a value, stops, or requests an operation and continues with the actual
reply. State, randomness, field arithmetic and concrete services enter only
through the [handler](../spec/core/execution.md#deterministic-interpretation)
that interprets the calls. The body is a mathematical object. Portable source
is [finite typed syntax](../spec/language/programs.md#typed-control) that
denotes one, and a compiler may hold loops and shared regions compactly;
nothing serializes a continuation or allocates the tree.

## Alternatives

**Take the compiler's own operations as the meaning.** Source meaning is then
tied to an implementation carrier that keeps changing. With a separate
denotation, each compiler representation is one more subject to relate to it.

**Let every body be an opaque action in some monad.** The calls disappear into
the action. [Conformance](../spec/language/interaction.md#all-reply-conformance)
and the [public call bound](../spec/core/execution.md#uniform-call-bounds) are
defined over the calls of a body and over every reply to each of them, so both
need that structure to stay visible.

**Use a coinductive interaction tree.** It supports divergence and recursive
interaction, and brings silent steps and equivalence up to weak bisimulation
with it [2]. The [execution envelope](../spec/conventions.md#execution-envelope)
uses well-founded bodies with a public call bound.
[Outer iteration](finite-bodies-under-iteration.md) can repeat those bodies and
retain pending prefixes without making each body coinductive. Interpretation,
the bound and the body laws remain recursion and induction on the finite body.

## Reason

An operation with a dependent reply type and a continuation keeps the actual
operand and the reply-dependent continuation visible, and leaves arithmetic,
state and services to the handler. One body can then be run deterministically,
inside [another monad](../spec/core/execution.md#outer-effects), or through an
[operation interpretation](../spec/core/interpretations.md#body-interpretation)
into a lower signature, under the same sequencing equations.

A signature carries no equations. Plotkin and Pretnar separate operations,
the equations imposed on them and the handlers that respect those equations
[1, Definition 4.5]. Accordingly a rewrite that depends on an algebraic law is
justified by a law about the interpretation in use, never by the signature
alone. The choice is a judgment about the contracts this compiler needs, not a
claim that one representation is best in general.

## Reopen when

A required protocol needs unbounded interaction, a property that is sensitive
to divergence, or a response in the middle of an action that is atomic in this
model. A transition system or a coinductive model is then compared against the
consumers that need it. Hiding such behaviour inside one opaque operation is
not an answer.

## References

1. Gordon D. Plotkin and Matija Pretnar, "Handling Algebraic Effects,"
   *Logical Methods in Computer Science* 9(4:23), 2013, §§4–5.
   [Author paper](https://arxiv.org/pdf/1312.1399).
2. Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha,
   Benjamin C. Pierce and Steve Zdancewic, "Interaction Trees: Representing
   Recursive and Impure Programs in Coq," *PACMPL* 4(POPL), Article 51, 2020,
   §§2–5. [Author preprint](https://arxiv.org/pdf/1906.00046).
