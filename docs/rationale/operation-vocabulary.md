# Control is common, and each protocol supplies its own operations

A [typed program](../spec/language/programs.md#typed-control) has five
constructors: return, stop, operation binding, branch and publicly counted
iteration. Sorts and operations are parameters of the
[language signature](../spec/language/programs.md#language-signatures), and an
[operation meaning](../spec/language/programs.md#operation-meanings) may expand
one source operation into several interface calls. A whole polynomial query, a
group operation or a Merkle path check therefore stays one logical operation
until an interpretation expands it.

## Alternatives

**Syntax shaped around one protocol's messages.** A tree built for Sumcheck
rounds has no place for the
[contrasting clients](../spec/profiles/README.md#contrasting-domain-clients):
a Sigma verifier over separate scalar and group sorts, and a Merkle opening
that expands into ordered node operations and keeps the effects of a failure
inside that expansion.

**Host callbacks as program bodies.** The source stops being inspectable and
portable: the captures of arbitrary host code cannot be examined.

**One universal syntax that contains every domain operation.** Each new
algebra becomes an edit to the common control language, although its laws
belong to its interpretation.

**A shared polynomial object, or an opaque verifier operation.** These are the
two ends the parameter avoids. A polynomial object gives a Merkle opening
nothing, and an opaque verifier operation hides the path computation that the
opening's law is about. A logical operation with an interpretation sits
between them.

## Reason

The parameter keeps what differs between protocols out of what they share.
Formation, binding, denotation, renaming, sequencing and the
[structural call bound](../spec/language/programs.md#structural-call-bounds)
are defined once for every language, and mixed field, group and index sorts
need no change to control.

A parameter is not a format. Choosing a type of operations fixes no codec and
does not exclude function-valued payloads, so each portable profile resolves
its actual finite descriptors, and positions that arrive from outside are
[formed with checks](../spec/language/programs.md#raw-formation) instead of
being looked up totally.

## Reopen when

A required language feature cannot be expressed compositionally without hiding
control, an observation or structure that a proof needs inside an operation.
A more convenient spelling is not such a feature and does not call for another
semantic layer.
