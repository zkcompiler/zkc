# Interactive Sumcheck ends by evaluating the original polynomial

The [interactive Sumcheck profile](../spec/profiles/sumcheck/interactive.md#complete-verifier-source)
returns a Boolean obtained by evaluating the original bound polynomial at the
actual ordered challenge point. It does not accept a final oracle value from
its caller. The statement defined by the tables is therefore an input the
verifier reads under its input policy, as in the
[supplied local terminal](../spec/profiles/sumcheck/interactive.md#supplied-local-endpoints).
A native evaluation may avoid dense coefficients when its representation law
proves the same evaluation; it then needs the table data, or a corresponding
retained representation, at the terminal. The profile claims no verifier that
is sublinear in an arbitrary private table.

## Alternatives

**Return the residual scalar and leave its use to the caller.** A completed
round does not establish its terminal relation. The
[soundness bound](../spec/profiles/sumcheck/interactive.md#honest-execution-and-interactive-soundness)
concerns acceptance against the original statement, so the entry that carries
the bound contains the terminal.
[Scalar rounds](../spec/profiles/sumcheck/scalar-rounds.md) remain a separate
component whose result is a scalar.

**End in a commitment opening.** An opening terminal is a different contract.
It needs a selected construction and a security argument of its own, and the
direct-terminal theorem does not prove that composition. The
[committed experiment](../compiler/protocol-pipeline.md#8-assurance-and-the-next-design-boundary)
is stated over the direct terminal, not instead of it: outside a false-opening
event, committed acceptance implies direct-terminal acceptance, and the opening
loss is added to the bound.

**Put a digest of the statement in the framed root.** The
[framed root](../spec/profiles/sumcheck/framing.md#complete-statement-root-and-framed-execution)
holds the entire ordered list of `3^n` coefficients, which the provider can
inspect. Replacing it with a digest changes the query input and the observer.
It is not a storage optimization.

## Reason

Thaler counts the terminal evaluation as part of Sumcheck's cost, and
distinguishes a product of multilinear extensions from access to a free
evaluation oracle [1]. Evaluating the original polynomial keeps that work
measurable and keeps the degree premise with the statement. The reference
supplies no theorem about a native representation. Private captures of a table
computation stay private in their own workload; compilation does not authorize
exporting them as a shared statement. A longer factor list needs its own degree
and message profile.

## Reopen when

An application must withhold the polynomial from the verifier, or needs a
verifier sublinear in the table, and no composition over the direct terminal
gives it the bound it needs. It then selects a terminal contract of its own,
such as a proved opening construction.

## References

1. Justin Thaler, *Proofs, Arguments, and Zero-Knowledge*, §4.1, Theorem 4.1
   and Table 4.1.
   [Author PDF](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf).
