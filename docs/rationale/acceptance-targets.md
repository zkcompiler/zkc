# A relation target may be reached by several routes and declares its input boundary

Both choices concern realizing a verifier's acceptance as a relation, under the
[target design](../compiler/targets.md) and the
[representation contracts](../spec/realization/representations.md).

## More than one route to a relation target

Three routes are permitted and may be combined within one target: expanding
the logical verifier operations, reusing a precisely defined and total
arithmetic subset shared with ordinary execution, and substituting an
independently supplied component. A substituted component is admitted only with
an exact statement of the values it receives, the field and representation they
are in, and either an adequacy result for the predicate it is claimed to
enforce or an explicitly recorded assumption.

**Rejected: one low-level lowering for every target.** It excludes specialized
implementations that are already correct and efficient.

**Rejected: admit a component by its name, signature or shape.** Identity
establishes nothing about the predicate it computes, and a component that
computes a value has a weaker obligation than one that enforces a condition.

**Reopen when** the freedom makes checking a produced candidate impractical, or
a component family has no adequacy statement that can be written.

## A target declares whether it acts on decoded values or on bytes

The declaration is part of the target's contract. A decoded boundary is
permitted when the received bytes do not affect anything the statement depends
on. When bytes feed a transcript, a hash, an external commitment or a claim
about canonical form, the target also constrains the decoding and the binding
between bytes and values.

**Rejected: treat the decoded relation as the statement about received bytes.**
It is a strictly weaker proposition. A byte sequence outside the valid range can
reduce into a value that the decoded relation accepts, while the honest
receiver rejects the same input.

**Reopen when** a decoder is proved total and injective over the advertised
byte domain, which makes the two propositions coincide for that target.
