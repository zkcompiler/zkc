# Formal associations and reduction inference

This contract retains the pending-claim association rules needed by typed formal
elaboration. The native layout checker currently retains formal source and
inventories obligations; it does not implement the formal association or
reduction assistance described here. Until the formal consumer implements these
rules, a source-claim export requiring them remains unavailable.

## Ownership and proof aids

`spec for P` may attach an owner specification to the unspecialized protocol in
the same defining module, regardless of declaration order. This replaces the
earlier requirement to nest a contract in its protocol. It keeps executable
signatures authoritative, permits execution without a spec, and gives owners
and consumer audits the same explicit subject syntax. Named audits and external
or specialized subjects are request-only; they cannot change provider premises.

Source ghost parameters and arguments express specification data dependencies.
They do not select a proof method or carry an executable argument. Loop
invariants, proof methods and reusable proof terms live in Lean companions.
The native profile refuses ghost actuals until it can keep their formal and
runtime positions separate. Erasing `ghost` before binding is never valid.

## One association for field-name binding

A declared pending-claim association maps a nominal claim type family to one
relation and a checked substitution of its fields into the relation's statement
formals. It must include the type and relation declaration identities, their
static arguments, field identities and purposes. Merely sharing a printed name
is insufficient. The association is declaration metadata, not a security claim.

The selected source annotation is `#[claim(Relation)]` on a pending-claim record.
It implies linear, sealed custody. Ordinary `#[linear] #[sealed]` records need
not opt into this convenience association. The annotation still requires the
logical-record and typed-formal integration; the current native resource reader
refuses it rather than accepting an unchecked association.

When a clause uses a claim value as the sole statement argument and binds the
relation's statement formals by field name, it must use that type's associated
relation. A second relation is not admitted through a proof adapter during
formation. A mathematical identity between presentations belongs in the proof.
This rule does not forbid a different relation from taking the entire claim as
an explicitly typed ordinary formal, or from describing a collection of claims.
The existing consistency rule for linear ports still applies to all clauses.

This preserves the earlier narrow one-relation rule. It does not create a global
rule that every property over a type has the same relation, and it does not
interpret all linear resources as cryptographic claims. Source and exported Lean
declaration metadata must agree before field-name binding is enabled.

## Explicit reductions and authoring assistance

Keep `reduces R(...) to S(...)` as the explicit source form. An absent clause
does not create a reduction claim. When no reduction clause is written, typed
authoring analysis may suggest exactly one same-relation clause only if:

1. There is exactly one pending claim input and one pending claim output.
2. They instantiate the same nominal claim family and associated relation.
3. Field-name binding fixes the associated statement fields on both sides.
4. Every remaining parameter or statement formal has one eligible same-name
   protocol input with the required type, purpose and role availability.
5. Any unbound witness formal is explicitly abstracted by the relation binding
   rules; no existential choice is silently selected as runtime data.

Ambiguity, multiple claims, different claim types, missing associations or
incompatible substitutions require an explicit clause. In particular, batching
and reductions that change the relation remain explicit. The derivation never
chooses a security property, probabilistic model, proof method or error bound.

The editor reports a reduction-shaped signature with no reduction claim and may
offer to insert the proposed clause as source text. The action records the
association and substitutions that justify its suggestion. It must not edit
source without the author's selection, choose a security request or create a
checked obligation while the clause remains absent. After insertion, normal
formation and independent source checking validate the written clause; the
suggestion carries no proof authority.

This replaces the earlier automatic same-relation derivation with authoring
assistance. Type-directed assistance still removes mechanical work, while the
relation being claimed stays visible and an omitted specification keeps its
execution-only meaning. The association reader and editor action remain pending;
examples currently write the relation pair explicitly.
Every declared postcondition remains mandatory independently of reduction or
security bundle selection; see [companions and requirements](companions.md).
