# Compiler transitions after the migration

> **Kind:** research note (design program, Compiler)
> **State:** Written 2026-09-03 from the family-instance probe and the
> oracle-proof compilation probe; no owner change proposed; two decisions
> named for the Compiler pass that follows the migration.
> **Authority:** None.

## 1. Why now

Two independent results this week arrive at the same mechanism. The
family-instance probe recommends that a protocol family's members be
generated outside the kernel and admitted one by one, and names a Compiler
transition as the generator's home. The oracle-proof compilation probe
finds that the commitment step of a BCS-style compilation is expressible
as a transition from a Core with logical Oracles to a Core with committed
ones, re-admitted under a new identity, and that nothing in the kernel
needs to change for it. Both therefore need the same thing to exist
exactly: a transition that is a checked change rather than an in-place
pass. The Compiler pages describe the model and defer the reconciliation of
foundational authority; this note fixes what a transition must carry so
that the reconciliation can be decided.

## 2. What a transition is

A transition takes an admitted subject and produces a candidate subject
together with an exact change record; the Compiler admits the candidate
like any other subject, under its own identity, and checks the change
record against a transition relation the transition names. Nothing about
the producer is trusted: it may be an MLIR pass, a generator, a hand-written
elaboration, or an external tool, and its output is admitted or refused on
the same terms. The two probes exercised the two halves:

- **Generation.** The producer takes a family parameter and emits one Core;
  the change record is the parameter and the regular function of it that
  the member's body realizes; the relation is membership in the family
  under that function.
- **Elaboration.** The producer takes a Core with `LogicalAccess` Oracles
  and emits a Core with `PublicBinding` Oracles and opening occurrences;
  the change record is the exact map from source occurrences, values, and
  Oracles to target ones; the relation is the commitment-opening profile's
  correspondence law.

## 3. What a transition must carry

1. **The source and target identities**, both admitted, and the profile
   under which each was admitted; a transition never carries bodies.
2. **The exact change record**, a canonical body under a transition-owned
   schema, from which the relation is decided without the producer's help;
   for elaboration this is the occurrence, value, and Oracle maps the
   compilation probe already forms; for generation it is the parameter and
   the regular function.
3. **The transition relation**, named as a declaration of a Compiler
   profile with its own selector and identity, so that "which relation was
   checked" is part of the transition's identity and rotates with the law.
4. **The property-relevant claim**, if any: which owner views the transition
   preserves exactly, which it changes, and under which Analysis premises a
   property of the source transports to the target; a transition that makes
   no claim is still a checked change, it just carries no transport.
5. **The decision**, deterministic and bounded, with the same outcome
   partition as admission: `Affirmative`, `Refused` with the exact clause,
   or a qualified noncompletion; a producer's failure is never a Compiler
   outcome.

## 4. Consequences for the pending reconciliation

- The kernel does not gain a template constructor, a family profile, or an
  in-place rewrite; the family-instance packet's first design and the
  compilation probe's composition both hold with transitions alone.
- The commitment elaboration is not a renaming. The compilation probe found
  that the target needs decoded asserted answers, separate evidence,
  claim-group checks, opening checks, and acceptance closure; the transition
  relation for it is the commitment-opening profile's law and the change
  record must carry enough to decide that law cold.
- The same-Core Fiat--Shamir checker must accept the migrated carrier before
  the elaboration transition can be checked end to end; that is a
  refreeze-class item of the migration, not a Compiler defect.
- Property transport across a transition is an Analysis judgment over named
  premises, never a Compiler assertion; the two premise kinds the compilation
  probe found missing belong to the Analysis catalog.

## 5. Decisions named for the Compiler pass

1. Whether transition relations are published as declarations of one
   Compiler profile that imports the owner profiles it reads, or as
   declarations of the owner profiles themselves; the first keeps owner
   pages free of Compiler vocabulary and is the reading this note takes.
2. Whether the exact change record is a subject with its own identity
   (portable, citable by an Analysis judgment) or process-local evidence
   retained by the transition's capability; portability argues for the
   first.

## 6. Non-claims

No transition is implemented, no relation is proved, and no property is
transported; the two probes are finite witnesses that the shape fits.
