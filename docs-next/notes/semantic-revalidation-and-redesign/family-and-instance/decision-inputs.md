# Families and instances: decision inputs

> **Kind:** decision packet (design program, prerequisite for the
> kernel-scope decision the peer review named)
> **State:** Drafted 2026-09-03 from the family-versus-instance probe; three
> decisions requested; nothing selected.
> **Authority:** None. A packet prepares a decision; the user takes it.

## 1. The question

A PIR Core is one finite explicit schedule: an instance. Protocols come in
families, indexed by a fold count, a variable count, a batch size, and the
theorems Analysis wants to bind are stated for the family. The peer review
asked how a family relates to its instances before the Analysis intake is
designed, and the intake is now authored. This packet asks for the decision.

## 2. Evidence

The probe (`README.md` in this directory, package
`evaluation/family-instance-probe/`) elaborated six bounded members of the
two retained family shapes, a fold count for FRI-like folding and a variable
count for sumcheck-like rounds, and measured each:

- every member admits as a separate finite Core with a distinct identity;
- the Core body grows by a regular function of the parameter, and the
  declarations that differ between consecutive members are exactly the
  repeated round or fold constructors;
- one family theorem source, sumcheck soundness, binds to every member
  through pointwise correspondence in the Analysis transport profile, with
  the parameter appearing only in the member's premise coordinates;
- what the probe could not measure: exact target graph counts (the retained
  fixture carrier lacks the full graph), template necessity, and
  family-profile attachment, all `CannotAnswer`.

## 3. The three designs

| Design | What changes | What rotates when a parameter changes | Where a theorem binds | Reopening condition triggered |
|---|---|---|---|---|
| Instances only; a generator outside the Core | nothing in the kernel; a front end or a Compiler transition emits one admitted Core per parameter | the instance's Core and Protocol identities only | to each member through the transport profile's member correspondence, with per-member premises | none |
| A template Core inside PIR | a bounded parametric constructor whose members are unfolded by an admission-time law | the Interaction kernel and every dependent profile | to the template, with an unfolding law as a premise | the constructor-sum reopening: a new Core constructor |
| A family as a semantic profile | a parametrized profile whose import fixes the parameters and the unfolding law | the family profile and its dependents | to the family profile | a new profile family and an import-time unfolding law |

The probe's regularity result is what a template or unfolding law would have
to state; the first design states nothing and generates it.

## 4. Recommendation

Adopt the first design. The kernel stays the finite explicit schedule that
every package, every mechanization, and every publication compiler already
reads; a parameter change is an ordinary new instance with its own identity;
and family theorems bind pointwise through the member correspondence the
transport profile already owns, which the named-premise intake now makes
explicit per member. The generator's natural home is a Compiler transition,
because generation is a checked change whose result is re-admitted under a
new identity, which is what the Compiler is; a front end may also emit
instances, since admission does not care who authored a Core.

The cost is real and bounded: a family-level statement about zkc's own
artifacts, "every member of this family admits", is a statement about the
generator, checked by running it on a finite range and by the regularity
finding, not a kernel theorem. That is the same discipline as the
expressibility matrix: predicted places, checked members.

## 5. Decisions requested

1. Adopt the first design: the Core stays instance-only; no template
   constructor and no family profile enter the kernel.
2. Name the generator's home as a Compiler transition (with a front end
   allowed to emit instances) and record that the generator is untrusted:
   every emitted Core is admitted like any other.
3. Record that family theorems bind to members through the transport
   profile's member correspondence with per-member named premises, so that
   the parameter is a premise coordinate and never a kernel field.

## 6. Reversal condition

Reverse the first decision if a selected protocol's members cannot be
finitely elaborated (an unbounded or data-dependent round structure) or a
required family theorem cannot be bound pointwise because its statement
quantifies over the parameter in a way the member premises cannot carry.
Either would reopen the constructor sum, which is the recorded condition.

## 7. What this packet does not decide

The peer review named a second prerequisite, how a BCS-style compilation of
an interactive oracle proof enters the kernel. That is a separate packet with
its own evidence; nothing here constrains it beyond keeping the Core
instance-only.

## 8. Non-claims

No theorem is proved, no family is adopted into the kernel, no generator
exists yet, and no soundness or completeness statement is made about any
member.
