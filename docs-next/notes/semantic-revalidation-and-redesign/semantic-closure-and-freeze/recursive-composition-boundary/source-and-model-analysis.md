# Recursive Composition Source and Model Analysis

> **Kind:** Temporary primary-source synthesis and candidate analysis
> **State:** Completed source synthesis
> **Authority:** None

## Source constraints

### Missing linkage is a semantic defect, not a weak implementation detail

The corrected Nova paper identifies an instance that the verifier assumed had
been folded into a running instance even though no check established that
linkage. Its repair removes that free instance and changes the hash check so the
running instance is included in the checked digest. The transferable design
constraint is total recursion-facing coverage: every instance occurrence that
can influence a recursive step needs an exact discharge or a checked binding
path into the carried obligation. Type compatibility and satisfiability of an
unrelated instance are insufficient.

Hash collision resistance is not a structural Relations fact. Relations can
check that the exact digest construction and equality paths cover every named
occurrence. Analysis must separately state the hash assumption and the theorem
that interprets that binding.

### Incrementality and non-transferability are different properties

The same Nova source shows that a proof carrying enough predecessor material
can be extended with a different final auxiliary input, and gives three
application-dependent mitigations. Compression and fixed context prevent the
attack but prevent efficient third-party continuation. Incremental context
preserves handoff by explicitly changing the digest-bound verification context
at each boundary.

ProtoStar makes the complementary point: outsourcing a final decider behind a
SNARK may be useful, but the resulting proof is not a strict IVC proof when an
arbitrary prover can no longer continue from it. ProtoGalaxy observes that a
mutually distrustful receiving party may need to run the decider on incoming
accumulators before extending them.

Therefore a portable value and a causal continuation right must remain
different:

```text
serialized accumulator/witness material
  -> decode + ordinary source admission + optional decision/proof check
  -> new local input occurrence

same-process accepted continuation
  -> one-use owner capability
  -> exact fresh target ingress occurrence
```

The first path may support a theorem after independent checking. It does not
recreate the second path's occurrence identity or capability.

### One step does not imply an induction theorem

The accumulation-to-PCD source proves a conditional construction for
constant-depth compliance predicates under an explicit sublinear verifier
hypothesis. It explains why the depth restriction is necessary for its
extractor argument. ProtoStar applies that theorem only after separating its
random-oracle construction from the standard-model premise and naming a
Fiat--Shamir heuristic to bridge them.

Consequently an IVC/PCD theorem application must retain at least:

- the exact protocol or program family;
- the exact step/compliance relation and recurrence discipline;
- the accumulation/NARK theorem schema and source validation;
- the execution-depth and compliance-predicate-depth domains quantified by that
  theorem;
- the standard-model or random-oracle model distinction;
- any heuristic hash instantiation premise;
- the decider and outstanding-obligation meaning; and
- the theorem's completeness, soundness, and efficiency conclusions as
  separate families.

A sequence of live `CheckedCausalPlanStepRecurrence` results is not an Analysis
theorem subject. Those results are deliberately nonidentified and
nonserializable. A finite live-chain checker may confirm adjacency and complete
coverage for one execution context, but theorem identity must quantify over an
authenticated family and its exact induction law.

The live result still needs a lawful cross-owner path when Analysis establishes
one concrete occurrence premise. The selected path is a narrow Relations
owner-local source binding over the complete checked result, followed by an
exact Analysis source profile, concrete manifest, local support handle, and
matching fresh capability. It creates no portable recurrence record. The
recurrence and binding-coverage results occupy two mandatory,
noninterchangeable slots; CycleFold uses a separate one-slot profile. This
closes occurrence support without allowing a copied result or a finite chain
to stand for a family theorem.

### Uniformity closes the semantic loop without a fixpoint

HyperNova's non-uniform IVC chooses from a setup-fixed finite set of predicates
using a public program counter; it does not generate a new verifier relation at
runtime. Its compatibility conditions require structure and instance encoding
to be independent of witnesses. The corrected Nova construction similarly
derives augmented relations deterministically from fixed functions and uses
verification-key material as relation advice.

The selected uniformity candidate therefore has three independent clauses:

1. **Structure closure:** every possible continuation target is a closed,
   pre-authenticated finite owner subject independent of runtime instance and
   witness values.
2. **Self-reference discipline:** Analysis derives a description digest over
   the complete family body under the declared portable algorithm and
   evaluation; the relation exposes only an exactly grounded ordinary advice
   coordinate, and no subject embeds its own identity or the derived output.
3. **Selection, not generation:** runtime data may choose one member of a
   setup-fixed finite family, but cannot synthesize a new Core, Plan, relation,
   or admission law.

This is an admission condition on a recursion-facing family, not a claim that
all members satisfy an IVC theorem.

### Deferred verification needs a visible obligation type

Accumulation separates a cheap update verifier from a later decider. An
accepting update therefore may establish only that a new accumulator was
formed consistently, conditional on the decider accepting the carried
accumulator. Treating the step terminal as unconditional verification erases
the central semantic distinction of accumulation.

The selected Analysis shape derives an exact finite obligation set from the
theorem's hypothesis treatment and the family's carried slots. Each entry names
a relation/decider goal, the public carried coordinate that represents it, and
the only authorized discharge operation. Callers do not provide this set.
Reports distinguish a conditional result, complete carried-obligation
discharge with other hypotheses retained, and a genuinely hypothesis-free
result. PIR terminal acceptance and Relations recurrence remain unchanged.

### CycleFold's companion relation is intra-step

CycleFold creates a committed relaxed-R1CS instance whose public I/O contains
the fold challenge, two input commitments, and their claimed linear
combination. The primary verifier reads that claimed result only after checking
the companion instance's strict form and exact public-I/O agreement, then folds
the companion instance into its own running accumulator during the same
protocol step.

A future complete elaboration must preserve that same-step relationship. A
two-run encoding is admissible only if an exact checked relation proves the
same strictness, public-I/O equality, and before-step-completion fold. Merely
passing the companion witness through an accepted-terminal continuation would
recreate the unbound-instance shape.

## Candidate assessment

| Candidate | Source fidelity | Authority behavior | Disposition |
|---|---|---|---|
| no new laws | leaves known digest, reporting, and uniformity gaps implicit | downstream consumers can invent induction informally | reject |
| universal recursion subject | conflates folding, accumulation, decision, continuation, and theorem families that sources keep distinct | creates a second execution/theorem center | reject |
| owner-separated boundary laws | preserves current one-step semantics and adds only missing preconditions, exact cross-owner occurrence support, and theorem homes | matches existing PIR, Relations, Analysis, and Realization authority | selected and absorbed |
| serializable causal authority | confuses portable validity with process-local occurrence causality | equal bytes could recreate a consumed right | reject for v0 |

The selected laws, finite falsifiers, durable absorption, and review
adjudication are complete. Concrete recursive protocol implementations and
their theorem evidence remain future witness packages rather than unfinished
parts of this boundary decision.
