# Protocol semantics and transformation theory

> **Document kind:** Temporary theory research dossier
> **Document state:** First research pass complete; factorization reconciled
> **Authority:** None. Established results, zkc interpretations, and candidate
> laws are separated. This page makes no security claim about zkc.
> **Disposition:** Absorb reviewed semantic laws and architecture rationale into
> Protocol, Compiler, OIR, Analysis, and decision owners, then delete this page.

## 1. Central result

Theory supports the current idea that a Protocol has two coupled geometries:

```text
ordered protocol-effect spine
             +
typed linear claim and reduction graph
```

Ordinary SSA remains useful for pure computation and value dependencies. It is
not a sufficient equivalence model for message I/O, transcript state,
challenges, checks, decisions, and composition context.

The principal refinement is that “effect” and “commutation” are
observation-relative. At minimum distinguish:

- Fiat--Shamir and transcript observations;
- proof-wire and ABI observations;
- public statement binding;
- checks, rejection, and terminal decisions;
- claim flow and property-derivation sites; and
- imported-artifact verification.

A transformation can commute for one observer while changing another. “No
absorb and no challenge” may establish transcript-relative centrality; it does
not establish full Protocol or endpoint equivalence.

This is a carrier-independent normative semantics. It does not imply a second
Rust IR or removal of MLIR.

## 2. Interactive protocols and Fiat--Shamir

### 2.1 Round structure is semantic

**Established result.** Interactive oracle proofs expose prover messages,
verifier randomness, oracle access, queries, and round count explicitly. Their
Fiat--Shamir analysis depends on interaction and state-restoration structure.
See
[Interactive Oracle Proofs](https://eprint.iacr.org/2016/116.pdf).

**Established result.** Multi-round Fiat--Shamir transformations have bounds
that depend on round and extraction structure, with specialized results for
structured protocol classes. See
[Fiat--Shamir Transformation of Multi-Round Interactive Proofs](https://eprint.iacr.org/2021/1377.pdf).

**PIR transfer.** Two systems can decide the same final relation yet differ in
transcript trees, extraction structure, and quantitative loss. Round,
challenge, and dependency structure must remain authenticated Protocol
semantics rather than optimizer metadata.

### 2.2 Interactive and compiled denotations differ

**Design inference.** A public-coin interactive protocol and one of its
Fiat--Shamir constructions are related subjects, not literally identical
executions. Shared syntax is useful, but the relation has theorem, assumption,
and quantitative parameters.

A suitable result shape is:

```text
FSValid(interactive_core, construction, theorem, assumptions, parameters)
  => Security(compiled_protocol, adjusted_bound)
```

It is not unrestricted equality between fresh interactive randomness and a
stateful transcript construction.

## 3. Framing, codecs, and duplex state

**Established result.** Recent duplex-sponge Fiat--Shamir analysis makes the
concrete stateful construction and codec explicit. See
[A Fiat--Shamir Transformation From Duplex Sponges](https://eprint.iacr.org/2025/536).

**Established result.** SAFE binds an I/O pattern and domain separator at
initialization and checks later absorb/squeeze kinds and lengths. See
[SAFE](https://eprint.iacr.org/2023/522.pdf). STROBE likewise treats operation
kind, direction, metadata, length/framing, and domain separation as transcript
content. See the
[STROBE protocol framework](https://strobe.sourceforge.io/papers/strobe-20170103.pdf).

**PIR transfer.** A challenge is not merely `hash(previous_values)`. Its
semantics includes:

- an exact typed prefix;
- operation boundaries and injective framing;
- domain and composition context;
- codec and field/group representation;
- absorb/squeeze segmentation;
- sampling map, count, and scalar/vector interpretation; and
- construction parameters.

Adjacent sponge calls may be aggregatable at one construction layer without
being equivalent Protocol schedules. Any quotient needs an exact theorem and
sampling relation.

## 4. Ordered effects and independence

### 4.1 Theory basis

**Established result.** Premonoidal categories model effectful computation
without assuming a universal interchange law; central morphisms commute under
the relevant structure. See
[Premonoidal Categories and Notions of Computation](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/54C062AA3C990322C50595D5533B2BB4/S0960129597002375a.pdf/premonoidal_categories_and_notions_of_computation.pdf).

**Established result.** Mazurkiewicz trace theory identifies sequential words
only through swaps admitted by an explicit independence relation. See
[Theory of Traces](https://doi.org/10.1016/0304-3975(88)90051-5).

**PIR transfer.** The usable compiler concept should be a typed,
relation-indexed predicate:

```text
`Independent[claimed_relation](event_a, event_b)`
```

Independence cannot be inferred merely because ordinary SSA has no edge
between two operations.

### 4.2 Observation footprints

Candidate event footprints are:

```text
FS        absorb, squeeze, challenge derivation
WIRE      proof or message read/write and encoding
PUBLIC    statement and public-input binding
CHECK     verifier predicates and named rejection
ARTIFACT  imported-artifact verification
CLAIM     claim production, transformation, and discharge
TERMINAL  accept, reject, abort, and finish
```

Adjacent events commute for a claimed relation only when:

1. neither causally or computationally depends on the other;
2. their footprints commute for every protected observer in that relation;
3. no claim rule or property premise observes their relative position; and
4. their framing and construction behavior is equal under the selected
   transcript construction.

This yields distinct notions such as `CenterFS`, `CenterWire`,
`CenterJudgment`, and `CenterFull`. An unqualified `center` should mean the
full relation or be rejected as ambiguous.

## 5. Projection and compiler correctness

### 5.1 Observable relations

**Established result.** CompCert states correctness over observable event
traces and termination behaviors, not SSA similarity. See
[A Formally Verified Compiler Back-end](https://xavierleroy.org/publi/compcert-CACM.pdf).

**Established result.** When source and target have different event alphabets,
compiler correctness can use a relation between their traces rather than
literal equality. See
[Trace-Relating Compiler Correctness and Secure Compilation](https://arxiv.org/abs/1907.05320).

**PIR transfer.** PIR-to-OIR projection needs a relation from global role-
indexed events to local endpoint observations. It should establish matching
message occurrences, transcript actions, counterparty obligations, and
termination behavior without pretending the two IRs expose identical traces.

### 5.2 Translation validation

**Established result.** Translation validation checks each produced result
instead of verifying the whole optimizer implementation. See
[Translation Validation for an Optimizing Compiler](https://doi.org/10.1145/349299.349314).
Alive2 shows a practical bounded validator for LLVM refinements and also relies
on a precise source semantics. See
[Alive2](https://web.ist.utl.pt/nuno.lopes/pubs.php?id=alive2-pldi21).

**PIR transfer.** Search and optimization may remain untrusted, while a smaller
checker validates each accepted successor under a named Protocol relation.
Structural or trace validation still does not transport soundness, knowledge,
completeness, or zero knowledge. Those need explicit adversarial,
probabilistic, assumption-indexed rules; probabilistic relational logics are a
methodological precedent, not an off-the-shelf PIR theorem. See
[Probabilistic Relational Hoare Logics](https://www.microsoft.com/en-us/research/publication/probabilistic-relational-hoare-logics-for-computer-aided-security-proofs/).

## 6. Global-to-local projection

**Established result.** Multiparty session and choreography models define a
global interaction and project it into role-local behaviors, with results
about communication safety, linear use, progress, and fidelity. See
[Multiparty Asynchronous Session Types](https://www.doc.ic.ac.uk/~yoshida/multiparty/multiparty.pdf).

**Useful transfer.** PIR can borrow:

- global-to-local projection;
- send/receive duality;
- unique event occurrence correspondence;
- linear channel and obligation use; and
- refusal when a coherent local behavior cannot be derived.

**Analogy limit.** Session fidelity does not establish cryptographic
soundness, Fiat--Shamir validity, relation correspondence, or honest-prover
completeness.

## 7. Convergence-refined semantic factorization

Conceptually distinguish:

```text
InteractiveCore I
  = roles
  + canonical typed semantic ports
  + typed protocol events and causal dependencies
  + one selected total observable schedule extending those dependencies
  + claim and reduction graph
  + checks and terminal condition
  + fresh public-coin challenge occurrences
  + abstract prover obligations

TranscriptConstruction K
  = initialization and domain schema
  + duplex, hash, or oracle profile
  + typed framing and codecs
  + absorb and squeeze behavior
  + sampling maps and parameters

ChallengeInterpretation X
  = FreshPublicCoins
  | FiatShamir(K scoped to I)

Protocol P
  = I paired with X

ProtocolInterface J[P]
  = external callable ABI bound to P's canonical ports and proof events

ProverPlan L[P]
  = one construction realizing P's abstract prover obligations
```

The total schedule belongs to `InteractiveCore`: an interactive protocol is
already an ordered conversation, while Fiat--Shamir interprets that existing
history. A partial-order authoring form remains a template until one total
schedule is selected. This factorization does not imply separate serialized
files for every nested subject.

Useful denotations include:

```text
meaning(I, interactive)
meaning(I, K, fiat_shamir)
global_trace(P)
local_trace(project(P, J, role))
claim_derivation(P, property_rules, assumptions)
plan_realizes(P, L)
```

Stage 1 selected separate nested `CoreId` and
`TranscriptConstructionId`, a `ProtocolId` committing to Fresh or
Fiat--Shamir interpretation, dependent `ProtocolInterfaceId`, and separate
`ProverPlanId`. These identities do not require separate mutable IR
authorities. The durable owner is the
[Protocol IR Architecture](../../../project/protocol-ir-architecture.md).

## 8. Candidate semantic laws

1. **Visible-effect completeness.** Every Protocol-visible action has one
   explicit typed event. Opaque computation cannot hide transcript, wire,
   public-binding, check, claim, artifact-verification, or terminal effects.
2. **Linear state evolution.** Transcript and proof-stream states are consumed
   once and yield one successor; they cannot be cloned, dropped, or merged.
3. **Challenge occurrence fidelity.** Each sampling occurrence is distinct.
   Reuse of a sampled value is different from CSE of two occurrences.
4. **Prefix causality.** A challenge reads only its declared prior absorbed
   prefix and pinned initialization context.
5. **Injective typed framing.** Domain, event class, codec, count, and required
   boundaries participate in transcript construction.
6. **Context closure.** Protocol family, semantic version, construction
   profile, composition occurrence, and theorem-required statement data are
   bound at declared positions.
7. **Sampling fidelity.** Interactive sampling and Fiat--Shamir decoding have
   an explicit distributional relation and quantitative loss.
8. **Observer-indexed reordering.** Identity-neutral rewriting preserves every
   protected observer; other reordering requires a checked independence claim.
9. **Linear claim accounting.** Production, reduction, duplication, folding,
   and discharge are explicit typed operations governed by exact rules.
10. **Dual endpoint projection.** Both endpoints refer to the same global event
    occurrences with matching classes, positions, transcript actions, and
    exhaustive counterparty obligations.
11. **Security non-intrinsicness.** Security properties are judgments over an
    identified subject, rules, assumptions, and parameters, not booleans stored
    by the IR.
12. **Composition-context explicitness.** Sequential composition, parallel
    claim composition, transcript interleaving, shared challenges, and
    recursion are distinct constructors.
13. **Transformation evidence.** Every accepted successor names source,
    target, claimed relation, validation rule, open assumptions, and property
    or bound deltas.
14. **Semantic-input closure.** Every datum read by a normative transition is
    committed by its source or supplied as a separately identified input.
15. **Failure-class semantics.** Invalidity, unsupported profile, supplier
    failure, malformed proof, named rejection, and normal rejection remain
    distinct observations.

## 9. Counterexamples to ordinary dataflow equivalence

- Swap two absorbs with no SSA edge before one squeeze.
- Remove an absorbed commitment unused by the final boolean predicate.
- Move public-statement binding after the first challenge.
- CSE two same-typed challenge occurrences.
- Replace two scalar squeezes with one vector squeeze.
- Interleave two claim-independent reductions that share transcript state.
- Encode typed pairs by ambiguous raw concatenation.
- Invoke one child twice without an occurrence namespace.
- Reorder an unabsorbed proof slot: FS trace is unchanged, wire ABI is not.
- Replace a multi-round protocol by the same final acceptance predicate.
- Reorder total checks that return the same boolean but expose different named
  rejection or early termination.
- Preserve endpoint accept language while changing the claim graph needed by a
  soundness derivation.

## 10. Transformation relations to distinguish

- **representation equivalence:** carriers decode to one semantic subject;
- **exact Protocol equality:** identified events, graph, interfaces, and
  construction schedule agree;
- **observer-relative trace equivalence:** a named observer set agrees;
- **trace refinement:** every target trace relates to an allowed source trace;
- **distributional equivalence or coupling:** outcome distributions relate;
- **Fiat--Shamir preservation:** schedule equality or theorem-authorized
  construction relation;
- **property transport:** premises, assumptions, and quantitative bounds map;
- **checked non-preserving change:** semantic and property deltas are explicit;
- **cost improvement:** an orthogonal objective judgment.

No transform should merely claim “semantic equivalence.”

## 11. Concepts deliberately not selected

The current finite two-role public-coin scope does not yet justify:

- a complete pi-calculus or multiparty-session language;
- event structures or pomsets as the sealed deployed form;
- interaction trees as the primary compiler carrier;
- general effect quantales as user-facing syntax;
- robust-hyperproperty secure compilation for arbitrary hostile contexts;
- universal semantic-equivalence checking;
- symmetric-monoidal commutation for every transform; or
- probabilistic bisimulation as the default admission mechanism.

Some may remain useful formalization targets. For example,
[Interaction Trees](https://arxiv.org/abs/1906.00046) can model effectful
denotations, and the recent [VCVio](https://eprint.iacr.org/2026/899) preprint
explores oracle histories through algebraic effects and handlers. Neither
becomes semantic authority merely by being adopted as a proof tool.

## 12. Provisional theory pressure on Stage 1

Theory currently favors:

- retaining the ordered spine plus claim-flow graph;
- treating interactive and Fiat--Shamir meanings as distinct denotations;
- introducing an explicit observation and effect algebra;
- making centrality and commutation relation-indexed;
- specifying PIR-to-OIR with trace relation plus endpoint duality;
- validating each heuristic transform result under a named relation; and
- keeping property transport separate from structural and trace validation.

It does not decide whether those concepts occupy one MLIR dialect, several
dialects, a portable schema, or an independent checker view.
