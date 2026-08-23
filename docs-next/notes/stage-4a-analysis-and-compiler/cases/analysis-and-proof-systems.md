# Analysis and proof systems

> **Document kind:** Temporary primary-source comparative dossier
> **Document state:** Stage 4A.2 external-case research pass; convergence input
> **Authority:** None. This page records source facts, research deductions,
> candidate pressure, transfer limits, and falsifiers. It does not define an
> Analysis judgment, select an Analysis calculus or proof system, establish a
> theorem or model correspondence, prove a cryptographic property, mint a
> capability, or authorize implementation or migration.
> **Scope:** Typed judgments and contexts, equality and refinement,
> probabilistic and distributional reasoning, cryptographic hypotheses,
> derivation objects, theorem/model correspondence, independent checking,
> qualified outcomes, and replay.
> **Disposition:** Absorb reviewed constraints and selected rationale into the
> eventual durable `analysis/` and exact cross-domain owners; retain rejected
> alternatives and reversal triggers in the Stage 4A convergence record; delete
> this page before documentation cutover.

## 1. Research question

What can zkc learn from existing formal systems about asking and answering an
exact semantic or cryptographic question over admitted Stage 3 subjects without
letting a prover namespace, proof artifact, solver status, mutable session, or
compiler policy silently define the question's meaning?

The investigation tests the following possible separation:

```text
exact admitted zkc subjects and views
  -> exact zkc question and semantic proposition
  -> internal rule or external theorem/model instantiation
  -> checked derivation, proof term, or certificate
  -> Analysis-owned inference
  -> qualified result under an explicit hypothesis and trust basis
```

This is a research hypothesis, not a selected architecture. The cases are used
to expose which distinctions a Stage 4A candidate may need to preserve and
which mechanisms are artifacts of a host prover or historical design path.

## 2. Evidence and inference discipline

Only primary papers, official specifications, official project documentation,
and source repositories are used. The labels below have distinct force:

- **Source fact** reports a mechanism, theorem boundary, or limitation stated
  by a source.
- **Strength** identifies what that mechanism makes precise or independently
  checkable in its installed setting.
- **Pain point** records a constraint, ambiguity, or difficult-to-reverse
  choice exposed by the system's design path.
- **Research implication** names pressure that a Stage 4A candidate should
  answer. It is not a ratified zkc contract.
- **Non-transfer** states what the external result cannot establish for zkc.

No proof assistant, logic, checker, theorem library, or certificate format is
treated as a vote. A machine-checked external theorem establishes only its
exact formal statement under its exact logic, imports, definitions, axioms,
and assumptions. Its correspondence to a zkc question remains separate.

## 3. Comparative map

| Case | Principal strength | Path-dependent pain point | Narrow Stage 4A research implication | Non-transfer |
|---|---|---|---|---|
| [EasyCrypt](https://easycrypt.gitlab.io/easycrypt-web/docs/welcome/) | Distinct unary, relational, probabilistic, and probabilistic-relational judgments over procedures, memories, and adversarial modules | Global state can alter auxiliary-input assumptions; module limitations complicate compositional correspondence; protocol-specific experiment shapes can become rigid | Test explicit initial-state, adversary, experiment, relation, and quantitative-bound fields rather than a property label alone | EasyCrypt modules, theorem names, and namespaces cannot identify a zkc claim |
| [SSProve](https://github.com/SSProve/ssprove/tree/c6d7d4bc3a0a671c92899aa49dfcfb065d1bdbbd) | Machine-checked connection between a high-level package algebra and low-level probabilistic relational reasoning | Raw composition is totalized and relies on interface, validity, and state-separation premises to exclude semantically bad cases; global locations leak into theorem shape | Test a separation among raw construction, admitted composition, property judgment, and quantitative transport | SSProve packages and Gallina terms cannot replace admitted Protocol subjects |
| [CryptHOL](https://isa-afp.org/browser_info/current/AFP/Game_Based_Crypto/CryptHOL_Tutorial.html) | Subprobability semantics, explicit losslessness, hidden oracle state, and separate concrete and asymptotic theorem forms | Locale dependencies can be ambient; extensional semantics does not by itself formalize feasible adversaries or cost | Test explicit termination, oracle, query, resource, and concrete-to-asymptotic contexts | Distribution equality cannot be imported as computational indistinguishability or feasibility |
| [F*](https://fstar-lang.org/tutorial/book/) and [Low*](https://www.microsoft.com/en-us/research/publication/verified-low-level-programming-embedded-f/) | Typed preconditions, postconditions, effects, ghost/runtime separation, and implementation refinement | Mainline F* trusts its SMT encoding and solver; proof terms are generally unavailable; unimplemented interfaces introduce axioms; Low* targets implementation correctness | Test typed property-family schemas, explicit trust profiles, and separation of property proof from implementation proof | F* acceptance or verified extraction cannot automatically transport a Protocol property |
| [Lean](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) | Small-kernel checking, inspectable axiom closure, and workflows that separate statement comparison from proof replay | Kernel acceptance proves the elaborated proposition under exact imports and axioms, not that the proposition means the intended zkc claim; compiled artifacts remain environment-sensitive | Test separate identities for semantic proposition, external statement, proof, basis, and replay occurrence | A checked Lean theorem is not a zkc judgment without checked correspondence |
| [Rocq](https://rocq-prover.org/doc/master/refman/practical-tools/coq-commands.html) | Kernel rechecking and standalone `rocqchk` checking of logical contents and dependencies | `.vos` can expose statements without opaque proofs; `Admitted` adds assumptions; `.vo` artifacts are version- and environment-bound | Test separate states for interface availability, completed proof, accepted assumption closure, and cold replay | A checked `.vo` establishes only the corresponding Rocq proposition |
| [Why3](https://why3.org/doc/itp.html) | Session DAGs retain transformations, provers, versions, limits, outcomes, obsolescence, and replay | A session is mutable orchestration state; a repeated status does not show that theorem meaning or model correspondence is unchanged | Test derivation plans and checker attempts as replayable but non-authoritative records | A Why3 session result cannot mint a zkc semantic capability |
| [SMT-LIB](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf), [Alethe](https://verit.loria.fr/alethe.pdf), and [Carcara](https://github.com/ufmg-smite/carcara/tree/6624ea80cf1985ada473c0705869c78353e4282d) | Clear `sat`, `unsat`, and `unknown` statuses; proof-producing solvers can be separated from certificate checkers | SMT-LIB has no universal proof format; proof production is optional; certificate-rule and theory coverage evolve; query encoding and polarity remain part of the basis | Test qualified attempt outcomes and exact query, polarity, theory, certificate, and checker binding | `unsat` is not inherently an affirmative property result; an invalid certificate is not a negative property judgment |
| [Dedukti](https://github.com/Deducteam/Dedukti/tree/f3c0eba869ddd46f2e75c123a59f2b612076dba0) | A small logical framework can check proofs translated from several source systems | Translation correctness, logical alignment, encoded theory, and rewrite assumptions remain additional obligations | Test proof-language translation as an explicit adapter basis rather than an invisible bridge | A common proof language relocates trust and does not prove zkc model adequacy |
| [CompCert](https://compcert.org/doc/) | Simulation theorems name exact source/target semantics and direction; stronger results retain determinacy and receptiveness conditions | The proof architecture is coupled to the selected intermediate semantics and observation model | Test relation direction, observers, and every side condition as part of rule instantiation | CompCert's trace and undefined-behavior model is not a Protocol relation |
| [Interaction Trees](https://www.cis.upenn.edu/~stevez/papers/XZHH%2B20.pdf) | Trace refinement is defined over an explicit event interpretation and trace model | Finite traces do not distinguish every divergence or stuckness behavior; changing interpretation changes observation | Test observer, event projection, termination, divergence, abort, and failure policy in trace claims | There is no model-independent `TraceEq` or `TraceRefines` |
| [Iris](https://iris-project.org/) and [ReLoC](https://iris-project.org/pdfs/2021-lmcs-reloc-reloaded-final.pdf) | First-class refinement judgments compose inside a logic more effectively than an external meta-level relation | Worlds, invariants, ghost state, and step indexing add substantial machinery for concurrency and higher-order state | Test relations as first-class typed judgments while keeping automation outside semantic rule meaning | Concurrency machinery has no automatic place in a finite Protocol core |
| [eRHL](https://www-sop.inria.fr/members/Martin.Avanzini/publications/ABDG%3APOPL%3A25.html) and [Lilac](https://www.ccs.neu.edu/home/amal/papers/lilac.pdf) | Quantitative relational pre/postconditions can express distance, equivalence, independence, and conditioning | Completeness and expressiveness depend on termination and semantic class; full measure- or separation-logic machinery is expensive | Test metric, conditioning, correlation, abort mass, and termination as explicit indices | These systems do not imply that v0 needs a universal measure-theoretic logic |
| [Multi-round Fiat--Shamir](https://link.springer.com/article/10.1007/s00145-023-09478-y) and [VCVio](https://eprint.iacr.org/2024/1819) | Theorem statements expose dependence on property notion, oracle model, rounds, challenge policy, query budget, and quantitative loss | No one forking lemma or Fiat--Shamir theorem covers every Protocol class, adversary regime, or property | Test `FSCompile` as property- and theorem-indexed with exact source, target, construction, model, premises, and loss | A structural Fiat--Shamir construction does not transport a property by itself |
| [Foundational proof-carrying code](https://www.cs.princeton.edu/~appel/papers/fpcc.pdf) | An untrusted producer supplies a certificate for an exact subject and a consumer-defined policy, checked by a smaller trusted basis | Machine semantics, policy interpretation, certificate logic, and checker remain trusted; certificates may be expensive | Test persistence only where a named independent consumer and real trust separation justify it | Machine-code safety certificates do not imply that every Analysis result needs one portable proof format |

## 4. Cryptographic judgment systems

### 4.1 EasyCrypt

**Source facts.** EasyCrypt provides distinct probability expressions, unary
Hoare logic, probabilistic Hoare logic, relational Hoare logic, and
probabilistic relational Hoare logic. Probability expressions identify a
module instantiation, procedure, arguments, initial memory, and event.
Subdistributions permit nontermination, while losslessness is an additional
property. Abstract theories can be cloned with concrete types and operators,
but their assumptions must then be discharged.

The primary [Zero-Knowledge in EasyCrypt](https://eprint.iacr.org/2022/926.pdf)
development formalizes completeness, special soundness, extractability,
soundness, zero knowledge, and sequential composition as different properties
and derivations. It also records that changing a party representation from a
stateful program to a mathematical distribution simplified one proof pattern
but made results across the two representations incompatible.

**Strength.** The exact experiment, memory policy, adversary, relation, and
bound are visible. Generic theorems expose their premise substitutions and
bound transformers instead of producing a generic `secure` marker.

**Pain points.** Ambient globals can introduce auxiliary input. Missing
module-copy and module-equality mechanisms complicate some composition
arguments. A three-message Sigma-protocol framework can embed that protocol
shape into property definitions, making later repetition or generalization
require new experiments rather than a generic instantiation.

**Research implications.** An Analysis candidate is pressured to identify an
exact property experiment, initial-state policy, adversary initialization,
auxiliary input, state sharing, rewinding permission, relation, and loss
function. A change from programs to distributions, or from one experiment
representation to another, appears to require an explicit correspondence
rather than a name match.

### 4.2 SSProve

**Source facts.** The [SSProve paper](https://eprint.iacr.org/2021/397.pdf) and
[formal repository at the research snapshot](https://github.com/SSProve/ssprove/tree/c6d7d4bc3a0a671c92899aa49dfcfb065d1bdbbd) separate raw
probabilistic code, packages with import/export interfaces and location
footprints, valid package composition, relational judgments, and high-level
game indistinguishability. The connection from the low-level relational logic
to high-level package reasoning is machine checked in Rocq. Advantage
relations and triangle inequalities support quantitative game hopping.

**Strength.** Structural package composition, state compatibility, relational
proof, and security transport are separately visible. A game-hop theorem can
retain exact left and right games, adversary, invariant, intermediate claims,
and accumulated bound.

**Pain points.** Raw package composition is totalized: unresolved calls or
overlapping exports have defined fallback behavior, while validity premises
prevent those cases from legitimizing a theorem. Concrete global locations
simplify the formalization but make private state, freshness, and separation
premises difficult and sometimes verbose. Its free-monad/Gallina split is a
host-language design, not a neutral Protocol carrier.

**Research implications.** The case pressures candidates to distinguish a raw
composition proposal, structural admission, a relation over composed subjects,
and property-specific composition. It also motivates testing a derivation DAG
whose nodes retain exact premise occurrences, substitutions, side conditions,
and bound algebra.

### 4.3 CryptHOL

**Source facts.** CryptHOL uses subprobability distributions and generative
probabilistic values for stateful black-box oracles. Losslessness is a material
premise. Concrete security theorems can be lifted to asymptotic theorems under
explicit negligibility and eventual side conditions. Isabelle locales provide
parameterized theories and Transfer supports representation-independence
arguments.

The official tutorial explicitly notes that extensional semantics does not
formalize polynomial-time feasibility, so the fully quantified statement over
all feasible adversaries lies outside that model.

**Strength.** Hidden oracle state, query behavior, termination, concrete
advantage, reduction, and asymptotic lifting are separately exposed.

**Pain points.** Locale parameters and assumptions can be visually ambient
even though they remain logically present. Extensional equality is stronger
than bounded computational indistinguishability. Shared randomness requires
explicit sequencing rather than an implicit common probability space.

**Research implications.** The case pressures candidates to treat concrete
and asymptotic claims as different judgments or as an explicit derivation, to
retain losslessness and oracle restrictions, and to keep operational resource
semantics separate from extensional distribution semantics.

### 4.4 F* and Low*

**Source facts.** F* refinement and computation types express preconditions,
postconditions, effects, and state relations. User-defined indexed effects can
package a reasoning discipline behind ordinary program syntax. Ghost content
is erased. Low* relates a restricted source language to memory-safe,
functionally correct low-level implementations and extracted C.

F* documentation states that its SMT-based workflow trusts the encoding and
Z3; solver success does not generally yield a proof term. An interface without
an implementation acts as an assumption.

**Strength.** Logical specifications, ghost evidence, executable content,
implementation refinement, and extraction are distinguishable.

**Pain points.** Solver trust and proof sensitivity are part of the basis.
Erased proof material does not travel with runtime artifacts. Low* solves an
implementation-verification problem, not a canonical game-based property
calculus.

**Research implications.** A candidate is pressured to retain the proof
engine, encoding, solver, versions, assumptions, and residual trust, and to
keep Protocol-property conclusions separate from implementation correctness
and compilation preservation.

## 5. Proof objects, theorem correspondence, and replay

### 5.1 Kernel checking does not settle intended meaning

Lean and Rocq strongly separate proof-producing automation from kernel
checking. Lean's official validation guide additionally separates checking an
exported proof from matching its statement to a trusted challenge. Rocq's
standalone checker can recheck logical contents and dependencies without
loading the tactic plugins that produced the proof.

These mechanisms establish propositions inside their exact environments. They
do not establish that an external proposition correctly interprets an admitted
zkc Protocol, view, observer, trace model, distribution, or property
experiment.

One resulting research decomposition is:

```text
zkc semantic proposition
external formal statement
statement instantiation
subject and model interpretation
checked correspondence in the required direction
proof or certificate checking under an exact dependency closure
Analysis-owned property inference
```

The decomposition itself remains a candidate pressure. In particular, a
correspondence cannot be reduced to an unchecked theorem name, README mapping,
artifact digest, or Boolean returned by the external prover.

The cases also leave an unavoidable root question: what checks the
correspondence checker, the semantic-model definition, and the translation
from its specification to the running checker? A candidate must terminate that
chain in named direct or mechanized roots and explicit residual trust. Sending
the same obligation through another adapter or proof language does not by
itself close it.

### 5.2 Proof identity is not proposition identity

Lean's proof irrelevance provides a direct warning against identifying theorem
meaning by proof bytes. Several proofs may establish the same proposition.
Several independent checkers may replay one proof. Conversely, identical proof
bytes loaded under different definitions, axioms, or imports need not have the
same basis.

A Stage 4A candidate therefore needs to test whether it can keep at least these
axes distinct:

```text
semantic proposition identity
theorem, rule, model, assumption, and dependency-basis identity
particular derivation or proof-object identity
qualified judgment identity
one checker or replay occurrence identity
```

This list is not a selected identity schema. It is a collision test derived
from the cases.

### 5.3 Sessions and certificates are different products

Why3 sessions record proof-search structure and operational observations such
as prover versions, resource limits, timeouts, failures, and obsolete tasks.
SMT-LIB distinguishes `sat`, `unsat`, and `unknown`; Alethe-style certificates
allow a separate checker to receive both the original problem and a purported
proof. Proof-carrying code instead binds an exact consumer policy, subject, and
certificate for a named relying boundary.

These cases expose three different artifacts:

- a derivation or transformation plan;
- a checker-attempt and status record; and
- evidence sufficient for an independent consumer to replay an exact claim.

They should not be assumed to share one authority or persistence policy.
Cheap internal derivations may be better recomputed. A durable proof object may
be justified by cross-process use, independent release checking, expensive
reconstruction, or a real trust separation. Persistence alone never preserves
a live capability.

## 6. Equality, refinement, trace, and probability

### 6.1 Relation kind and direction are semantic

CompCert, Interaction Trees, and ReLoC show that equality and refinement are
not generic labels. A simulation theorem is relative to exact source and
target semantics, observations, and side conditions. A trace-set inclusion has
a direction. Deriving a stronger backward result can require determinacy,
receptiveness, or other well-behavedness premises. A first-class refinement
judgment composes differently from an unstructured Boolean relation.

Interaction Trees additionally shows that a finite-trace model can fail to
distinguish divergence from other unproductive behavior. The event
interpretation itself determines what is observable.

The research pressure on Stage 4A candidates is therefore to preserve the
Stage 3 separation among `CoreEq`, `ProtocolEq`, `TraceEq[O]`, directed
`TraceRefines[source, target, O]`, and `IntentionalChange`. A trace question
may need to bind its event alphabet and projection, observer, termination,
divergence, abort, failure, nondeterminism, and probabilistic policy.

### 6.2 Distributional relation is a family, not one predicate

EasyCrypt, CryptHOL, eRHL, and Lilac distinguish exact distribution equality,
bounded statistical distance, probabilistic relational pre/postconditions,
independence, conditioning, and subdistribution mass. Computational
indistinguishability additionally depends on adversary class and resource
regime rather than extensional equality alone.

One case-supported candidate pressure is a typed quantitative algebra rather
than generic real numbers or string formulas. Probability, advantage, query
count, rounds, running time, and asymptotic functions have different domains
and side conditions. A rule that adds, scales, maximizes, or lifts a bound
needs to own the exact transformer and its premises.

The sources do not determine whether v0 should support only exact finite
subdistributions, symbolic concrete bounds, asymptotic families, or a broader
measure-theoretic profile. They show that collapsing these regimes would erase
the theorem's meaning.

## 7. ZK-specific theorem pressure

The EasyCrypt ZK development, SSProve's Sigma-protocol case study, VCVio's
verified oracle reasoning, and the multi-round Fiat--Shamir results all expose
property-specific experiment structure. Completeness, special soundness,
knowledge extraction, soundness, and zero knowledge do not necessarily read
the same relation, adversary, state, or distribution.

Fiat--Shamir theorems further depend on exact source Protocol class, target
construction, oracle model, static or adaptive statement binding, challenge
schedule, rounds, query budget, soundness or knowledge parameters, abort
treatment, and loss expression.

This supports a research pressure already present in the frozen Stage 3
intake:

```text
admitted Fresh Protocol
+ admitted Fiat--Shamir Protocol
+ exact admitted transcript construction
+ affirmative CheckedFSConstruction
+ property-specific theorem/model basis and assumptions
+ exact quantitative parameters
  -> qualified property-specific FSCompile result
```

The sources do not establish that this exact shape is the final Stage 4A
calculus. They do rule out treating structural construction, a generic
`FS-valid` marker, or a cited forking lemma as universal property transport.

## 8. Cross-case deductions

The following deductions are convergence inputs rather than selected target
rules.

### 8.1 The exact subject is larger than a Protocol identifier

Across the cryptographic systems, the meaningful subject of a property is
closer to:

```text
admitted subject tuple
× property experiment
× property-indexed relation
× observer and initial-state policy
× adversary, oracle, and auxiliary-input regime
× termination, abort, and conditioning policy
× assumptions and quantitative parameters
× semantic and resource models
```

A candidate that identifies only a Protocol and a property label would need to
show how the omitted dimensions cannot alter the conclusion.

### 8.2 Common lifecycle does not imply one universal judgment payload

Equality, trace refinement, distributional closeness, soundness, knowledge,
completeness, Fiat--Shamir transport, and cost share lifecycle concerns:
subjects, context, derivation, outcome, authority, and replay. The sources do
not show that they share one subject tuple, negative-result meaning,
quantitative algebra, or proof rule.

This creates pressure toward a thin common envelope around typed property
families, but it does not select a particular type system, host language, or
extensibility mechanism.

### 8.3 Hypotheses are part of the conclusion's meaning

Locales, theory clones, module assumptions, F* interfaces, proof-assistant
axioms, losslessness, adversary restrictions, and solver encodings all show how
premises can become ambient. A candidate hypothesis model should be tested as
an explicit typed dependency closure rather than a string list.

Useful distinctions to test include prior checked judgments, declared
hardness assumptions, semantic idealizations, environment conditions,
adversary restrictions, quantitative side conditions, and model-
correspondence premises. An affirmative conditional result is of the form
`Gamma entails P`; it is not an unconditional `P` with provenance attached.
Consequently, retaining a missing correspondence as a hypothesis changes the
semantic claim identity. It cannot answer a request for unconditional `P` or
mint the unconditional capability.

### 8.4 Derivation validation and proof search are different

SSProve game hops, proof-assistant kernels, Why3 transformations, SMT
certificates, and proof-carrying code all separate some form of producer from
checker. This supports testing an acyclic, premise-identified derivation plan
whose rule instances retain substitutions, side conditions, bound
transformers, and exact conclusion.

It does not imply that every property is decidable, that every proof should be
serialized, or that one proof term can represent every basis.

### 8.5 Qualified outer and inner outcomes cannot collapse

A valid proof of an exact proposition may support an affirmative property
result. A valid proof of its exact negation, an exact validated countermodel,
or a complete decision procedure may support a fact-retaining negative. The
following do not establish a negative property result:

- failure to find a proof;
- solver `unknown`, timeout, or resource exhaustion;
- an invalid proof or certificate;
- an unsupported theory or rule; or
- failure to reconstruct the named authority or correspondence basis.

The certificate-check result, derivation-search result, and property result
therefore need separate interpretation even if a public API later groups them
under the Stage 3 qualified-outcome family.

### 8.6 Durable material is a replay recipe, not preserved authority

A meaningful cold replay may need to reconstruct and check:

```text
exact admitted subject tuple and purpose-specific views
exact semantic proposition, model, observer, and hypotheses
external statement and instantiation, when used
model and statement correspondence
proof, certificate, or internal derivation
theory, imports, axioms, assumptions, rules, versions, and checker regime
Analysis-owned inference and qualified outcome
residual trust and named consumer
```

The cases support no inference from stored bytes, a digest, a prior exit code,
or a session marker to a live Analysis capability.

### 8.7 Compiler remains a downstream pressure, not a semantic owner

No surveyed proof system justifies allowing candidate enumeration, objective
scores, provider availability, or optimization policy to define property
meaning. A Compiler candidate may expose missing Analysis subject, map,
quantitative, or outcome fields. It cannot repair them by reinterpreting the
property inside selection logic.

## 9. Candidate axes exposed by the cases

This table records alternatives that Stage 4A.3 should compare at equal
resolution. The final column is research pressure, not a selected answer.

| Axis | Alternatives to compare | Case-supported pressure |
|---|---|---|
| Claim authority | Prover-native theorem; zkc-native claim; zkc-native claim plus checked external correspondence | External proof validity and intended zkc meaning remain separate |
| Family structure | One generic predicate; closed typed families; typed families with versioned extension profiles | Property families share lifecycle but not necessarily subjects, bounds, or negative-result semantics |
| Context closure | Ambient module/locale environment; explicit immutable dependency closure | Hidden globals, locales, imports, axioms, and state policies repeatedly affect theorem meaning |
| Proof basis | One universal proof object; internal checker only; federated internal and external adapters | No surveyed artifact covers every relation and property without translation or trust obligations |
| Probabilistic base | Full distributions; subdistributions; several explicit semantic profiles | Abort, failure, and nontermination make losslessness material |
| Quantitative regime | Generic real expression; typed concrete algebra; concrete plus explicit asymptotic lifts | Bound operations and side conditions are theorem-specific and dimension-sensitive |
| Trace relation | Trace sets; simulations; contextual/logical refinement; profile-indexed alternatives | Observer and divergence policy change relation meaning |
| Theorem correspondence | Citation or name; literal statement equality; checked instantiation plus directional adequacy | Kernel checking alone does not establish intended interpretation |
| Trust roots | Unchecked adapter chain; direct specified checker; mechanized root; explicit residual trust; qualified combinations | Correspondence, encoding, model, and checker adequacy do not become self-justifying by translation |
| Derivation representation | Flat success receipt; rule tree; shared DAG; external proof term | Game hopping and replay need exact premises, while proof identity must remain separate from claim identity |
| Negative result | Failed search; checked refutation; completeness-backed decision | Existing tools sharply distinguish inconclusive search from semantic refutation |
| Persistence | No durable result; opaque receipt; replayable sidecar bound to a named consumer | Persistence is justified by a consumer and cannot preserve live authority |
| Rule registry | Open runtime callbacks; closed v0 kernel; versioned extension profiles | Executable theorem meaning must not come from ambient loaded code or untyped names |
| Property transport | Blanket preservation; property-indexed partial theorem | Fiat--Shamir and composition losses depend on exact notions, models, and premises |
| Resource reasoning | Fold into distribution semantics; separate operational model; property-specific hybrid | Extensional equality does not establish feasibility or execution cost |

## 10. Transfer limits

The comparative cases do not establish any of the following:

1. that zkc should adopt EasyCrypt, Rocq, Lean, Isabelle, F*, Why3, Dedukti, an
   SMT solver, or any other host as its semantic authority;
2. that one proof-object format can faithfully carry every Stage 4A family;
3. that a small kernel proves the adequacy of the model checked by that kernel;
4. that theorem-name identity, source-file identity, or proof-artifact identity
   is semantic claim identity;
5. that exact distribution equality implies computational
   indistinguishability, or that either implies feasibility or cost;
6. that a trace-set, simulation, contextual refinement, and logical relation
   are interchangeable;
7. that every true relation has a complete decision procedure or compact
   certificate;
8. that a counterexample emitted by an incomplete abstraction is a checked
   negative for the original property;
9. that a structural Protocol transformation transports soundness, knowledge,
   completeness, zero knowledge, or another property;
10. that one Sigma-protocol, oracle, rewinding, or Fiat--Shamir theorem applies
    outside its exact protocol class and assumptions;
11. that implementation correctness, verified extraction, test success, or
    compiler replay establishes a Protocol-level theorem; or
12. that durable evidence is useful without a named consumer and cold-replay
    contract.

## 11. Candidate falsifiers

The following scenarios can falsify a Stage 4A candidate or force it to expose
an additional distinction. They do not select the replacement.

1. Two questions differing in observer, direction, initial state, auxiliary
   input, losslessness, adversary model, assumptions, or quantitative regime
   receive the same semantic identity.
2. Replacing one proof by another changes the semantic proposition rather than
   only its derivation or trust basis.
3. A theorem citation or successful external checker can mint an affirmative
   result before exact model and statement correspondence is checked.
4. An incomplete search, timeout, solver `unknown`, or invalid certificate can
   become a negative property result.
5. A conditional theorem loses an inherited hypothesis at composition,
   transport, persistence, or consumption.
6. A bound rule can combine probability, advantage, time, query count, or
   asymptotic functions without domain checking and explicit side conditions.
7. Trace equality or refinement can be asked without naming its observer,
   event projection, and termination/divergence/abort policy.
8. Computational indistinguishability or feasibility is inferred from
   extensional distribution equality alone.
9. `FSCompile`, composition, or another transformation transports a property
   through a generic preservation label rather than an exact property-specific
   theorem.
10. Persisted bytes or an earlier checker success mint authority without cold
    reconstruction of subjects, basis, correspondence, and derivation.
11. A basis identity remains unchanged after its imports, axioms, definitions,
    model, theorem instantiation, checker contract, or trust regime changes.
12. Measurements, tests, or compiler receipts establish a semantic theorem
    without an exact Analysis-owned inference rule.
13. Model correspondence is represented only by an unchecked Boolean, source
    annotation, README mapping, or artifact signature.
14. Compiler logic must define or reinterpret a property to decide candidate
    eligibility.
15. The exact zkc claim cannot be identified or compared when its external
    prover or proof artifact is unavailable.

## 12. Primary-source index

### Cryptographic and probabilistic reasoning

- EasyCrypt: [official documentation](https://easycrypt.gitlab.io/easycrypt-web/docs/welcome/),
  [repository snapshot](https://github.com/EasyCrypt/easycrypt/tree/ef1b4076ae83a43df58811ea10c7d22864452153), and
  [Zero-Knowledge in EasyCrypt](https://eprint.iacr.org/2022/926.pdf).
- SSProve: [repository snapshot and documentation](https://github.com/SSProve/ssprove/tree/c6d7d4bc3a0a671c92899aa49dfcfb065d1bdbbd)
  and [foundational paper](https://eprint.iacr.org/2021/397.pdf).
- CryptHOL: [AFP entry](https://isa-afp.org/entries/CryptHOL.html),
  [current tutorial](https://isa-afp.org/browser_info/current/AFP/Game_Based_Crypto/CryptHOL_Tutorial.html),
  and [primary paper](https://eprint.iacr.org/2017/753.pdf).
- F*: [Proof-Oriented Programming in F*](https://fstar-lang.org/tutorial/book/),
  including [effects and Hoare-style refinements](https://fstar-lang.org/tutorial/book/part4/part4_pure.html)
  and [SMT trust](https://fstar-lang.org/tutorial/book/part1/part1_prop_assertions.html).
- Low*: [Verified Low-Level Programming Embedded in
  F*](https://www.microsoft.com/en-us/research/publication/verified-low-level-programming-embedded-f/)
  and the [KaRaMeL repository snapshot](https://github.com/FStarLang/karamel/tree/9abbb865b10a0cd5c557da81c024c3965cb6ff53).
- eRHL: [primary publication page](https://www-sop.inria.fr/members/Martin.Avanzini/publications/ABDG%3APOPL%3A25.html).
- Lilac: [primary paper](https://www.ccs.neu.edu/home/amal/papers/lilac.pdf).

### Proof checking, translation, and replay

- Lean: [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/),
  [Axioms](https://lean-lang.org/doc/reference/latest/Axioms/), and
  [Propositions](https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/).
- Rocq: [proof mode](https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/proof-mode.html),
  [compiled interfaces and `rocqchk`](https://rocq-prover.org/doc/master/refman/practical-tools/coq-commands.html),
  and [dependency inspection](https://docs.rocq-prover.org/master/refman/proof-engine/vernacular-commands.html).
- Why3: [interactive proof sessions and replay](https://why3.org/doc/itp.html)
  and [manual pages](https://why3.org/doc/manpages.html).
- SMT-LIB: [Version 2.7
  specification](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf).
- Alethe: [proof-format specification](https://verit.loria.fr/alethe.pdf) and
  [Carcara checker snapshot](https://github.com/ufmg-smite/carcara/tree/6624ea80cf1985ada473c0705869c78353e4282d).
- Dedukti: [repository snapshot](https://github.com/Deducteam/Dedukti/tree/f3c0eba869ddd46f2e75c123a59f2b612076dba0),
  [logical-framework paper](https://arxiv.org/abs/2311.07185), and
  [HOL translation](https://arxiv.org/abs/1507.08720).
- Proof-carrying code: [Necula's PCC overview](https://people.eecs.berkeley.edu/~necula/pcc.html)
  and [Foundational Proof-Carrying Code](https://www.cs.princeton.edu/~appel/papers/fpcc.pdf).

### Equality, refinement, traces, and ZK-specific transformations

- CompCert: [official documentation](https://compcert.org/doc/) and
  [simulation composition source](https://compcert.org/doc/html/compcert.driver.Compiler.html).
- Interaction Trees: [primary POPL paper](https://www.cis.upenn.edu/~stevez/papers/XZHH%2B20.pdf).
- Iris: [official project](https://iris-project.org/) and
  [ReLoC Reloaded](https://iris-project.org/pdfs/2021-lmcs-reloc-reloaded-final.pdf).
- Fiat--Shamir: [Fiat--Shamir Transformation of Multi-Round Interactive
  Proofs](https://link.springer.com/article/10.1007/s00145-023-09478-y).
- VCVio: [primary paper](https://eprint.iacr.org/2024/1819) and
  [formal repository snapshot](https://github.com/Verified-zkEVM/VCVio/tree/3ecd5523d5beaa10b026f663174e8b9d9708c24b).

## 13. Research conclusion

No surveyed system supplies a portable Stage 4A authority object without also
bringing its own language, state model, probability semantics, ambient
environment, trust base, or theorem-representation choices.

The strongest shared research implication is to compare candidates in which
zkc retains exact semantic question and qualified-result meaning, while proof
assistants, internal calculi, decision procedures, solvers, translated proof
frameworks, and persisted certificates appear as explicit checked bases with
their correspondence and residual trust intact.

That implication does not select the final calculus, the v0 property-family
set, the probabilistic profile, the internal rule kernel, an external adapter,
or a persistence format. Those decisions remain Stage 4A.3 convergence work.
