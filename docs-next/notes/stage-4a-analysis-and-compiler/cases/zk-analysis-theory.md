# ZK proof-property and Fiat--Shamir Analysis theory

> **Document kind:** Temporary primary-source research dossier
> **Document state:** Stage 4A.2 ZK-specific research complete; target-neutral
> **Authority:** None. Source results, design inferences, candidate constraints,
> and non-transfer limits are labeled separately. This page defines no zkc
> Analysis judgment, proves no property of any zkc Protocol or implementation,
> establishes no external-theorem correspondence, selects no target
> architecture, and authorizes no implementation or migration.
> **Scope:** Completeness, soundness, knowledge, special soundness,
> round-by-round and state-restoration security, zero knowledge,
> Fiat--Shamir in classical and quantum oracle models, duplex sponges,
> occurrence-sensitive composition, aborts, quantitative bounds, and
> mechanized proof scope.
> **Method:** Primary papers, authors' repositories, mechanization repositories,
> and official standards drafts. A paper theorem is recorded only with the
> property, subject, experiment, model, resources, and side conditions that
> bound its use here.
> **Disposition:** Use this dossier during Stage 4A candidate construction and
> scenario comparison. Absorb reviewed conclusions into durable `analysis/`
> and exact shared owners, then delete this page with the temporary package.

## 1. Research question and answer

What common structure can zkc safely reuse across ZK proof-property questions,
and what must remain specific to completeness, soundness, extraction, zero
knowledge, Fiat--Shamir transport, and composition?

The primary sources support a **shared exact experiment and judgment lifecycle
with property-family-specific semantic calculi**:

```text
exact admitted subjects and occurrence graph
  + exact relation or language orientation
  + exact experiment, adversary or observer, model, and resources
  + property-family-specific proposition and result
  + exact theorem/rule correspondence and quantitative transformer
  -> qualified Analysis judgment
```

The common layer may own subject closure, model and assumption closure, basis
identity, derivation, qualified outcomes, replay, and residual trust. It must
not turn every property into a tag plus one scalar `epsilon`. The studied
notions have different bad events, witnesses, observers, auxiliary algorithms,
abort obligations, composition laws, and quantitative domains. Several
published separation results directly refute a universal implication lattice.

This answer strengthens, but does not ratify, the frozen Stage 4A separation
between structural construction, theorem applicability, property transport,
and use-specific reliance.

## 2. Source discipline and primary cases

| Source | Primary result used | Transfer limit |
|---|---|---|
| [ArkLib repository snapshot](https://github.com/Verified-zkEVM/ArkLib/tree/df2339f7a5024a55369705fc78488abb2b4a996f) and [Oracle Reductions blueprint](https://verified-zkevm.github.io/ArkLib/blueprint/chap-oracle_reductions.html) | Typed public-coin IORs, relation-to-relation execution, notion-specific completeness and soundness, RBR state functions, extractors, sequential composition, lifting, and a structural FS development | Active development; state restoration, full ZK, and FS security beyond completeness are not a completed generic authority |
| [Interactive Oracle Proofs](https://eprint.iacr.org/2016/116.pdf) | IOP-to-NIROP compilation with separate restricted state-restoration soundness, proof-of-knowledge, and ZK transports and concrete bounds | One compiler and its exact ROM experiment; not an arbitrary FS or concrete-hash theorem |
| [On Round-By-Round Soundness and State Restoration Attacks](https://eprint.iacr.org/2019/1261) | Equivalence of public-coin RBR and state-restoration soundness; separation from FS random-oracle security | Plain soundness result; does not collapse knowledge variants or provide a universal FS converse |
| [Building Cryptographic Proofs from Hash Functions snapshot](https://github.com/hash-based-snargs-book/hash-based-snargs-book/tree/305fa3d9d19ee6dba135de64b3156d1760df8426) | Exact modern experiments for FS, salt-indexed state restoration, straightline and rewinding knowledge, failure, time, queries, and adaptive instances | A theory framework and theorem library, not a zkc proposition schema or implementation correspondence |
| [On Soundness Notions for Interactive Oracle Proofs](https://eprint.iacr.org/2023/1256.pdf) | Generalized special soundness/RBR relationships, separations, tight soundness comparisons, and a QROM FS variant | Theorems use exact generalized notions and protocol shapes; names alone do not transfer them |
| [Fiat--Shamir Transformation of Multi-Round Interactive Proofs](https://eprint.iacr.org/2021/1377.pdf) | Transcript-tree extraction, protocol-class-sensitive classical ROM loss, adaptive statement binding, and repetition counterexamples | Special-sound positive theorem does not cover arbitrary multi-round protocols or other hash chains |
| [A Fiat--Shamir Transformation From Duplex Sponges](https://eprint.iacr.org/2025/536.pdf) | Direct ideal-duplex construction and distinct soundness, knowledge, and ZK analyses with codec, salt, rate, capacity, and query terms | Ideal permutation/oracle model; not a concrete sponge implementation or an indifferentiability-only transport |
| [The Measure-and-Reprogram Technique 2.0](https://eprint.iacr.org/2020/282.pdf) | Multi-round QROM measure-and-reprogram theorem and quantum-specific loss | Constant-round preservation under its exact quantum notions; no ROM-to-QROM inheritance |
| [On Composition of Zero-Knowledge Proof Systems](https://www.wisdom.weizmann.ac.il/~oded/PSX/zk-comp.pdf) | Sequential and parallel composition limitations under precisely distinguished ZK formulations | Classical foundational separation; does not say that every modern ZK formulation fails every composition operator |
| [On Defining Proofs of Knowledge](https://www.wisdom.weizmann.ac.il/~oded/pok.html) | Knowledge error and expected extraction as definition-level content; PoK validity is not simply plain soundness | Definition framework; a concrete implication still needs matching relations and theorem premises |
| [Fixing and Mechanizing Security Proof of Fiat--Shamir with Aborts and Dilithium](https://par.nsf.gov/servlets/purl/10425243) and [EasyCrypt repository snapshot](https://github.com/formosa-crypto/dilithium/tree/368acabdf65c7756a6f5696ff11e8c051f991769) | A formalization-discovered FSwA gap; accepted/rejected transcript programming, unbounded retry, expectation reasoning, and exact mechanization scope | Fully mechanized ROM result for a specific template; QROM and some runtime correspondence remain outside that checked claim |
| [Fiat--Shamir Security of FRI and Related SNARKs](https://eprint.iacr.org/2023/1071.pdf) | Protocol-specific doomed states and RBR/knowledge bounds for FRI-family systems | Concrete algebraic/code-theoretic analyses, not a universal RBR rule |
| [CFRG Fiat--Shamir draft](https://datatracker.ietf.org/doc/draft-irtf-cfrg-fiat-shamir/) | Engineering separation of protocol/session/instance framing, codecs, duplex state, and proof serialization | Internet-Draft without theorem authority; narrower protocol scope than zkc |

Draft standards are used only as engineering evidence. Repository and
blueprint declarations are used only to delimit what one mechanized system
represents and currently claims. No citation or proof file is treated as an
affirmative zkc judgment.

## 3. The shared envelope is not a shared property semantics

### Source result

The sources repeatedly reuse the same outer ingredients—protocol, relation,
security parameter, adversary, oracle, transcript, randomness, error, and
theorem—while changing their semantic roles by property. For example:

- completeness quantifies over a valid instance-witness pair and honest
  execution;
- plain soundness quantifies over false instances and malicious provers;
- knowledge soundness quantifies over a relation and an extractor, and counts
  accepting executions on which extraction fails;
- zero knowledge compares a real observer view with a simulated distribution;
- state restoration gives the prover a branching challenge experiment that
  does not exist in standard soundness;
- QROM exposes superposition queries and permits only quantum-valid reduction
  steps.

ArkLib reflects part of this distinction through notion-indexed results and
different completeness, soundness, RBR, and knowledge lens conditions. The
IOP, duplex, and QROM theorems then use different transports even when they
start from the same protocol.

### Design inference

An ideal common proposition envelope should close:

```text
PropertyQuestion<P> {
  exact_subject_closure,
  exact_occurrence_and_composition_graph,
  exact_relation_or_language_operands,
  P::ExperimentRegime,
  parameters_and_resources,
  requested_basis_profile
}
```

The property family `P` should determine at least:

- the required subject tuple and owner-created views;
- the experiment and bad event or distribution comparison;
- the adversary, observer, extractor, or simulator interface;
- the result and quantitative sorts;
- valid direct checks and derivation rules;
- valid implication, transport, and composition laws; and
- the meaning, if any, of an affirmative or successful negative outcome.

The shared lifecycle may coordinate exact bases, assumptions, qualified
outcomes, identities, authority, replay, persistence, and residual trust. A
common lifecycle does not justify a common result payload or one universal
`HoldsProperty` predicate.

### Candidate constraint

The current Soundness Kernel should be representable as one Analysis basis
profile for selected property families. Its typed rules, explicit plans,
symbolic bounds, and small checker are strengths to preserve. Its current
subject and result algebra must not define the entire future Analysis domain.

## 4. Completeness is an honest-execution property

### Source result

ArkLib completeness begins with an input statement-witness pair in the input
relation and requires honest execution to produce a valid output
statement-witness pair and matching prover/verifier output statements, except
with the declared error. Perfect completeness requires this for every possible
challenge choice.

The BCS compiler preserves the interactive accepting probability by
construction. ArkLib's structural FS development likewise has a completeness
preservation theorem, while its cryptographic soundness and ZK FS theorems are
still marked under development. This is direct evidence that even the easiest
FS property is a separate theorem conclusion rather than an annotation on the
constructed target.

### Design inference

A completeness proposition needs:

- exact input and output relations or an exact accept/reject relation;
- honest prover and verifier algorithms;
- the source of honest randomness and oracle sampling;
- output-statement agreement when the subject is a reduction;
- failure, abort, and termination semantics; and
- a completeness-error result distinct from adversarial advantage.

Completeness does not require a malicious-prover model or an extractor. It
also does not imply that an external witness actually exists at a particular
invocation. Relation satisfaction and occurrence-local witness capability
remain separate questions.

## 5. Soundness and extraction families

### 5.1 Plain soundness

#### Source result

Plain soundness is language-oriented. In an accepting-proof presentation the
bad event is a false statement being accepted. In ArkLib's functional
reduction presentation it is an input outside the input language producing an
output inside the output language. Whether the prover is computationally
bounded, unbounded, classical, quantum, static, or adaptive belongs to the
experiment.

#### Candidate constraint

`PlainSoundness` must identify exact languages induced by exact relations,
input/output orientation, malicious-prover class, verifier and oracle model,
false-input event, adaptivity, and its probability or computational-advantage
bound. It contains no implicit witness extractor.

### 5.2 Knowledge soundness and proof of knowledge

#### Source result

ArkLib's straightline extractor reads the output witness, initial statement,
transcript, and relevant query logs. Its bad event is an accepting valid output
for which extraction fails to recover an input witness. Extractor failure
counts as an adversarial win on such an accepting execution; verifier abort
creates no extraction obligation in that definition.

The hash-based SNARG framework separately defines straightline and rewinding
knowledge. Rewinding knowledge tracks black-box access to the prover, prover
failure probability, and expected extraction time. The foundational PoK work
of Bellare and Goldreich makes knowledge error and extractor time part of the
definition rather than deriving PoK validity from plain soundness alone.

#### Candidate constraint

`KnowledgeSoundness` needs:

- an exact relation rather than only its language;
- an extractor identity and access mode;
- straightline, rewinding, state-restoring, algebraic, or quantum regime;
- transcript, oracle trace, verifier trace, prover code/access, and randomness
  supplied to the extractor;
- accepting-event and abort conditioning;
- extraction error or success function;
- prover failure and running time where the theorem reads them; and
- expected or worst-case extractor time.

An extractor artifact is result-family content, not generic evidence metadata.

### 5.3 Special soundness

#### Source result

Generalized special soundness extracts from an accepting transcript tree with
specified branching factors and challenge diversity. Block et al. establish:

```text
generalized special soundness
  -> generalized round-by-round soundness

generalized round-by-round knowledge soundness
  -> generalized special soundness

generalized special soundness
  -/-> generalized round-by-round knowledge soundness
```

The non-implication is a theorem under the paper's stated complexity
assumption. For a `(k_1, ..., k_mu)` special-sound protocol, their construction
uses per-round RBR errors `(k_i - 1) / |C_i|`.

#### Design inference

`SpecialSoundness` requires a transcript-tree schema, branch coordinates,
challenge-distinctness conditions, extraction operation, target relation, and
information-theoretic or computational failure. It must not be encoded as an
alias for `KnowledgeSoundness`, RBR knowledge, or one scalar error.

### 5.4 Round-by-round soundness and knowledge

#### Source result

ArkLib represents RBR soundness using a deterministic state function over
partial transcripts. A false input begins doomed, prover messages cannot
repair a doomed state, and a doomed full state cannot yield a valid output. At
each verifier-challenge occurrence, the chance of moving from doomed to
non-doomed is bounded by the round's error.

Its RBR knowledge variant uses a knowledge-state function and round extractor.
Within ArkLib's exact definitions:

- RBR soundness with errors `epsilon_i` implies plain soundness with bound
  `sum_i epsilon_i`;
- RBR knowledge implies RBR soundness with the same error vector; and
- RBR knowledge implies knowledge soundness with bound `sum_i epsilon_i`.

Block et al.'s generalized analysis obtains a tighter relationship
`1 - product_i (1 - epsilon_i)` under its exact definitions and matching
premises. These are not interchangeable formulas. FRI-family analyses further
use protocol-specific doomed states and bounds involving field size, degree,
distance, powers, and maxima.

#### Candidate constraint

RBR results must retain:

- each exact challenge occurrence;
- its challenge distribution and space;
- the partial-transcript prefix;
- the exact doomed or knowledge-state predicate;
- the round extractor when applicable; and
- the per-round error expression.

Summation, `1 - product`, maximum, repetition, or another aggregation is a
named later theorem application. It is not a built-in normalization of every
RBR result.

### 5.5 State restoration

#### Source result

In a state-restoration game a malicious prover selects or extends stored
partial transcripts and obtains challenges from random functions indexed by
the statement, transcript prefix, salt, and round. Definitions distinguish
full and restricted restoration, straightline and rewinding extraction,
adaptive and fixed instances, salt size, move budget, query budget, instance
size, prover failure, and extractor time.

Holmgren proves that public-coin RBR soundness and state-restoration soundness
are equivalent. He also exhibits the decisive converse failure: FS security in
the random-oracle model does not imply either property. The hash-based SNARG
framework uses state restoration as the exact sufficient premise for broad FS
compiler theorems, not as a semantic synonym for FS security.

#### Candidate constraint

`StateRestoration` needs its own game subject:

```text
StateRestorationRegime {
  challenge_function_family,
  statement_and_prefix_indexing,
  salt_space,
  move_and_query_budget,
  restricted_or_full,
  static_or_adaptive_instance,
  straightline_or_rewinding_extraction,
  failure_and_time_profile
}
```

An implication from RBR, special soundness, or standard knowledge must be a
named theorem instance with its exact bound transformer. The label
`state-restoration` cannot be inferred from a successful FS target.

### 5.6 Implication graphs are definition- and theorem-specific

#### Source result

ArkLib has a knowledge-soundness-to-soundness theorem for its corresponding
languages when the knowledge error is less than one. The Bellare--Goldreich
framework warns against treating PoK validity as plain soundness by definition.
The two observations are consistent: the implication is available only under
the exact matched definition, relation-to-language projection, and side
condition.

#### Candidate constraint

Analysis should store an explicit, versioned graph of theorem instances, not a
type hierarchy such as `KnowledgeSoundness <: Soundness`. Each edge must cite:

- source and target proposition schemas;
- relation/language projection;
- side conditions;
- adversary and model correspondence;
- bound transformation; and
- theorem basis and residual trust.

## 6. Fiat--Shamir is a new subject plus separate property transports

### 6.1 Structural construction is not security

#### Source result

All studied FS constructions derive verifier challenges from some exact
combination of statement, transcript prefix, salt, labels, counters, and oracle
state. The interactive and non-interactive systems therefore have related but
different algorithms, transcripts, oracle interfaces, randomness, and
security experiments.

The CFRG draft makes protocol ID, session ID, instance label, prefix-free
encoding, codec, duplex state, and serialized proof responsibilities explicit.
The duplex paper proves that codec bias, salt, rate, and capacity enter security
bounds. These are not printer details.

#### Candidate constraint

The Stage 4A seam should be:

```text
Admitted Fresh Protocol
+ Admitted target FiatShamir Protocol
+ exact transcript construction
+ CheckedFSConstruction with source-to-target occurrence maps
  -> structural FS subject relation

structural FS subject relation
+ exact theorem-construction and model correspondence
  -> FSCompile / FS theorem-instance capability

FS theorem-instance capability
+ source Property[P]
+ P-specific premises
  -> PropertyTransport[P] to the target
```

`FSCompile` should establish exact applicability to a named construction
theorem, including transcript program, codec, oracle, salt, model, observer,
abort policy, parameters, and quantitative transformer. It should transport no
property by default.

### 6.2 IOP/BCS transport has property-specific premises and bounds

#### Source result

For a public-coin IOP with restricted state-restoration soundness
`s_sr_bar(x, m)`, the BCS IOP-to-NIROP theorem gives ROM soundness:

```text
s'(x, m, lambda)
  = s_sr_bar(x, m) + 3 * (m^2 + 1) * 2^(-lambda).
```

Proof of knowledge is transported separately from restricted
state-restoration proof of knowledge with the analogous collision term.
Statistical honest-verifier zero knowledge is transported separately as:

```text
z'(x, lambda)
  = z(x) + p(x) * 2^(-lambda/4 + 2).
```

The theorem also reads round complexity, proof length, oracle-query count,
prover/verifier time, move budget, security parameter, and statement. Its
completeness claim follows by construction rather than either adversarial
transport.

#### Design inference

One theorem family can expose several typed transport adapters, but it must not
expose one unqualified `preserves_security` edge. Removing the knowledge or ZK
premise must invalidate only that property's transport, not the admitted target
Protocol or the other transports.

### 6.3 Classical multi-round FS is protocol-class-sensitive

#### Source result

For a `(k_1, ..., k_mu)`-special-sound `(2*mu + 1)`-move protocol with
knowledge error `kappa`, Attema, Fehr, and Klooß prove classical-ROM FS
knowledge error at most:

```text
(Q + 1) * kappa.
```

The extractor's expected oracle work also depends on
`K = product_i k_i`. The exact accepting transcript tree and hash-input chain
are premises.

Their negative example is equally important. A `mu`-fold sequential
repetition can have interactive error `|C|^(-mu)`, while an FS adversary that
distributes `Q` oracle trials across rounds gains an approximately
`(Q/mu)^mu` multiplicative factor. Interactive repetition therefore does not
carry its error formula through FS automatically.

Adaptive security requires the theorem's exact statement binding in the hash
inputs. A theorem over one prefix grammar is not authority for a target that
omits, reorders, duplicates, or reframes a statement or message occurrence.

### 6.4 Duplex-sponged FS is not an implementation detail

#### Source result

The duplex-sponged transform takes:

- a public-coin interactive proof for an exact relation;
- a finite alphabet `Sigma`;
- injective prover-message encodings;
- verifier-challenge decoders with per-round statistical bias;
- rate `r`, capacity `c`, and an ideal permutation distribution;
- salt length `delta`; and
- round-specific encoded message lengths.

Its soundness theorem bounds the target using a transformed
state-restoration error plus explicit codec-bias and ideal-permutation
collision terms. Its knowledge theorem separately requires straightline or
rewinding state-restoration knowledge and tracks extraction time and prover
failure.

If the source has statistical HVZK error `z_IP`, the paper's adaptive ZK
theorem gives:

```text
z_NARG(lambda, t, n)
  <= z_IP
     + t / |Sigma|^min(delta, c)
     + t * sum_i ceil(l_V(i) / r) / |Sigma|^(r + c).
```

The target adversary adaptively chooses a valid `(x, w)`, and the simulator
programs the ideal oracle through a query-answer list. The paper explicitly
uses direct analysis because ordinary indifferentiability is not sufficient
for these knowledge and ZK claims.

#### Candidate constraint

Transcript codec, decoder bias, salt, rate, capacity, oracle interfaces,
inverse access, query bound, and programming mode belong to exact theorem and
property identity. A concrete sponge implementation needs a separate
implementation/construction correspondence and cannot inherit the ideal-model
judgment from the word `sponge`.

### 6.5 ROM and QROM are different theorem regimes

#### Source result

In the QROM, adversaries query the random oracle in superposition and
measurement/reprogramming disturbs their state. The multi-round
measure-and-reprogram theorem constructs an interactive adversary whose
success is at least:

```text
n! / (2*q + n + 1)^(2*n) * FS_success - additive_error,
```

where the additive error sums to `n! / |C|` over fixed statement/transcript
coordinates. For constant rounds, the theorem transports its exact
statistical/computational soundness and quantum proof-of-knowledge notions.
The quantum loss is not the classical ROM loss.

#### Candidate constraint

The model must distinguish at least:

```text
ClassicalROM
QuantumROM {
  superposition_query_interface,
  measurement_and_reprogram_profile,
  quantum_adversary_class
}
IdealPermutationModel
ConcreteHashModel
```

No model is a boolean refinement of another. A classical extractor, oracle
trace, or theorem cannot be reused as a QROM basis without an explicit quantum
transport theorem.

## 7. Zero knowledge is observer- and schedule-indexed

### 7.1 Exact experiment dimensions

#### Source result

Zero knowledge compares a real view with a simulated distribution. Different
theorems distinguish:

- honest-verifier and malicious-verifier observers;
- perfect, statistical, and computational comparison;
- static and adaptive instance or witness selection;
- auxiliary input;
- black-box and non-black-box simulation;
- programmable and non-programmable oracle access;
- classical and quantum observers;
- single-theorem and multi-theorem use; and
- sequential, parallel, interleaved, and concurrent schedules.

The duplex theorem's source is statistical HVZK, while its target is an
adaptive non-interactive experiment with a programmed ideal oracle and a query
bound. The IOP/BCS theorem has its own statistical HVZK-to-ZK transport and
loss. These are exact theorems, not a generic `HVZK -> ZK` law.

#### Candidate constraint

`ZeroKnowledge` needs a regime resembling:

```text
ZeroKnowledgeRegime {
  real_experiment,
  simulated_experiment,
  observer_and_auxiliary_input,
  simulator_interface_and_programming,
  perfect_statistical_or_computational_metric,
  static_or_adaptive_input,
  classical_or_quantum,
  session_and_schedule_regime,
  query_and_time_profile,
  abort_and_termination_policy
}
```

The result contains a distance or distinguishing-advantage expression and, as
needed, simulator identity and time. It is not a soundness scalar with another
property tag.

### 7.2 ZK composition is not generic

#### Source result

Goldreich and Krawczyk show that the original ZK formulation is not closed
under sequential composition. Stronger non-uniform formulations repair that
specific sequential case, while even strong black-box formulations are not
generically closed under parallel execution. Their result does not say that no
particular protocol or modern formulation composes. It says that composition
requires the exact formulation and theorem.

#### Candidate constraint

The following is not a valid generic rule:

```text
ZK(child_1) + ZK(child_2) + structural composition
  -> ZK(composite).
```

Sequential, parallel, interleaved, concurrent, multi-theorem, and
shared-oracle ZK each require an exact simulator-composition theorem with its
observer, schedule, auxiliary input, oracle programming, and bound.

## 8. Occurrences, relations, and randomness topology

### Source result

Every FS theorem hashes or absorbs exact message occurrences and prefixes.
State restoration indexes challenge functions by exact statements and partial
transcripts. Multi-round special soundness extracts from a particular tree of
accepting occurrences. ZK composition changes what one observer can schedule
and correlate. Batching and FRI-like analyses use bespoke shared-randomness and
algebraic bounds.

The same protocol definition used twice can therefore have different security
meaning when the two invocations use independent challenges, one shared
challenge, a derived challenge, a shared oracle namespace, different session
labels, or a different total interleaving.

### Design inference

An exact property subject must include occurrences rather than only definitions:

```text
PropertySubject {
  protocol_and_relation_definitions,
  exact_occurrences,
  total_or_partial_schedule,
  source_target_occurrence_maps,
  transcript_prefix_maps,
  setup_and_oracle_occurrences,
  randomness_topology
}
```

Useful randomness forms include:

```text
IndependentChallenge(occurrence, sampler)
JointChallenge(occurrences, joint_sampler)
SharedChallenge(source, consumers)
DerivedChallenge(source_occurrences, derivation)
ImportedRandomness(owner, occurrence)
SubstitutedRandomness(source, target_map)
```

These constructors describe structure. Independence, unpredictability,
uniformity, or security follows only when an exact model or theorem establishes
it.

### Relation constraint

Plain soundness reads languages, while knowledge and completeness read
relations and witness flow. A property transport may need a statement map, a
witness map, a language reflection condition, or an extractor lens. Equality
of relation IDs or compatible carrier types does not supply these
property-specific obligations.

`RelationSatisfies` ownership remains outside this dossier. If offered later,
it must remain distinct from completeness, soundness, correspondence, and the
occurrence-local capability to hold or reveal a witness.

## 9. Composition must be operator- and property-indexed

### Source result

ArkLib proves sequential composition for reductions with compatible
intermediate contexts. Under its exact theorems, completeness, soundness, and
knowledge errors add; perfect completeness is preserved; and RBR/RBR knowledge
structures compose. ArkLib lifting uses distinct conditions for completeness,
plain soundness, RBR soundness, and knowledge.

The ZK composition separations, multi-round FS repetition behavior, and
protocol-specific RBR bounds show why these theorems cannot be generalized to
arbitrary graph union, interleaving, or shared challenge.

### Candidate constraint

Stage 4A should distinguish at least:

```text
Sequential
Parallel
Interleaved
Concurrent
SharedChallenge
Batched
Repeated
Lift
FailureCapture
FiatShamirTransform
```

Each property family offers only the laws justified for an operator. A
property-composition rule begins from independently admitted children and
target, an exact composition specification, affirmative structural
composition with resolved maps, and an exact property theorem. It must retain
joint/shared/derived randomness, suppression, captured failure, terminal
combination, and intentional change whenever the property reads them.

Shared challenges correlate bad events. Product bounds or independence cannot
be inferred. Repetition powers, sums, maxima, or degree/field losses must come
from the selected theorem.

## 10. Aborts, retries, and termination are semantic inputs

### Source result

The EasyCrypt work on Fiat--Shamir with aborts found a gap in earlier
Dilithium ROM and QROM reductions. A signing procedure repeats rejection
sampling until it accepts, so its number of random-oracle queries may be
unbounded and depend on the adversary's selected message. The repaired proof
must handle accepted and rejected transcripts, conditional sampling, expected
iterations, and convergence of an unbounded hybrid sequence.

The work fully mechanizes the ROM proof for a specific Dilithium template.
The QROM proof remains pen-and-paper because the required EasyCrypt support was
not available, and some runtime correspondence is checked by inspection rather
than by the mechanized theorem.

ArkLib's knowledge definition supplies another important distinction:
extractor failure is a bad event on the relevant accepting execution, while a
protocol execution that itself aborts imposes no extraction obligation in that
definition.

### Candidate constraint

Property identity must state:

- every abort source and owner;
- retry and rejection-sampling policy;
- whether rejected transcripts or oracle queries are observable;
- finite, bounded, almost-sure, or potentially nonterminating execution;
- expected and worst-case cost where read;
- conditioning of acceptance, failure, and extraction events; and
- whether the simulator or extractor programs or observes rejected paths.

An endpoint or implementation claim that a loop terminates does not establish
the probabilistic termination premise used by a security theorem.

## 11. Mechanized systems and theorem correspondence

### ArkLib scope

The ArkLib repository states an active-development goal of executable IOR
specifications and proofs of completeness and RBR knowledge via composition
and lifting. Its blueprint exposes Lean declarations for the typed protocol,
extractor, security, composition, and lifting surfaces studied here.

The same public material explicitly marks state-restoration development as
incomplete, defers a full ZK definition, and lists only FS completeness as a
current theorem while other FS security results remain under development. The
FS blueprint section also carries a documentation cleanup warning. Candidate
design must record that exact scope rather than promoting the project goal or
documentation outline into a completed theorem set.

### EasyCrypt FSwA scope

The Dilithium work demonstrates why a mechanized receipt must retain:

- the exact template and algorithms formalized;
- ROM versus QROM scope;
- exact theorem and reduction chain;
- loop and expectation model;
- library and proof-assistant dependency closure; and
- unmechanized runtime or implementation-correspondence obligations.

### Design inference

An external proof lane requires at least:

```text
ExternalTheoremBasis {
  external_statement_and_version,
  external_model_and_definitions,
  proof_object_or_checked_module,
  dependency_closure,
  zkc_proposition_correspondence,
  subject_and_occurrence_correspondence,
  parameter_substitution,
  residual_unchecked_obligations
}
```

Proof checking, statement matching, model correspondence, zkc inference, and
implementation correspondence are separate results. A successful proof-file
check cannot mint a zkc property capability without all required bridges.

The bridge chain must terminate in explicit roots. The semantic-model
definition, proposition correspondence, checker algorithm, proof-language
translation, and correspondence between checker specification and running
implementation are each directly or mechanistically established or retained
as residual trust. Moving one bridge into another prover does not make it
self-authenticating.

A missing bridge may appear only in the identity of a distinct conditional
claim, for example `Gamma + ModelCorrespondence |- P`. It cannot answer an
unconditional request for `P` or mint the unconditional property capability.

## 12. Quantitative results require a typed symbolic algebra

### Source result

The studied bounds use materially different forms:

- ArkLib's sum of per-round errors;
- `1 - product_i(1 - epsilon_i)` in generalized RBR analysis;
- special-soundness ratios `(k_i - 1) / |C_i|`;
- BCS collision term `3 * (m^2 + 1) * 2^(-lambda)`;
- classical multi-round FS loss `(Q + 1) * kappa` for the special-sound class;
- QROM factors polynomial of degree twice the challenge-round count;
- duplex codec bias, salt, rate, capacity, and collision terms;
- FRI-family maxima, powers, field sizes, degrees, and distances;
- statistical distance, extraction failure/success, and expected runtime.

### Candidate constraint

One untyped scalar is insufficient. The target needs symbolic variables for at
least:

- security parameter and instance size;
- statement or index where a theorem is instance-dependent;
- round and challenge occurrence;
- query and move budgets;
- challenge, field, and alphabet sizes;
- salt, rate, capacity, and codec bias;
- degree, distance, repetition, and branch count;
- adversary acceptance and failure;
- abort and termination probability;
- extractor/simulator/adversary time; and
- proof, communication, and query costs.

Required operators include exact rational arithmetic, sum, product,
`1 - product`, maximum, minimum, powers, binomial coefficients, substitution,
reindexing, and named negligible or primitive-game leaves.

The following must be distinct quantitative sorts:

```text
ProbabilityError
StatisticalDistance
ComputationalAdvantage
KnowledgeError
ExtractionSuccess
ExpectedTime
WorstCaseTime
NaturalResourceCount
CostObservation
```

Every theorem transport should return its exact substitution and loss ledger,
domain, and side conditions. Unsupported algebra must refuse rather than
approximate or coerce between sorts.

## 13. Non-transfer ledger

The target architecture should make every item below impossible without an
exact named rule and matched premises.

| Available fact | Unsupported conclusion | Reason |
|---|---|---|
| Standard soundness | RBR or state-restoration soundness | General public-coin protocols need not satisfy the stronger branching experiment |
| FS random-oracle security | RBR or state-restoration soundness of the source | Holmgren gives a separation; state restoration is not a necessary converse |
| Generalized special soundness | RBR knowledge soundness | Published separation under the stated complexity assumption |
| Knowledge soundness or PoK label | Plain soundness | Requires exact relation-to-language projection, definition, theorem, and side conditions |
| HVZK | Malicious-verifier, adaptive, multi-theorem, parallel, or concurrent ZK | Observer, simulator, input, and schedule experiments differ |
| ZK children and structural composition | ZK composite | Sequential/parallel closure depends on the exact formulation and theorem |
| Interactive repetition error | FS repetition error | Multi-round FS can incur `Q^mu`-scale loss |
| Classical ROM theorem | QROM theorem | Superposition access and measure/reprogram loss differ |
| Ideal random oracle or permutation theorem | Concrete hash or sponge security | Model realization and property transport are separate obligations |
| Indifferentiability | NARG knowledge soundness or ZK | Duplex analysis requires direct property reasoning beyond ordinary indifferentiability |
| Correct transcript shape or `CheckedFSConstruction` | Any cryptographic property | Structural construction has no property authority |
| Relation equality, correspondence, or trace equivalence | Security-property preservation | Requires a property-specific observer/experiment theorem and maps |
| Compatible intermediate carrier types | Sequential property composition | Property-specific relation, language, witness, or extractor lens remains necessary |
| Reused challenge value | Independent challenge samples | Occurrence aliasing cannot establish sampling independence |
| Same protocol definition at two sites | Same property subject | Session, oracle, setup, prefix, schedule, randomness, and abort occurrence can differ |
| External theorem citation or checked proof file | zkc property judgment | Exact statement/model/subject correspondence and zkc inference remain separate |
| Mechanized ROM proof | QROM or implementation security | Adversary model and implementation correspondence exceed the checked theorem |
| Structural deterministic replay | Correct probabilistic sampling distribution | Replay checks one occurrence; it does not prove how an external producer sampled |

This table is a candidate refusal requirement, not a report that current code
already enforces every row.

## 14. Pressure scenarios for candidate comparison

### Z1. Independent versus shared challenge

Use the same child Protocol twice. Candidate A gives each occurrence an
independent sampler; candidate B derives one challenge and shares it. Hold all
carrier types and child IDs equal.

**Required result:** different property subjects and no inherited product or
sum bound for B without a shared-challenge theorem.

**Falsifier:** child IDs or equal challenge types make the two compositions
property-equivalent.

### Z2. Missing FS statement binding

Construct a well-typed FS target whose first challenge hash omits the statement
or whose later challenge omits one prior prover message.

**Required result:** structural admission may remain possible only if the
Protocol defines that meaning, but correspondence to a theorem requiring the
complete prefix fails; all dependent property transports are unavailable.

**Falsifier:** a generic `FiatShamir` tag supplies theorem applicability.

### Z3. ROM-to-QROM laundering

Keep the Protocol, transcript, and relation fixed. Change only the adversary's
oracle access from classical queries to superposition queries.

**Required result:** a new proposition/model identity and a QROM-specific
theorem, extractor, and loss are required.

**Falsifier:** model widening preserves the prior judgment or merely changes a
diagnostic field.

### Z4. HVZK under concurrent sessions

Start with a single-session statistical HVZK source. Request malicious-verifier
concurrent ZK for two interleaved sessions sharing an oracle namespace.

**Required result:** `CannotAnswer` or another qualified non-affirmative
outcome until an exact concurrent simulator theorem and occurrence schedule are
provided.

**Falsifier:** the `ZeroKnowledge` name or statistical metric alone closes the
request.

### Z5. Special soundness requested as RBR knowledge

Provide an affirmative generalized special-soundness result and request
straightline RBR knowledge.

**Required result:** no generic implication; a separate stronger theorem basis
is required.

**Falsifier:** the target treats special soundness as a subtype of knowledge
soundness.

### Z6. Competing RBR aggregations

Provide the same vector-shaped round data to one theorem whose conclusion uses
`sum_i epsilon_i` and another whose conclusion uses
`1 - product_i(1 - epsilon_i)` under different exact definitions or premises.

**Required result:** two theorem-specific propositions/derivations and bounds;
no automatic canonicalization from the vector alone.

**Falsifier:** one built-in aggregation silently replaces the other.

### Z7. FSwA unbounded retry

Use a prover that samples until a response is accepted, with rejected
transcripts making oracle queries and an adversary-controlled message.

**Required result:** the question reads retry, rejected-path visibility,
termination, conditional sampling, expected queries, and programming policy.

**Falsifier:** only the final accepted transcript enters property identity.

### Z8. Same relation through different witness lenses

Compose two reductions with carrier-compatible intermediate statements but
different witness maps or extraction obligations.

**Required result:** structural composition can be affirmative while
completeness or knowledge composition remains unavailable without the exact
property lens.

**Falsifier:** matching relation IDs or statement types transport witness
properties.

### Z9. Remove the theorem store

Hold admitted Fresh and FS Protocols, exact transcript construction, and
affirmative `CheckedFSConstruction` fixed. Remove every FS security theorem
and external proof bridge.

**Required result:** structural subjects remain; `FSCompile` theorem
applicability and every property transport become `CannotAnswer` or
unsupported as appropriate.

**Falsifier:** Protocol admission changes or a property survives without its
basis.

### Z10. Exact external mechanization with incomplete correspondence

Provide a successfully checked Lean or EasyCrypt theorem but omit one zkc
occurrence map, model equality, or unmechanized runtime obligation.

**Required result:** the external proof receipt remains evidence; the requested
unconditional zkc property judgment is unavailable until exact correspondence
closes. A separately requested conditional claim may retain the missing bridge
as a typed hypothesis, but is not the same proposition or capability.

**Falsifier:** proof checking alone mints Analysis authority.

### Z11. Adaptive statement substitution

Take a theorem for a fixed statement or a hash chain that binds the statement
only once. Request adaptive-instance security for a target whose later oracle
queries do not retain the required binding.

**Required result:** separate quantification/model identity and rejection of
the unmatched theorem instance.

**Falsifier:** a static theorem is weakened or widened by metadata.

### Z12. Several valid derivations with different loss and trust

Derive one target property through an RBR-to-state-restoration-to-FS path and
another through a protocol-class-specific special-sound FS theorem. Let their
bounds and residual assumptions differ.

**Required result:** one stable proposition may have multiple basis and
derivation identities, qualified results, and consumer-selectable trust/loss
profiles. No derivation silently overwrites the other.

**Falsifier:** result identity is only the conclusion digest or the entire
ambient theorem catalog.

## 15. Candidate architecture constraints

The research yields the following constraints for Stage 4A candidates. These
are design inferences, not selected normative decisions.

1. Use a thin common Analysis lifecycle with property-family-specific subject,
   regime, proposition, result, and rule types.
2. Make occurrence graphs, transcript prefixes, randomness topology, setup,
   oracle namespaces, observer, abort, and termination first-class whenever a
   property reads them.
3. Preserve exact relation/language orientation and property-specific
   statement, witness, and extractor lenses.
4. Represent special soundness, RBR, state restoration, knowledge, and ZK as
   different experiment families, not enum values over one scalar record.
5. Keep `CheckedFSConstruction`, theorem-construction correspondence or
   `FSCompile`, and `PropertyTransport[P]` as distinct judgments.
6. Expose separate completeness, soundness, knowledge, and ZK adapters even
   when one paper proves all four for one compiler.
7. Distinguish classical ROM, QROM, ideal-permutation, and concrete-hash
   regimes by identity and interface.
8. Index property composition by both property and composition operator.
9. Preserve per-round and protocol-specific bounds until an exact theorem
   performs aggregation.
10. Use a typed symbolic, multi-sort quantitative algebra with explicit
    substitution and loss ledgers.
11. Treat external mechanization as a federated basis lane whose statement,
    model, subject, dependency, and residual-obligation correspondence is
    independently checked.
12. Retain multiple derivations of one semantic proposition without conflating
    proposition, basis, derivation, judgment, and replay identities.
13. Return qualified non-affirmative outcomes when a model, theorem,
    correspondence, or bound form is missing; theorem search failure alone is
    not a successful negative property judgment.
14. Keep compiler policy downstream: it may compare exact qualified property
    results but cannot define their meaning, relax their model, or create a
    transport.
15. Terminate model, theorem, correspondence, encoding, and checker-validation
    chains in named direct or mechanized roots and explicit residual trust;
    another unchecked adapter is not closure.

## 16. Capabilities enabled by the separation

If a candidate satisfies the constraints above, zkc can support capabilities
that a monolithic soundness record cannot express safely:

- compare two proof constructions under the same semantic proposition but
  different theorem bases, bounds, and residual trust;
- analyze an interactive Protocol before choosing any FS construction;
- construct and admit an FS Protocol while honestly reporting that no
  property theorem is available;
- compare classical ROM, ideal duplex, and QROM transforms without pretending
  that their adversaries or losses coincide;
- reason about independent, shared, joint, imported, and derived challenges;
- retain exact per-round RBR results and later apply alternative valid
  aggregation theorems;
- express straightline versus rewinding extraction and expected-time costs;
- distinguish single-session HVZK from adaptive, multi-theorem, and concurrent
  ZK;
- audit aborting and rejection-sampling protocols without erasing rejected
  paths; and
- consume Lean, EasyCrypt, paper, and native small-checker derivations under
  one zkc proposition meaning while keeping their trust boundaries separate.

## 17. Preserved nonclaims

This dossier does not establish that:

- any current or target zkc Protocol is complete, sound, knowledge sound,
  special sound, RBR sound, state-restoration sound, zero knowledge, or secure
  after Fiat--Shamir;
- any ArkLib declaration, EasyCrypt theorem, paper theorem, or standards draft
  corresponds to a zkc subject;
- state-restoration security is necessary for every secure FS transform;
- every special-sound protocol obtains knowledge security under every FS
  construction;
- every ZK formulation fails sequential, parallel, or concurrent composition;
- a random oracle, ideal permutation, sponge, codec, hash function, or QROM
  model has been selected;
- any concrete hash or sponge realizes an ideal-model theorem;
- relation satisfaction belongs to Analysis rather than Relations;
- the proposed shared envelope or property-family split has been selected as
  the final Stage 4A architecture;
- the current Soundness Kernel is incorrect in its bounded intended scope; or
- implementation, migration, persistence, or Stage 4B design is authorized.

The dossier's only conclusion is architectural pressure: exact ZK properties
can share lifecycle infrastructure, but their experiment meaning, theorem
premises, quantitative results, transport, and composition must remain
property- and model-specific.
