# Compiler and transformation-system boundaries

> **Document kind:** Temporary primary-source comparative research dossier
> **Document state:** Stage 4A.2 research input; comparative pass, candidate
> use, and independent review complete
> **Stage:** Stage 4A — Analysis and Compiler co-design
> **Cases:** CompCert, TVOC, Alive2, PEC, proof-carrying and proof-generating
> compilation, MLIR Dialect Conversion and Transform Dialect, egg, Souper,
> CryptOpt, finite-domain and certifying optimization, ZKCrypt, certifying ZK
> compilers, CirC, Jasmin, and Fiat Cryptography
> **Authority:** None. Source facts describe only the cited systems within the
> cited boundaries. Cross-case deductions, transfer candidates, candidate
> axes, and red flags are research hypotheses. This dossier does not select a
> Stage 4A target, define an Analysis or Compiler judgment, admit a Protocol,
> establish a predecessor/successor relation, transport a property, prove
> domain completeness or optimality, report implementation support, or
> authorize migration.
> **Research snapshot:** 2026-08-22. Repository and documentation links that
> track a mutable branch must be rechecked before later reliance.
> **Disposition:** Use only as one input to equal-resolution Stage 4A
> candidates and scenario review. Absorb reviewed conclusions into their exact
> durable owners, then delete this temporary dossier before documentation
> cutover.

## 1. Question and comparison method

This dossier asks what can be learned from mature compiler, validation,
certificate, optimization, and cryptographic-compilation systems when designing
the Stage 4A boundary fixed by the [charter](../charter.md) and the [Stage 4A
entry contract](../../stage-3-protocol-and-relations/stage-4a-entry-contract.md):

```text
provider request + admitted predecessor
  -> unauthoritative successor proposal
  -> PIR authentication and independent target admission
  -> exact predecessor/successor relation check
  -> constraints and objectives over exact qualified inputs
  -> deterministic selection over one declared complete finite domain
  -> qualified Compiler decision
```

The comparison therefore does not ask which existing compiler zkc should copy.
It examines nine narrower questions:

1. Is the producer trusted, verified, proof-producing, or independently
   checked?
2. What exact source and target subjects does the claim relate?
3. Is the relation equality, directed refinement, simulation, safety,
   property preservation, or something else?
4. Are adjacent steps checked, only the final pair checked, or both?
5. Which outcomes distinguish rejection, unsupportedness, boundedness,
   timeout, refusal, and checker failure?
6. How are constraints, objectives, domain coverage, and selection separated?
7. What makes an optimum or no-solution result complete and deterministic?
8. Which non-functional, adversarial, probabilistic, or cryptographic
   properties are transported, and by what separate theorem?
9. What may be cached or persisted, and what must be independently rechecked?

Only primary papers, official documentation, and first-party repositories are
used for source facts. A mechanism is considered a transfer candidate only
after its theorem boundary and analogy limit are stated.

## 2. Central findings

### 2.1 Producer construction and semantic acceptance need not share trust

The cases repeatedly support three implementation modes:

| Mode | Representative case | Useful boundary | Dominant cost |
|---|---|---|---|
| Verified construction | CompCert passes; Fiat rewriting | The producer itself establishes a pass theorem | Semantics and proof maintenance for every evolving pass |
| Proof-producing construction | PCC and proof-generating compilers | Producer emits a result and certificate checked by a smaller consumer | Certificate language, checker, and exact statement remain critical |
| Untrusted construction plus validation | CompCert allocation, TVOC, Alive2, ZKCrypt optimization, CryptOpt | Any producer may propose; only the concrete checked pair is accepted | Checker coverage, semantic adequacy, and indeterminate outcomes |

No one mode dominates every transform. Stable, small, algebraic families are
better candidates for verified construction than rapidly changing heuristic or
search-heavy producers. Conversely, an untrusted producer is safe only to the
extent that an independent checker covers the exact claimed relation.

**Research implication.** Stage 4A candidates should permit producer trust to
vary by transform family without varying Protocol admission or relation
authority. A generic producer interface may be shared; a generic semantic
meaning should not be assumed.

### 2.2 The relation is exact, directional, and bounded by its semantic model

CompCert proves simulations between named intermediate languages. Alive2
checks directed refinement in the presence of LLVM nondeterminism and undefined
behavior. TVOC validates one concrete compilation. PCC typically proves a
safety policy rather than source/target equivalence. CryptOpt proves
straight-line functional equivalence, while ZKCrypt separately transports
cryptographic properties through a restricted protocol compiler.

The word `equivalent` would erase these distinctions. A successful checker
means only that its precise predicate holds for its precise subjects under its
precise model, assumptions, and checker basis.

**Research implication.** Candidate transform contracts should expose the
predecessor and successor, direction, observer, semantic regime, maps,
assumptions, rule or checker, and result qualification. Functional,
transcript, distributional, adversarial, intentional-change, and
property-specific relations should not acquire common authority merely because
they fit one record envelope.

### 2.3 Admission, transformation, property transport, and selection are four
different judgments

None of the surveyed mechanisms justifies collapsing these stages:

```text
the proposed target is a well-formed admitted subject
  != the target bears relation R to the predecessor
  != a predecessor property holds for or transports to the target
  != the target satisfies compiler-local constraints
  != the target is preferred over a complete comparison domain
```

Proof-producing systems bind a certificate to a proposition; they do not make
the target into a zkc-admitted subject. Translation validators establish one
source/target relation; they do not establish every source property. Solvers
can find a feasible candidate without proving complete coverage or optimality.

**Research implication.** A candidate should state which owner establishes
each judgment, the exact capability or qualified fact emitted, and the
non-implications among them.

### 2.4 Search success and search completeness are different products

Equality saturation, synthesis, superoptimization, and constraint solving can
find valuable candidates without closing their search spaces. Iteration, node,
time, memory, unrolling, grammar, and solver limits are ordinary operating
conditions, not exceptional evidence that no candidate exists.

**Research implication.** The authoritative comparison domain, if any, should
be declared independently of the provider's discovered set. `NoSelection` and
global optimality require a coverage argument over that declared domain.
Incomplete search may still produce a useful, explicitly qualified feasible
candidate or partial frontier.

### 2.5 Functional correspondence does not transport cryptographic properties

ZKCrypt separates a reference implementation's security theorem from
equivalence validation of an optimized implementation. Jasmin treats
constant-time preservation as a dedicated obligation rather than a corollary
of functional correctness. Certifying ZK compilers distinguish proof-protocol
security from lower-level generated-code correctness.

**Research implication.** Property transport should cite a property-specific
rule with exact source property, predecessor/successor relation, model,
assumptions, substitutions, observers, and any quantitative loss. The default
result of a transform relation should transport no property.

### 2.6 Reproduction data and replayable authority are not the same thing

MLIR can record an initial IR and pass pipeline for crash reproduction. Souper
can cache synthesis results, but its first-party documentation warns that its
Redis cache lacks versioning across incompatible changes. Build systems such
as [Bazel remote caching](https://bazel.build/versions/8.3.0/remote/caching)
and [Nix derivations](https://nix.dev/manual/nix/2.34/store/derivation/) make
declared commands, inputs, and execution attributes explicit for their own
cache or store models. Neither source establishes that a cached result or
derivation closes zkc semantic inputs, proves a Protocol relation, or recreates
live authority.

**Research implication.** A receipt may preserve subjects, evidence, and a
complete claimed basis for cold replay. It should not preserve a live admitted
capability. Decision replay, producer rerun, and bit-for-bit reproduction are
different claims.

## 3. Verified compilation: CompCert

### 3.1 Source model

**Source fact.** [CompCert](https://compcert.org/doc/) defines a succession of
formally specified intermediate languages and proves semantic preservation for
its passes. Its [manual](https://compcert.org/man/manual001.html) states the
theorem over an exact compiler boundary and permits compilation to fail rather
than promising a target for every source input. The proof is composed from
pass-local preservation results rather than one opaque end-to-end checker.

**Source fact.** CompCert also uses a validation-backed pass. The
[register-allocation module](https://compcert.org/doc/html/compcert.backend.Allocation.html)
calls an external allocator, then checks the returned allocation and
translation before the result can enter the proved compiler pipeline.

### 3.2 Strengths and accumulated pressure

CompCert demonstrates that adjacent relation proofs support understandable
composition and isolate changes. It also demonstrates that an external,
complex algorithm does not have to enter the trusted base when its output can
be validated by a simpler proved checker.

The cost is substantial. Direct verification requires formal semantics for
every intermediate representation, a theorem for every pass, and maintenance
when semantics or transformations change. Its theorem remains bounded by the
front-end, assembler, linker, runtime, extraction, and environment assumptions
that are actually included. The result does not silently establish timing,
constant-time, complexity, or cryptographic preservation.

### 3.3 Transfer candidate and analogy limit

**Transfer candidate.** A Stage 4A candidate may validate every adjacent
semantic Protocol step and compose affirmative results only through a named
composition rule. Small stable families may be verified by construction;
complex producers may be external and checked.

**Analogy limit.** CompCert's deterministic program simulation does not define
a universal relation for interactive, probabilistic, adversarial Protocols.
The useful transfer is the proof architecture and boundary discipline, not its
specific relation.

## 4. Translation validation: TVOC, Alive2, and PEC

### 4.1 TVOC and producer-supplied correspondence

**Source fact.** [Translation Validation for Optimizing
Compilers](https://theory.stanford.edu/~barrett/pubs/BFG%2B05-abstract.html)
checks the particular source and target produced by a compiler rather than
proving the compiler implementation correct once for all. Work extending TVOC
to loop transformations required explicit correspondence between source and
target iterations and exposed the difficulty of recovering that mapping after
several transformations have been combined.

**Transfer candidate.** A provider may supply lineage, occurrence,
iteration-like, message, randomness, commitment, or interface maps as checking
witnesses. The checker must authenticate and validate them; their presence
cannot establish the relation by assertion.

### 4.2 Alive2 and directed refinement

**Source fact.** [Alive2](https://web.ist.utl.pt/nuno.lopes/pubs.php?id=alive2-pldi21)
formalizes LLVM transformation validation as directed refinement. With
undefined behavior and nondeterminism, target behavior must be contained in
source behavior; the result is not necessarily symmetric equivalence. Its
practical checker has explicit scope and resource boundaries, including
bounded treatment of loops and solver timeout or unsupported outcomes.

**Transfer candidate.** Relation direction and observer/model identity should
be first-class. A bounded or solver-dependent result should preserve its exact
qualification.

**Analogy limit.** An Alive2-style relation cannot be applied unchanged to
protocol transcripts, adversarial environments, challenge distributions, or
security experiments.

### 4.3 PEC and parameterized transform families

**Source fact.** [PEC](https://www.cs.cornell.edu/~lerner/papers/pldi09-pec.html)
checks parameterized equivalence of partially specified programs. This permits
many-to-many transformation schemas, including loop transformations, to be
proved once and instantiated at concrete matches.

**Transfer candidate.** Stable transform families may amortize proof work in a
parameterized rule. Each use must still bind the exact rule identity,
predecessor match, successor match, substitution, maps, and discharged side
conditions.

### 4.4 Shared pressure

Translation validation accumulates pressure at semantic mismatches, undefined
or underspecified behavior, loops, memory, concurrency, solver limits, and
correspondence inference after combined transforms. A validator can give
verified-compiler-strength assurance only for the exact relation it completely
and correctly checks. Incomplete checking must remain visible.

## 5. Proof-carrying, proof-producing, and certifying systems

### 5.1 Source models

**Source fact.** Necula's [Proof-Carrying
Code](https://doi.org/10.1145/263699.263712) lets an untrusted producer supply
code and a proof of a consumer-defined safety policy; the consumer checks the
proof before accepting the code.

**Source fact.** [Foundational Proof-Carrying
Code](https://www.cs.princeton.edu/~appel/fpcc.html) reduces dependence on a
large specialized verifier by grounding acceptance in a smaller logical
foundation.

**Source fact.** A [proof-generating
compiler](https://doi.org/10.1016/j.entcs.2005.03.023) emits target code and a
proof of a translation predicate. The certificate is checked independently of
the producer.

**Source fact.** The certifying-algorithm discipline surveyed in [Certifying
Algorithms](https://people.mpi-inf.mpg.de/~mehlhorn/ftp/master-final.pdf)
returns an output and witness, then validates the witness with a preferably
simple and deterministic checker.

### 5.2 Strengths and pressure

These systems cleanly separate expensive construction from acceptance and
make exact evidence portable between a producer and checker. They do not make
the checker, proof calculus, proposition encoding, logical axioms, extraction,
or model correspondence disappear. A small checker is useful only if the
certificate is bound to the intended statement and subjects.

### 5.3 Transfer candidate and analogy limit

**Transfer candidate.** A common proposal envelope may carry proposed Protocol
bytes, exact subject identities, lineage/maps, a transform-family certificate,
and optional domain or optimality certificates. The payload remains
unauthoritative until the exact checker accepts it against the exact basis.

**Analogy limit.** Traditional PCC usually proves target safety rather than a
predecessor/successor relation. A proof object also cannot mint or serialize a
live zkc capability. A common certificate envelope need not imply one common
proof language or semantic proposition.

## 6. MLIR as a transformation carrier

### 6.1 Source model

**Source fact.** [MLIR Dialect
Conversion](https://mlir.llvm.org/docs/DialectConversion/) represents legal,
dynamically legal, illegal, and unknown operations relative to a declared
conversion target. Conversion patterns and type converters attempt to produce
an IR satisfying the requested partial or full conversion mode.

**Source fact.** The [MLIR Transform
Dialect](https://mlir.llvm.org/docs/Dialects/Transform/) represents transform
IR separately from payload IR. It provides matching, sequencing, handle
tracking, silenceable and definite failure behavior, and extension operations
whose implementation may invoke arbitrary compiler infrastructure.

**Source fact.** [MLIR pass
management](https://mlir.llvm.org/docs/PassManagement/) can emit crash
reproducers containing initial IR and a pass pipeline.

### 6.2 Strengths and accumulated pressure

MLIR is strong infrastructure for proposal plans, matching, rewriting,
multi-level lowering, and debugging. It also exposes operational hazards:
handle consumption and invalidation, mutation before failure, client-defined
extension behavior, registry state, and differences among partial and full
legality.

### 6.3 Transfer candidate and analogy limit

**Transfer candidate.** Candidate architectures may use MLIR for the producer
plane: transform-plan representation, matching, rewrite execution,
intermediate structural carriers, and reproducer generation.

**Analogy limit.** MLIR verification and conversion legality mean only what the
loaded dialects, conversion target, extensions, and process establish. They do
not imply PIR admission, a Protocol predecessor/successor relation, property
transport, constraint satisfaction, or optimal selection. Ambient C++
extension state cannot become semantic authority merely because the transform
interpreter executed successfully.

## 7. Equality saturation: egg

### 7.1 Source model

**Source fact.** [egg](https://arxiv.org/abs/2004.03082) uses e-graphs to
compactly represent congruent expressions, applies rewrite rules until a stop
condition, and extracts an expression under a chosen cost model. Rebuilding
and e-class analyses support efficient congruence maintenance and domain-
specific reasoning.

**Source fact.** egg's [explanation
facility](https://docs.rs/egg/latest/egg/tutorials/_03_explanations/index.html)
can record rewrite and congruence steps explaining an equality. The same
documentation also illustrates that unsound supplied rewrites can derive
false equalities; the e-graph does not prove the semantic soundness of its
rules.

### 7.2 Strengths and accumulated pressure

Equality saturation separates exploration from extraction and shares common
candidate structure effectively. Its practical limits include e-graph growth,
rule scheduling, conditional and contextual rewriting, resource stop
conditions, and extraction objectives that may be difficult or
non-decomposable.

### 7.3 Transfer candidate and analogy limit

**Transfer candidate.** An e-graph can be an unauthoritative candidate
compactor and derivation producer. An explanation can be translated into a
family certificate that cites exact checked rules and side conditions.

**Analogy limit.** Resource-bounded saturation does not close the semantic
candidate domain. An explanation is not a zkc proof until every rule,
instantiation, and side condition is checked under the intended Protocol
semantics. Extraction is optimal only inside the represented e-graph under the
declared cost model.

## 8. Synthesis and superoptimization: Souper and CryptOpt

### 8.1 Souper

**Source fact.** [Souper at the research snapshot](https://github.com/google/souper/tree/963d4df436f3dc0b039cc0e47ada0577a26f5c4e) uses an LLVM-derived
IR and SMT solving to discover and validate peephole improvements. The [Souper
paper](https://arxiv.org/abs/1711.04422) presents synthesis as a way to find
missed optimizations within that language and semantic scope.

**Source fact.** Souper supports an external Redis cache. Its first-party
documentation warns that the cache has no versioning and should be deleted
when incompatible upgrades make stored results stale.

**Transfer candidate.** Search and synthesis may remain untrusted providers,
and caching may accelerate them, if each accepted target is checked afresh
against a complete semantic basis.

**Analogy limit.** A failed synthesis search does not prove the absence of a
valid target. Solver `UNSAT` is not independently checked unless the solver
emits a proof accepted by an adequate proof checker. The search grammar and
modeled operations bound every result.

### 8.2 CryptOpt

**Source fact.** [CryptOpt](https://arxiv.org/abs/2211.10665) uses randomized,
benchmark-guided search to propose optimized cryptographic assembly. Its final
output is accepted through a formally verified equivalence checker against
formal source and target semantics; search strategy and benchmark guidance are
outside the correctness argument.

This is strong evidence that a volatile performance producer can be separated
from a stable correctness boundary. It also exposes a limit: the checked
domain is straight-line arithmetic code, while the measured objective is
platform-sensitive and does not establish global optimality over all possible
programs.

**Research implication.** Candidate architectures should test whether
performance evidence belongs in an exact `CostRelation` basis, while the
producer that uses it remains unauthoritative. Measured superiority should not
be silently treated as a timeless semantic score.

## 9. Finite-domain optimization and checked completeness

### 9.1 Solver outcomes are deliberately qualified

**Source fact.** The [MiniZinc
specification](https://docs.minizinc.dev/en/2.9.4/spec.html) distinguishes found
solutions from output that establishes completed search. Without the relevant
completion result, the solver has not established exhaustive enumeration,
unsatisfiability, or optimality.

**Source fact.** [OR-Tools
CP-SAT](https://developers.google.com/optimization/cp/cp_solver) distinguishes
`OPTIMAL`, `FEASIBLE`, `INFEASIBLE`, `MODEL_INVALID`, and `UNKNOWN`. A feasible
solution is not an optimality claim, and an unknown result is not
infeasibility.

**Source fact.** [VeriPB](https://veripb.org/) and its [proof-format
documentation at the research snapshot](https://gitlab.com/MIAOresearch/software/VeriPB/-/blob/e61f09a40837da9a805177edc4acd69e67986dfe/proof_format_overview.md)
show how pseudo-Boolean solving, objective bounds, optimality, and enumeration
claims can be accompanied by independently checked proof logs.

**Source fact.** [SCIP exact
solving](https://www.scipopt.org/doc-10.0.0/html/EXACT.php) separates exact
rational solving and certificate support from ordinary floating-point solver
execution, and documents that certificate coverage depends on supported
inference steps.

### 9.2 Domain obligations

A finite comparison domain needs more than a finite provider run. Candidate
architectures should make the following claims independently inspectable:

- the candidate grammar and every numeric or structural bound;
- a canonical pre-admission identity for every declared member, including a
  member whose proposal is malformed or whose target fails admission;
- canonical enumeration order;
- admitted-target, transition-claim, qualification-basis, assessment, and
  duplicate identities without collapsing them;
- completeness of generation or symbolic coverage;
- soundness and coverage of every pruned region;
- exact constraint predicates;
- exact objective algebra and comparison direction; and
- deterministic tie handling.

A symbolic-domain certificate must bind the exact denotation, encoding
correspondence, finiteness, membership, duplicate policy, and claimed coverage.
Closure, infeasibility, and optimality are different propositions. None alone
establishes target admission, predecessor/successor validity, constraints, or
objective adequacy unless those exact obligations occur in the checked
certificate statement.

For a deliberately small v0 domain, full canonical enumeration is a useful
baseline against which symbolic or certifying solver alternatives can be
compared. This is a research implication, not a selected Stage 4A policy.

### 9.3 Outcome distinctions to preserve in candidate comparison

The cases motivate at least the following semantically different result
classes:

| Research-level outcome | Minimum meaning |
|---|---|
| Closed selection | A winner is preferred under the exact objective over every member of one closed domain |
| Closed no-selection | The complete domain was covered and no candidate passed admission, relation, and constraints |
| Feasible, optimality open | At least one candidate passed, but global comparison is incomplete |
| Partial frontier | A qualified nondominated subset was found without a complete frontier claim |
| Search incomplete | A resource, bound, interruption, or unproved pruning event prevents closure |
| Unsupported | The requested semantics, transform family, model, or certificate is outside checker support |
| Refused | Policy declines an otherwise meaningful request without deciding it |
| Malformed | The request, proposal, or evidence cannot be interpreted as required |
| Checker failure | Infrastructure did not return a semantic result |

At this research phase, names and ownership remained open for candidate
comparison. The important research result is that these meanings must not
collapse into one boolean or one `NoSelection` state.

Under the frozen Stage 3 ordering, only closed selection and closed
no-selection are `QualifiedDecision` results. Feasible candidates, partial
frontiers, and incomplete search are useful attempt, search, or assessment
reports, but carry no complete-domain decision authority. Making them a new
decision family would require an explicit reopening rather than a name change.

## 10. ZK- and cryptography-specific precedents

### 10.1 ZKCrypt

**Source fact.** Microsoft's
[ZKCrypt](https://www.microsoft.com/en-us/research/publication/full-proof-cryptography-verifiable-compilation-of-efficient-zero-knowledge-protocols/)
starts from a high-level cryptographic goal, resolves sufficient conditions,
uses a verified compiler to construct a reference implementation with a
once-for-all security argument, then validates an optimized implementation
against the reference. Its property argument explicitly connects
implementation correspondence to completeness, proof-of-knowledge, and
zero-knowledge results.

ZKCrypt is the closest surveyed precedent for a hybrid stable semantic kernel
plus per-output optimization validation. Its boundary is also instructive: it
supports a restricted class of Sigma-protocol and group-homomorphism
constructions, validation is not complete for every possible optimization,
and lower-level code generation remains a separate correctness boundary.

**Transfer candidate.** A Protocol compiler may combine once-for-all proofs
for stable transform families with per-proposal validation, and may transport
a cryptographic property only through an explicit theorem chain.

**Analogy limit.** zkc cannot inherit ZKCrypt's protocol class, observational
relation, security model, or property theorem as a universal Protocol
semantics.

### 10.2 Certifying zero-knowledge compilers

**Source fact.** The [certifying compiler for zero-knowledge proofs of
knowledge](https://eprint.iacr.org/2010/339) generates certificates checked in
Isabelle for a supported protocol subset. The work distinguishes certification
of theoretical protocol properties from correctness of subsequent executable
code generation.

**Transfer candidate.** A cryptographic-property certificate can accompany a
transform result, but its theorem boundary and checker are separate from PIR
admission, predecessor/successor checking, endpoint code generation, and
runtime support.

### 10.3 CirC

**Source fact.** [CirC at the research snapshot](https://github.com/circify/circ/tree/271f911bab2c8ab15f12f599fd7abf89c4561093), described in the
[CirC paper](https://eprint.iacr.org/2020/1586), uses a shared compiler
infrastructure and an intermediate representation for several cryptographic
frontends, optimizations, and backends such as R1CS, SMT, and ILP.

**Transfer candidate.** Shared structural compiler machinery can reduce
duplicated lowering and optimization implementations.

**Analogy limit.** A shared program-to-constraint IR is not an admitted
Protocol subject, and successful lowering does not by itself establish an
exact Protocol-to-Protocol relation or cryptographic property transport.

### 10.4 Jasmin

**Source fact.** Jasmin's [verified preservation of
constant-time](https://eprint.iacr.org/2019/926) treats side-channel behavior as
a dedicated semantic property across compilation rather than deriving it from
ordinary functional correctness.

**Transfer candidate.** A Stage 4A candidate should test functional relation
checking and security-property transport as separately owned proof
obligations, even when they reuse the same step graph.

### 10.5 Fiat Cryptography

**Source fact.** [Fiat Cryptography at the research
snapshot](https://github.com/mit-plv/fiat-crypto/tree/4f7645db355b426123d3585b8a283921913dfbed) generates correct
finite-field arithmetic implementations from mathematical specifications. Its
[verified rewriting engine](https://arxiv.org/abs/2205.00862) composes
separately justified algebraic rewrites within a proved compilation
framework.

**Transfer candidate.** Small, local, algebraically stable Protocol-transform
families may admit verified-by-construction implementations and reusable rule
proofs.

**Analogy limit.** The success of verified algebraic rewriting does not show
that interactive scheduling, probabilistic behavior, adversarial observation,
Fiat--Shamir construction, composition, or quantitative security loss fit the
same rewrite relation.

## 11. Cross-case deductions for candidate construction

These are hypotheses that Stage 4A candidates and scenarios should test, not a
selected architecture.

### 11.1 A two-plane split is plausible but insufficient by itself

The sources support separating an extensible producer plane from a stable
checking plane:

```text
producer plane
  MLIR plans | e-graphs | synthesis | solvers | manual providers
  -> proposal + maps + optional certificate

checking plane
  independent target admission
  + exact family relation check
  + optional property transport
  + constraint and objective evaluation
  + closed-domain decision
```

However, one checking plane must not become one universal checker. It may share
an envelope and evidence discipline while dispatching to relation-family-
specific checkers and result algebras.

### 11.2 Adjacent validation and end-to-end validation answer different questions

Adjacent validation localizes failure and supports composition, as in
CompCert. End-to-end validation can catch an incorrect composition rule or an
intermediate abstraction mismatch. Candidate architectures should compare:

- adjacent checks only;
- end-to-end check only; and
- adjacent checks plus an independently stated end-to-end relation.

If semantic intermediates appear in the checked step graph, each must be an
exact admitted subject. Producer-internal operational IR need not become a
Protocol merely because it helps compute the proposal.

### 11.3 A certificate should be bound to a complete basis

Cross-case evidence suggests a certificate or receipt basis may need:

- exact predecessor and successor identities and admission bases;
- transform family, rule, direction, observer, model, and assumption identities;
- checker, proof format, ABI or statement, version, and dependency closure;
- lineage, occurrence, randomness, commitment, interface, and other maps read;
- constraint, objective, comparison, tie, and domain definitions;
- solver and resource basis for solver-qualified or incomplete results; and
- platform, environment, sampling, and noise treatment for measured results.

Whether every field belongs in one object remains a candidate-design question.
The cross-case requirement is that no read dependency remain ambient when it
can change the result.

The chain also needs explicit roots. Certificate-language semantics, query
encoding, checker soundness, any claimed completeness, and correspondence
between the specified checker and its running implementation must terminate in
named direct or mechanized checks or explicit residual trust. Translating the
certificate into another proof language does not close these obligations by
itself.

### 11.4 Persistence should re-establish, not deserialize, authority

A plausible cold-replay experiment is:

```text
stored subjects + certificate + complete claimed basis
  -> reauthenticate subjects
  -> independently re-admit predecessor and successor
  -> reload the exact checker/model basis
  -> recheck relation and optional property transport
  -> recheck domain, constraints, objective, and decision
  -> mint fresh process-local capabilities
```

Candidate architectures should compare recomputation, certificate replay, and
cache-hint reuse without allowing any stored record to become authority by
deserialization.

### 11.5 Determinism belongs in declared comparison semantics

Parallel scheduling, solver branching, hash-table order, e-graph extraction
order, cache state, and provider discovery order should not silently determine
an authoritative selection. A candidate claiming deterministic selection
should expose exact score domains, comparison order, and a final canonical
identity tie-break. If the objective is Pareto-valued, the candidate should
state whether the authoritative result is a complete canonical frontier or a
later policy choice over that frontier.

## 12. Transfer limits

The following limits apply across the entire dossier:

1. **Program semantics are not Protocol semantics.** LLVM, C, assembly, and
   term-rewriting relations do not directly model interactive events,
   transcript observations, adversarial scheduling, or challenge sampling.
2. **Functional preservation is not security preservation.** Constant-time,
   soundness, knowledge, zero knowledge, completeness, and composition require
   their own exact obligations.
3. **A checker is not automatically complete.** Bounded unrolling, incomplete
   rule sets, solver timeout, unsupported operations, and heuristic matching
   constrain affirmative and negative interpretations.
4. **A proof object is not self-authenticating.** Its proposition, subject
   binding, proof calculus, checker, axioms, extraction, and dependency closure
   remain part of the basis.
5. **IR legality is not semantic validity.** MLIR and other compiler IR
   verifiers establish only their declared structural and dialect invariants.
6. **Saturation is not domain closure.** An e-graph stopped by resources is a
   partial explored space, even when extraction succeeds.
7. **Solver optimality is encoding-relative.** A solver proof establishes the
   encoded objective over the encoded domain only if encoding adequacy and
   proof checking are also established.
8. **Measured cost is environment-relative.** Benchmark results require exact
   platform and methodology identity and generally do not establish a global,
   timeless optimum.
9. **Cache identity is a semantic concern.** Version-insensitive or
   dependency-incomplete cache keys can turn valid historical results into
   invalid current claims.
10. **Restricted ZK compilers do not universalize.** Sigma protocols,
    straight-line arithmetic, circuits, and one proof-system stack provide
    strong precedents only within their stated models.

## 13. Candidate axes exposed by the research

Equal-resolution Stage 4A candidates should make explicit choices on at least
these axes:

| Axis | Alternatives requiring comparison |
|---|---|
| Producer assurance | Verified producer; proof-producing producer; untrusted producer plus checker; family-dependent hybrid |
| Relation granularity | Adjacent steps; final pair; both with an explicit composition theorem |
| Relation family | Structural equality; Protocol equality; observer trace equality; directed refinement; distributional relation; intentional change; property-specific relation |
| Checker assurance | Direct recomputation; verified checker; proof-assistant replay; checked solver certificate; solver-trusted qualified result |
| Proposal witness | No hints; checked correspondence maps; proof derivation; producer trace; combinations |
| Identity layers | Pre-admission alternative; admitted target; transition claim; qualification basis; assessment; attempt; decision |
| Domain closure | Canonical enumeration; certified symbolic coverage; heuristic open search |
| Objective semantics | Exact lexicographic order; complete Pareto frontier; measured or stochastic objective with qualification |
| Output authority | Complete-domain qualified decision; non-decision feasible report; partial frontier; incomplete-search or operational report |
| Trust roots | Direct or mechanized roots; proof translation; checker implementation correspondence; explicit residual trust |
| Property transport | None; exact preservation; refinement; conditional or loss-bearing family theorem |
| Persistence | Recompute; certificate replay; cache hint; combinations with complete basis identity |
| Extension | New producer under an existing contract; new transform family requiring a new relation and checker |

The research does not select values on these axes. It does indicate that a
candidate is underspecified if it leaves them to provider convention or
ambient process state.

## 14. Red flags for later candidate review

A Stage 4A candidate should be challenged if it:

- introduces one unqualified `Equivalent` predicate for all transforms;
- lets target admission stand in for predecessor/successor checking;
- lets a successful transform relation stand in for property transport;
- lets MLIR verification or dialect legality stand in for Protocol legality;
- treats producer-supplied maps or explanations as facts without checking;
- lets provider enumeration define a supposedly complete domain;
- gives a domain member no identity until target admission succeeds;
- reports `NoSelection` after timeout, failed synthesis, or solver `UNKNOWN`;
- gives a feasible result, partial frontier, or incomplete search the same
  authority kind as a complete-domain decision;
- calls an e-graph extraction globally optimal without domain closure;
- accepts solver `SAT` or `UNSAT` as kernel-checked without stating proof and
  checker status;
- hides observer, semantic model, transcript regime, assumptions, or
  quantitative loss behind a transform-family name;
- makes benchmark noise or provider discovery order part of an undeclared
  selection policy;
- composes adjacent relation results without a named compatibility rule;
- persists a live authority token or recreates one from a cache hit;
- omits checker, model, rule, dependency, or environment identity from replay;
- terminates checker, certificate, model, or correspondence trust only in an
  unchecked adapter chain;
- lets compiler policy redefine Analysis meaning; or
- lets selection create a Protocol, relation, or transported-property
  capability.

## 15. Primary-source index

### Verified and validation-backed compilation

- [CompCert documentation](https://compcert.org/doc/)
- [CompCert manual](https://compcert.org/man/manual001.html)
- [CompCert validated register allocation](https://compcert.org/doc/html/compcert.backend.Allocation.html)
- [Translation Validation for Optimizing Compilers](https://theory.stanford.edu/~barrett/pubs/BFG%2B05-abstract.html)
- [Alive2: Bounded Translation Validation for LLVM](https://web.ist.utl.pt/nuno.lopes/pubs.php?id=alive2-pldi21)
- [PEC: A Program Equivalence Checker](https://www.cs.cornell.edu/~lerner/papers/pldi09-pec.html)

### Certificates and proof-producing systems

- [Proof-Carrying Code](https://doi.org/10.1145/263699.263712)
- [Foundational Proof-Carrying Code](https://www.cs.princeton.edu/~appel/fpcc.html)
- [Proof-generating compiler](https://doi.org/10.1016/j.entcs.2005.03.023)
- [Certifying Algorithms](https://people.mpi-inf.mpg.de/~mehlhorn/ftp/master-final.pdf)

### Transformation and optimization infrastructure

- [MLIR Dialect Conversion](https://mlir.llvm.org/docs/DialectConversion/)
- [MLIR Transform Dialect](https://mlir.llvm.org/docs/Dialects/Transform/)
- [MLIR pass management and crash reproducers](https://mlir.llvm.org/docs/PassManagement/)
- [egg: Fast and Extensible Equality Saturation](https://arxiv.org/abs/2004.03082)
- [egg explanations](https://docs.rs/egg/latest/egg/tutorials/_03_explanations/index.html)
- [Souper repository snapshot](https://github.com/google/souper/tree/963d4df436f3dc0b039cc0e47ada0577a26f5c4e)
- [Souper: A Synthesizing Superoptimizer](https://arxiv.org/abs/1711.04422)
- [CryptOpt](https://arxiv.org/abs/2211.10665)

### Finite-domain and certifying optimization

- [MiniZinc language specification](https://docs.minizinc.dev/en/2.9.4/spec.html)
- [OR-Tools CP-SAT result statuses](https://developers.google.com/optimization/cp/cp_solver)
- [VeriPB](https://veripb.org/)
- [VeriPB proof-format snapshot](https://gitlab.com/MIAOresearch/software/VeriPB/-/blob/e61f09a40837da9a805177edc4acd69e67986dfe/proof_format_overview.md)
- [SCIP exact solving and certificates](https://www.scipopt.org/doc-10.0.0/html/EXACT.php)
- [Bazel remote caching](https://bazel.build/versions/8.3.0/remote/caching)
- [Nix derivations](https://nix.dev/manual/nix/2.34/store/derivation/)

### ZK- and cryptography-specific compilation

- [ZKCrypt: Full Proof Cryptography](https://www.microsoft.com/en-us/research/publication/full-proof-cryptography-verifiable-compilation-of-efficient-zero-knowledge-protocols/)
- [A Certifying Compiler for Zero-Knowledge Proofs of Knowledge](https://eprint.iacr.org/2010/339)
- [CirC repository snapshot](https://github.com/circify/circ/tree/271f911bab2c8ab15f12f599fd7abf89c4561093)
- [CirC paper](https://eprint.iacr.org/2020/1586)
- [Jasmin constant-time preservation](https://eprint.iacr.org/2019/926)
- [Fiat Cryptography repository snapshot](https://github.com/mit-plv/fiat-crypto/tree/4f7645db355b426123d3585b8a283921913dfbed)
- [Fiat Cryptography verified rewriting engine](https://arxiv.org/abs/2205.00862)
