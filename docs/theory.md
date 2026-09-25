# Theory behind the model

zkc combines source typing, effect semantics, program analysis and relational
proofs. Each supplies a different part of a compiler argument. This chapter
connects those parts; [assurance](assurance.md) identifies the exact Lean sources.

## 1. From a source check to a reusable compiler law

The proof structure is:

```text
source check → interpreted body and input premises
             → valid facts at each program point
             → justified local replacement
             → complete execution relation
             → the chosen consumer's property
```

Every arrow needs a law. Scoped syntax alone does not establish a runtime
invariant; a valid invariant alone does not justify a replacement; an execution
relation transports only properties covered by its observation and context.

**Typed operations and handlers** separate a computation from the implementation
of its calls. PIR's dependent reply type makes the continuation consume the
reply of that particular operation. Induction on `Proc` proves `run_bind` and
`run_related`, so one handler proof can serve many caller programs. This uses
the operation/handler method of Plotkin and Pretnar [1]; PIR does not quotient
all operations by a universal effect theory. See [execution](guides/execution.md).

Interpretation can itself produce another program. An interpreter comparison
proves composition and execution fusion in the existing process calculus, plus
rewrite transport under explicit model laws. Interaction Trees [15] supplies a
related event-translation method, including richer coinductive behavior outside
the present scope. The [abstraction decision](rationale/semantic-abstraction.md)
therefore retains interpretation-based semantics while requiring structured
compiler forms where analyses and transformations consume them.

[Outer iteration](spec/core/iteration.md) applies that distinction to partial
services. Each finite body returns a continuation or a final result. Coherent
finite prefixes retain actual state and events; a deployment cap explicitly
converts pending work into exhaustion. Interpretation and complete per-body
simulation lift through those prefixes. This adds partial service behavior
without replacing every finite compiler theorem with a coinductive proof.

The maintained `Proc.run_interpret_bind` instantiates these laws at separately
constructed components: the suffix receives the prefix's actual residual
state. `Proc.interpret_interchange` requires a per-operation commuting square;
`Execution.follow_rebase` requires equality of the reached suffix's complete
execution before and after rebasing. [Construction controls](../formal/Tests/ConstructionSequencing.lean)
use the actual framed Sumcheck handler to distinguish sequencing from resetting
a transcript. No general interchange or state-reset rule is inferred from
associativity.

**Dependent indexing and checked erasure** connect a source check to usable
data. `Fin size` rules out an invalid capture position; `Scoped scope` carries
membership evidence. `erase_restrict` and `erase_eval` reconnect that evidence
to the original syntax and evaluator. Availability is checked separately because
a permitted slot can still lack a value. This follows the distinction between
static indices, data and evidence discussed in [2]. See [inputs](guides/source-and-inputs.md#source-inputs-scoped-expressions-and-captures).

## 2. Analysis facts need both unary and relational meanings

An abstract fact list describes possible concrete worlds. Write its
concretization, as explanatory notation, as:

```text
γ(facts) = {s | ∀ f ∈ facts, Means f s}

s ∈ γ(facts) ∧ moduleContract(actual call)
  ⇒ successorState ∈ γ(transfer(summary, facts))
```

This is the sound-transfer obligation of abstract interpretation [3]. The
current `call_transfer` proves the applicable instance, including writes on
failure. Unknown writes discard retained facts; a conservative dependency set
can contain variables that do not affect a particular run. The finite analysis
does not require a widening or a general fixpoint engine.

The query-plan theorem then has a different shape:

```text
Valid state facts ∧ check(facts, available, query, plan)
  ⇒ runPlan(state, query, plan) = runQuery(state, query)
```

`checked_value` proves this implication; `inferred_checked` supplies the checker
premise for the inferred plan. The module/caller laws keep `Valid` true at the
actual point of use. This is why a sound analysis and a correct transformation
are separate obligations. Benton's relational account of analysis and program
transformation [4] is a particularly close methodological fit.

**Hoare contracts** describe legal initial states and complete post-results.
Consequence and sequencing follow [5], adapted to retain failed states and
ordered events. **Local framing** proves which facts survive a call. The current
model uses explicit semantic footprints and implications; it does not implement
the separating conjunction or permission algebra of separation logic [6].
See [contracts](guides/contracts.md) and [state and modules](guides/contracts.md#state-modules-and-reusable-facts).

**Memoization** requires an immutable interpretation and a key covering its
dependencies. The current preparation instance uses a complete immutable key
and proves cache validity and value preservation separately from cost savings.
Selective memoization [12] suggests ways to expose finer dependencies and control
reuse; its modal language and execution traces are not implemented here.
Mutable queries still require the live fact/framing argument above.

`Preparation.contextual_memo` applies that invariant under arbitrary stateful
external calls using a product-state frame. `resolved_execution` relates the
prepared program to resolving preparation directly to its immutable value.
Both reuse `run_related`; their observer retains ordered external events and
forgets accounting. The [Sumcheck client](../formal/Zkc/Protocols/Sumcheck/Preparation.lean)
uses the prepared value in the next claim, while challenge and transcript calls
remain external. Word-valued and correlated-service controls use the same API;
a repeated parameter does not permit a repeated masked response. These are
finite atomic contextual laws, not a separation-logic resource algebra or an
asynchronous cache model.

## 3. Deterministic relations and probabilistic couplings

A cache optimization relates two executions of the same source under different
handlers. `SameWorld` permits different valid caches while equating the logical
worlds. `run_related` preserves outcomes and projected events for the shared
reply-adaptive continuation. A representation change instead needs a relation
on returned values and a corresponding source/target interpretation.

A probabilistic coupling is a joint distribution whose marginals are the two
executions being compared. Its support must satisfy the desired relation.
For example, over a finite field, compare publications `w+r` and `w'+r'` with
uniform masks. Pairing `r' = r+w-w'` preserves uniformity and makes the two
publications equal. Requiring the same mask in both runs would miss this proof.
This example explains the method; the service theorem uses its own full
setup/session bijection and conditions.

The link from couplings to relational program proofs is developed in [7].
zkc proves its product-suffix reconstruction and correlated-service mass laws
directly in Lean. The [normalized joint-release laws](../formal/Zkc/Probability/Disclosure.lean)
consume one actual coupling for the whole artifact/runtime pair. zkc has
not implemented pRHL or its proof-search system.
[Probability](guides/security-properties.md#probability-initialization-and-persistent-providers) explains the actual provider and
scalar-consumer laws, including the pre-draw view and exceptional outcomes.

The [iteration probability laws](../formal/Zkc/Probability/Iteration.lean)
push forward complete finite transitions, including stopped results. A geometric
retry tail requires a bound on continued mass at each reached step; marginal
retry rates do not suffice. Accepted publication additionally accounts for
fatal and publication loss. These are conditional accounting laws, not inferred
termination probabilities for a concrete prover.

**Information-flow reasoning** compares permitted observations across input
worlds [8]. Fixed-source input agreement and `Disclosure.Permitted` are concrete
instances. Cryptographic zero knowledge additionally needs the experiment,
simulator and distribution or computational relation stated in
[Properties](guides/security-properties.md). Public code and receipts join the observation
when they are released.

## 4. Communication, resources and implementation

Session-type and choreography theory [9, 10] asks whether global interaction
can be implemented by participants using their local information. PIR uses
returned-phase invariants and supplied endpoint correspondences. It does not
yet solve general asynchronous projection, progress or deadlock freedom.
The concrete issue is knowledge of a choice: a global phase can distinguish
two branches while a participant has received nothing that tells it which
branch to execute. `Conforms` alone cannot supply that information.

[Invocation-selected families](spec/profiles/source/families.md) make this
obligation constructive: each role selects its required program from its
permitted view. Actual ingress selects the admitted member; compact count
instantiation commutes with both participant projections. The same-view law
rules out a selector when indistinguishable worlds require different schedules.
It does not communicate the configuration or resolve a later distributed choice.

Affine resource reasoning guides at-most-once continuation use: a right may be
abandoned, but an accepted target cannot be reused. The installed atomic service
enforces that meaning through its isolated ledger. An affine source type system
or distributed capability protocol would be a further implementation, with its
own correspondence law. See [continuations](guides/accepted-continuations.md).

Data refinement and verified-compilation methods [11] guide the MLIR/Rust
boundary: relate source and target values, complete results and observations,
then compose the justified passes. Proof of a general compiler pass and checking
one produced result are different assurance routes. zkc's current local
mathematical laws support that architecture. The finite direct-plan and phase
checkers have implemented clients; native correspondence and substantive
optimization checking remain separate delivery obligations.

Secure compilation also asks what happens after linking target code chosen by
an adversary [13]. A common-continuation simulation does not answer that question
without a model of those target contexts. The current boundary keeps the same
reply-adaptive program and declared observer; arbitrary target linking is a
separate [research trigger](roadmap.md#3-research-triggers).

Fresh-name theory [14] helps separate a newly allocated identity from a reusable
immutable value. The current allocator proves freshness relative to its pool.
Its numeric identifiers are observable, so allocation does not automatically
license arbitrary renaming or prove global world ownership. Supplied-namespace
installation remains an explicit mutation.

The [component connection laws](spec/properties/relations.md#component-connections)
apply relational composition and contextual replacement directly. Local witnesses
remain existential within their component, while shared boundary values stay
available to the connector. Pointwise equivalence permits arbitrary connectors;
conditional replacement permits removing a check that a specific connected
component still enforces. Its staged premises prevent circular reliance on a
check removed from both components. Relational representation changes additionally
require coverage of valid boundaries and compatible target connectors. These
predicate laws do not constitute a general concurrent rely-guarantee calculus
or a cryptographic composition theorem.

[Acceptance realization](spec/realization/representations.md#acceptance-and-output-realization)
uses an input/output-indexed relation and arbitrary-witness adequacy. Its clients
bind a deterministic verifier's actual result, then connect a consumer of that
same result. The maintained Sumcheck instance joins the actual staged source to
direct evaluation using its existing source correspondence and completeness
theorems. These are applications of established relation and refinement methods;
the interfaces do not imply a new protocol security result.

[Input coverage](spec/verification/refinement.md#advertised-input-coverage)
adds a total-on-admitted-domain selection obligation to conditional refinement.
It prevents a vacuous initial relation from justifying an executable profile,
without confusing forward source coverage with full target-domain adequacy.
[Observation summaries](spec/verification/analysis.md#summaries-and-exact-consumers)
apply sound abstract interpretation through an explicit meaning predicate.
They permit conservative loss of precision, while exact later consumers still
need the existing locality/factorization law. The specialization control uses
the same law: having a suitable consumer for each configuration does not produce
one uniform consumer after the configuration is erased. No general abstract
domain or fixed-point solver is introduced by these pointwise laws.

## 5. Application status and further theory

The maintained [located-call profile](spec/profiles/source/located-execution.md)
applies local factorization and framing to actual shared definitions, reuses
all-reply interaction conformance to exclude hidden communication, and connects
checked guard agreement to actual typed branches. These are concrete parts of
the choreography boundary. They do not import a general endpoint-projection or
deadlock-freedom theorem. The original
[Pirouette study](https://www.mpi-sws.org/tr/2021-004.pdf) motivates keeping local
computation, distributed functions and communicated branch choice distinct;
the source/participant correspondence still needs its own proof for zkc.

| Status | Theories and concrete application |
|---|---|
| Definitions and laws in Lean | Typed effect interpretation; scoped indexing/erasure; Hoare consequence and sequencing; conservative dependency/fact transfer; handler refinement; conditional product probabilities; the service coupling instance and normalized joint release; conditional evidence; atomic custody |
| Design methods with a narrower current instance | Separation logic informs explicit framing; session types inform phase/role boundaries; information flow informs fixed-source and release relations; data refinement informs native adapter contracts |
| Triggered extensions | Full separation/resource logic, asynchronous choreography projection, higher-order logical relations, staged frontend metatheory, general abstract fixpoints, computational game logics, aggregate-attempt bounds and native side-channel semantics |

The distinction is about application, not the maturity of those established
theories. [Research triggers](roadmap.md#3-research-triggers) identify the concrete
capability that would require each extension. The
[worked transformation](guides/adding-a-transformation.md) shows several of the
current laws operating together on one actual source.

The [verification map](../formal/design/verification-map.md) extends this map to
implementation boundaries, connecting verified validation, heterogeneous data
refinement, proof replay, Rust extraction and external tools to explicit theorem
obligations.

## References

1. Gordon D. Plotkin and Matija Pretnar. [Handling Algebraic Effects](https://lmcs.episciences.org/705/pdf). *LMCS* 9(4:23), 2013, pp. 1–36.
2. Thorsten Altenkirch, Conor McBride and James McKinna. [Why Dependent Types Matter](https://people.cs.nott.ac.uk/psztxa/publ/ydtm.pdf). Draft, April 2005, pp. 1–21.
3. Patrick Cousot and Radhia Cousot. [Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs by Construction or Approximation of Fixpoints](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml). *POPL*, 1977, pp. 238–252.
4. Nick Benton. [Simple Relational Correctness Proofs for Static Analyses and Program Transformations](https://nickbenton.name/correctnesspopl2004.pdf). *POPL*, 2004, pp. 14–25; linked author version is revised.
5. C. A. R. Hoare. [An Axiomatic Basis for Computer Programming](https://www.cs.ox.ac.uk/publications/publication8205-abstract.html). *Communications of the ACM* 12(10), 1969, pp. 576–580, 583.
6. John C. Reynolds. [Separation Logic: A Logic for Shared Mutable Data Structures](https://doi.org/10.1109/LICS.2002.1029817). *LICS*, 2002, pp. 55–74.
7. Gilles Barthe, Benjamin Grégoire, Justin Hsu and Pierre-Yves Strub. [Coupling Proofs Are Probabilistic Product Programs](https://arxiv.org/abs/1607.03455). *POPL*, 2017, pp. 161–174; linked preprint appeared in 2016.
8. Dennis Volpano, Cynthia Irvine and Geoffrey Smith. [A Sound Type System for Secure Flow Analysis](https://journals.sagepub.com/doi/10.3233/JCS-1996-42-304). *Journal of Computer Security* 4(2–3), 1996, pp. 167–187.
9. Pierre-Malo Deniélou, Nobuko Yoshida, Andi Bejleri and Raymond Hu. [Parameterised Multiparty Session Types](https://lmcs.episciences.org/924/pdf). *LMCS* 8(4:6), 2012, pp. 1–46.
10. Elaine Li, Felix Stutz, Thomas Wies and Damien Zufferey. [Complete Multiparty Session Type Projection with Automata](https://cs.nyu.edu/wies/publ/cav23_mst.pdf). *CAV*, 2023, LNCS 13966, pp. 350–373; linked author manuscript includes the corrected complexity discussion.
11. Xavier Leroy. [Formal Verification of a Realistic Compiler](https://xavierleroy.org/publi/compcert-CACM.pdf). *Communications of the ACM* 52(7), 2009, pp. 107–115.
12. Umut A. Acar, Guy E. Blelloch and Robert Harper. [Selective Memoization](https://www.cs.cmu.edu/~rwh/papers/memoization/popl.pdf). *POPL*, 2003, pp. 14–25.
13. Carmine Abate, Roberto Blanco, Deepak Garg, Cătălin Hriţcu, Marco Patrignani and Jérémy Thibault. [Journey Beyond Full Abstraction: Exploring Robust Property Preservation for Secure Compilation](https://arxiv.org/abs/1807.04603). *CSF*, 2019, pp. 256–271; linked author version includes extended proofs.
14. Andrew M. Pitts and Ian D. B. Stark. [Observable Properties of Higher Order Functions that Dynamically Create Local Names, or: What's new?](https://homepages.inf.ed.ac.uk/stark/obspho-mfcs.pdf). *MFCS*, 1993, LNCS 711, pp. 122–141.
15. Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha, Benjamin C. Pierce and Steve Zdancewic. [Interaction Trees: Representing Recursive and Impure Programs in Coq](https://www.cis.upenn.edu/~stevez/papers/XZHH%2B20.pdf). *PACMPL* 4(POPL), Article 51, 2020, 32 pp., especially §3.3.
