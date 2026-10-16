# Research design: source-bound protocol verification

## Question

How can security theorems from independently evolving libraries be reused for
varied authored protocol programs, while keeping the program, intended relation,
experiment assumptions and theorem application tied together?

## Implemented design

The semantic center is a typed role-local open process. A source certificate
establishes its contract once; separate consumers establish properties under
explicit experiments. Exact process equality gives strong shared-state
composition and can be checked by an untrusted normalization-based generator.
Typed adapters, not source-name recognition, connect mathematical interfaces.
The CLI deliberately admits a bounded source language and reviewed schema;
Lean's typed API supports new contracts and consumers beyond that registry.

External connections test different reasoning styles: ArkLib's interactive
polynomial soundness bound, VCVio's simulation and extraction games, and ArkLib's
all-prefix restoration bound. A more complex factor-opening verifier tests
residual composition and a conditional bad-opening bound.
Helper-based, reordered, Horner and renamed source forms test whether proofs
follow semantics rather than fixed source identities. A separate authored-target
check tests whether a mathematically wrong relation can hide behind a correct
protocol or familiar name.

The Fiat–Shamir extension keeps construction explicit. It imports the actual
native constructed participant, gives each admitted primitive a fixed meaning,
and proves a complete denotation equation before applying a security observation.
This avoids assuming that an abstract construction was the one implemented by a
candidate. Source normalization and the security theorem remain reusable across
different authored forms, while exact native identities bind each request.

The two security families deliberately stress different interfaces. Schnorr
requires a fixed-statement extraction experiment and a replay query bound.
Sumcheck permits an adaptively selected public statement and arbitrary oracle
queries on full message/challenge prefixes. A proved salted-key simulation
connects that model to ArkLib. Its extra access is explicit in the bound;
discarding earlier challenges from a query key is not an assumed simplification.
All-prefix residual knowledge predicates include earlier failed checks, and the
local bad event retains its existential witness quantifier.

## Evaluation and falsification

Evaluate admission, semantic correspondence, security transport and native
adequacy separately. Positive examples must be actual exported subjects.
Negative controls should change protocol timing, residuals, selectors, relation
bodies, effect sites, domains, probability models and certificate subjects.
Check the checker itself with forbidden axioms and valid proofs about different
programs. Audit transitive proof dependencies rather than upstream build warnings.
Differential execution compares complete observable prefixes using an independent
native SSA interpreter; it supplements but never replaces theorem checking.

The architectural review asks whether generic consumers import particular
examples and whether each new source requires duplicating every theorem. The
semantic review examines role-local availability, termination, observation
budgets, state and stop distinctions. The proof-chain review reconstructs all
source-to-game equalities and external theorem premises. The generator review
reconstructs the requested subject independently of candidate aliases.
Independent read-only agents also reviewed the foundations and external theorem
candidates; this does not constitute a human external audit.
The [implementation review](review.md) records the reviewed boundaries, findings
and their resolutions.

## What remains open beyond the implemented profile

Exact equality is too strong for some optimizing transformations. Observational
adapters must state which events and resources they may hide. The Sumcheck
completion adapter transports acceptance while distinguishing final caches and
query counts after early rejection; it is not arbitrary contextual replacement.
General branches and Local control import, waiting schedulers, production fields/groups, provider
randomness, DSL compiler correctness and lower-stage preservation require their
own adequacy proofs or maintained tests. Runtime-variable security schedules beyond the proved fixed finite-round family,
concrete transcript instantiation, general PCS and concurrent zero-knowledge
composition need appropriate external theorems and adapters.
A generic automation claim must quantify the supported contract language and
state what obligations remain when normalization does not succeed.

The implementation is an extensible research baseline, not an assertion that
all programs can be automatically proved safe. New protocol families should be
chosen to falsify the interfaces: variable-round protocols, stateful commitments,
lookup arguments and different adversary/query structures are useful tests.
Research can adjust package boundaries when these tests expose a concrete need.

## Semantic intermediate representation as a proof boundary

An intermediate representation is useful when it makes the observations required
by the security game explicit: roles, challenge dependencies, state transitions,
message order, stopping and mathematical domains. Its benefit is conditional on
adequacy. Adding a translation alone cannot decrease trust or establish that a
source program has the intended meaning. The implemented independent evaluators
and elaboration/decoding laws remove specific within-model translation premises;
actual native extraction and production primitive conformance remain separate.

The selected theorem chain is: retained carrier, checked typed process,
proved contract, selected experiment, security consumer. A source transformation
may be proposed by untrusted code and validated by a sound but incomplete
normalizer. A single contract certificate can support multiple consumers; a
consumer can apply to multiple source forms. Changing observations requires a
proved adapter with explicit state relations and coverage. Equality of accepted
bits cannot justify replacing a residual oracle cache in arbitrary continuations.
This factoring reduces duplicated proof obligations without claiming all
source/contract/experiment combinations are compatible.

The implementation tests three distinct security interfaces: Schnorr extraction,
finite-round Sumcheck bad-query bounds, and KZG-backed evaluation-sum binding.
The KZG route uses a concrete reduction and an explicit bound for its reduced
adversary. The pinned upstream convenience assumption quantifies unrestricted
adversaries, so it is not presented as standard efficient-adversary hardness.
Broader PCS composition needs its own extraction and representation connections.

The implementation order follows dependency rather than protocol popularity:
semantic adequacy and raw/typed correspondence; finite FS experiments and control;
concrete commitment composition; structural decoding and native controls; then
shared proof automation and explicit requests. At each boundary, falsification
cases challenge dormant malformed paths, state/capture substitutions, wrong
subjects, incompatible experiments, stops and actual provider calls. Resource
capacity is kept distinct from semantic correctness: string-size enforcement is
an executable preflight, while a compositional theorem validates structural
JSON interpretation without reducing large byte arrays inside each certificate.
