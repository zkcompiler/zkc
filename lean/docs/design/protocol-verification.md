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
General native control import, waiting schedulers, production fields/groups, provider
randomness, DSL compiler correctness and lower-stage preservation require their
own adequacy proofs or maintained tests. Variable-round full-prefix reductions,
concrete transcript instantiation, general PCS and concurrent zero-knowledge
composition need appropriate external theorems and adapters.
A generic automation claim must quantify the supported contract language and
state what obligations remain when normalization does not succeed.

The implementation is an extensible research baseline, not an assertion that
all programs can be automatically proved safe. New protocol families should be
chosen to falsify the interfaces: variable-round protocols, stateful commitments,
lookup arguments and different adversary/query structures are useful tests.
Research can adjust package boundaries when these tests expose a concrete need.
