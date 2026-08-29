# Analysis closure reference instrument

This package is a bounded executable pressure test for the first Analysis
consumer above the Relations layer. It imports that layer exactly and reaches
Protocol IR and Foundation only through the authenticated import chain. It does
not copy their Protocol, Plan, Relations, execution, or identity semantics into
an Analysis-owned shadow model.

The instrument has three deliberately separate layers.

## 1. Global theorem schema

`AFK_V2_THM4_CLASSICAL_ROM` identifies a family-neutral schema for the selected
classical-ROM result from Attema--Fehr--Klooß, ePrint 2021/1377 v2. Its identity
contains closed templates for the source and target properties, both experiment
shapes, required semantic views and maps, side conditions, four local
quantitative operators, the transform program, and the conclusion law.

It contains no Schnorr family identity, native Foundation/PIR/Relations
subject, fixed member, model instantiation, selector, or concrete formula
identity. Those coordinates belong to later layers. Creating or changing a
family therefore does not rotate the global theorem identity.

The theorem-statement digest is derived from the exact profiled semantic
schema body; it is not a second, independently encoded statement copy. The
single source of truth for the PDF digest, ordered locator tuple, and
`ImportedPaperOnly` status is `AFKV2SelectedSourceAuthority` in the
[cryptographic property profile](../../docs-next/analysis/cryptographic-properties.md#5-afk-theorem-profile).
This instrument asserts that source record byte for byte rather than restating
it.

Schema formation establishes identity and shape only. The theorem's truth is a
separate goal and remains `Assumed`; no proof artifact is admitted here.

## 2. Abstract family applicability and transport

`AFKAsymptoticFamily` is an Analysis-level symbolic family indexed by logical
statement length `n`. For the selected source-exact lane, `k=2` and one finite
challenge cardinality `N` are fixed across every member. The random-oracle
index family is the finite set of bitstrings of length at most `u(n)`, with
explicit efficient encoding, equality, lookup, and sampling operations and a
finite lazy-function table at each `n`.

Applicability binds the global theorem's local roles to one such family. It
requires exact family denotation, Fresh/FS projection, public-coin uniformity
and independence, efficient source algorithms, the bounded-bitstring oracle
domain, adaptive lazy-random-function process correspondence, exact framing and
programming/rerun adequacy, and `0 <= Q < N`. Theorem truth is explicitly
refused as applicability evidence.

Transport then requires two additional capabilities:

1. an externally issued all-`n` two-special-soundness source result; and
2. a separate theorem-truth treatment.

Without the all-`n` source capability, transport returns `CannotAnswer`. A
finite `n0` Schnorr judgment cannot fill that slot. The fixture constructor for
the all-`n` capability is visibly conditional and supplies no proof.

The selected target prefix is:

```text
exists positive polynomial q_KS
exists one uniform black-box extractor E
forall logical statement lengths n
forall query bounds 0 <= Q < N
forall total-output adaptive classical provers P^a
```

The Statement is an output of `P^a`, not an outer universal binder. `P^a` is
input-free, total-output, and not restricted to polynomial time. `E` receives
only `n` and black-box access to `P^a`; it does not receive `Q`, `epsilon`, the
prover code as data, or a hidden oracle table. The conclusion preserves the
full `(x, pi, aux, v)` law and adds `w`, with success defined as verifier
acceptance and the family relation holding for `(x,w)`.

The outer prover experiment may sample a randomized prover's coin tape. Within
one theorem-granted extractor invocation, that tape is fixed into one
deterministic next-message strategy and every authorized sibling run resets to
its authenticated root frame. A new extractor invocation receives a fresh tape
and a fresh lazy-function table. The executable contract exposes only
`ProgramSibling` and root `Rerun`; it exposes no ambient `Rewind` or `Fork`.

## 3. Pointwise `n0` specialization

Only after family transport may a checked correspondence specialize the result
to the executable `n0=1` member. The selected witness uses the same
prime-order-11 group as the stock Relations-layer Schnorr fixture but challenge
set `C={0,...,7}`. One uniformly sampled byte and one attempt decode totally
and uniformly because 8 divides 256.

This layer alone owns the concrete Foundation/PIR/Relations subject projection,
Fresh and FS member selectors, models, manifests, fixed public setup, full 20-role map,
four formula correspondences, and exact PIR challenge-query encoding. The role
coordinates are symbolic catalog positions, while separate resolved endpoints
bind every abstract and native role to family or Foundation/PIR/Relations
content. The gate checks both endpoints and the exact twenty-entry shape; the verifier and
verifier-output roles resolve specifically to the PIR check and accepting
terminal occurrences. The
claim that those paired coordinates have the same denotation remains an
explicit pointwise premise; structural equality is not promoted into semantic
equivalence. The authenticated formula templates are parsed and normalized
independently from the concrete typed expressions, then checked for exact
canonical AST equality after substitution, and every member formula identity
is re-derived from its ordinal, subject, and authenticated transform. The AFK
Statement is raw `Y`; `(g,q,p,session,application-domain,namespace,framing)` is
fixed public setup. Its timing flags are derived from the immutable PIR source
objects and exact pre-challenge influence prefix; the remaining family-process
adequacy is still a premise. The table checks the exact PIR carrier for all 121
valid `(Y,A)` pairs and verifies injectivity on that finite domain.

The conditional correspondence is formed over one exact nine-node hypothesis
DAG. In ordinal order its nodes are family denotation and length embedding,
pointwise family projection, the concrete challenge model, the concrete
acceptance relation, fixed challenge cardinality, finite random-oracle indexing
and operations, role-map adequacy, quantitative-normalization adequacy, and
full process correspondence. Their dependency ordinals are exactly:

```text
[], [0], [], [], [0,1], [0,1],
[0,1,2,3,4,5], [0,1,2,4,6], [0,1,5,6]
```

The unique outward root frontier is `[7,8]`. The support partition covers every
reachable node exactly once as established or assumed. Its source-support
domain is also closed: two dependent family support-schema bindings cover the
Fresh-source and adaptive-FS-target family manifests, and two exact concrete
support coordinates cover the selected Fresh and target manifests. Missing,
extra, reordered, or cross-axis support does not admit the correspondence.

The family oracle index is finite bounded bitstrings. Its authenticated bound
is a closed polynomial `u(n)`; at `n0`, the gate evaluates that polynomial and
requires the result to match the bit length of Foundation's maximum raw
canonical-datum encoding. This is the raw encoded query index, not the smaller
payload capacity of a nested Foundation `BytesValue`. The selected native statement length is derived
from the raw Statement and retained alongside an explicit pointwise length-
embedding premise; it is not a free literal. Prover queries may be outside the
verifier image but remain inside that bound, and all calls, including repeats
and off-image calls, count toward `Q`. The local
`lazy_random_function_trace` helper checks only realized finite-table behavior;
it is not evidence for the adaptive process correspondence.

The stock modulus-11 bounded-rejection fixture is not selected for this
specialization. Concrete SHA-256 execution is never random-oracle evidence.
The finite helper executes `BeginExtractorExperiment`, one `Baseline`, and
typed `ProgramSibling`/`Rerun` transitions over immutable frame, tape, and table
lineages. Experiment identity commits the exact capability contract, invocation
nonce, independent root and tape commitments, `N`, and `Q`. Baseline and rerun
acceptance are internally issued only after the checked PIR challenge-query
carrier, observed or programmed challenge, and exact bounded Schnorr Check and
Terminal rules agree. The derived pair retains both full transcripts and
applies the exact admitted-pair predicate; it is not an execution capability.
Every adaptive-prover oracle call spends the per-invocation `Q`, including
repeats and off-image calls; verifier calls and programming do not. Non-target
table answers are shared only inside that extractor invocation, and successful
rerun authority is process-locally consumed even against an older state value.
Only one exact state occurrence per experiment is current; every successful
transition supersedes the predecessor, preventing stale immutable states from
forking or reverting the persistent lazy table.

These tests establish only the transition invariants and exact bounded
Schnorr/PIR acceptance joins of this finite classical instrument. Root and tape
commitments label lineage; the helper consumes caller-supplied finite call
traces and does not authenticate or execute a generic adaptive-prover strategy.
The tests therefore do not establish theorem truth, the adaptive process
correspondence, ROM security, concrete-hash security, QROM behavior, or a PIR
`ReplayRun` interpretation.

Correspondence formation produces a portable inert judgment, inert checked
result, and owner authority binding. It separately issues a fresh,
process-local capability restricted to the member-specialization consumer and
purpose. The live token, issuer occurrence, and live wrapper enter none of the
semantic IDs or portable records. Cold validation reconstructs and compares
the exact inert semantic components without minting authority. Invocation-time
validation additionally authenticates the supplied live capability against
that exact authority binding and checks the concrete witness fields; it does
not call formation recursively or compare against a newly minted live wrapper.

Pointwise specialization consumes two independently live inputs: the checked
all-`n` family-target capability and the checked one-member correspondence
capability. It forms the member hypothesis context with
`CanonicalGoalDagUnion` over the family-target DAG and the nine-node instance
DAG. Equal goals are merged by exact goal identity, their dependency sets are
unioned, cycles are rejected, fresh canonical ordinals are assigned, and the
outward frontier is derived rather than copied. The inherited support treatment
is complete on that union: an established occurrence dominates an assumed
occurrence of the same goal, and every other undischarged goal remains assumed.

The specialization result is terminal and inert-only. It retains the exact
family and correspondence judgments, their checked results and portable
authority bindings, the joined support, validation basis, policy, and
quantitative conclusion. It retains neither consumed live capability, a token,
nor an issuer, and its empty consumer map permits no downstream capability.

The historical negative cases remain part of the bounded validation: formation
cannot answer for a family whose evaluated oracle-index bound differs from the
native bound or for the stock modulus-11 bounded-rejection member, and
post-issuance substitutions are refused when the inert or live authority
boundary is consumed.

Qualification is executable for exactly the seven active result constructors.
Each law reconstructs its exact question-bound semantic basis and result
carrier; judgment-backed results also reconstruct their conclusion,
quantitative witness, operation policy, and used-source policy closure.
External assumed results reconstruct their complete opaque result preimage.
Concrete and experiment source profiles likewise admit only their exact active
slot payloads, including the failure partition and strategy/execution join.

## Quantitative boundary

For `k=2`, the four theorem-local operators are:

```text
kappa(n,Q,N)                  = (Q + 1) / N
knowledge-success lower bound = (epsilon - kappa) / q_KS(n)
Lemma-4 transcript bound       = N/(N-1) * (epsilon - kappa)
expected calls to P^a          = Q + 2
```

The theorem-instance substitution `q_KS(n)=1` is explicit. Signed lower bounds
remain signed and are never clamped or admitted as probabilities. Expected
adversary invocations use a resource dimension distinct from random-oracle
query count.

Run the focused gate from the repository root:

```sh
python3 -B evaluation/k3-analysis-closure/run.py --check
```

## Evidence boundary

Passing the gate establishes only constructor behavior, conditional judgments,
one finite specialization, and the listed falsifiers. It does not prove
Schnorr special soundness, the AFK theorem, the assumed all-`n` family source
property, family uniformity or efficiency, the PIR-to-ideal-oracle process
correspondence, SHA-256/ROM correspondence, asymptotic security, QROM security,
production security, or arbitrary protocol-family coverage. The N=8 member is
a research witness, not a production challenge size. Constructor guards model
identity and authority attenuation; they are not a Python security boundary.

The exact-acceptance tests execute only the selected Schnorr fixture with one
`Check`, one `Terminal`, and direct references; they do not execute generic
derived-value or multi-`Check` owner-closure semantics.

The bounded executable also has no checked finite-cover enumerator and no
portable Schnorr pair-to-Witness extractor. The authenticated candidate
algorithm used by the fixture is a generic modulus surface, while complete
extraction remains host-language occurrence code. Consequently finite
evaluation mints no affirmative fixed-extractor universal judgment: the
Schnorr source judgment retains its explicit fixed-extractor correctness
assumption. A future discharge must authenticate a normalization/quotient
cover, streaming representative enumeration, and separate coverage,
congruence, and success-transfer certificates. It would discharge only fixed
correctness, not the independent polynomial-time premise.

Directional-loss import remains a separate negative probe: even a checked Relations
loss occurrence plus matching fixture fact returns `CannotAnswer` until an
owner-issued Relations semantic rule binds the occurrence, bridge, premise,
sort, and formula.
