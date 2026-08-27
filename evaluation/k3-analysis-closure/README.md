# K3-C Analysis closure reference instrument

This package is a bounded executable pressure test for the first Analysis
consumer above K3-B. It imports K3-B exactly and reaches K2 and K1 only through
that import chain. It does not copy their Protocol, Plan, Relations, execution,
or identity semantics into an Analysis-owned shadow model.

The instrument has three deliberately separate layers.

## 1. Global theorem schema

`AFK_V2_THM4_CLASSICAL_ROM` identifies a family-neutral schema for the selected
classical-ROM result from Attema--Fehr--Klooß, ePrint 2021/1377 v2. Its identity
contains closed templates for the source and target properties, both experiment
shapes, required semantic views and maps, side conditions, four local
quantitative operators, the transform program, and the conclusion law.

It contains no Schnorr family identity, native K1/K2/K3 subject, fixed member,
model instantiation, selector, or concrete formula identity. Those coordinates
belong to later layers. Creating or changing a family therefore does not rotate
the global theorem identity.

The authority record independently pins:

- the verified PDF SHA-256
  `93837e2dd7c0e99ef3d06bbb4f235d9ed0dcafb8b96e56d867e7548751e9122c`;
- Definition 4, Definitions 10--11, Lemma 4, the adaptive construction in
  Section 6.3 immediately before Theorem 4, Remark 2 for deterministic
  next-message access and rewinding, Remark 6 for consistent oracle answers
  across reruns, and Theorem 4; and
- SHA-256
  `f449dd9a41b8d4ef6f4ed7794d68398f81d562e31e828252fabd09ca551ae0bc`
  of this instrument's independently encoded selected-statement template.

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

The outer prover experiment may sample a randomized prover's coin tape. For
the theorem-granted extractor interaction, that tape is fixed into one
deterministic next-message strategy before any rerun. Rewinding retains that
same strategy state and coin fixing; it never resamples prover coins between
reruns. This is the Remark 2 condition used by the `Q + 1` argument.

## 3. Pointwise `n0` specialization

Only after family transport may a checked correspondence specialize the result
to the executable `n0=1` member. The selected witness uses the same
prime-order-11 group as the stock K3-B Schnorr fixture but challenge set
`C={0,...,7}`. One uniformly sampled byte and one attempt decode totally and
uniformly because 8 divides 256.

This layer alone owns the concrete K1/K2/K3 subject projection, Fresh and FS
member selectors, models, manifests, fixed public setup, full 20-role map,
four formula correspondences, and exact K2 challenge-query encoding. The role
coordinates are symbolic catalog positions, while separate resolved endpoints
bind every abstract and native role to family or K1/K2/K3 content. The gate
checks both endpoints and the exact twenty-entry shape. The
claim that those paired coordinates have the same denotation remains an
explicit pointwise premise; structural equality is not promoted into semantic
equivalence. The authenticated formula templates are parsed and normalized
independently from the concrete typed expressions, then checked for exact
canonical AST equality after substitution. The AFK
Statement is raw `Y`; `(g,q,p,session,application-domain,namespace,framing)` is
fixed public setup. Its timing flags are derived from the immutable K2 source
objects and exact pre-challenge influence prefix; the remaining family-process
adequacy is still a premise. The table checks the exact K2 carrier for all 121
valid `(Y,A)` pairs and verifies injectivity on that finite domain.

The family oracle index is finite bounded bitstrings. Its authenticated bound
is a closed polynomial `u(n)`; at `n0`, the gate evaluates that polynomial and
requires the result to match the bit length of K1's maximum raw canonical-datum
encoding. This is the raw encoded query index, not the smaller payload capacity
of a nested K1 `BytesValue`. Prover
queries may be outside the
verifier image but remain inside that bound, and all calls, including repeats
and off-image calls, count toward `Q`. The local
`lazy_random_function_trace` helper checks only realized finite-table behavior;
it is not evidence for the adaptive process correspondence.

The stock modulus-11 bounded-rejection fixture is not selected for this
specialization. Concrete SHA-256 execution is never random-oracle evidence.
Programming, rerun, forking, and lazy sampling are theorem-level contracts,
not K2 `ReplayRun` operations.

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
property, family uniformity or efficiency, the K2-to-ideal-oracle process
correspondence, SHA-256/ROM correspondence, asymptotic security, QROM security,
production security, or arbitrary protocol-family coverage. The N=8 member is
a research witness, not a production challenge size. Constructor guards model
identity and authority attenuation; they are not a Python security boundary.

Directional-loss import remains a separate negative probe: even a checked K3-B
loss occurrence plus matching fixture fact returns `CannotAnswer` until an
owner-issued Relations semantic rule binds the occurrence, bridge, premise,
sort, and formula.
