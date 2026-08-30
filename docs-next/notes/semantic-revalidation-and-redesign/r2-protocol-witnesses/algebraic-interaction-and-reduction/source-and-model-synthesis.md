# Algebraic Interaction and Reduction: Source and Model Synthesis

> **Kind:** Temporary primary-source reconstruction and target-pressure record
> **State:** Complete for the four selected cases at constructive depth
> **Authority:** None. This page records what was reconstructed and where the
> current target fits or fails. It does not define PIR, establish a theorem, or
> claim implementation support.
> **Parent:** [Algebraic Interaction and Reduction](README.md)

## 1. Result in one view

The selected cases do not support one symmetric conclusion.

| Case | Source-faithful result | Pressure on the target |
|---|---|---|
| Classical Sumcheck | A fixed-round, explicit-polynomial form is directly representable as a chain of typed claims and reductions. | No new Core primitive. A realistic symbolic polynomial Oracle and the classical soundness family remain separate open capabilities. |
| Modern layered GKR | A fixed-depth protocol is directly representable as one flat Core containing output compression, Sumcheck chains, line reductions, and a final input check. | No nested runtime protocol. Reusable child elaboration and property composition remain satellites, not Core effects. |
| Duplex-sponge Fiat--Shamir | The state machine fits the portable-algorithm substrate, but the literal transform does not fit the current construction envelope. | A narrow construction alternative is required for runtime instance initialization, transform-owned public proof material, and raw fixed-codec absorption. |
| Packed Boolean GKR | The verifier remains GKR over a hybrid polynomial representation. “RAM operations” are a prover cost measure, not RAM-consistency semantics. | Native use of existing typed algorithms and relation dependencies; input Booleanity must be an explicit premise rather than inferred from output bits. |

The central `InteractiveCore + ChallengeInterpretation` factorization survives.
The only shared semantic obstruction found here is local to the transcript-
construction envelope, not the interactive Core.

## 2. Source ledger

The reconstruction used primary papers for protocol and theorem claims, with
official author expositions and ArkLib used only to disambiguate modern
formulations or compare representation choices.

| Subject | Exact source and reviewed role |
|---|---|
| Sumcheck origin | Lund, Fortnow, Karloff, and Nisan, [*Algebraic Methods for Interactive Proof Systems*](https://lance.fortnow.com/papers/files/ip.pdf), especially Section 3 and Lemma 4. Reviewed PDF SHA-256: `926388d68334bc8cdcd586c70f0b97b2b7e957fe0f360858f4574e91a36622ab`. |
| Modern Sumcheck syntax | Justin Thaler, [*Proofs, Arguments, and Zero-Knowledge*](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf), Chapter 4, Section 4.1. This is an author exposition, not a replacement theorem source. |
| Original GKR | Goldwasser, Kalai, and Rothblum, [*Delegating Computation: Interactive Proofs for Muggles*](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/2008-DelegatingComputation.pdf), Sections 2--3. Reviewed PDF SHA-256: `493bca78c42e05d07469d5adbef39997f14d63bfda0c84abee468df853e163b0`. |
| Modern Boolean-MLE GKR | Justin Thaler, [*A Note on the GKR Protocol*](https://people.cs.georgetown.edu/jthaler/GKRNote.pdf), and Chapters 4.5--4.6 of the book above. These clarify a modern formulation whose trace differs from the original grid-extension presentation. |
| Duplex Fiat--Shamir | Chiesa and Orrù, [*A Fiat--Shamir Transformation From Duplex Sponges*](https://eprint.iacr.org/2025/536), latest reviewed revision dated 27 March 2026; Definitions 4.1--4.2 and Construction 4.3 are the construction anchor. Reviewed PDF SHA-256: `fca7ba09ebe59141c3c041ac660b4e3e161fdab8a709aee67e236db8d8da3a35`. |
| Packed Boolean GKR | Hu et al., [*GKR for Boolean Circuits with Sub-linear RAM Operations*](https://eprint.iacr.org/2025/717), revision dated 3 May 2025; Sections 2.2, 3, and 4. Reviewed PDF SHA-256: `3ae9fe7d6bc23607cb5ab9deb72485804f29d1c59e48a311590310fdaf387d23`. |
| Typed reduction comparison | ArkLib, [Oracle Reductions blueprint](https://verified-zkevm.github.io/ArkLib/blueprint/chap-oracle_reductions.html) and its Sumcheck sources at commit [`fad5cbf`](https://github.com/Verified-zkEVM/ArkLib/tree/fad5cbf808774838924dc8273715724c6a6caa1f). This is design evidence; unfinished proof obligations prevent treating the repository as theorem authority. |
| Operational transcript comparison | [CFRG Fiat--Shamir draft 03](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-fiat-shamir-03), dated 17 August 2026. Its parsing and session guidance are useful Interface/OIR inputs, but its prefix-XOF adapter is not the duplex construction. |

## 3. Classical Sumcheck

Let `P : F^v -> F`, let `B` be the summation set, and let `d_i` bound
the individual degree in variable `X_i`. The clean statement form is

```text
R_0(P,H) : H = sum_{b in B^v} P(b).
```

At the beginning of round `i`, the residual claim is

```text
R_{i-1}(P, r_<i, t_{i-1}) :
  t_{i-1} = sum_{b_i,...,b_v in B}
              P(r_1,...,r_{i-1},b_i,...,b_v).
```

The source chronology is exact:

1. the prover fixes a degree-bounded univariate polynomial `p_i`;
2. the verifier checks the degree and
   `sum_{a in B} p_i(a) = t_{i-1}`;
3. only after those checks, the verifier samples fresh `r_i`;
4. the next target becomes `t_i = p_i(r_i)`; and
5. the residual claim is `R_i(P,r_<=i,t_i)`.

After round `v`, the residual is `P(r_1,...,r_v) = t_v`. A standalone
verifier checks it directly. An oracle-reduction form exports it to a later
evaluation or opening protocol. These are different terminal contracts; local
round checks do not themselves prove the exported residual.

For independent uniform field challenges and valid individual-degree bounds,
the classical statistical soundness error is bounded by
`sum_i d_i / |F|`. The proof uses the fact that the prover polynomial is fixed
before its challenge. It does not yield knowledge extraction, zero knowledge,
Fiat--Shamir security, or commitment security.

### 3.1 Target correspondence

The current target has an exact home for every structural object:

| Source object | Target owner |
|---|---|
| `(P,H)` and static parameters | Statement and PublicParameter bindings |
| `p_i` | typed `ProverMessage` occurrence |
| degree and recurrence tests | exact `CheckDecl` algorithms and guarded Reject terminals |
| `r_i` | one typed Challenge occurrence with a fresh public-coin law |
| `R_{i-1} -> R_i` | linear `ClaimDecl` and `ReductionDecl` chain |
| polynomial, challenge, and target used by the transition | Relations recipe and reduction-parameter bindings |
| adaptive honest or malicious prover | prefix-restricted strategy relation |
| statistical theorem and error accumulation | a future Analysis profile |

`required_publications` and `next_challenge` give the correct strong-
Fiat--Shamir ordering: `p_i` must be fixed before `r_i`. The reduction output
is formed only on the path where the local check did not select Reject.

The fixed explicit-polynomial form is therefore native. A generic evaluation-
oracle form is not: the current standard Oracle is a bounded canonical finite
map, while a realistic polynomial query domain `F^v` is not enumerable within
that bound. This package does not turn the explicit polynomial into a fake
finite Oracle or treat a commitment as the same subject.

### 3.2 ArkLib lesson and limit

ArkLib independently validates the useful decomposition

```text
SendClaim -> CheckClaim -> RandomQuery -> ReduceClaim
```

and makes the residual relation first-class. Its dependent contexts and
sequential composition machinery are valuable formal-design evidence. They
also carry substantial lifting and restoration proof obligations, some still
unfinished at the reviewed commit. zkc should retain its finite generated
Core plus explicit Relations and Analysis bindings rather than copying that
context machinery into runtime semantics.

## 4. Layered GKR

For the modern Boolean-hypercube presentation, let `W_i` be the gate-value
table at layer `i` and `~W_i` its multilinear extension. The persistent layer
claim is

```text
C_i(a_i,v_i) : ~W_i(a_i) = v_i.
```

A multi-output protocol can either receive a claimed output table as its first
prover publication or take that table as part of the supplied public claim.
The selected encoding uses the latter front-end: `D` is one Statement value,
is never republished, and is fixed before the output-compression point. Each
layer then performs:

```text
one layer-i evaluation claim
          |
          v
  Sumcheck over the layer identity
          |
          v
two child-layer evaluations at b* and c*
          |
          v
  line polynomial q(t) = ~W_{i+1}(b* + t(c*-b*))
          |
          v
fresh line challenge tau_i
          |
          v
one layer-(i+1) evaluation claim
```

The line polynomial is fixed and its endpoint/final-kernel checks pass before
`tau_i` is sampled. At the input layer, the verifier evaluates the public input
extension and checks the final residual claim.

The original GKR paper and the modern Boolean-MLE presentation must not share
a Core merely because both are called GKR. The original uses a grid extension,
an additional parent-label variable, and a different Sumcheck kernel. The
modern form changes message, challenge, degree, and wiring coordinates.

### 4.1 Target correspondence

A fixed-depth instance is one finite flat `InteractiveCore`:

```text
statement claim
  -> output-compression reduction
  -> per-layer Sumcheck reductions
  -> per-layer line reduction
  -> final public-input check
```

Sumcheck and the line reduction remain distinct `ReductionDecl` occurrences.
Relations assigns each partial-sum and layer-evaluation claim its exact
instance recipe and transform. Analysis, not Relations, owns the probabilistic
soundness composition.

No runtime child Core is necessary. Source structure is preserved by the
flat occurrence, claim, and reduction coordinates. A future authoring tool may
instantiate a reusable Sumcheck template, but it must elaborate to the same
flat Core; any retained template-to-Core map is a checked authoring satellite,
not an execution handle or an extra Core identity field.

The source also requires explicit wiring authority. A uniform public wiring-
evaluation algorithm, an admitted preprocessing artifact, or another exact
capability must be selected. “The verifier can evaluate the wiring predicate”
is not an ambient privilege.

## 5. Duplex-sponge Fiat--Shamir

The paper's state is `(s,i_A,i_S)`, where `s` has a rate and capacity segment.
Absorption overwrites the rate segment, and squeezing mutates the same state.
The edge cases are semantic:

- an empty absorb resets the squeeze index and is not always a no-op;
- a zero-length squeeze leaves the state unchanged;
- consecutive squeezes continue one stream;
- a later absorb resets that stream and overwrites from rate position zero;
- filling the final rate cell does not eagerly permute; and
- exact permutation-call boundaries follow actual rate crossings.

Construction 4.3 initializes from the runtime instance through `Start_h(x)`,
samples one salt `tau`, absorbs it, then for each round absorbs an injective
fixed-length encoding of the prover message, squeezes symbols, and decodes the
verifier message. The abstract proof is `(tau,alpha_1,...,alpha_k)`; verifier
coins are reconstructed and are not serialized.

The paper deliberately does not absorb labels or message lengths. Its parsing
discipline comes from the fixed round structure and codec lengths. Its
classical security theorems additionally read capacity, rate, salt length,
codec bias, efficient encoder inversion where needed, state-restoration
security, and adversarial access to the permutation and its inverse. Ordinary
sponge indifferentiability is explicitly insufficient. QROM and UC remain
open in the reviewed revision.

### 5.1 Exact current obstruction

The current FS target is stateful, so it is not merely a prefix-hash model.
Its portable algorithms can implement the duplex state transition. Literal
Construction 4.3 nevertheless fails at the envelope:

1. initialization starts from a static state and mandatory zkc headers rather
   than `Start_h(runtime_instance)`;
2. the challenge interpretation has no prover-supplied public proof material
   for `tau`;
3. every publication uses canonical typed zkc frames rather than the paper's
   raw fixed-codec image; and
4. every squeeze uses a zkc namespace and optional retry, while the source
   construction uses a namespace-free one-shot total decoder.

Putting `tau` in SessionContext or adding it as a Core message is not a fix.
Both change the Fresh source interaction for transform-only material and break
the literal same-Core relation. Likewise, calling the current canonical-framed
construction “DSFS” would attach the paper theorem to a different transcript.

The correct boundary is a closed, separately identified transcript
construction alternative with one Fiat--Shamir-specific public-material input.
The canonical-framed construction remains unchanged and default. The selected
shape is detailed in the candidate decision.

## 6. Packed Boolean GKR and the word-RAM claim

The recent construction retains a finite data-parallel layered Boolean
circuit. It replaces the `log B` multilinear copy-index variables with one
degree-`B-1` Lagrange variable over `B` distinct points. In the optimized
Sumcheck, the prover sends the degree-`3(B-1)` polynomial for that variable
first; the verifier checks its domain sum, samples `b'`, and continues ordinary
multivariate Sumcheck over within-copy gate indices.

The protocol packs the `B` Boolean values across copies into one machine word
and precomputes a table to accelerate the prover. Those are Plan and
realization choices. The source contains no address trace, load/store
semantics, memory-consistency permutation, or RAM-program relation. Its word-
RAM model is an Analysis cost model in which field operations span multiple
words; it is not a new verifier-observable effect.

The correct ownership split is:

| Material | Owner |
|---|---|
| `B`, interpolation domain, degree bounds, message/check/challenge order | Core and exact existing algorithm/module declarations |
| Boolean-circuit satisfaction and hybrid polynomial correspondence | Relations and algebra modules |
| packed words, precomputation table, accumulator algorithm | Prover Plan |
| cache, vector instructions, concrete memory layout | Realization/Evidence |
| asymptotic word-RAM proposition and soundness | Analysis |
| optional binary-polynomial commitment | a later Oracle/commitment construction |

One theorem argument in the paper claims that binary outputs force binary
inputs. That is false without an additional premise: for a non-binary field
element `a`, `AND(a,0)=0` is binary. Input Booleanity must therefore be part of
the source relation, an explicit bit constraint, or an exact input/commitment
grounding. It cannot be inferred from output Booleanity plus GKR consistency.

## 7. Cross-case deductions

The four reconstructions support five design deductions:

1. **Claims are residual obligations, not Boolean checks.** Sumcheck and GKR
   need a typed claim chain even though every transition also has local checks.
2. **Flat execution and reusable authorship are different.** GKR needs the
   former now; a checked elaboration map may serve the latter later without
   adding nested runtime authority.
3. **Transcript construction is not one universal framing law.** Strong typed
   frames are a valuable profile, but literal duplex constructions require a
   different exact profile rather than a global weakening or an opaque action
   map.
4. **Verifier semantics and prover cost models must not merge.** Packed-word
   techniques do not create RAM semantics, and two prover Plans can share one
   Core.
5. **Structural representation and theorem applicability remain separate.**
   Every positive trace here can exist without establishing Sumcheck/GKR
   soundness, Fresh-to-FS transport, DSFS security, zero knowledge, or a PCS
   theorem.
