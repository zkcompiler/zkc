# WHIR Source and Protocol Anatomy

> **Kind:** Temporary source lock and source-language reconstruction
> **State:** Complete
> **Frozen target:** `63c48b22c7aac56d9af3ab460e4ea135a87039f3`
> **Authority:** None. The cited paper is authoritative for the studied
> construction; this page is a research interpretation.

## 1. Source lock and precedence

The primary source is Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, and Eylon
Yogev, [*WHIR: Reed--Solomon Proximity Testing with Super-Fast
Verification*](https://eprint.iacr.org/2024/1586.pdf), dated 2024-11-21. The
retrieved 83-page PDF has SHA-256
`ccacc62cf5529ff95c3cf115cf730b020336f8d95c310c8deb64e3beac30ce61`.

The studied subject is Construction 5.1 and its definitions in Sections
2.1, 2.1.4, 3.1, and 4. Construction 5.1 owns the protocol schedule. Theorem
5.2 owns the source's round-by-round soundness statement and hypotheses. The
paper's informal overview and performance sections are explanatory only when
they disagree in indexing or precision with the construction.

The official [WHIR repository](https://github.com/worldfnd/whir) was inspected
at commit `c274cd5898d31af2cd9be1707a44ccad92c22eaa`, dated
2026-08-26. It is supplemental realization evidence only. Its current verifier
includes commitments, batching, out-of-domain evaluations, random linear
combinations, Sumcheck, proof-of-work, and a final vector, and has evolved
beyond the literal paper schedule. The repository also identifies itself as an
academic prototype. It cannot establish byte compatibility, theorem truth, or
semantic correspondence for this holdout.

The exact retrieval metadata and file digests are in
[the machine-readable source ledger](source-ledger.json).

## 2. What WHIR is

WHIR is an interactive oracle proof of proximity for constrained
Reed--Solomon codes. The studied construction is not by itself:

- a polynomial commitment scheme;
- a noninteractive argument;
- a zero-knowledge proof;
- a claim that a supplied codeword is exactly a codeword rather than close to
  a constrained code; or
- an implementation of a random-oracle compiler.

Those capabilities can be built around or from WHIR, but they have different
objects, assumptions, and conclusions. The holdout therefore models the Fresh
interactive-oracle protocol first.

For a field `F`, smooth evaluation domain `L`, number of multilinear variables
`m`, weight polynomial `w_hat(Z,X)`, and target `sigma`, the source defines the
constrained code informally as:

```text
CRS[F,L,m,w_hat,sigma] = {
  f : L -> F |
  there exists multilinear f_hat(X_1,...,X_m) such that
    f(x) = f_hat(pow(x,m)) for all x in L, and
    sum_{b in {0,1}^m} w_hat(f_hat(b),b) = sigma
}
```

The initial Oracle `f_0` is the IOPP's oracle input. The honest prover also
knows a multilinear extension `f_hat_0` that realizes it. Code parameters and
`sigma_0` are public protocol data. The private extension is honest-prover
material and is not verifier-observable protocol meaning.

## 3. Source-level objects

The following reconstruction intentionally does not use target-owner names.

| Source object | Visibility and lifecycle | Semantic role |
|---|---|---|
| `F` | public static | field and arithmetic |
| `L_i`, `m_i`, `k_i`, repetition parameters | public static | round domains, remaining variables, folding widths, query counts |
| `w_hat_0`, `sigma_0` | public static | initial constrained-code predicate |
| `f_0 : L_0 -> F` | verifier Oracle input; prover knows its extension in the honest case | word being proximity tested |
| `f_hat_0` | private honest-prover input | multilinear extension of `f_0` |
| `h_hat_i,l` | direct prover message | univariate Sumcheck polynomial |
| `alpha_i,l` | fresh verifier field coin | folds one variable and advances Sumcheck |
| `f_i : L_i -> F`, `i > 0` | proof Oracle message | evaluation of the folded multilinear polynomial in an honest run |
| `z_i,0` | fresh verifier field coin, deterministically lifted by `pow` | out-of-domain point |
| `y_i,0` | direct prover field message | claimed out-of-domain evaluation of `f_hat_i` |
| shifted `z_i,j` | fresh verifier samples from the declared shifted domain | grouped reads of the previous folded Oracle |
| `gamma_i` | fresh verifier field coin | combines the OOD and shifted evaluation constraints |
| `f_hat_M` | final direct prover message | fully folded multilinear polynomial |
| final `r_fin` values | fresh verifier samples from the final shifted domain | consistency reads against `f_hat_M` |
| Oracle answers | verifier reads during the decision phase | values used by fold and final-consistency checks |

The prover's messages are adaptive only to the preceding public transcript.
The verifier's Oracle queries occur after all prover publications in the
source decision phase, so the proof cannot adapt to the queried indices or
answers. This ordering must be preserved even if a target evaluator could
compute a needed value earlier.

## 4. Construction 5.1 schedule

Let `M` be the iteration count and let folding width `k_i` remove that many
variables at stage `i`. The complete source schedule is:

1. **Initial Sumcheck.** For each eliminated initial variable, the prover sends
   `h_hat_0,l`; the verifier samples `alpha_0,l`.
2. **Each main-loop iteration `i = 1,...,M-1`.**
   1. The prover publishes folded Oracle `f_i` over `L_i`.
   2. The verifier samples the OOD scalar and derives `z_i,0`.
   3. The prover publishes `y_i,0 = f_hat_i(z_i,0)` in an honest run.
   4. The verifier samples the shifted-domain points and `gamma_i`.
   5. For each variable removed in this stage, the prover publishes
      `h_hat_i,l` and the verifier samples `alpha_i,l`.
3. **Final polynomial.** The prover sends `f_hat_M`.
4. **Final randomness.** The verifier samples the declared final shifted-domain
   points.
5. **Decision.** The verifier queries the necessary grouped locations of the
   initial and proof Oracles and checks all Sumcheck links, fold consistency,
   final polynomial consistency, and the final weighted sum.

At main-loop stage `i`, the weight evolves as:

```text
w_hat_i(Z,X) =
    w_hat_(i-1)(Z, alpha_(i-1), X)
  + Z * sum_j gamma_i^(j+1) * eq(z_i,j, X)
```

The first main-loop Sumcheck equality therefore links the prior claim, the
OOD reply, and shifted Oracle reads. This is not merely a local Boolean check:
it is the public data defining the next constrained-code claim.

The decision rejects unless all of the following hold:

- the initial `h_hat_0,1(0) + h_hat_0,1(1)` equals `sigma_0`;
- every later Sumcheck message has the exact prior-message/challenge link;
- each main-loop first Sumcheck polynomial agrees with the prior folded claim,
  OOD reply, and shifted folded-Oracle values;
- `f_hat_M` agrees with the final folded Oracle at every sampled final point;
  and
- the final weighted Boolean-hypercube sum equals the last Sumcheck
  evaluation.

Any source abort caused by malformed typing, degree, unavailable Oracle
access, or arithmetic noncompletion is distinct from an ordinary false check.
The mathematical presentation assumes well-formed field objects; a semantic
carrier must make those failures explicit.

## 5. Grouped Oracle representation

Reading one folded value ordinarily requires `2^k` evaluations of the previous
Oracle. Section 2.1.4 gives an equivalent alphabet representation. For each
`y` in the `2^k`-power domain, define:

```text
p_y(A_1,...,A_k) = Fold(f,A_1,...,A_k)(y)
```

The Oracle symbol at `y` is the complete `2^k`-coefficient vector of the
multilinear polynomial `p_y`. After sampling the fold point `alpha`, the
verifier reads one symbol and evaluates `p_y(alpha)`. The paper states that
message length and alphabet size are unchanged and that the protocol checks
depend only on this evaluated value.

The constructive holdout uses this representation because it exposes a clean
typed distinction:

- Oracle index type: one member of the exact shifted domain;
- Oracle element type: a fixed coefficient vector of length `2^k`; and
- derived fold value: deterministic evaluation of that vector at the exact
  prior fold challenge.

The representation is not treated as a free codec. Its exact domain,
coefficient ordering, field type, and evaluation algorithm are semantic
dependencies. Changing any one creates a different profile or fails the
correspondence question.

## 6. Claim evolution

The source's state after a completed stage can be reconstructed as a
constrained-code claim:

```text
Claim_i = CRS[F,L_i,m_i,w_hat_i,sigma_i]
```

`Claim_0` is the input claim about `f_0`. A main-loop transition consumes the
prior claim and creates the claim about the newly published `f_i`. The new
weight and target are functions of exactly the preceding prover publications,
fresh coins, and grouped Oracle answers. The final checks discharge the last
claim without creating a new one.

This is an ordered claim transformation, not a statement that each individual
check proves a theorem. It is also not an arbitrary universal transition
algebra: the constrained-code claim and transition recipe remain
WHIR-specific owner-local content.

## 7. Theorem 5.2 is a separate subject

Theorem 5.2 states a round-by-round soundness result for Construction 5.1. Its
premises include, for the exact family of intermediate Reed--Solomon codes:

- an initial word outside the constrained code and a distance range;
- mutual correlated agreement of the proximity generator;
- per-stage distance bounds relative to that agreement bound; and
- list decodability with explicit list sizes.

Its conclusion is a vector of round-local error bounds for folds, OOD steps,
shift steps, and the final sampling step. It is not one unqualified Boolean
`Sound` result.

The paper proves the required mutual-correlated-agreement property in the
unique-decoding regime. It explicitly leaves broader regimes as conjectural or
conditional. Consequently these are distinct Analysis candidates:

```text
WHIR unique-decoding theorem application
WHIR Johnson-style conditional application
WHIR capacity-style conjecture-dependent application
```

They cannot share theorem truth, provenance, or support merely because they
use the same protocol identity. A benchmark parameter choice also cannot
activate the corresponding theorem premises.

## 8. Finite constructive member

The target pressure uses one small exact member whose arithmetic is large
enough to contain a real main-loop Oracle and a scalar terminal:

```text
F       = prime field F_17
L_0     = <2> = [1,2,4,8,16,15,13,9]        // order 8
L_1     = L_0^(2) = [1,4,16,13]              // order 4
m_0     = 2
m_1     = 1
m_2     = 0
M       = 2
k_0     = 1
k_1     = 1
w_hat_0 = Z
sigma_0 = 0
d_star  = 2
d       = 3
shift repetitions = 2                        // OOD plus one shifted point
final repetitions = 2
```

All source inequalities hold: `k_0 + k_1 = m_0`, `|L_0| >= 2^m_0`, and
`|L_1| >= 2^m_1`. A nontrivial honest private polynomial is
`f_hat_0(X_1,X_2) = X_1 - X_2`, whose Boolean-hypercube sum is zero. The
constructive mapping remains symbolic in the sampled field values, so it
represents every well-typed Fresh run of this exact member rather than one
chosen transcript.

The grouped initial Oracle has four indices and two field coefficients per
entry. The grouped proof Oracle has two indices and two coefficients per
entry. The final polynomial is a typed zero-variable multilinear polynomial,
not an unlabelled scalar substitution.

## 9. Source-level nonclaims

This reconstruction does not claim:

- that the finite `F_17` member has useful security;
- that its parameters satisfy Theorem 5.2;
- that the source implementation realizes these exact bytes or schedule;
- that the grouped representation's paper argument has been reproved;
- that a logical Oracle is authenticated;
- that direct Fiat--Shamir over a logical Oracle is sound;
- that WHIR is zero knowledge; or
- that passing the protocol checks establishes a general proximity theorem.

