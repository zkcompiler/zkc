# Source Reconstruction

> **Kind:** Temporary primary-source and current-model dossier
> **State:** Complete at the package's assigned depth
> **Authority:** None. Source theorems and implementation behavior do not
> become zkc semantics by citation.

## 1. Frozen source ledger

| Coordinate | Reviewed source | Exact use |
|---|---|---|
| Binary-field zero-knowledge IOPCS | [ePrint 2025/1015](https://eprint.iacr.org/2025/1015.pdf), reviewed PDF SHA-256 `b6db1430de0cd46cba2719b1d1b23ebdc0f0e14a8e546df767fd011800beaeaf` | Construction 4.1, Definitions 3.2--3.3, Theorems 4.2--4.3, Lemma 4.4, and the zero-knowledge BCS discussion |
| Imported binary BaseFold construction | [archived 24 March 2025 revision of ePrint 2024/504](https://eprint.iacr.org/archive/2024/504/1742810970.pdf), reviewed SHA-256 `314700ed34ff6b388885baef392452c4005fe2f91811c9a6345465f58b8dcfa1` | Construction 4.11 and its interleaved Sumcheck/binary-FRI schedule; this is the revision whose numbering matches the importing paper |
| Original KZG PCS | Kate--Zaverucha--Goldberg, [CACR 2010-10 PDF](https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf), dated 1 December 2010, reviewed SHA-256 `15cda500272b20c04fc71dda0db8fb31bbc56b1caee4b02172f5ecf41079ff0d` | Setup, deterministic and randomized commitment variants, single opening, original multipoint opening, and original property statements |
| Modern same-point KZG aggregation | [ePrint 2026/326](https://eprint.iacr.org/2026/326.pdf), reviewed PDF SHA-256 `80ebc4270406ad1022dddbf4d0a1d1d66d4283db9bf43b3280e1488ea422f602` | Section 5.1, Figure 3, and Theorem 8; ordered many-polynomial/same-point aggregation and its theorem boundary |
| Distinct-equation aggregation and Last-Challenge pressure | [ePrint 2024/398](https://eprint.iacr.org/2024/398.pdf), reviewed current PDF SHA-256 `e75620cd44f7ca40275423ae0c38813d9bc3265e53604727174b9601f260acdf` | Final verification-equation aggregation, challenge order, and the adaptive Last-Challenge counterexample |
| Concrete KZG suite comparison | Ethereum consensus specifications, [Deneb polynomial commitments at commit `86fb82b221474cc89387fa6436806507b3849d88`](https://github.com/ethereum/consensus-specs/blob/86fb82b221474cc89387fa6436806507b3849d88/specs/deneb/polynomial-commitments.md), reviewed file SHA-256 `6073466f5b6c824995bca12a223cb95f55537bc0e8f56b939ff849118170ead4` | Concrete encodings and batch verification of independent proofs; not generic KZG authority |

The latest revision of ePrint 2024/504 renumbers the imported construction.
Using the archived matching revision prevents a citation that names the wrong
algorithm. Publication dates and theorem labels are provenance, not proof
applicability.

## 2. Binary-field zero-knowledge IOPCS

### 2.1 Semantic anatomy

The source is an interactive Oracle polynomial commitment scheme in the ideal
vector-Oracle model. Its commitment handle denotes a logical immutable word,
not a Merkle root and not a group element.

For a multilinear polynomial `t` in `ell` variables:

1. setup selects a binary extension field, additive evaluation domains, a
   novel polynomial basis, folding factor `theta`, repetition count `gamma`,
   and `kappa = gamma * 2^theta` queried positions;
2. commitment appends `kappa` random high coefficients to `t`'s `2^ell`
   Lagrange coefficients, zero-completes the remaining upper half needed by
   the declared code dimension, additive-NTT encodes them, and publishes
   logical Oracle `f`;
3. one evaluation session samples an independent padded polynomial and
   publishes logical Oracle `f_prime`;
4. the prover sends the clear value `s_prime = t_prime(r,0)`;
5. only then does the verifier draw `alpha`;
6. the parties use the virtual word
   `f_zero(x) = alpha * f(x) + f_prime(x)` and claim
   `s_zero = alpha * s + s_prime`;
7. Sumcheck and binary-FRI folding are interleaved, sharing their prescribed
   challenges and publishing only the positive folded Oracles;
8. the prover sends the final two coefficients, the verifier checks the final
   Sumcheck relation, and the FRI query phase checks the virtual initial word,
   positive words, and clear final word.

The virtual initial word is verifier-derived query semantics. It has no
independent prover publication and no commitment handle. A literal Core can
query `f` and `f_prime` at the same selected index and combine their answers;
inventing a third commitment would change the protocol.

### 2.2 Three distinct randomness authorities

The source uses three non-interchangeable kinds of private randomness:

| Randomness | Phase and purpose | Public exposure |
|---|---|---|
| high coefficient pads of `f` | commitment time; hide unqueried coefficients within the prescribed query budget | opened only through selected evaluations |
| all-random `f_prime` and `s_prime` | one evaluation session; mask the interleaved Sumcheck/FRI interaction | `f_prime` is an Oracle and `s_prime` is clear |
| per-tag Merkle salts | only in the zero-knowledge BCS compilation | selected salts accompany selected authentication paths |

A single undifferentiated “commitment advice” bucket would erase phase,
dependency, lifetime, and disclosure laws. The selected Core and construction
must keep these roles separately typed.

### 2.3 Setup and source inconsistencies

The reviewed text is operationally reconstructible, but three literal gaps
block unqualified theorem import:

1. Construction 4.1 says to run the imported setup at `ell + 1`, whose
   folding factor is constrained relative to that dimension, and then fixes a
   factor `theta` dividing `ell`. A literal opaque reuse requires a factor
   dividing consecutive dimensions, generally leaving only `theta = 1`.
2. The construction uses basis element `beta_(ell+R+1)`. This requires field
   extension degree at least `ell + R + 2`, one larger than the lower bound
   obtained by naively substituting `ell + 1` into the imported setup prose.
3. Lemma 4.4 needs `2^ell >= kappa`, while Construction 4.1 does not state the
   inequality. The same inequality is needed to fit the random padding inside
   the declared `ell + 1` coefficient space.

The phrase saying that `2^ell + kappa` sampled coefficients define an
`ell + 1`-variate multilinear polynomial also omits the remaining coefficient
values. The source's later argument requires zero completion.

The target therefore selects an explicit source completion for structural
inhabitance:

```text
theta divides ell
field_degree >= ell + R + 2
kappa = gamma * 2^theta <= 2^ell
all unspecified upper-half coefficients are zero
```

This completion is recorded as zkc's source interpretation. It does not repair
or inherit Theorems 4.2--4.3. Their exact applicability remains unanswered
until the source is clarified or an independent proof discharges the completed
parameterization.

### 2.4 Lifecycle and BCS boundary

The zero-knowledge definition and theorem cover one prescribed evaluation
interaction. The `kappa` pads are budgeted against that interaction's maximum
revealed initial-word positions. Reusing the same commitment for additional
evaluation sessions accumulates leakage and is outside the reviewed claim.

The paper also explains why ordinary unsalted BCS is insufficient for its
EPROM zero-knowledge argument: after seeing the witness and opened positions,
a distinguisher can reconstruct the missing padded coefficients and recompute
an unsalted Merkle root. The zero-knowledge BCS variant salts each leaf/tag.
Consequently:

- the ideal IOPCS is not itself a Merkle construction;
- salted and unsalted BCS are different commitment profiles;
- structural execution of either profile proves no zero knowledge; and
- one evaluation session and its query budget must be explicit in the exact
  Analysis subject.

## 3. KZG opening families

### 3.1 Setup and single opening

For a degree-bounded polynomial `f`, KZG setup publishes powers of a hidden
trapdoor. In modern Type-3 notation the minimum single-opening verifier basis
is equivalent to:

```text
([1], [tau], ..., [tau^n]) in G1, and ([1], [tau]) in G2.
```

The exact field, groups, pairing, generators, codecs, supported degree, and
public SRS value are semantic inputs. Ceremony provenance and destruction of
the trapdoor are Evidence/Analysis questions. The trapdoor is never runtime
advice.

For point `z` and explicit claimed value `y`:

```text
C = [f(tau)]
q(X) = (f(X) - y) / (X - z)
W = [q(tau)]
```

The verifier checks the pairing equation relating `(SRS,C,z,y,W)`. The answer
`y` is public claim material. It is not decoded or extracted from `W`.

### 3.2 Original one-polynomial multipoint opening

The original KZG batch construction opens one commitment at a distinct set of
points `B` without a batching challenge:

```text
Z_B(X) = product over b in B of (X-b)
r(X)   = f(X) mod Z_B(X)
q_B(X) = (f(X)-r(X)) / Z_B(X)
W_B    = [q_B(tau)]
```

The remainder or its evaluations remain claim data. A Type-3 verifier needs a
G2 capability for `[Z_B(tau)]`, which the minimal `([1],[tau])` basis does not
provide. The source prints `deg r = |B|`; polynomial division requires
`deg r < |B|`. The target records the mathematical inequality and the source
erratum.

This is not authority for a random-challenge aggregation of several
commitments.

### 3.3 Same-point many-polynomial proof aggregation

For ordered commitments and claims `(C_i,z,y_i)`, ePrint 2026/326 Figure 3
fixes all commitments and claimed values, then draws `v`, then receives one
proof:

```text
h(X) = sum_i v^(i-1) * (f_i(X)-y_i)/(X-z)
W    = [h(tau)]
```

The verifier checks one aggregated pairing equation. Member order, powers of
one challenge, common point, and the position of `v` are construction
semantics. Replacing them with an independent challenge vector is another
profile.

This is a probabilistic claim aggregation, not equality-based evidence
deduplication and not an exact rewrite of completed single-opening proofs.
Theorem 8 is scoped to its exact compiler, PIOP special-soundness premise, and
ARSDH assumption; it is not a structural PIR conclusion.

### 3.4 Verification aggregation of existing proofs

Another construction retains each complete tuple `(C_i,z_i,y_i,W_i)`. Only
after every proof is fixed does it draw a challenge and combine the pairing
equations into one check. Ethereum's Deneb batch verifier is a concrete suite
instance that hashes all tuple inputs before deriving its coefficient.

This saves verifier work. It does not reduce the number of evaluation claims
or opening proofs. If the final coefficient is chosen before every `W_i` is
bound, the Last-Challenge attack can adapt proof elements to a false aggregate
equation. Fresh and Fiat--Shamir interpretations therefore need the full
pre-challenge tuple prefix.

## 4. Pre-package model pressure

The target entering this package had a strong construction shell: exact source
and target Cores, independent target admission, deterministic elaboration,
complete maps, process-local authority, public replay, and one-run receipts. It
also had five incompatible specializations that the durable package revisions
are intended to remove:

1. `LogicalAccess` is an explicitly enumerated finite table with at most
   `2^14` entries; it cannot denote evaluation of a bounded polynomial at an
   arbitrary field point.
2. commitment/opening algorithm ABIs cannot consume an exact public setup or
   SRS instance.
3. `ExtractAnswers(public_opening)` makes proof evidence the universal source
   of an answer.
4. physical sharing is equality deduplication of
   `(class,oracle,index,value,commitment)`, not a general evidence-incidence
   law.
5. one commitment class is tied to one finite source Oracle.

The existing target-only insertion grammar is not itself a V02 blocker: its
full Sumcheck, FRI, `f_prime`, `s_prime`, and `alpha` interaction belongs in
the logical source Core. The BCS construction should insert only commitment
and authentication effects. KZG aggregation challenges, however, belong to
separate opening constructions rather than being disguised as Oracle
authentication effects.

The current implementation's same-point KZG pass is useful correspondence
evidence for ordered claims, a later challenge, one proof, and a reduction. It
does not make KZG10 the correct citation, establish the target abstraction, or
prove the optimization sound.

## 5. Property non-equivalences

Keep at least these Analysis questions distinct:

- algebraic correctness versus evaluation binding;
- commitment binding versus degree or interpolation binding;
- deterministic KZG versus a separately randomized hiding variant;
- original multipoint binding versus same-point aggregation soundness;
- random-linear-combination collision probability versus PCS knowledge;
- ideal-IOPCS zero knowledge versus salted-BCS EPROM zero knowledge; and
- Fresh analysis versus ROM or QROM Fiat--Shamir transport.

No successful pairing check, Merkle path, construction receipt, or source
citation answers any of those questions by itself.
