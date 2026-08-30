# LogUp-GKR and Logup* Lookup Variants

> **Portfolio case:** recent lookup-organization variants
> **Depth:** T1 boundary analysis
> **Result:** `Native` within finite v0 limits
> **Authority:** Source-grounded temporary research, not a complete transcript,
> implementation, or security proof

## 1. Source lock

The selected variants are:

1. Papini and Haböck,
   [Improving Logarithmic Derivative Lookups Using GKR](https://eprint.iacr.org/2023/1284),
   latest content revision `20230918:134233`, PDF SHA-256
   `3cdb575a514425592407c4e31af49f9d4410d2a65fc10d8fae9c289d2c49352e`;
   and
2. Soukhanov, [Logup*](https://eprint.iacr.org/2025/946), revision
   `20250524:035344`, PDF SHA-256
   `91c721d63646c07b3b44a6855ee9ad481ed75c061e005c9e87b901bb7888c098`.

Plookup and the later characteristic-bound analysis serve as baselines. T1 is
the correct stopping point: the reviewed sources intentionally leave parts of
the transcript, inter-branch schedule, and final PCS packaging unspecified. A
T2 record would invent those choices rather than recover them.

## 2. Delta from Plookup

Plookup proves membership by sorting the witness/table concatenation, committing
two helper columns, sampling challenges, and checking a grand-product
polynomial.

LogUp-GKR instead:

- publishes table values, witness columns, and one table-sized multiplicity
  column;
- samples a logarithmic-derivative challenge;
- proves a rational identity through a projective-coordinate GKR tree;
- reduces to evaluations at one random multilinear point; and
- optionally converts those claims to a univariate PCS through a challenge-
  dependent Lagrange oracle.

It removes sorting and the Plookup grand product, but introduces multi-round
GKR/Sumcheck interaction.

Logup* changes indexed lookup organization again. For index map
`I:[n]->[m]`, table `T:[m]->F`, and pullback `P[i]=T[I[i]]`, it avoids a
relation-sized large-field commitment to `I^*T`. After an upstream evaluation
point `r`, the prover constructs the table-sized pushforward:

```text
Y = I_* eq_r
```

and splits the proof into:

1. an inner-product Sumcheck establishing `<T,Y> = e`; and
2. a logarithmic-derivative/GKR branch establishing that `Y` is the correct
   pushforward.

## 3. Representative LogUp-GKR graph

```text
lookup relation: every W_i entry belongs to T
        |
        v
Plan derives multiplicity advice m
        |
        v
publish or commit T, W_i, m
        |
        v
sample alpha
        |
        v
publish first projective numerator/denominator values
        |
        v
sample fold point
        |
        v
for each later GKR layer:
  sample batching challenge
  Sumcheck messages and round challenges
  publish child evaluations
  sample branch-fold challenge
        |
        v
final T, m, W_i evaluation claims
        |
        v
optional univariate conversion:
  sample combination challenge
  publish challenge-dependent c_r oracle
  periodic checks and univariate Sumcheck
        |
        v
exact PCS claims/evidence/checks
        |
        v
Accept / Reject
```

The verifier must check both the top numerator identity and the nonzero
accumulated denominator. The source's GKR and Sumcheck structure is one finite
flat Core for any selected depth; it is not a runtime child-Protocol tree.

## 4. Representative Logup* graph

```text
indexed relation:
  I:[n]->[m], T:[m]->F, P[i]=T[I[i]]
        |
        v
publish/commit I and T
        |
        v
upstream point r and claim e=P(r)
        |
        v
Plan derives and publishes Y=I_*eq_r
        |
        +-------------------------------+
        |                               |
        v                               v
inner-product branch              pushforward branch
<T,Y>=e Sumcheck                  challenge c after C_Y
 -> T/Y claims                    fractional GKR identity
                                  -> I/Y/eq_r claims
        |                               |
        +---------------+---------------+
                        v
      merge only identical semantic claim coordinates
                        |
                        v
      exact PCS openings and verifier checks
```

The source does not fix one total interleaving between the branches or one
final PCS batching package. A future profile must make both choices explicit;
the shared model need not guess them.

## 5. Ownership

| Concern | Owner |
|---|---|
| lookup membership, indexed pullback, table/index meaning | Relations |
| exact messages, challenges, reductions, checks, and terminal | PIR Core |
| multiplicity, `Y`, `c_r`, projective layers, honest generation | ProverPlan |
| exact commitment/query/answer/evidence verification | existing commitment-opening profiles |
| proof material to public commitment equality | Relations commitment grounding |
| lookup reduction soundness, GKR/Sumcheck composition, poles, field premises, PCS security, challenge sharing, FS, ZK/knowledge | Analysis |

Multiplicity, `Y`, and `c_r` are proof-system advice, not relation witness.
Changing the lookup argument must not change the application relation.
Challenge-dependent `Y` and `c_r` are ordinary Plan-derived
`ProverOracle` publications; their recipes cannot read `r` before it exists.

## 6. Shared challenge and composition

Logup* uses one evaluation point across two reductions.

- If the point is sampled in the same Core, both consumers cite one exact
  Challenge occurrence under `Shared(challenge-sharing-contract)`.
- If it is imported from an enclosing reduction, it is an exact phase input or
  public claim coordinate and needs no local shared-challenge declaration.

The structural sharing contract proves only that the consumers use the same
occurrence. Analysis must prove that reuse is sound. Equal sampled values or
two independently named challenges do not substitute for one occurrence.

The two proof branches remain logical reductions in one flat Core. Their
source-level modularity does not justify multiple transcripts or terminal
authorities.

## 7. Pole, field, and overflow premises

For ordinary LogUp-GKR, Analysis retains:

- field characteristic greater than two;
- distinct table values or an explicit deduplication transform;
- the multiplicity bound preventing cancellation modulo the characteristic;
- explicit denominator/pole behavior and the top nonzero-denominator check;
- Boolean-domain and packing premises;
- GKR and Sumcheck error terms; and
- for univariate conversion, the exact subgroup, degree, and query-coordinate
  restrictions.

These are not PIR admission or relation-satisfaction facts.

For Logup*, the index map `I` must **not** be injective. It is intentionally
many-to-one; its fibers are what the pushforward sums over. The actual
requirements are:

- every `I[i]` lies in `[m]`;
- distinct table-index labels have distinct field encodings;
- the pole challenge has an explicit abort/rejection convention;
- shared-point composition is sound; and
- the inner-product, fractional-GKR, and PCS error terms compose.

`Y` is a field-linear weighted pushforward rather than an integer count vector,
so the ordinary count-overflow premise changes. Index encoding and pole
premises do not disappear.

## 8. Recovered source defect

The Logup* PDF says in one protocol summary that the prover commits to
`I,T,I_*T`. That expression is ill-typed under the paper's own pushforward
definition: `I_*` consumes an `n`-sized source while `T` is table-sized.

The surrounding construction, rational identity, and later claims all use
`I_*eq_r`, and that is the only reading that preserves the stated goal of
avoiding a size-`n` large-field commitment. The target records this as a
source-internal inconsistency and uses `I_*eq_r`; it does not claim an author-
issued erratum.

## 9. Negative pressure

LogUp-GKR must expose or reject:

1. sampling the first challenge before table, witness, and multiplicity are
   fixed;
2. omitting any GKR publication from the next FS prefix;
3. sampling a batching or branch-fold challenge before its inputs;
4. omitting the nonzero denominator check;
5. treating the rational identity as relation satisfaction;
6. treating `c_r` as a static verifier constant or publishing it before `r`;
7. hiding multilinear-to-univariate conversion in an opaque PCS callback; or
8. replacing the finite GKR graph with an opaque runtime subprotocol.

Logup* must expose or reject:

1. implementing the source's `I_*T` typo;
2. requiring `I` itself to be injective;
3. producing `Y` before `r` or after the later pole challenge;
4. making `Y` static relation material;
5. reintroducing a commitment to `I^*T`;
6. sampling the pole challenge before committing `Y`;
7. merging claims because runtime values happen to be equal;
8. generic batching across incompatible schemes, points, or value shapes;
9. inferring overflow immunity or soundness from structural execution; or
10. leaving the upstream evaluation claim `e` ungrounded.

## 10. Classification and nonclaims

Both variants are `Native` at T1. They need owner-local relation languages,
reduction contracts, Plan recipes, exact commitment-profile instances, and
future Analysis rules, but no new shared root, challenge mechanism, commitment
abstraction, or runtime composition primitive.

The result establishes no formal security proof, zero knowledge, extraction,
Fiat--Shamir/ROM/QROM result, concrete PCS implementation, exact Logup*
transcript, arbitrary-size support, performance claim, or repository
implementation support. The current LogUp fixture and claim-routing probe stop
far before fractional GKR or Logup* and remain bounded diagnostic evidence.
