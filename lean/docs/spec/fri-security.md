# FRI security at the ideal interpretation

This page specifies the independent model of the verifier of
[`fri::LowDegree`](../../../libraries/protocols/polynomial/fri/lib.zkc), its completeness on the
tested code, its round-by-round soundness theorem, its Fiat–Shamir transfer
with one query-block site and the same verifier with words committed by Merkle
trees. The model is a transcription of the library verifier, related line by
line to the source; it makes no claim about the compiled library, its proof
Entry or native execution. Before [committed words](#committed-words) it reads
every commitment as the vector it commits to. The modules are
`ZkcSecurity.ArkLib.Fri.*`, `ZkcSecurity.Examples.FriFiatShamir` and
`ZkcSecurity.Examples.CommittedFri` in the
[security integration](../../integrations/arklib/README.md).

## Subject

`LowDegree<C, LogSize, TerminalLog, Rounds, Queries>` tests one word of
`2^LogSize` evaluations on the coset `shift * <g>` in logical order
`x_i = shift * g^i` ([two-adic cosets](../../../docs/spec/domains/polynomials.md#two-adic-cosets-and-folding)).
Write `n = LogSize`, `t = TerminalLog`, `R = Rounds` and `s = Queries`; the library
requires `1 ≤ R`, `t + R + 1 ≤ n` and `1 ≤ s`. The tested code is the
Reed–Solomon code of degree below `2^(t + R)` on the initial coset, at rate
`ρ = 2^(t + R) / 2^n`.

The model is a public-coin interactive oracle proof:

1. The prover commits the initial word.
2. For each of the `R` folding rounds the verifier draws a uniform field
   challenge `beta`; the prover then commits the next word of half the size, or,
   after the last round, sends the final coefficient vector.
3. The verifier checks that at most `2^t` coefficients were sent.
4. The verifier draws `s` positions, uniform in `[0, 2^n)`.
5. For each position it checks every round's fold and the final polynomial.

At the ideal interpretation, `oracle::check(root, 1, size, position, row, path)`
holds exactly when `row` is the one-element row at `position` of the committed
vector and that vector has length `size`. A prover that commits a vector of
another length, or opens another row, is rejected at its first opening, so the
model's words have their expected sizes and the verifier reads committed values.

## Source correspondence

Line numbers refer to `libraries/protocols/polynomial/fri/lib.zkc`. Each model definition is in
`ZkcSecurity.ArkLib.Fri.Protocol` unless the table names another module.

| Source (lines) | Model | Relation to ArkLib |
|---|---|---|
| `coset::point(shift, size, position)` | `point roots shift m position = shift * roots m ^ position` (`Domain`) | `cosetDomain` is the coset as an ArkLib `SmoothCosetFftDomain` in the same natural order (`cosetDomain_apply`) |
| `TwoAdicField(F)` roots | a family `roots m` of primitive `2^m`-th roots with `roots (m + 1)^2 = roots m` (`Compatible`) | `compatible_powers`: `m ↦ ω ^ 2 ^ (n - m)`, the installed convention, is compatible |
| `query_shift * query_shift` and `halve(size)` after a fold (166–171) | the next round uses `shift * shift` and half the size | ArkLib's first subdomain is that coset (`subdomain_one_apply`, `subdomain_point`) |
| `remainder(position, half)` (145–146, 167–168) | `lowHalf` | ArkLib's fold index map `sqFoldMapGen` (`lowHalf_eq`) |
| positions `low` and `low + half` (147–148, 153–156) | `lowIndex`, `highIndex` | both square to the same subdomain point (`pair_sq`) |
| `fold_value`, `folded_value` (42–54, 164–165) | `foldValue`, `foldedValue` | equal to ArkLib's binary fold `foldWord D word 1 beta` at the paired point (`foldedValue_eq`, from `foldWord_k_1_of_sq_roots`) |
| `select_half` (61–63, 157–159) | `selectHalf` | reads the word at the query position (`selectHalf_eq`) |
| `chain` (55–57, 160–161) | `chain`; from the second round the selected value must equal the previous fold | together with the next round, `FoldTrace.accepting` (`walk_iff`, `walk_first_iff`) |
| `terminal` (34–39, 173–175) | `terminal`, `evaluate` | the last fold equals the final polynomial's evaluation, the final step of `FoldTrace.accepting` |
| `bounded` (30–33, 120–121) | `bounded`: fewer than `2^t + 1` coefficients | places the final word in its code, `FoldTrace.FinalInCode` (`finalInCode_of_bounded`) |
| query loop (133–176) | `walk`, `verify` | `verify` accepts exactly when the coefficient bound holds and every position is accepting (`verify_iff`); then the trace accepts in ArkLib's sense (`accepts_of_verify`) |
| `keep_first` and `valuesV` (162–163) | `firstValue`, `values` | the initial word at each position (`firstValue_eq`); an output, not an acceptance check |
| commit loop (104–117), final message (118–119) | `Layers`, `Strategy`, `commit` | `toTrace` builds ArkLib's `FoldTrace` from committed words, challenges and the final polynomial's evaluations |
| position draws (125–132) | `drawPositions`, `positionAt` | uniform on vectors (`evalDist_drawPositions`); every event has its probability under the uniform draw of all `s` positions together (`prEvent_positions`) |
| `configured`, `shape` (64–75, 93–99) | static `R` and `s`; nonzero shift and a primitive root for `cosetDomain` | premises of the theorems |

`coset::fold` (115) and `interpolate_coefficients` (118) are the honest
prover's operations. `Honest` states that each committed word after the first,
and the final polynomial's evaluations, are ArkLib's fold of the previous word,
which is the library's fold formula by `foldedValue_eq`. `verify_of_honest`
shows that the verifier accepts every position of such layers when the final
coefficients satisfy the bound.

## Completeness

The honest prover (`honest`, in `ZkcSecurity.ArkLib.Fri.Completeness`) commits
ArkLib's fold of the current word with each challenge and, after the last fold,
sends the coefficients of the folded word's interpolant. On a codeword of degree
below `2^(t + R)`, each fold is a codeword of half the degree on the next coset
(ArkLib's `foldWord_mem_code_of_mem_code`), so the last fold evaluates a
polynomial of degree below `2^t`. `honest_commit` shows that every run of the
honest commit phase gives honestly folded layers whose final coefficients meet
the bound, and `honest_accepted` that the verifier accepts every query position:
the test is perfectly complete on its code, for every folding challenge and every
position. The verifier reads the final message only through its length and the
polynomial it defines, so any list of at most `2^t` coefficients of that
polynomial is accepted alike.

## Certificate

The certificate has the persistent bad-event form of ArkLib pull request #992,
which follows Garreta–Mohnblatt–Wagner, *A Simplified Round-by-round Soundness
Proof of FRI* (ePrint 2025/1993). Fix a tradeoff radius `θ` and a distance `δ`.
A state is doomed when the committed initial word has relative distance at least
`δ` from the code (`Far`) and no earlier challenge has escaped. Prover messages
leave this state unchanged, because escape events depend only on the word
committed before a challenge and on that challenge.

| Site | Challenge | Escape event | Error |
|---|---|---|---|
| Folding round `r` | one uniform field element | the word committed before it loses the ability to lift large agreement sets through the fold (`FoldingAgreementFailure`) | `foldError r`, for every committed word (`FoldingEscapes`) |
| Query block | one compound challenge of all `s` positions | acceptance of a safe trace with a far initial word | `(1 - min θ δ)^s` (`FoldTrace.query_soundness`) |

`RoundByRound` states these obligations. The folding errors come from the
proximity premise `FoldingProximity`: mutual correlated agreement of the line
generator (the powers generator of degree one) on every folded Reed–Solomon code
at radius `θ`. It is a named hypothesis; `foldingEscapes_of_proximity` turns it
into the folding obligations with ArkLib's `foldingAgreementFailure_prob_le_powers`.
`query_escape_le_of_accepts` gives the query obligation for any verifier whose
acceptance implies ArkLib's acceptance at positions related to natural-order
indices by an equivalence.

`RoundByRound.soundness` bounds acceptance with a far committed initial word,
for every adaptive prover strategy and any private randomness, by
`∑ r < R, foldError r + (1 - min θ δ)^s`. `soundness` composes it with the
proximity premise. The bound uses the source's sequential position draws.

## Unique-decoding instance

`foldingProximity_uniqueDecoding` discharges the proximity premise with ArkLib's
proved results for every positive `θ` at most the relative unique-decoding radius
`(1 - ρ) / 2`, which is the same for every folded code because binary folding
keeps the rate: the line generator's error on a Reed–Solomon code of block length
`N` is at most `N / |F|` (`rs_mcaError_le_of_le_relUDR`, after Ben-Sasson, Carmon,
Ishai, Kopparty and Saraf, *Proximity Gaps for Reed–Solomon Codes*). Folding
round `r` therefore contributes `2^(n - r - 1) / |F|` (`uniqueDecodingError`).

`soundness_uniqueDecoding` states the resulting bound and
`soundness_uniqueDecoding_le` its closed form `2^n / |F| + (1 - min θ δ)^s`. At
the parameters of `examples/projects/fri` and the authored STARK tables
(`n = 5`, `t = 0`, `R = 3`, `s = 8`, rate `1/4`, `θ = 3/8`), on the coset of any
primitive 32nd root of unity, the interactive acceptance bound, with commitments read as the committed words,
is `(16 + 8 + 4) / |F| + (1 - min (3/8) δ)^8` with no remaining premise
(`example_bound` in `TestsSecurity.FriSecurity`).

## Cube-root radius instance

`ZkcSecurity.ArkLib.Fri.GeneralizedJohnson` discharges the folding obligations
up to the cube-root proximity radius `1 - (ρ + η)^(1/3)`, strictly inside the
Johnson radius `1 - ρ^(1/2)`, with the powers-generator bound of Bordage,
Chiesa, Guan and Manzur, *All Polynomial Generators Preserve Distance with
Mutual Correlated Agreement*, in ArkLib's form for one FRI folding round, which
ArkLib names after the generalized Johnson bound
(`foldingAgreementFailure_prob_le_generalizedJohnson`). For a binary fold the
generator is the line, and the bound holds at every radius
`θ ≤ 1 - (1 - δmin + η)^(1/3)`, where `δmin` is the relative minimum distance of
the code after the fold and `0 < η < δmin` a slack. A Reed–Solomon code of
degree below `d` on `2^m` points has `δmin = (2^m - d + 1) / 2^m`, more than
`1 - ρ` (`relativeDistance`), and folding keeps the rate, so every
`θ ≤ 1 - (ρ + η)^(1/3)` with `0 < η < 1 - ρ` serves every round
(`foldingEscapes_generalizedJohnson`). Folding round `r` folds onto
`2^(n - r - 1)` points; with `x = 1 - δmin + η` for the code there, it errs at
most `2^(n - r - 1) (1 - x^(1/2)) / (η |F|) + max (2 / (η (x^(1/3) - x^(1/2)) |F|)) (6 / (η |F|))`
(`johnsonError`).

`soundness_generalizedJohnson` and `afterCommit_doomed_generalizedJohnson` state
the round-by-round bound and the residual certificate with these errors. As `η`
tends to zero, the radius exceeds the unique-decoding radius exactly when
`ρ < ((√5 - 1) / 2)^3 ≈ 0.236`, so at rates up to `1/8`. At rate `1/8`
(`n = 6`, `t = 0`, `R = 3`, `s = 8`) with `η = 1/100`, the radius `12/25` exceeds
the unique-decoding radius `7/16`, with no remaining premise (`lowRate_bound` in
`TestsSecurity.FriSecurity`).

## Certificate over verifier residuals

`ZkcSecurity.ArkLib.Fri.Certificate` states the certificate over the residual
processes of the verifier after the first commitment, the form a Fiat–Shamir
transfer consumes. The verifier is a process over four operations
(`Operation`): a folding challenge, one field element; a committed word, read as
the vector it commits to; the final coefficient vector; and the query block, all
`s` positions together in `Fin s → Fin (2^n)`. `afterCommit word` is the
verifier once the initial word is committed, and `foldPhase`, `finalPhase` and
`queryPhase` are its residuals.

The doomed residuals (`Doomed`) are those reached while the committed initial
word is at relative distance at least `δ` from the code and no folding challenge
has escaped. Each records what every completion of its transcript satisfies: the
initial word is far, and the completed rounds are safe exactly when the
remaining rounds are. `certificate` proves the local obligation (`Step`) of every
doomed residual, with every query answered by a uniform value of its sort:

| Residual | Obligation |
|---|---|
| a result | it rejects |
| a committed word or the final coefficients | every message keeps the residual doomed |
| the folding challenge of round `r` | the residual leaves the set with probability at most `foldError r` |
| the query block | the residual leaves the set with probability at most `(1 - min θ δ)^s` |

`afterCommit_doomed` places the verifier after a far initial word in the set,
given the folding obligations; `afterCommit_doomed_of_proximity` takes them from
the proximity premise and `afterCommit_doomed_uniqueDecoding` from the
unique-decoding instance, in which round `r` errs at most `2^(n - r - 1) / |F|`.

A Fiat–Shamir transfer takes the initial word as the statement and its
commitment as the initial history, which determines the statement. Each query
site answers with its own decoding of a transcript output, and the errors above
are under the uniform law of each site's sort: the query block's error
`(1 - min θ δ)^s` is a bound under the uniform law of `Fin s → Fin (2^n)`. A
decoding whose law is dominated by the uniform law with a factor multiplies its
site's error by that factor.

## Fiat–Shamir transfer

`ZkcSecurity.Examples.FriFiatShamir` presents the verifier after the first
commitment through a [typed transcript interface](fiat-shamir-security.md#typed-query-sites)
(`absorb`) and turns the certificate above into a typed certificate
(`typedCertificate`):

- Events: committed words and the final coefficients, read in the clear (ideal
  commitments); the occurrence of each folding challenge, answered by one field
  element and decoded exactly; and the occurrence of the query block, answered
  by the raw answer of a block sampler (`Block`). A sampler decodes its raw
  answer into the `s` positions, may refuse, and has a realized law against the
  uniform law of `Fin s → Fin (2^n)` with a factor and an additive slack.
  `Block.exact` reads the positions directly, with factor one and slack zero;
  `Block.gatedKoalaBear` gates them by a proof-of-work test on one KoalaBear
  element and masks them from the low bits of `s` KoalaBear elements. The
  verifier queries only the block of its own shape; any other shape refuses.
- Statement: the initial word. Its commitment event is the initial history and
  determines it (`initial_determined`).
- Errors: folding round `r` errs at most `foldError r` and the query block at
  most `factor · (1 - min θ δ)^s + slack`. The verifier charges each folding
  round once and the block once (`costBound_foldPhase`).

`fiatShamir_soundness` applies `Typed.adaptive_soundness_weighted`. For initial
words the prover chooses after its queries, the transform accepts with an
initial word at relative distance at least `δ` from the code with probability
at most `proverCost + ∑ r < R, foldError r + (factor · (1 - min θ δ)^s + slack)`,
from the proximity premise. `proverCost` bounds the prover's charge with every
oracle key charged the error of its last event, so a prover with `Q` queries is
charged at most `Q` times the largest site error. This is a complete
Fiat–Shamir bound for the model, not one round's error.
`fiatShamir_soundness_uniqueDecoding` instantiates the folding errors in the
unique-decoding regime, `2^(n - r - 1) / |F|` for `0 < θ ≤ (1 - ρ) / 2`, and
`fiatShamir_soundness_koalaBear` also the gated KoalaBear block: with a `g`-bit
gate and positions of `n` bits, `g, n ≤ 24`, its query term is
`(1 + (2^g - 1) / p) / 2^g · (1 + (2^n - 1) / p)^s · (1 - min θ δ)^s`, with `p`
the KoalaBear modulus. `koalaBear_queryPhase` states the same query error as a
probability over the raw answer.

## Committed words

`ZkcSecurity.Examples.CommittedFri` replaces the word events of the transfer by
commitments, as a [verifier with committed tables](fiat-shamir-security.md#verifiers-with-committed-tables):

- Verifier: `verifier` receives the root of the next word after the folding
  challenge of every round but the last, with the round and the word's
  logarithmic size as its shape; the initial word is the statement's root. After
  the final coefficients and the query block, each query reads the two entries
  of its pair from the word of every round (`walkReads`), in the order of the
  source's checks, and rejects at the first failed check.
- Ideal reading: answering every read from the words in the clear, the verifier
  is the transfer's verifier after the initial word (`withTables_verifier`). The
  reads of one query decide as that query's checks on the committed transcript
  (`withTables_walkReads`), and the commit phase is the transfer's commit phase
  under the invariant that the received tables are the words of every transcript
  it completes (`withTables_foldPhaseReads`).
- Commitments: Merkle trees with hashed leaves of one field element and depth
  the word's logarithmic size; an authentication makes at most `n + 1` hash
  calls. An extracted table is read as the word with zero at every entry the
  extraction misses.
- Bound: the verifier commits at most `R - 1` words besides the statement's and
  makes `R` folding queries, one block query and at most `2 s R` reads. With the
  transfer's typed certificate, `soundness` bounds the probability that the
  verifier accepts while the initial word extracted at the checkpoint of one of
  its transcript queries is at relative distance at least `δ` by the prover's
  charge plus `∑ r < R, foldError r`, the query block's error and
  `2 s R (n + 1) · hashError`, with
  `hashError = (R + 3) (Q + R + 1 + 2 s R (n + 1)) / |Digest|` for a prover
  with at most `Q` oracle calls, from the proximity premise.

## Boundaries

- Commitments are ideal in the theorems before [committed words](#committed-words),
  which adds the commitment step for Merkle trees with hashed leaves of one field
  element. The installed schemes' leaf encoding (tag, codec, width and height)
  and its relation to that leaf hash are not modeled.
- The committed-words bound covers acceptance together with the initial word
  being far from the code for the extraction at the checkpoint of a verifier
  transcript query, completed with zero at the entries the extraction misses. It
  does not directly bound the acceptance of an externally specified false
  statement: that an application's bad event implies this checkpoint event is a
  separate obligation. Zero completion belongs to the analysis; the ideal reading
  rejects an unavailable read.
- The theorems concern this model, a transcription of the library verifier, not
  the compiled library or its `Proof` Entry.
  The residual certificate has one query block site, while the source draws the
  `s` positions one at a time. In the transform, each draw's history ends with the
  verifier's send of the previous position, so no prover message separates the
  draws, but the histories differ. The Fiat–Shamir transfer above has one
  query-block key; relating the source's draws to it, and decoding indices from
  the deployed transcript's outputs, remain open. Its events carry whole words;
  [committed words](#committed-words) replaces them by roots with extraction.
- The library has no grinding. The gated KoalaBear block is a sampler of the
  Fiat–Shamir model, not of the library.
- The returned first-layer values are tied to the initial word
  (`firstValue_eq`); binding them to a caller's opening equations is the caller's
  obligation.
- The unique-decoding and cube-root radius instances are proved. Larger
  radii, up to the Johnson radius `1 - ρ^(1/2)`, need other proximity results as
  the named hypothesis; at the pinned revision ArkLib's Johnson-range
  Reed–Solomon bounds are still admitted without proof.
- ArkLib pull request #992 is applied to the pinned revision as a declared patch
  until it merges ([dependencies](../dependencies.md)).
