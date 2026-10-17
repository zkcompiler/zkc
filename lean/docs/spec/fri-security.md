# FRI security at the ideal interpretation

This page specifies the independent model of the verifier of
[`fri::LowDegree`](../../../libraries/fri/lib.zkc), its completeness on the
tested code and its round-by-round soundness theorem. The model reads every
commitment as the vector it commits to; it makes no claim about Merkle
commitments, Fiat–Shamir, the compiled proof Entry or native execution. The
modules are `ZkcSecurity.ArkLib.Fri.*` in the
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

Line numbers refer to `libraries/fri/lib.zkc`. Each model definition is in
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
primitive 32nd root of unity, the bound is `(16 + 8 + 4) / |F| + (1 - min (3/8) δ)^8`
with no remaining premise (`example_bound` in `TestsSecurity.FriSecurity`).

## Generalized Johnson instance

`ZkcSecurity.ArkLib.Fri.GeneralizedJohnson` discharges the folding obligations
with the powers-generator bound of Bordage, Chiesa, Guan and Manzur, *All
Polynomial Generators Preserve Distance with Mutual Correlated Agreement*, in
ArkLib's form for one FRI folding round
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

## Boundaries

- Commitments are ideal. Security of the Merkle-based verifier needs a
  commitment step (binding and extraction) that this model does not contain.
- The theorems concern this interactive model, not the compiled `Proof` Entry.
  The residual certificate has one query block site, while the source draws the
  `s` positions one at a time. In the transform, each draw's history ends with the
  verifier's send of the previous position, so no prover message separates the
  draws, but the histories differ. Relating these draws to one block site, and
  decoding indices from transcript outputs, are part of the transfer.
- No grinding is modelled; the library has none.
- The returned first-layer values are tied to the initial word
  (`firstValue_eq`); binding them to a caller's opening equations is the caller's
  obligation.
- The unique-decoding and generalized Johnson instances are proved. Larger
  radii, up to the Johnson radius `1 - ρ^(1/2)`, need other proximity results as
  the named hypothesis; at the pinned revision ArkLib's Johnson-range
  Reed–Solomon bounds are still admitted without proof.
- ArkLib pull request #992 is applied to the pinned revision as a declared patch
  until it merges ([dependencies](../dependencies.md)).
