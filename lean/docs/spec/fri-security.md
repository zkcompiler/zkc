# FRI security at the ideal interpretation

This page specifies the independent model of the verifier of
[`fri::LowDegree`](../../../libraries/fri/lib.zkc) and its round-by-round
soundness theorem. The model reads every commitment as the vector it commits to;
it makes no claim about Merkle commitments, Fiat–Shamir, the compiled proof Entry
or native execution. The modules are `ZkcSecurity.ArkLib.Fri.*` in the
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

`coset::fold` (115) and `interpolate_coefficients` (118) are honest-prover
operations and are not modelled. `Honest` states that each committed word after
the first, and the final polynomial's evaluations, are ArkLib's fold of the
previous word, which is the library's fold formula by `foldedValue_eq`.
`verify_of_honest` shows that the verifier accepts every position of such layers
when the final coefficients satisfy the bound, so the checks are consistent with
folding. Completeness for codewords, that folding a codeword of degree below
`2^(t + R)` ends at a polynomial with at most `2^t` coefficients, is not proved
here.

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

## Boundaries

- Commitments are ideal. Security of the Merkle-based verifier needs a
  commitment step (binding and extraction) that this model does not contain.
- The theorems concern this interactive model, not the compiled `Proof` Entry.
  A Fiat–Shamir transfer must treat the `s` consecutive position draws as one
  block: in the transform, each draw's history ends with the verifier's send of
  the previous position, so no prover message separates the draws, but the
  histories differ. Decoding an index from a transcript output is also part of
  that transfer.
- No grinding is modelled; the library has none.
- The returned first-layer values are tied to the initial word
  (`firstValue_eq`); binding them to a caller's opening equations is the caller's
  obligation.
- The unique-decoding instance is proved. Larger radii need other proximity
  results as the named hypothesis. At the pinned revision ArkLib proves the
  powers-generator bound of Bordage, Chiesa, Guan and Manzur, which for lines
  reaches `1 - (1 - δmin + η)^(1/3)` and exceeds the unique-decoding radius only at
  low rates; its Johnson-range Reed–Solomon bounds are still admitted without
  proof.
- ArkLib pull request #992 is applied to the pinned revision as a declared patch
  until it merges ([dependencies](../dependencies.md)).
