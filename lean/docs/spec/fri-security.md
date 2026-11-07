# FRI security at the ideal interpretation

This page specifies the independent model of the verifier of
[`fri::LowDegree` at `1f57002c30ec980137fc1ad28281ecb4d7df6c0a`](https://github.com/zkcompiler/zkc/blob/1f57002c30ec980137fc1ad28281ecb4d7df6c0a/libraries/protocols/polynomial/fri/lib.zkc), its completeness on the
tested code, its round-by-round soundness theorem, its Fiat–Shamir transfer
with one query-block site and the same verifier with words committed by Merkle
trees. The model is a transcription of the library verifier, related line by
line to the source; it makes no claim about the compiled library, its proof
Entry or native execution. Before [committed words](#committed-words) it reads
every commitment as the vector it commits to. The modules are
`ZkcArkLib.Fri.*`, `ZkcArkLibExamples.FriFiatShamir` and
`ZkcArkLibExamples.CommittedFri` in the
[security integration](../../integrations/arklib/README.md).

The current library has separate commitment, query and checking phases. In
particular, its `Check` requires exactly `2^TerminalLog` padded coefficients;
this historical model accepts any list up to that length. The correspondence
below is to the pinned verifier, not the current phased implementation.
Connecting the current implementation to these mathematical results remains
separate work; this page does not establish that connection.

## Retained Direct scalar source

The current octic KoalaBear entry has a separate theorem on the admitted
source verifier. Fix a nonzero shift, 32 cells, a degree bound of eight,
three folding challenges, eight scalar queries with replacement, and the
clear full-word provider. The installed interactive service draws fresh
uniform field elements and positions. For every adaptive network and word
chooser, the probability that the verifier returns true **and its first
successfully published word is far** is bounded by the sum of the three
unique-decoding folding errors and `(1 − min(1/4, δ))^8`. The word is read
from the provider's final publication history. An abort retains its mass,
post-state and observations. A later word can depend on earlier challenges.
[Original source-event theorem](../../integrations/arklib/ZkcArkLibExamples/Fri/InteractiveSoundness.lean)

The clear provider preserves the published cells, nominal anchor and order
under subsequent source operations. The FRI library proves which parent,
challenge and coset a virtual fold uses. For every eligible codeword and
every triple of draws, the linked holder helpers produce folded words and
one terminal coefficient satisfying the scalar predicate at all positions.
Two paired executions additionally run both original roles through every
return. Universal honest termination and the connection from the compiled
scalar verifier to its charged random-oracle queries are separate proof
obligations. [Provider laws](../../Zkc/Source/Structured/PublishedWordsLaws.lean)
· [Holder theorem](../../integrations/arklib/ZkcArkLibExamples/Fri/HonestMessages.lean)
· [Paired source controls](../../security/TestsSecurity/FriHonestExchange.lean)

The clear-store representation laws separately connect a provider publication to
an immutable nominal record. The record contains the actual enclosing iteration
coordinates, row count, one base leaf and the exact published data. The actual
provider return supplies publication validity and freshness; appending the record
assigns its old sequence length as the reference slot. Provider-preserving changes
and physical append preserve that association. Existing checked sequence access
and typed record projections recover the same word; equal payloads at different
source anchors cannot justify exchanging their references. These are local
representation and instruction laws. The common five-instruction allocator rule
now establishes the appended record and returned reference in actual constructed
instruction semantics, retaining every intermediate cell and checkpoint. A checked
recognizer extracts nominal types and SSA positions from an instruction fragment;
both the base and virtual FRI allocator fragments have been checked against that
rule. The same rule applies at arbitrary caller offsets, and an invalid constructor
refuses before reading the store. Returning allocation requires the explicit
constructor and store-length bounds. The common four-instruction lookup rule
checks the reference constructor before reading the immutable slot. Its execution
rule applies to all 66 lookup fragments in the retained FRI tree. `Stored.lookup`
connects a returning lookup to the exact publication record, and the existing
projections recover that word's data. These are static helper occurrences, not
runtime read counts. Virtual capture layouts are checked against the original
oracle's declared input types and the actual allocator's record fields. The
shared relation keeps ordinary parameters equal and resolves each parent
reference through immutable storage; typed projections preserve source order.
For the actual Fold record, this checks nine captures following three index
metadata fields. The metadata's dynamic source meaning still belongs to the
whole-run relation. A two-parent control rejects exchanging distinct same-typed
anchors even when their published words have identical cells. The complete query
controller, generated-event ownership,
root allocation bounds and whole-run simulation remain open. The common virtual
record rule now additionally preserves the original captures through actual
allocation and typed projection. Its source-installation rule uses the actual
returning virtual instruction to recover the exact checked body, captures,
location and registry entry. The source return and physical allocation still
need to be composed at every reached location in the full verifier.
The common guarded field-vector read now retains all outcomes: finite-index
checking, row-bound refusal and missing-cell refusal. Its physical execution
agrees with the exact stored provider word for every position once publication
has established a valid length. Fixed and unsized handle annotations may share
that word when both admit its length; query locations remain independent of the
publication location. This closes the local base-read boundary, not dispatch or
virtual-child continuation execution.
[Clear-store laws](../../Zkc/Realization/ClearStorage.lean)
· [Constructed reads](../../Zkc/Realization/ClearStorageCalculations.lean)
· [Actual allocation](../../Zkc/Realization/ClearStorageAllocation.lean)
· [Common allocator rule](../../Zkc/Realization/RecordAllocator.lean)
· [Checked lookup](../../Zkc/Realization/ClearStorageLookup.lean)
· [Guarded table reads](../../Zkc/Realization/TableRead.lean)
· [Provider read connection](../../Zkc/Realization/ClearStorageRead.lean)
· [Typed captures](../../Zkc/Realization/CaptureLayout.lean)
· [Capture storage association](../../Zkc/Realization/ClearStorageCaptures.lean)
· [Virtual records](../../Zkc/Realization/VirtualStorage.lean)
· [Source installation](../../Zkc/Realization/VirtualStorageInstallation.lean)
· [Publication and swap controls](../../Tests/ClearStorage.lean)

The fixed-table access transport preserves both replies and the complete
ordered query log. At the selected field and scalar sites, it recovers the
same challenge values and charged keys used in the FRI experiment. The
scalar segment reads eight positions even when values or keys repeat.
The complete compiled endpoint additionally needs an admitted interpretation
of the selected constructed participant and a realization correspondence
for its generated clear-store helpers. The native export now retains both
roles, including closed ranges and actual mathematical computation bodies.
The retained validator has 1,566 exported instructions and fits the unchanged
1 MiB bound. Nominal record construction and empty single-constructor
projections now use the shared structured product calculations, with kernel
laws for arbitrary fields and controls for same-typed ordering and nominal
mismatches. Closed local tests use a kind-sensitive checker and evaluator that
preserve guard rejection and exclude transcript effects. The independent
construction renderer now admits closed conditional ranges using the structured
finite traversal and retains the embedded Math bodies, including folds resolved
against the original domain and callback definitions. The export renders as a
complete instruction tree with no unsupported operations. Checked scalar and
immutable sequence operations use the shared structured evaluator. Their nominal
element types, out-of-range refusal and distinction from total mathematical
operations remain explicit. The actual participant passes `checkExport` in the
kernel, including the shared loop rule for local carries that leave the transcript
unchanged. This is construction formation only: `checkCompiled` still refuses
`construction-source-occurrence` because the generated clear-delivery event is not
an ordinary authored exchange. Its association to the original oracle publication
and the complete clear-store execution correspondence remain required. Natural field constants use
the exact nominal field's catalogue characteristic.

The executable-byte reader separately requires support for the nominal
sequence-of-record storage representation. Whole-run event transport and finite
sampling-retry accounting remain required by the compiled-ideal theorem.
[Access transport](../../security/ZkcSecurity/Bindings/Transcript/QueryTreeSource/Composition/AccessLog.lean)
· [Scalar source path](../../integrations/arklib/ZkcArkLibExamples/Fri/ClearScalarPath.lean)

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

Line numbers refer to the pinned source above. Each model definition is in
`ZkcArkLib.Fri.Protocol` unless the table names another module.

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

The honest prover (`honest`, in `ZkcArkLib.Fri.Completeness`) commits
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
(`example_bound` in `TestsArkLib.FriSecurity`).

## Cube-root radius instance

`ZkcArkLib.Fri.GeneralizedJohnson` discharges the folding obligations
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
`TestsArkLib.FriSecurity`).

## Johnson and weighted-Johnson instances

`ZkcArkLib.Fri.Johnson` exposes the pinned ArkLib all-candidate agreement
bounds for binary folds. The ordinary instance uses the integer threshold
`ceil((sqrt(degree/n) + eta) * n)` and its exact exceptional-set count.
The weighted instance takes a checked `IsJohnsonWeightedCertificate`, an
integer agreement threshold and an explicit ceiling inequality for the requested
radius. Neither instance adds a field-characteristic assumption.

The exceptional set is fixed for the two input words before the challenge,
and its guarantee holds for every qualifying candidate polynomial. The
`foldingProximity_cons_johnson` and `foldingProximity_cons_weightedJohnson`
constructors prepend these bounds to the existing `FoldingProximity` chain.
The same `foldingEscapes_of_proximity`, ideal soundness theorem and residual
certificate consume the result. There is no second FRI security model.

These heads require post-fold code dimension at least two. The unchanged
terminal-dimension-one example therefore retains its applicable analysis;
the new constructors do not prove that every round fits a Johnson instance.
`TestsArkLib.FriAdoption` checks a two-round weighted chain, its existing
soundness consumer, the exact integer thresholds and this dimension boundary.
This is a mathematical client, not an installed parameter or security-level claim.

`ZkcArkLib.Fri.SourceCalculations` supplies the mathematical halves of the current
helper contracts: masked u64 pair indices under representability bounds,
Horner evaluation after zero padding, the exact padded-length condition,
prepared-inverse folding and equality at each ordered query occurrence.
Repeated positions are retained. These equations do not prove source-body
association, successful ingress, primitive implementation or complete source
outcomes. In particular, equality at queried positions is not global word equality.

## Certificate over verifier residuals

`ZkcArkLib.Fri.Certificate` states the certificate over the residual
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

`ZkcArkLibExamples.FriFiatShamir` presents the verifier after the first
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

`ZkcArkLibExamples.CommittedFri` replaces the word events of the transfer by
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
- Unique-decoding, cube-root, and the conditional Johnson/weighted-Johnson
  heads above are proved against the pinned roots. A complete parameter chain
  must meet every head's degree, threshold and certificate premises; dimension
  one is not covered by the new Johnson heads. General upstream combination
  results with admitted dependencies are not used as proof authority.
- The pinned ArkLib includes the end-to-end FRI results previously carried by
  pull request #992. This integration uses unmodified upstream sources
  ([dependencies](../dependencies.md)).
