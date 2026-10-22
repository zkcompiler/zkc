module

public import ZkcArkLib.Fri.Certificate
public import ZkcSecurity.FiatShamir.Typed
public import ZkcSecurity.FiatShamir.Grinding
public import ZkcSecurity.FiatShamir.Lifting

@[expose] public section

/-! # The FRI certificate in the typed Fiat–Shamir interface

`ZkcSecurity.ArkLib.Fri.Certificate` states the certificate of `fri::LowDegree` over the
verifier's residual processes after the first commitment, with uniform answers of each query
site's sort. This module presents that verifier through a typed transcript interface and turns
the certificate into a typed Fiat–Shamir certificate.

- Events: committed words and final coefficients in the clear (the ideal interpretation of
  commitments), and the occurrences of the folding challenges and of the query block. Proof
  messages are lists of field elements.
- The oracle answers a key in the raw type of its last event. After a folding occurrence it is a
  field element, decoded exactly. After the query block occurrence it is the raw answer of a
  block sampler (`Block`), which decodes it into the `s` positions in `[0, 2^n)`, may refuse,
  and has a realized law against the uniform law of the block: a factor and an additive slack.
  `Block.exact` reads the positions directly; `Block.gatedKoalaBear` gates them by a
  proof-of-work and masks them from KoalaBear elements. The verifier queries only the block of its
  own shape; any other block shape refuses.
- The statement is the initial word; its commitment is the initial history, which determines it.

`typedCertificate` is the typed certificate: folding round `r` errs at most `foldError r` and the
query block at most `factor * (1 - min θ δ)^s + slack`. `fiatShamir_soundness` applies the
weighted adaptive theorem: a prover with cost `proverCost` makes the transform accept with an
initial word at relative distance at least `δ` with probability at most `proverCost` plus every
folding error and the query block's error. `fiatShamir_soundness_uniqueDecoding` instantiates the
folding errors in the unique-decoding regime, and `fiatShamir_soundness_koalaBear` the gated
KoalaBear block.

`koalaBear_queryPhase` states the same query phase error directly as a probability over the raw
answer, from `koalaBear_queryPhase_escape_le`.
-/

namespace ZkcSecurity.Examples.FriFiatShamir

open OracleComp OracleSpec Domain
open ZkcSecurity.ArkLib.Fri
open ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Typed

/-- A sampler of the query block of `count` positions in `[0, 2 ^ logSize)`: the raw answer type
of its oracle keys, its decoding, which may refuse, and its realized law against the uniform law
of the block. -/
structure Block (logSize count : ℕ) where
  Raw : Type
  [sampleable : SampleableType Raw]
  decode : Raw → Option (Fin count → Fin (2 ^ logSize))
  factor : ENNReal
  slack : ENNReal
  realized : Realized decode factor slack

attribute [instance] Block.sampleable

/-- Exact sampling: the raw answer is the block of positions. -/
def Block.exact (logSize count : ℕ) : Block logSize count where
  Raw := Fin count → Fin (2 ^ logSize)
  decode := some
  factor := 1
  slack := 0
  realized := dominated_id.realized

/-- The gated KoalaBear block: one KoalaBear element whose low `gateBits` bits must be zero, and
`count` KoalaBear elements whose low `logSize` bits are the positions. -/
noncomputable def Block.gatedKoalaBear (gateBits logSize count : ℕ) (gateSmall : gateBits ≤ 24)
    (indexSmall : logSize ≤ 24) : Block logSize count where
  Raw := ZMod koalaBear × (Fin count → ZMod koalaBear)
  decode answer := if lowBits koalaBear gateBits answer.1 = 0 then
      some fun index => lowBits koalaBear logSize (answer.2 index)
    else none
  factor := (1 + ((2 ^ gateBits - 1 : ℕ) : ENNReal) / koalaBear) / 2 ^ gateBits *
    (1 + ((2 ^ logSize - 1 : ℕ) : ENNReal) / koalaBear) ^ count
  slack := (1 + ((2 ^ gateBits - 1 : ℕ) : ENNReal) / koalaBear) / 2 ^ gateBits * 0
  realized := koalaBear_queryPhase_realized gateBits logSize count gateSmall indexSmall

/-- Absorbed events: a committed word read in the clear, the final coefficients, and the
occurrences of the folding challenges and of the query block. -/
inductive Event (F : Type) where
  | word (values : List F)
  | final (coefficients : List F)
  | fold (round : ℕ)
  | positions (logSize count : ℕ)
  deriving DecidableEq

variable {F : Type} {b s : ℕ}

/-- The raw answer of a query occurrence: a field element after a folding occurrence, the block
sampler's raw answer after the query block occurrence. -/
def Raw (F : Type) (block : Block b s) : Event F → Type
  | .fold _ => F
  | .positions _ _ => block.Raw
  | _ => Unit

/-- The oracle's answer type at a key: the raw answer of its last event. -/
abbrev Answer (F : Type) (block : Block b s) : List (Event F) → Type :=
  ByLast (Raw F block)

instance rawSampleable [SampleableType F] (block : Block b s) :
    ∀ event : Event F, SampleableType (Raw F block event)
  | .fold _ => inferInstanceAs (SampleableType F)
  | .positions _ _ => inferInstanceAs (SampleableType block.Raw)
  | .word _ => inferInstanceAs (SampleableType Unit)
  | .final _ => inferInstanceAs (SampleableType Unit)

/-- A committed word of size `2 ^ logSize`, recovered from its event. -/
def recoverWord (logSize : ℕ) : Event F → Option (Fin (2 ^ logSize) → F)
  | .word values =>
      if found : values.length = 2 ^ logSize then
        some fun index => values[index.val]'(by rw [found]; exact index.isLt)
      else none
  | _ => none

/-- The final coefficients, recovered from their event. -/
def recoverFinal : Event F → Option (List F)
  | .final coefficients => some coefficients
  | _ => none

/-- The block decoding at a block shape: the sampler's decoding at its own shape, a refusal at any
other. -/
def decodeBlock (block : Block b s) (logSize count : ℕ) (raw : block.Raw) :
    Option (Fin count → Fin (2 ^ logSize)) :=
  if shape : logSize = b ∧ count = s then
    cast (by rw [shape.1, shape.2]) (block.decode raw)
  else none

theorem decodeBlock_self (block : Block b s) (raw : block.Raw) :
    decodeBlock block b s raw = block.decode raw := by
  simp [decodeBlock]

/-- The transcript interface of the verifier with the block sampler `block`. -/
def absorb (block : Block b s) : Interface (operations F) (Event F) (List F) (Raw F block)
  | .fold round => .query (.fold round) fun raw => some raw
  | .positions logSize count => .query (.positions logSize count) fun raw =>
      decodeBlock block logSize count raw
  | .word _ logSize => .receive Event.word (recoverWord logSize)
  | .final => .receive Event.final recoverFinal

/-- The error of each absorbed occurrence. -/
def eventError (foldError : ℕ → ENNReal) (blockError : ENNReal) : Event F → ENNReal
  | .fold round => foldError round
  | .positions _ _ => blockError
  | _ => 0

variable [Field F] [DecidableEq F] [SampleableType F]

omit [Field F] [DecidableEq F] in
/-- The block decoding at a block shape is realized with the sampler's factor and slack: at the
sampler's own shape it is the sampler's decoding, and at any other it refuses. -/
theorem decodeBlock_realized (block : Block b s) (logSize count : ℕ) :
    Realized (decodeBlock block logSize count) block.factor block.slack := by
  by_cases shape : logSize = b ∧ count = s
  · obtain ⟨rfl, rfl⟩ := shape
    have same : decodeBlock block logSize count = block.decode := funext (decodeBlock_self block)
    rw [same]
    exact block.realized
  · intro event
    refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun raw escaping => ?_)) zero_le
    obtain ⟨value, decoded, -⟩ := escaping
    have refused : decodeBlock block logSize count raw = none := by
      unfold decodeBlock
      split
      · exact absurd ‹_› shape
      · rfl
    exact absurd (refused.symm.trans decoded) (by simp)

omit [Field F] [DecidableEq F] in
/-- The law record of the query block at a block shape: the block decoding with the sampler's
realized law. -/
def blockLaw (block : Block b s) (logSize count : ℕ) :
    LawRecord block.Raw (Fin count → Fin (2 ^ logSize)) :=
  LawRecord.dominated (decodeBlock block logSize count) block.factor block.slack
    (decodeBlock_realized block logSize count) 1 (prEvent_le_one _)

omit [Field F] [DecidableEq F] in
/-- The law interface of the verifier: folding challenges read the field answer exactly, and the
query block is decoded by its law record. -/
def laws (block : Block b s) : LawInterface (operations F) (Event F) (List F) (Raw F block)
  | .fold round => .query (.fold round) (inferInstanceAs (SampleableType F)) (LawRecord.identity F)
  | .positions logSize count =>
      .query (.positions logSize count)
        (inferInstanceAs (SampleableType (Fin count → Fin (2 ^ logSize))))
        (blockLaw block logSize count)
  | .word _ logSize => .receive Event.word (recoverWord logSize)
  | .final => .receive Event.final recoverFinal

omit [Field F] [DecidableEq F] in
/-- The law interface presents the verifier's transcript interface. -/
theorem laws_absorb (block : Block b s) : (laws (F := F) block).absorb = absorb block := by
  funext operation
  cases operation <;> rfl

omit [Field F] [DecidableEq F] in
/-- The local obligations over uniform sorts are the uniform-sort obligations of the law
interface. -/
theorem uniformStep (block : Block b s) {doomed : PIR.Process (operations F) Bool → Prop}
    {foldError : ℕ → ENNReal} {queryError : ENNReal} (process : PIR.Process (operations F) Bool)
    (step : Step doomed (siteError foldError queryError) process) :
    UniformEventStep (laws block) doomed (· = true) (siteError foldError queryError) process := by
  cases process with
  | done accepted =>
      change accepted = false at step
      change ¬ accepted = true
      simp [step]
  | halt stop => trivial
  | call operation next =>
      cases operation with
      | fold round =>
          change Pr{let beta ← $ᵗ F}[¬ doomed (next beta)] ≤ foldError round at step
          exact (le_of_eq (SampleableType.prEvent_uniformSample_equiv (Equiv.refl _)
            fun beta : F => ¬ doomed (next beta))).trans step
      | positions logSize count =>
          change Pr{let positions ← $ᵗ (Fin count → Fin (2 ^ logSize))}[
            ¬ doomed (next positions)] ≤ queryError at step
          exact (le_of_eq (SampleableType.prEvent_uniformSample_equiv (Equiv.refl _)
            fun positions : Fin count → Fin (2 ^ logSize) => ¬ doomed (next positions))).trans step
      | word round logSize => exact step
      | final => exact step

omit [Field F] [DecidableEq F] in
/-- The local obligations over uniform sorts are the typed obligations, by the generic lifting of
law interfaces: folding challenges decode exactly, and the query block's error is scaled by its
sampler's realized law. -/
theorem typedStep (block : Block b s) {doomed : PIR.Process (operations F) Bool → Prop}
    {foldError : ℕ → ENNReal} {queryError : ENNReal} (process : PIR.Process (operations F) Bool)
    (step : Step doomed (siteError foldError queryError) process) :
    Typed.Step (absorb block) doomed (· = true)
      (eventError foldError (block.factor * queryError + block.slack)) process := by
  rw [← laws_absorb]
  refine UniformEventStep.typed (laws block) (fun operation event sort law site => ?_) process
    (uniformStep block process step)
  cases operation <;> simp only [laws] at site <;> cases site
  · simp [LawRecord.identity, LawRecord.exact, siteError, eventError]
  · simp [blockLaw, LawRecord.dominated, siteError, eventError]

/-- The typed certificate of the verifier after the first commitment, with the block sampler
`block` of the verifier's own block shape. -/
def typedCertificate (roots : ℕ → F) (t : ℕ) (shift : F) {N K : ℕ}
    (block : Block (N + 1) s) (D : SmoothCosetFftDomain (N + 1) F)
    (hD : ∀ i : Fin (2 ^ (N + 1)), D i = point roots shift (N + 1) i)
    (hcompat : Compatible roots (N + 1) (K + 1)) (θ δ : ℝ) (foldError : ℕ → ENNReal) :
    Typed.Certificate (absorb (F := F) block) (· = true)
      (eventError foldError (block.factor * ENNReal.ofReal (1 - min θ δ) ^ s + block.slack))
    where
  doomed := Doomed (n := N + 1) (R₀ := K + 1) roots t shift s D θ δ foldError
  step process member :=
    typedStep block process (certificate D hD hcompat θ δ foldError process member)

/-- The commitment of the initial word, absorbed before the verifier runs. -/
def initial {N : ℕ} (word : Fin (2 ^ (N + 1)) → F) : List (Event F) :=
  [.word (List.ofFn word)]

omit [Field F] [DecidableEq F] [SampleableType F] in
theorem initial_determined {N : ℕ} : Determined (initial (F := F) (N := N)) := by
  intro word other rest otherRest same
  simp only [initial, List.singleton_append, List.cons.injEq, Event.word.injEq] at same
  exact List.ofFn_injective same.1

omit [SampleableType F] in
/-- The query block charges its error once. -/
theorem costBound_queryPhase (roots : ℕ → F) (t : ℕ) (shift : F) {n R₀ : ℕ}
    (block : Block b s) (foldError : ℕ → ENNReal) (blockError : ENNReal)
    (layers : Layers F n R₀) :
    CostBound (absorb block) (eventError foldError blockError)
      (queryPhase roots t shift s layers) blockError :=
  Exists.intro 0 ⟨by simp [eventError], fun _ => trivial⟩

omit [SampleableType F] in
/-- The verifier charges each folding round's error once and the query block's error once. -/
theorem costBound_foldPhase (roots : ℕ → F) (t : ℕ) (shift : F) {n R₀ : ℕ}
    (block : Block b s) (foldError : ℕ → ENNReal) (blockError : ENNReal) :
    ∀ {m R : ℕ} (round : ℕ) (wrap : Layers F (m + 1) (R + 1) → Layers F n R₀)
      (word : Fin (2 ^ (m + 1)) → F),
      CostBound (absorb block) (eventError foldError blockError)
        (foldPhase roots t shift s round wrap word)
        ((∑ later ∈ Finset.range (R + 1), foldError (round + later)) + blockError)
  | m, 0, round, wrap, word => by
      rw [foldPhase_last]
      refine Exists.intro blockError ⟨by simp [eventError], fun beta coefficients => ?_⟩
      change CostBound (absorb block) _ (if bounded t coefficients then
          queryPhase roots t shift s (wrap (.fold word beta (.final coefficients)))
        else .halt .reject) blockError
      split
      · exact costBound_queryPhase roots t shift block foldError blockError _
      · trivial
  | m + 1, R + 1, round, wrap, word => by
      rw [foldPhase_next]
      refine Exists.intro ((∑ later ∈ Finset.range (R + 1), foldError (round + 1 + later)) +
        blockError) ⟨?_, fun beta next => costBound_foldPhase roots t shift block foldError
          blockError (round + 1) (fun rest => wrap (.fold word beta rest)) next⟩
      have shifted : ∑ later ∈ Finset.range (R + 1), foldError (round + 1 + later) =
          ∑ later ∈ Finset.range (R + 1), foldError (round + (later + 1)) :=
        Finset.sum_congr rfl fun later _ => by rw [Nat.add_assoc, Nat.add_comm 1 later]
      change foldError round + _ ≤ _
      rw [Finset.sum_range_succ' _ (R + 1), shifted, Nat.add_zero]
      exact le_of_eq (by ring_nf)
  | 0, R + 1, round, wrap, word => by
      rw [foldPhase_exhausted]
      refine Exists.intro 0 ⟨?_, fun _ => trivial⟩
      change foldError round + 0 ≤ _
      rw [add_zero, Finset.sum_range_succ' _ (R + 1), Nat.add_zero]
      exact le_add_right le_add_self

/-- Fiat–Shamir soundness of `fri::LowDegree` with commitments read in the clear, for statements
chosen adaptively: the transform accepts with an initial word at relative distance at least `δ`
with probability at most the prover's charge plus every folding error and the query block's
error, from the proximity premise. -/
theorem fiatShamir_soundness [Fintype F] (roots : ℕ → F) (t : ℕ) (shift : F) {N K : ℕ}
    (block : Block (N + 1) s) (D : SmoothCosetFftDomain (N + 1) F)
    (hD : ∀ i : Fin (2 ^ (N + 1)), D i = point roots shift (N + 1) i)
    (hcompat : Compatible roots (N + 1) (K + 1)) (θ δ : ℝ) (foldError : ℕ → ENNReal)
    (proximity : FoldingProximity t θ D (K + 1) foldError)
    (prover : OracleComp (OracleSpec.ofFn (Answer F block))
      ((Fin (2 ^ (N + 1)) → F) × List (List F)))
    (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover
      ⟨keyError (eventError foldError
        (block.factor * ENNReal.ofReal (1 - min θ δ) ^ s + block.slack))⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (Typed.experiment (absorb block)
        (fun word => afterCommit (R := K) roots t shift s word) initial prover)).run' ∅}[
      Far D (degreeBound (K + 1) (2 ^ t)) δ result.1 ∧ Accepted (· = true) result.2.1] ≤
      proverCost + ((∑ round ∈ Finset.range (K + 1), foldError round) +
        (block.factor * ENNReal.ofReal (1 - min θ δ) ^ s + block.slack)) :=
  Typed.adaptive_soundness_weighted
    (typedCertificate roots t shift block D hD hcompat θ δ foldError)
    (fun word => afterCommit (R := K) roots t shift s word) initial initial_determined
    (fun word => Far D (degreeBound (K + 1) (2 ^ t)) δ word)
    (fun word far => afterCommit_doomed_of_proximity (roots := roots) (t := t) (shift := shift)
      (s := s) D θ δ foldError proximity word far)
    _ (fun word => by
      have bound := costBound_foldPhase roots t shift (n := N + 1) (R₀ := K + 1) block foldError
        (block.factor * ENNReal.ofReal (1 - min θ δ) ^ s + block.slack) 0 id word
      simp only [zero_add] at bound
      exact bound)
    prover proverCost proverBound

/-- Fiat–Shamir soundness in the unique-decoding regime: folding round `r` errs at most
`2^(N - r) / |F|`. -/
theorem fiatShamir_soundness_uniqueDecoding [Fintype F] (roots : ℕ → F) (t : ℕ) (shift : F)
    {N K : ℕ} (block : Block (N + 1) s) (D : SmoothCosetFftDomain (N + 1) F)
    (hD : ∀ i : Fin (2 ^ (N + 1)), D i = point roots shift (N + 1) i)
    (hcompat : Compatible roots (N + 1) (K + 1)) (θ : NNReal) (positive : 0 < θ)
    (size : degreeBound (K + 1) (2 ^ t) ≤ 2 ^ (N + 1))
    (radius : θ ≤ ((1 : NNReal) - (degreeBound (K + 1) (2 ^ t) : NNReal) /
      (2 ^ (N + 1) : NNReal)) / 2) (δ : ℝ)
    (prover : OracleComp (OracleSpec.ofFn (Answer F block))
      ((Fin (2 ^ (N + 1)) → F) × List (List F)))
    (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover
      ⟨keyError (eventError (uniqueDecodingError F (N + 1))
        (block.factor * ENNReal.ofReal (1 - min (θ : ℝ) δ) ^ s + block.slack))⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (Typed.experiment (absorb block)
        (fun word => afterCommit (R := K) roots t shift s word) initial prover)).run' ∅}[
      Far D (degreeBound (K + 1) (2 ^ t)) δ result.1 ∧ Accepted (· = true) result.2.1] ≤
      proverCost + ((∑ round ∈ Finset.range (K + 1), uniqueDecodingError F (N + 1) round) +
        (block.factor * ENNReal.ofReal (1 - min (θ : ℝ) δ) ^ s + block.slack)) :=
  fiatShamir_soundness roots t shift block D hD hcompat θ δ _
    (foldingProximity_uniqueDecoding t θ positive D (K + 1) size radius) prover proverCost
    proverBound

/-- Fiat–Shamir soundness with the gated KoalaBear block, in the unique-decoding regime: the query
block errs at most the gate's pass probability times the block factor times `(1 - min θ δ)^s`. -/
theorem fiatShamir_soundness_koalaBear [Fintype F] (roots : ℕ → F) (t : ℕ) (shift : F)
    {N K : ℕ} (gateBits : ℕ) (gateSmall : gateBits ≤ 24) (indexSmall : N + 1 ≤ 24)
    (D : SmoothCosetFftDomain (N + 1) F)
    (hD : ∀ i : Fin (2 ^ (N + 1)), D i = point roots shift (N + 1) i)
    (hcompat : Compatible roots (N + 1) (K + 1)) (θ : NNReal) (positive : 0 < θ)
    (size : degreeBound (K + 1) (2 ^ t) ≤ 2 ^ (N + 1))
    (radius : θ ≤ ((1 : NNReal) - (degreeBound (K + 1) (2 ^ t) : NNReal) /
      (2 ^ (N + 1) : NNReal)) / 2) (δ : ℝ)
    (prover : OracleComp
      (OracleSpec.ofFn (Answer F (Block.gatedKoalaBear gateBits (N + 1) s gateSmall indexSmall)))
      ((Fin (2 ^ (N + 1)) → F) × List (List F)))
    (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover
      ⟨keyError (eventError (uniqueDecodingError F (N + 1))
        ((Block.gatedKoalaBear gateBits (N + 1) s gateSmall indexSmall).factor *
            ENNReal.ofReal (1 - min (θ : ℝ) δ) ^ s +
          (Block.gatedKoalaBear gateBits (N + 1) s gateSmall indexSmall).slack))⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (Typed.experiment
        (absorb (Block.gatedKoalaBear gateBits (N + 1) s gateSmall indexSmall))
        (fun word => afterCommit (R := K) roots t shift s word) initial prover)).run' ∅}[
      Far D (degreeBound (K + 1) (2 ^ t)) δ result.1 ∧ Accepted (· = true) result.2.1] ≤
      proverCost + ((∑ round ∈ Finset.range (K + 1), uniqueDecodingError F (N + 1) round) +
        (1 + ((2 ^ gateBits - 1 : ℕ) : ENNReal) / koalaBear) / 2 ^ gateBits *
          (1 + ((2 ^ (N + 1) - 1 : ℕ) : ENNReal) / koalaBear) ^ s *
          ENNReal.ofReal (1 - min (θ : ℝ) δ) ^ s) := by
  refine (fiatShamir_soundness_uniqueDecoding roots t shift
    (Block.gatedKoalaBear gateBits (N + 1) s gateSmall indexSmall) D hD hcompat θ positive size
    radius δ prover proverCost proverBound).trans (le_of_eq ?_)
  simp only [Block.gatedKoalaBear, mul_zero, add_zero]

omit [SampleableType F] in
/-- The query block's uniform-law error, composed with the gated KoalaBear query phase as a
probability over the raw answer: one absorbed prefix is answered by a field element for a
`gateBits`-bit proof-of-work test and `s` field elements whose low `N + 1` bits are the
positions. -/
theorem koalaBear_queryPhase (roots : ℕ → F) (t : ℕ) (shift : F) {N K : ℕ}
    (D : SmoothCosetFftDomain (N + 1) F)
    (hD : ∀ i : Fin (2 ^ (N + 1)), D i = point roots shift (N + 1) i)
    (hcompat : Compatible roots (N + 1) (K + 1)) (θ δ : ℝ) (layers : Layers F (N + 1) (K + 1))
    (safe : (toTrace t D layers).Safe θ)
    (far : Far D (degreeBound (K + 1) (2 ^ t)) δ (toTrace t D layers).initial)
    (gateBits : ℕ) (gateSmall : gateBits ≤ 24) (indexSmall : N + 1 ≤ 24) :
    Pr{let answer ← $ᵗ (ZMod koalaBear × (Fin s → ZMod koalaBear))}[
        lowBits koalaBear gateBits answer.1 = 0 ∧
          verify roots t shift layers
            (fun index => lowBits koalaBear (N + 1) (answer.2 index)) = true] ≤
      (1 + ((2 ^ gateBits - 1 : ℕ) : ENNReal) / koalaBear) / 2 ^ gateBits *
        ((1 + ((2 ^ (N + 1) - 1 : ℕ) : ENNReal) / koalaBear) ^ s *
          ENNReal.ofReal (1 - min θ δ) ^ s) :=
  koalaBear_queryPhase_escape_le gateBits (N + 1) s gateSmall indexSmall
    (fun answer => answer.1 = 0 ∧ verify roots t shift layers answer.2 = true)
    (fun positions => verify roots t shift layers positions = true)
    (fun _ _ escaping => escaping)
    (query_escape_le roots t s D shift hD hcompat θ δ layers safe far)

end ZkcSecurity.Examples.FriFiatShamir
