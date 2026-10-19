module

public import ZkcSecurity.FiatShamir.Lifting
public import ArkLib.OracleReduction.Security.RoundByRound
public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded

@[expose] public section

/-! Import adapters from ArkLib's round-by-round soundness.

An ArkLib verifier for a protocol specification `pSpec` with `n` rounds reads a
full transcript and outputs a statement. Its **process form** is a validator
over one operation per round (`signature`): a prover-message round receives the
round's message and a challenge round queries the round's challenge, in round
order, and the process returns the verifier's verdict on the full transcript
(`validator`). The verdict is read from the verifier's `Verifier.GuardedForm`:
the verifier outputs a deterministic statement where a Boolean guard passes and
fails elsewhere, which covers verifiers that reject by `guard` or by any other
`OptionT` failure. The process returns the output where the guard passes and no
output where it fails (`guardedVerdict`); only an output in the output language
accepts (`Accepts`). A pure verifier is the guard that always passes
(`Verifier.PureForm.toGuardedForm`). Verifiers that query oracles of their own or
sample are not covered.

The process form has a transcript interface (`absorb`): a statement is bound by
one event (`initial`, which determines it), a message round absorbs the message
with its round, and a challenge round absorbs its occurrence and reads the
challenge from the raw answer of that occurrence, uniform on the round's
challenge type (raw answers by the last event, `Typed.ByLast`).

**`ofWorstCase`.** ArkLib's worst-case-per-prefix round-by-round soundness
(`rbrSoundnessWorstCase`) gives a state function and, for every false input and
every fixed transcript prefix before a challenge round, a bound on the
probability over the fresh challenge alone that the state turns true. That is
exactly a typed certificate's local obligation: the doomed residuals are the
process form's residuals at false states of false inputs (`Doomed`), prover
messages keep them doomed (`toFun_next`), a doomed full transcript is rejected
(`toFun_full`, read through the guarded verdict, `verdict_rejected`), and the
challenge round's escape is the worst-case bound. Each challenge occurrence is
charged its round's error (`eventError`).

**Charges.** The process form queries once per challenge round and nowhere else
(`validator_queryBound`, the number of challenge indices), and its queries charge
the sum of the challenge rounds' errors (`validator_costBound`).
`worstCase_soundness_weighted` and `worstCase_adaptive_soundness_weighted` bound
the transform's acceptance of a false input by the prover's charge plus that sum,
for fixed inputs and for inputs the prover chooses after its queries;
`worstCase_soundness` and `worstCase_adaptive_soundness` are the uniform forms,
`(queries + challenges) · bound` when every round's error is at most `bound`.

The averaged form `rbrSoundness` is not imported: its bound is over a mixture of
prefixes the prover samples, not a per-prefix step, and the typed engine's
certificate needs the per-prefix step.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.Upstream
open OracleComp OracleSpec ProtocolSpec ZkcSecurity.FiatShamir.Typed

variable {n : ℕ} (pSpec : ProtocolSpec n) (StmtIn : Type)

/-- The operations of a protocol's process form: one per round, replying with
the round's message or challenge. -/
abbrev signature : PIR.Signature := ⟨Fin n, fun round => pSpec.«Type» round⟩

/-- Absorbed events: the bound statement, a prover message with its round, and a
challenge occurrence. -/
inductive Event where
  | statement (statement : StmtIn)
  | message (round : Fin n) (value : pSpec.«Type» round)
  | challenge (round : Fin n)

instance [DecidableEq StmtIn] [∀ round, DecidableEq (pSpec.«Type» round)] :
    DecidableEq (Event pSpec StmtIn)
  | .statement first, .statement second =>
      if same : first = second then isTrue (by rw [same]) else isFalse fun equal => by
        cases equal
        exact same rfl
  | .message round value, .message other value' =>
      if sameRound : round = other then by
        subst sameRound
        exact if same : value = value' then isTrue (by rw [same]) else isFalse fun equal => by
          cases equal
          exact same rfl
      else isFalse fun equal => by
        cases equal
        exact sameRound rfl
  | .challenge round, .challenge other =>
      if same : round = other then isTrue (by rw [same]) else isFalse fun equal => by
        cases equal
        exact same rfl
  | .statement _, .message _ _ => isFalse nofun
  | .statement _, .challenge _ => isFalse nofun
  | .message _ _, .statement _ => isFalse nofun
  | .message _ _, .challenge _ => isFalse nofun
  | .challenge _, .statement _ => isFalse nofun
  | .challenge _, .message _ _ => isFalse nofun

/-- A proof message: a round and its message. -/
abbrev Message := (round : Fin n) × pSpec.«Type» round

/-- The raw answer type of a challenge occurrence: the round's challenge type at
a challenge round, and `Unit` at any other round. -/
def ChallengeRaw (round : Fin n) : Type :=
  if challengeRound : pSpec.dir round = .V_to_P then pSpec.Challenge ⟨round, challengeRound⟩
  else Unit

/-- The raw answer type of an event: a challenge occurrence's challenge raw type,
`Unit` for every other event. -/
def Raw : Event pSpec StmtIn → Type
  | .challenge round => ChallengeRaw pSpec round
  | _ => Unit

/-- The error of a round: its challenge error at a challenge round, zero at a
message round. -/
def roundError (error : pSpec.ChallengeIdx → NNReal) (round : Fin n) : ENNReal :=
  if challengeRound : pSpec.dir round = .V_to_P then error ⟨round, challengeRound⟩ else 0

/-- One at a challenge round, zero at a message round. -/
def challengeIndicator (round : Fin n) : ℕ := if pSpec.dir round = .V_to_P then 1 else 0

omit pSpec in
/-- The sum of a weight over the rounds from `round` on. -/
def fromRound {M : Type} [AddCommMonoid M] (weight : Fin n → M) (round : ℕ) : M :=
  ∑ index : Fin n, if round ≤ index.val then weight index else 0

omit pSpec in
theorem fromRound_succ {M : Type} [AddCommMonoid M] (weight : Fin n → M) {round : ℕ}
    (inside : round < n) :
    fromRound weight round = weight ⟨round, inside⟩ + fromRound weight (round + 1) := by
  have split : ∀ index : Fin n, (if round ≤ index.val then weight index else 0) =
      (if index = ⟨round, inside⟩ then weight index else 0) +
        (if round + 1 ≤ index.val then weight index else 0) := by
    intro index
    by_cases same : index = ⟨round, inside⟩
    · subst same
      simp
    · have different : index.val ≠ round := fun equal => same (Fin.ext equal)
      by_cases after : round ≤ index.val
      · simp [same, after, show round + 1 ≤ index.val by omega]
      · simp [same, after, show ¬ round + 1 ≤ index.val by omega]
  unfold fromRound
  rw [Finset.sum_congr rfl fun index _ => split index, Finset.sum_add_distrib,
    Finset.sum_ite_eq']
  simp

omit pSpec in
theorem fromRound_zero {M : Type} [AddCommMonoid M] (weight : Fin n → M) :
    fromRound weight 0 = ∑ index, weight index := by
  simp [fromRound]

/-- The rounds' errors sum to the challenge indices' errors. -/
theorem sum_roundError (error : pSpec.ChallengeIdx → NNReal) :
    ∑ round, roundError pSpec error round =
      ∑ index : pSpec.ChallengeIdx, (error index : ENNReal) := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun round => pSpec.dir round = .V_to_P)
    (roundError pSpec error)]
  have zero : ∀ round : {round // ¬ pSpec.dir round = .V_to_P},
      roundError pSpec error round = 0 := fun round => by simp [roundError, round.2]
  simp only [zero, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun index _ => ?_
  simp [roundError, index.2]

/-- The challenge rounds are the challenge indices. -/
theorem sum_challengeIndicator :
    ∑ round, challengeIndicator pSpec round = Fintype.card pSpec.ChallengeIdx := by
  change _ = Fintype.card {round : Fin n // pSpec.dir round = .V_to_P}
  rw [Fintype.card_subtype, Finset.card_filter]
  rfl

variable [∀ index, SampleableType (pSpec.Challenge index)]

instance challengeRawSampleable (round : Fin n) : SampleableType (ChallengeRaw pSpec round) := by
  unfold ChallengeRaw
  split <;> infer_instance

instance rawSampleable : ∀ event, SampleableType (Raw pSpec StmtIn event)
  | .challenge round => challengeRawSampleable pSpec round
  | .statement _ => inferInstanceAs (SampleableType Unit)
  | .message _ _ => inferInstanceAs (SampleableType Unit)

omit [∀ index, SampleableType (pSpec.Challenge index)] in
theorem challengeRaw_eq {round : Fin n} (challengeRound : pSpec.dir round = .V_to_P) :
    ChallengeRaw pSpec round = pSpec.«Type» round := by
  simp [ChallengeRaw, challengeRound]

/-- The challenge a raw answer of a challenge round reads as. -/
def decodeChallenge {round : Fin n} (challengeRound : pSpec.dir round = .V_to_P) :
    ChallengeRaw pSpec round → pSpec.«Type» round :=
  cast (challengeRaw_eq pSpec challengeRound)

/-- The message of a round, recovered from its event. -/
def recover (round : Fin n) : Event pSpec StmtIn → Option (pSpec.«Type» round)
  | .message other value => if same : other = round then some (same ▸ value) else none
  | _ => none

/-- The transcript interface of the process form: a challenge round asks the
oracle at its occurrence and reads the challenge from the raw answer; a message
round receives the round's message. -/
def absorb : Interface (signature pSpec) (Event pSpec StmtIn) (Message pSpec)
    (ByLast (Raw pSpec StmtIn)) := fun round =>
  if challengeRound : pSpec.dir round = .V_to_P then
    Absorption.queryLast (Raw pSpec StmtIn) (.challenge round) fun _ raw =>
      some (decodeChallenge pSpec challengeRound raw)
  else .receive (fun message => .message message.1 message.2) (recover pSpec StmtIn round)

/-- The bound statement, the initial history. -/
def initial (statement : StmtIn) : List (Event pSpec StmtIn) := [.statement statement]

omit [∀ index, SampleableType (pSpec.Challenge index)] in
theorem initial_determined : Typed.Determined (initial pSpec StmtIn) := by
  intro statement other rest otherRest same
  simp only [initial, List.singleton_append, List.cons.injEq, Event.statement.injEq] at same
  exact same.1

variable {pSpec} {StmtIn} {StmtOut : Type}

/-- A transcript up to round `last`, read as a full transcript. -/
def fullTranscript {last : Fin (n + 1)} (finish : last.val = n)
    (transcript : Transcript last pSpec) : FullTranscript pSpec :=
  cast (by
    have : last = Fin.last n := Fin.ext finish
    subst this
    rfl) transcript

/-- The process form from round `round` with transcript `transcript`, with
`remaining` rounds left: receive or query each remaining round in order, then
return the verdict on the full transcript. -/
def processFrom {A : Type} (verdict : FullTranscript pSpec → A) :
    (remaining : ℕ) → (round : Fin (n + 1)) → round.val + remaining = n → Transcript round pSpec →
      PIR.Proc (signature pSpec) A
  | 0, _, finish, transcript => .done (verdict (fullTranscript finish transcript))
  | remaining + 1, round, finish, transcript =>
      .call (I := signature pSpec) (⟨round.val, by omega⟩ : Fin n) fun value =>
        processFrom verdict remaining (Fin.succ (⟨round.val, by omega⟩ : Fin n)) (by simp; omega)
          (Transcript.concat (m := ⟨round.val, by omega⟩) value transcript)

/-- The process form of a verdict on a statement: from round `0` with the empty
transcript. -/
def validator {A : Type} (verdict : StmtIn → FullTranscript pSpec → A) (statement : StmtIn) :
    PIR.Proc (signature pSpec) A :=
  processFrom (verdict statement) n 0 (by simp) default

/-- The error of each event: a challenge round's error at its occurrence, zero
for every other event. -/
def eventError (error : pSpec.ChallengeIdx → NNReal) : Event pSpec StmtIn → ENNReal
  | .challenge round => roundError pSpec error round
  | _ => 0

omit [∀ index, SampleableType (pSpec.Challenge index)] in
/-- The process form makes one query at each remaining challenge round. -/
theorem processFrom_queryBound {A : Type} (verdict : FullTranscript pSpec → A) :
    ∀ (remaining : ℕ) (round : Fin (n + 1)) (finish : round.val + remaining = n)
      (transcript : Transcript round pSpec),
        Typed.QueryBound (absorb pSpec StmtIn)
          (processFrom verdict remaining round finish transcript)
          (fromRound (challengeIndicator pSpec) round.val)
  | 0, _, _, _ => trivial
  | remaining + 1, round, finish, transcript => by
      have inside : round.val < n := by omega
      rw [fromRound_succ _ inside]
      by_cases challengeRound : pSpec.dir (⟨round.val, inside⟩ : Fin n) = .V_to_P
      · simp only [processFrom, Typed.QueryBound, absorb, challengeRound, ↓reduceDIte,
          Absorption.queryLast, challengeIndicator, ↓reduceIte]
        refine ⟨by omega, fun value => ?_⟩
        rw [Nat.add_sub_cancel_left]
        exact processFrom_queryBound verdict remaining _ _ _
      · simp only [processFrom, Typed.QueryBound, absorb, challengeRound, ↓reduceDIte,
          challengeIndicator, ↓reduceIte, zero_add]
        exact fun value => by
          exact processFrom_queryBound verdict remaining _ _ _

omit [∀ index, SampleableType (pSpec.Challenge index)] in
/-- The process form's queries from `round` on charge the remaining challenge
rounds' errors. -/
theorem processFrom_costBound {A : Type} (error : pSpec.ChallengeIdx → NNReal)
    (verdict : FullTranscript pSpec → A) :
    ∀ (remaining : ℕ) (round : Fin (n + 1)) (finish : round.val + remaining = n)
      (transcript : Transcript round pSpec),
        Typed.CostBound (absorb pSpec StmtIn) (eventError error)
          (processFrom verdict remaining round finish transcript)
          (fromRound (roundError pSpec error) round.val)
  | 0, _, _, _ => trivial
  | remaining + 1, round, finish, transcript => by
      have inside : round.val < n := by omega
      rw [fromRound_succ _ inside]
      by_cases challengeRound : pSpec.dir (⟨round.val, inside⟩ : Fin n) = .V_to_P
      · simp only [processFrom, Typed.CostBound, absorb, challengeRound, ↓reduceDIte,
          Absorption.queryLast]
        refine ⟨fromRound (roundError pSpec error) (round.val + 1), le_rfl, fun value => ?_⟩
        exact processFrom_costBound error verdict remaining _ _ _
      · simp only [processFrom, Typed.CostBound, absorb, challengeRound, ↓reduceDIte,
          roundError, zero_add]
        exact fun value => by
          exact processFrom_costBound error verdict remaining _ _ _

omit [∀ index, SampleableType (pSpec.Challenge index)] in
/-- The process form of a statement makes one query per challenge index. -/
theorem validator_queryBound {A : Type} (verdict : StmtIn → FullTranscript pSpec → A)
    (statement : StmtIn) :
    Typed.QueryBound (absorb pSpec StmtIn) (validator verdict statement)
      (Fintype.card pSpec.ChallengeIdx) := by
  have bound := processFrom_queryBound (StmtIn := StmtIn) (verdict statement) n 0 (by simp) default
  have total : fromRound (challengeIndicator pSpec) ((0 : Fin (n + 1)) : ℕ) =
      Fintype.card pSpec.ChallengeIdx := by
    rw [Fin.val_zero, fromRound_zero, sum_challengeIndicator]
  rw [total] at bound
  exact bound

omit [∀ index, SampleableType (pSpec.Challenge index)] in
/-- The process form of a statement charges the sum of the challenge indices'
errors. -/
theorem validator_costBound {A : Type} (error : pSpec.ChallengeIdx → NNReal)
    (verdict : StmtIn → FullTranscript pSpec → A) (statement : StmtIn) :
    Typed.CostBound (absorb pSpec StmtIn) (eventError error) (validator verdict statement)
      (∑ index : pSpec.ChallengeIdx, (error index : ENNReal)) := by
  have bound := processFrom_costBound (StmtIn := StmtIn) error (verdict statement) n 0 (by simp)
    default
  have total : fromRound (roundError pSpec error) ((0 : Fin (n + 1)) : ℕ) =
      ∑ index : pSpec.ChallengeIdx, (error index : ENNReal) := by
    rw [Fin.val_zero, fromRound_zero, sum_roundError]
  rw [total] at bound
  exact bound

/-- An output in the output language. A missing output, from a failed guard, is
never accepted. -/
def Accepts (langOut : Set StmtOut) : Option StmtOut → Prop
  | some output => output ∈ langOut
  | none => False

section WorstCase
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type} (init : ProbComp σ)
  (impl : QueryImpl oSpec (StateT σ ProbComp)) {langIn : Set StmtIn} {langOut : Set StmtOut}
  {verifier : Verifier oSpec StmtIn StmtOut pSpec} (guarded : verifier.GuardedForm)

/-- The verdict of a guarded verifier: its output where the guard passes, no
output where it fails. -/
def guardedVerdict (statement : StmtIn) (transcript : FullTranscript pSpec) : Option StmtOut :=
  if guarded.check statement transcript then some (guarded.out statement transcript) else none

omit [∀ index, SampleableType (pSpec.Challenge index)] in
/-- A guarded verifier's run is its guarded verdict. -/
theorem run_eq (statement : StmtIn) (transcript : FullTranscript pSpec) :
    (verifier.run statement transcript : OracleComp oSpec (Option StmtOut)) =
      (Pure.pure (guardedVerdict guarded statement transcript) :
        OracleComp oSpec (Option StmtOut)) := by
  simp only [Verifier.run, guarded.verify_eq statement transcript, guardedVerdict]
  split <;> rfl

/-- The doomed residuals of the process form under a state function: a
residual at some round of a false input whose state is false. -/
def Doomed (stateFunction : verifier.StateFunction init impl langIn langOut) :
    PIR.Proc (signature pSpec) (Option StmtOut) → Prop := fun process =>
  ∃ statement remaining round finish transcript, statement ∉ langIn ∧
    process = processFrom (guardedVerdict guarded statement) remaining round finish transcript ∧
    ¬ stateFunction round statement transcript

omit [∀ index, SampleableType (pSpec.Challenge index)] in
/-- A guarded verdict outside the output language, a failed guard included, is
outside it with probability one: the form of `toFun_full` a state function of a
guarded verifier discharges. -/
theorem prEvent_verdict_eq_zero (statement : StmtIn) (transcript : FullTranscript pSpec)
    (rejected : ¬ Accepts langOut (guardedVerdict guarded statement transcript)) :
    Pr{let stmtOut ← OptionT.mk do
        (simulateQ impl (verifier.run statement transcript)).run' (← init)}[
      stmtOut ∈ langOut] = 0 := by
  rw [OptionT.prEvent_mk]
  simp only [run_eq guarded, simulateQ_pure, StateT.run'_pure']
  cases verdict : guardedVerdict guarded statement transcript with
  | none => simp
  | some output =>
      rw [verdict] at rejected
      have outside : output ∉ langOut := rejected
      simp [outside]

omit [∀ index, SampleableType (pSpec.Challenge index)] in
/-- A full transcript at a false state is rejected: the guarded verdict is
outside the output language, or the guard fails. -/
theorem verdict_rejected (stateFunction : verifier.StateFunction init impl langIn langOut)
    (statement : StmtIn) (transcript : FullTranscript pSpec)
    (false_ : ¬ stateFunction (Fin.last n) statement transcript) :
    ¬ Accepts langOut (guardedVerdict guarded statement transcript) := by
  intro accepted
  have zero := stateFunction.toFun_full statement transcript false_
  rw [OptionT.prEvent_mk] at zero
  simp only [run_eq guarded, simulateQ_pure, StateT.run'_pure'] at zero
  cases verdict : guardedVerdict guarded statement transcript with
  | none =>
      rw [verdict] at accepted
      exact accepted
  | some output =>
      rw [verdict] at accepted zero
      have member : output ∈ langOut := accepted
      exact absurd zero (by simp [member])

/-- The typed certificate of the process form from a state function whose every
challenge round meets the worst-case bound, each challenge occurrence charged
its round's error. -/
def worstCaseCertificate (stateFunction : verifier.StateFunction init impl langIn langOut)
    {error : pSpec.ChallengeIdx → NNReal}
    (worstCase : ∀ statement ∉ langIn, ∀ index : pSpec.ChallengeIdx,
      ∀ transcript : Transcript index.1.castSucc pSpec,
        Pr{let challenge ← $ᵗ (pSpec.Challenge index)}[
          ¬ stateFunction index.1.castSucc statement transcript ∧
            stateFunction index.1.succ statement (transcript.concat challenge)] ≤ error index) :
    Typed.Certificate (absorb pSpec StmtIn) (Accepts langOut) (eventError error) where
  doomed := Doomed init impl guarded stateFunction
  step process member := by
    obtain ⟨statement, remaining, round, finish, transcript, outside, rfl, false_⟩ := member
    cases remaining with
    | zero =>
        obtain rfl : round = Fin.last n := Fin.ext (by simpa using finish)
        exact verdict_rejected init impl guarded stateFunction statement _ false_
    | succ remaining =>
        by_cases challengeRound : pSpec.dir (⟨round.val, by omega⟩ : Fin n) = .V_to_P
        · simp only [processFrom, Typed.Step, absorb, challengeRound, ↓reduceDIte,
            Absorption.queryLast]
          intro preceding
          rw [prEvent_read (Raw pSpec StmtIn) preceding (.challenge _) fun raw =>
            ∃ value, some (decodeChallenge pSpec challengeRound raw) = some value ∧
              ¬ Doomed init impl guarded stateFunction
                (processFrom (guardedVerdict guarded statement) remaining
                  (Fin.succ ⟨round.val, by omega⟩) (by simp; omega)
                  (Transcript.concat (m := ⟨round.val, by omega⟩) value transcript))]
          have transported := SampleableType.prEvent_uniformSample_equiv
            (Equiv.cast (challengeRaw_eq pSpec challengeRound :
              ChallengeRaw pSpec _ = pSpec.Challenge ⟨_, challengeRound⟩))
            fun challenge : pSpec.Challenge ⟨_, challengeRound⟩ =>
              ¬ stateFunction (Fin.castSucc ⟨round.val, by omega⟩) statement transcript ∧
                stateFunction (Fin.succ ⟨round.val, by omega⟩) statement
                  (Transcript.concat (m := ⟨round.val, by omega⟩) challenge transcript)
          refine (prEvent_mono _ _ _ fun raw escaping => ?_).trans
            ((le_of_eq transported).trans ?_)
          · obtain ⟨value, decoded, notDoomed⟩ := escaping
            cases Option.some.inj decoded
            refine ⟨false_, ?_⟩
            by_contra stillFalse
            exact notDoomed ⟨statement, remaining, _, _, _, outside, rfl, stillFalse⟩
          · simp only [eventError, roundError, challengeRound, ↓reduceDIte]
            exact worstCase statement outside ⟨_, challengeRound⟩ transcript
        · simp only [processFrom, Typed.Step, absorb, challengeRound, ↓reduceDIte]
          intro value
          have message : pSpec.dir (⟨round.val, by omega⟩ : Fin n) = .P_to_V := by
            cases direction : pSpec.dir (⟨round.val, by omega⟩ : Fin n)
            · rfl
            · exact absurd direction challengeRound
          exact ⟨statement, remaining, _, _, _, outside, rfl,
            stateFunction.toFun_next _ message statement transcript false_ value⟩

omit [∀ index, SampleableType (pSpec.Challenge index)] in
/-- The process form of a false input is doomed. -/
theorem validator_doomed (stateFunction : verifier.StateFunction init impl langIn langOut)
    {statement : StmtIn} (outside : statement ∉ langIn) :
    Doomed init impl guarded stateFunction (validator (guardedVerdict guarded) statement) :=
  ⟨statement, n, 0, by simp, default, outside, rfl, fun holds =>
    outside ((stateFunction.toFun_empty statement).mpr holds)⟩

/-- Import of worst-case round-by-round soundness: a certificate of the process
form, each challenge occurrence charged its round's error. -/
noncomputable def ofWorstCase {error : pSpec.ChallengeIdx → NNReal}
    (sound : verifier.rbrSoundnessWorstCase init impl langIn langOut error) :
    Typed.Certificate (absorb pSpec StmtIn) (Accepts langOut) (eventError error) :=
  worstCaseCertificate init impl guarded sound.choose sound.choose_spec

theorem ofWorstCase_doomed {error : pSpec.ChallengeIdx → NNReal}
    (sound : verifier.rbrSoundnessWorstCase init impl langIn langOut error)
    {statement : StmtIn} (outside : statement ∉ langIn) :
    (ofWorstCase init impl guarded sound).doomed (validator (guardedVerdict guarded) statement) :=
  validator_doomed init impl guarded sound.choose outside

omit [∀ index, SampleableType (pSpec.Challenge index)] in
theorem eventError_le {error : pSpec.ChallengeIdx → NNReal} {bound : ENNReal}
    (bounded : ∀ index, (error index : ENNReal) ≤ bound) (event : Event pSpec StmtIn) :
    eventError error event ≤ bound := by
  cases event with
  | challenge round =>
      by_cases challengeRound : pSpec.dir round = .V_to_P
      · simp only [eventError, roundError, challengeRound, ↓reduceDIte]
        exact bounded _
      · simp only [eventError, roundError, challengeRound, ↓reduceDIte]
        exact zero_le
  | statement _ => exact zero_le
  | message _ _ => exact zero_le

variable [DecidableEq StmtIn] [∀ round, DecidableEq (pSpec.«Type» round)]

/-- Fiat–Shamir soundness of the process form of a worst-case round-by-round
sound verifier, for a fixed false input, with an error per challenge round: a
prover whose queries charge at most `proverCost`, each query the error of the
challenge round its key ends with, makes the transform accept with probability
at most `proverCost` plus the sum of the challenge rounds' errors. -/
theorem worstCase_soundness_weighted {error : pSpec.ChallengeIdx → NNReal}
    (sound : verifier.rbrSoundnessWorstCase init impl langIn langOut error) {statement : StmtIn}
    (outside : statement ∉ langIn)
    (prover : OracleComp (OracleSpec.ofFn (ByLast (Raw pSpec StmtIn))) (List (Message pSpec)))
    (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨keyError (eventError (StmtIn := StmtIn) error)⟩
      proverCost) :
    Pr{let result ← (simulateQ randomOracle (Typed.fixedExperiment (absorb pSpec StmtIn)
        (validator (guardedVerdict guarded) statement) (initial pSpec StmtIn statement)
        prover)).run' ∅}[Accepted (Accepts langOut) result.1] ≤
      proverCost + ∑ index : pSpec.ChallengeIdx, (error index : ENNReal) :=
  Typed.soundness_weighted (ofWorstCase init impl guarded sound)
    (validator (guardedVerdict guarded) statement)
    (ofWorstCase_doomed init impl guarded sound outside)
    _ (validator_costBound error _ statement) _ prover proverCost proverBound

/-- The weighted bound for inputs the prover chooses after its queries: a false
input is accepted with probability at most the prover's charge plus the sum of
the challenge rounds' errors. -/
theorem worstCase_adaptive_soundness_weighted {error : pSpec.ChallengeIdx → NNReal}
    (sound : verifier.rbrSoundnessWorstCase init impl langIn langOut error)
    (prover : OracleComp (OracleSpec.ofFn (ByLast (Raw pSpec StmtIn)))
      (StmtIn × List (Message pSpec)))
    (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨keyError (eventError (StmtIn := StmtIn) error)⟩
      proverCost) :
    Pr{let result ← (simulateQ randomOracle (Typed.experiment (absorb pSpec StmtIn)
        (validator (guardedVerdict guarded)) (initial pSpec StmtIn) prover)).run' ∅}[
      result.1 ∉ langIn ∧ Accepted (Accepts langOut) result.2.1] ≤
      proverCost + ∑ index : pSpec.ChallengeIdx, (error index : ENNReal) :=
  Typed.adaptive_soundness_weighted (ofWorstCase init impl guarded sound)
    (validator (guardedVerdict guarded)) (initial pSpec StmtIn) (initial_determined pSpec StmtIn)
    (fun statement => statement ∉ langIn)
    (fun _ outside => ofWorstCase_doomed init impl guarded sound outside) _
    (validator_costBound error _) prover proverCost proverBound

/-- Fiat–Shamir soundness of the process form for a fixed false input: a prover
with `queries` queries makes the transform accept with probability at most
`(queries + challenges) · bound`, for the number `challenges` of challenge
rounds, when every round's error is at most `bound`. -/
theorem worstCase_soundness {error : pSpec.ChallengeIdx → NNReal}
    (sound : verifier.rbrSoundnessWorstCase init impl langIn langOut error) {bound : ENNReal}
    (bounded : ∀ index, (error index : ENNReal) ≤ bound) {statement : StmtIn}
    (outside : statement ∉ langIn)
    (prover : OracleComp (OracleSpec.ofFn (ByLast (Raw pSpec StmtIn))) (List (Message pSpec)))
    (queries : ℕ) (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (Typed.fixedExperiment (absorb pSpec StmtIn)
        (validator (guardedVerdict guarded) statement) (initial pSpec StmtIn statement)
        prover)).run' ∅}[Accepted (Accepts langOut) result.1] ≤
      (queries + Fintype.card pSpec.ChallengeIdx) * bound :=
  Typed.soundness (ofWorstCase init impl guarded sound) (eventError_le bounded)
    (validator (guardedVerdict guarded) statement)
    (ofWorstCase_doomed init impl guarded sound outside)
    _ (validator_queryBound _ statement) _ prover queries proverBound

/-- Fiat–Shamir soundness of the process form for inputs the prover chooses
after its queries: a false input is accepted with probability at most
`(queries + challenges) · bound`. -/
theorem worstCase_adaptive_soundness {error : pSpec.ChallengeIdx → NNReal}
    (sound : verifier.rbrSoundnessWorstCase init impl langIn langOut error) {bound : ENNReal}
    (bounded : ∀ index, (error index : ENNReal) ≤ bound)
    (prover : OracleComp (OracleSpec.ofFn (ByLast (Raw pSpec StmtIn)))
      (StmtIn × List (Message pSpec)))
    (queries : ℕ) (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (Typed.experiment (absorb pSpec StmtIn)
        (validator (guardedVerdict guarded)) (initial pSpec StmtIn) prover)).run' ∅}[
      result.1 ∉ langIn ∧ Accepted (Accepts langOut) result.2.1] ≤
      (queries + Fintype.card pSpec.ChallengeIdx) * bound :=
  Typed.adaptive_soundness (ofWorstCase init impl guarded sound) (eventError_le bounded)
    (validator (guardedVerdict guarded)) (initial pSpec StmtIn) (initial_determined pSpec StmtIn)
    (fun statement => statement ∉ langIn)
    (fun _ outside => ofWorstCase_doomed init impl guarded sound outside) _
    (fun _ => validator_queryBound _ _) prover queries proverBound

end WorstCase

end ZkcSecurity.FiatShamir.Upstream
