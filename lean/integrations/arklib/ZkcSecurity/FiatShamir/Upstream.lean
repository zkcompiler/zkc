module

public import ZkcSecurity.FiatShamir.Lifting
public import ArkLib.OracleReduction.Security.RoundByRound

@[expose] public section

/-! Import adapters from ArkLib's round-by-round soundness.

An ArkLib verifier for a protocol specification `pSpec` with `n` rounds reads a
full transcript and outputs a statement. Its **process form** is a validator
over one operation per round (`signature`): a prover-message round receives the
round's message and a challenge round queries the round's challenge, in round
order, and the process returns the verifier's verdict on the full transcript
(`validator`). The verdict is the verifier's `Verifier.PureForm`: the adapters
read a deterministic verifier, not one that queries oracles of its own.

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
(`toFun_full`, read through the pure verdict), and the challenge round's escape
is the worst-case bound. Each challenge occurrence is charged its round's error
(`eventError`). `worstCase_soundness` and `worstCase_adaptive_soundness` are the
typed engine's bounds for the process form's transform.

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
def fullTranscript {last : Fin (n + 1)} (finish : last.val = n) (transcript : Transcript last pSpec) :
    FullTranscript pSpec :=
  cast (by
    have : last = Fin.last n := Fin.ext finish
    subst this
    rfl) transcript

/-- The process form from round `round` with transcript `transcript`, with
`remaining` rounds left: receive or query each remaining round in order, then
return the verdict on the full transcript. -/
def processFrom (verdict : FullTranscript pSpec → StmtOut) :
    (remaining : ℕ) → (round : Fin (n + 1)) → round.val + remaining = n → Transcript round pSpec →
      PIR.Proc (signature pSpec) StmtOut
  | 0, _, finish, transcript => .done (verdict (fullTranscript finish transcript))
  | remaining + 1, round, finish, transcript =>
      .call (I := signature pSpec) (⟨round.val, by omega⟩ : Fin n) fun value =>
        processFrom verdict remaining (Fin.succ (⟨round.val, by omega⟩ : Fin n)) (by simp; omega)
          (Transcript.concat (m := ⟨round.val, by omega⟩) value transcript)

/-- The process form of a verdict on a statement: from round `0` with the empty
transcript. -/
def validator (verdict : StmtIn → FullTranscript pSpec → StmtOut) (statement : StmtIn) :
    PIR.Proc (signature pSpec) StmtOut :=
  processFrom (verdict statement) n 0 (by simp) default

/-- The error of each event: a challenge round's error at its occurrence, zero
for every other event. -/
def eventError (error : pSpec.ChallengeIdx → NNReal) : Event pSpec StmtIn → ENNReal
  | .challenge round =>
      if challengeRound : pSpec.dir round = .V_to_P then error ⟨round, challengeRound⟩ else 0
  | _ => 0

section WorstCase
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type} (init : ProbComp σ)
  (impl : QueryImpl oSpec (StateT σ ProbComp)) {langIn : Set StmtIn} {langOut : Set StmtOut}
  {verifier : Verifier oSpec StmtIn StmtOut pSpec} (pure : verifier.PureForm)

/-- The doomed residuals of the process form under a state function: a
residual at some round of a false input whose state is false. -/
def Doomed (stateFunction : verifier.StateFunction init impl langIn langOut) :
    PIR.Proc (signature pSpec) StmtOut → Prop := fun process =>
  ∃ statement remaining round finish transcript, statement ∉ langIn ∧
    process = processFrom (pure.verify statement) remaining round finish transcript ∧
    ¬ stateFunction round statement transcript

omit [∀ index, SampleableType (pSpec.Challenge index)] in
/-- A full transcript at a false state is rejected: the pure verdict is outside
the output language. -/
theorem verdict_rejected (stateFunction : verifier.StateFunction init impl langIn langOut)
    (statement : StmtIn) (transcript : FullTranscript pSpec)
    (false_ : ¬ stateFunction (Fin.last n) statement transcript) :
    pure.verify statement transcript ∉ langOut := by
  intro member
  have zero := stateFunction.toFun_full statement transcript false_
  have run : (verifier.run statement transcript : OracleComp oSpec (Option StmtOut)) =
      (Pure.pure (some (pure.verify statement transcript)) : OracleComp oSpec (Option StmtOut)) := by
    simp only [Verifier.run, pure.verify_eq]
    rfl
  rw [OptionT.prEvent_mk] at zero
  simp only [run, simulateQ_pure, StateT.run'_pure'] at zero
  exact absurd zero (by simp [member])

omit [∀ index, SampleableType (pSpec.Challenge index)] in
/-- A rejected pure verdict is outside the output language with probability one:
the form of `toFun_full` a state function of a pure verifier discharges. -/
theorem prEvent_verdict_eq_zero (statement : StmtIn) (transcript : FullTranscript pSpec)
    (rejected : pure.verify statement transcript ∉ langOut) :
    Pr{let stmtOut ← OptionT.mk do
        (simulateQ impl (verifier.run statement transcript)).run' (← init)}[
      stmtOut ∈ langOut] = 0 := by
  have run : (verifier.run statement transcript : OracleComp oSpec (Option StmtOut)) =
      (Pure.pure (some (pure.verify statement transcript)) : OracleComp oSpec (Option StmtOut)) := by
    simp only [Verifier.run, pure.verify_eq]
    rfl
  rw [OptionT.prEvent_mk]
  simp only [run, simulateQ_pure, StateT.run'_pure']
  simp [rejected]

omit [∀ index, SampleableType (pSpec.Challenge index)] in
/-- The process form makes at most one query per remaining round. -/
theorem processFrom_queryBound (verdict : FullTranscript pSpec → StmtOut) :
    ∀ (remaining : ℕ) (round : Fin (n + 1)) (finish : round.val + remaining = n)
      (transcript : Transcript round pSpec) (budget : ℕ), remaining ≤ budget →
        Typed.QueryBound (absorb pSpec StmtIn) (processFrom verdict remaining round finish transcript)
          budget
  | 0, _, _, _, _, _ => trivial
  | remaining + 1, round, finish, transcript, budget, enough => by
      by_cases challengeRound : pSpec.dir (⟨round.val, by omega⟩ : Fin n) = .V_to_P
      · simp only [processFrom, Typed.QueryBound, absorb, challengeRound, ↓reduceDIte,
          Absorption.queryLast]
        exact ⟨by omega, fun value => processFrom_queryBound verdict remaining _ _ _ _
          (by omega)⟩
      · simp only [processFrom, Typed.QueryBound, absorb, challengeRound, ↓reduceDIte]
        exact fun value => processFrom_queryBound verdict remaining _ _ _ _ (by omega)

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
    Typed.Certificate (absorb pSpec StmtIn) (· ∈ langOut) (eventError error) where
  doomed := Doomed init impl pure stateFunction
  step process member := by
    obtain ⟨statement, remaining, round, finish, transcript, outside, rfl, false_⟩ := member
    cases remaining with
    | zero =>
        obtain rfl : round = Fin.last n := Fin.ext (by simpa using finish)
        exact verdict_rejected init impl pure stateFunction statement transcript false_
    | succ remaining =>
        by_cases challengeRound : pSpec.dir (⟨round.val, by omega⟩ : Fin n) = .V_to_P
        · simp only [processFrom, Typed.Step, absorb, challengeRound, ↓reduceDIte,
            Absorption.queryLast]
          intro preceding
          rw [prEvent_read (Raw pSpec StmtIn) preceding (.challenge _) fun raw =>
            ∃ value, some (decodeChallenge pSpec challengeRound raw) = some value ∧
              ¬ Doomed init impl pure stateFunction (processFrom (pure.verify statement) remaining
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
          · simp only [eventError, challengeRound, ↓reduceDIte]
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
    Doomed init impl pure stateFunction (validator pure.verify statement) :=
  ⟨statement, n, 0, by simp, default, outside, rfl, fun holds =>
    outside ((stateFunction.toFun_empty statement).mpr holds)⟩

/-- Import of worst-case round-by-round soundness: a certificate of the process
form, each challenge occurrence charged its round's error. -/
noncomputable def ofWorstCase {error : pSpec.ChallengeIdx → NNReal}
    (sound : verifier.rbrSoundnessWorstCase init impl langIn langOut error) :
    Typed.Certificate (absorb pSpec StmtIn) (· ∈ langOut) (eventError error) :=
  worstCaseCertificate init impl pure sound.choose sound.choose_spec

theorem ofWorstCase_doomed {error : pSpec.ChallengeIdx → NNReal}
    (sound : verifier.rbrSoundnessWorstCase init impl langIn langOut error)
    {statement : StmtIn} (outside : statement ∉ langIn) :
    (ofWorstCase init impl pure sound).doomed (validator pure.verify statement) :=
  validator_doomed init impl pure sound.choose outside

omit [∀ index, SampleableType (pSpec.Challenge index)] in
theorem eventError_le {error : pSpec.ChallengeIdx → NNReal} {bound : ENNReal}
    (bounded : ∀ index, (error index : ENNReal) ≤ bound) (event : Event pSpec StmtIn) :
    eventError error event ≤ bound := by
  cases event with
  | challenge round =>
      by_cases challengeRound : pSpec.dir round = .V_to_P
      · simp only [eventError, challengeRound, ↓reduceDIte]
        exact bounded _
      · simp only [eventError, challengeRound, ↓reduceDIte]
        exact zero_le
  | statement _ => exact zero_le
  | message _ _ => exact zero_le

variable [DecidableEq StmtIn] [∀ round, DecidableEq (pSpec.«Type» round)]

/-- Fiat–Shamir soundness of the process form of a worst-case round-by-round
sound verifier, for a fixed false input: a prover with `queries` queries makes
the transform accept with probability at most `(queries + n) · bound` when every
round's error is at most `bound`. -/
theorem worstCase_soundness {error : pSpec.ChallengeIdx → NNReal}
    (sound : verifier.rbrSoundnessWorstCase init impl langIn langOut error) {bound : ENNReal}
    (bounded : ∀ index, (error index : ENNReal) ≤ bound) {statement : StmtIn}
    (outside : statement ∉ langIn)
    (prover : OracleComp (OracleSpec.ofFn (ByLast (Raw pSpec StmtIn))) (List (Message pSpec)))
    (queries : ℕ) (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (Typed.fixedExperiment (absorb pSpec StmtIn)
        (validator pure.verify statement) (initial pSpec StmtIn statement) prover)).run' ∅}[
      Accepted (· ∈ langOut) result.1] ≤ (queries + n) * bound :=
  Typed.soundness (ofWorstCase init impl pure sound) (eventError_le bounded)
    (validator pure.verify statement) (ofWorstCase_doomed init impl pure sound outside) n
    (processFrom_queryBound _ n 0 _ default n le_rfl) _ prover queries proverBound

/-- Fiat–Shamir soundness of the process form for inputs the prover chooses
after its queries: a false input is accepted with probability at most
`(queries + n) · bound`. -/
theorem worstCase_adaptive_soundness {error : pSpec.ChallengeIdx → NNReal}
    (sound : verifier.rbrSoundnessWorstCase init impl langIn langOut error) {bound : ENNReal}
    (bounded : ∀ index, (error index : ENNReal) ≤ bound)
    (prover : OracleComp (OracleSpec.ofFn (ByLast (Raw pSpec StmtIn)))
      (StmtIn × List (Message pSpec)))
    (queries : ℕ) (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (Typed.experiment (absorb pSpec StmtIn)
        (validator pure.verify) (initial pSpec StmtIn) prover)).run' ∅}[
      result.1 ∉ langIn ∧ Accepted (· ∈ langOut) result.2.1] ≤ (queries + n) * bound :=
  Typed.adaptive_soundness (ofWorstCase init impl pure sound) (eventError_le bounded)
    (validator pure.verify) (initial pSpec StmtIn) (initial_determined pSpec StmtIn)
    (fun statement => statement ∉ langIn)
    (fun _ outside => ofWorstCase_doomed init impl pure sound outside) n
    (fun _ => processFrom_queryBound _ n 0 _ default n le_rfl) prover queries proverBound

end WorstCase

end ZkcSecurity.FiatShamir.Upstream
