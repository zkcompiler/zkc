import ZkcSecurity.Transformations.FiatShamir.ProviderSimulation

/-! Controls for the provider simulator laws.

A split-hash simulator satisfies every law (`splitHash`). A grinding attempt for
the nonce `n` is two primitive calls, `(n, false)` and `(n, true)`, declared to
make up one attempt, and both are answered from one ideal answer, a pair of
values in `Fin 2`. On every run the two halves of one nonce are answered from
one ideal answer, whichever half comes first and whatever calls come between
them (`halves_share`), and the second half called first makes the attempt's
TranscriptQuery (`second_half_first`).

The laws exclude the simulators that would charge an attempt less than once or
more than once: a start state that already records an answer violates
`recorded_start` (`preloaded_not_empty`), and an assignment of every call to a
fresh attempt numbered by a counter violates `attempt_record`
(`counter_not_persistent`).
-/

set_option autoImplicit false

namespace TestsSecurity.ProviderSimulation
open OracleComp OracleSpec ZkcSecurity.FiatShamir.Provider

/-- A primitive call: a nonce and the half of the split hash it asks. -/
abbrev Call := Fin 2 × Bool

abbrev primitive : OracleSpec Call := Call →ₒ Fin 2

/-- The ideal answer of a nonce: both halves. -/
abbrev Ideal (_ : Fin 2) : Type := Fin 2 × Fin 2

/-- The split-hash simulator: both halves of a nonce belong to the nonce's
attempt, and each half reads its component of the attempt's ideal answer. -/
def splitHash : Simulator primitive Ideal Unit where
  State := (nonce : Fin 2) → Option (Fin 2 × Fin 2)
  start _ := fun _ => none
  attempt _ call := some call.1
  recorded state key := state key
  record state key answer := Function.update state key (some answer)
  shared call _ ideal := if call.2 then ideal.2 else ideal.1
  respond state _ := (0, state)
  together first second := first.1 = second.1
  recorded_start _ _ := rfl
  recorded_record state key answer := by simp
  recorded_record_of_ne state key other answer different := by simp [different]
  recorded_respond _ _ _ := rfl
  attempt_record _ _ _ _ _ assigned := assigned
  attempt_respond _ _ _ _ assigned := assigned
  attempt_together _ _ _ same := by simp [same]

theorem splitHash_attempt {trace : List (Answered primitive (Fin 2))} {state : splitHash.State}
    (runs : splitHash.Runs () trace state) : ∀ entry ∈ trace, entry.attempt = some entry.query.1 := by
  induction runs with
  | start => simp
  | step _ _ ih =>
      intro entry member
      rcases List.mem_append.mp member with old | new
      · exact ih entry old
      · rw [List.mem_singleton] at new
        subst new
        rfl

/-- The two halves of one nonce share one ideal answer on every run, in either
order and with any calls between them. -/
theorem halves_share {trace : List (Answered primitive (Fin 2))} {state : splitHash.State}
    (runs : splitHash.Runs () trace state) {first second : Answered primitive (Fin 2)}
    (firstIn : first ∈ trace) (secondIn : second ∈ trace)
    (sameNonce : first.query.1 = second.query.1) :
    ∃ ideal, first.reply = splitHash.shared first.query first.query.1 ideal ∧
      second.reply = splitHash.shared second.query first.query.1 ideal :=
  Simulator.Runs.shared_answer splitHash runs firstIn secondIn
    (splitHash_attempt runs first firstIn)
    ((splitHash_attempt runs second secondIn).trans (congrArg some sameNonce.symm))

/-- The second half called first makes the attempt's TranscriptQuery. -/
theorem second_half_first :
    (splitHash.handle (0, true)).run (splitHash.start ()) =
      (fun ideal => (splitHash.shared (0, true) 0 ideal, splitHash.record (splitHash.start ()) 0 ideal)) <$>
        liftM ((OracleSpec.ofFn Ideal).query 0) :=
  Simulator.Runs.first_call splitHash Simulator.Runs.start rfl (by simp)

/-- A start state that records an answer. -/
def preloaded : (nonce : Fin 2) → Option (Fin 2 × Fin 2) := fun _ => some (0, 0)

theorem preloaded_not_empty : ¬ ∀ key, preloaded key = none := by
  intro empty
  cases empty 0

/-- An assignment of every call to the attempt numbered by the calls before it,
and the recording that advances the counter. -/
def counterAttempt (state : ℕ) (_ : Call) : Option ℕ := some state

def counterRecord (state : ℕ) (_ : ℕ) (_ : Fin 2) : ℕ := state + 1

theorem counter_not_persistent : ¬ ∀ state key answer query attemptKey,
    counterAttempt state query = some attemptKey →
      counterAttempt (counterRecord state key answer) query = some attemptKey := by
  intro persists
  have moved := persists 0 0 0 (0, false) 0 rfl
  simp [counterAttempt, counterRecord] at moved

end TestsSecurity.ProviderSimulation
