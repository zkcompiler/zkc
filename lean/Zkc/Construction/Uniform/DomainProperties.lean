module

public import Zkc.Construction.Uniform.DomainExecution

@[expose] public section
/-! Outcome projection laws for the Domain Process property handler. -/
set_option autoImplicit false
namespace Zkc.Construction.Uniform.DomainAdapter
variable {F G : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

def postOutcome {A B : Type} (finish : A → PIR.Outcome B) : PIR.Outcome A → PIR.Outcome B
  | .stopped reason => .stopped reason
  | .returned value => finish value

/-- A partial ABI projection may refuse a return; it cannot alter an earlier
stop or the unread suffix. -/
theorem run_postOutcome {A R : Type} (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F) (finish : A → PIR.Outcome R)
    (process : PIR.Process (Domain.effects (Source.Structured.uniformCarriers F G)) A)
    (proof : Proof F G) :
    (fun result => (postOutcome finish result.1, result.2)) <$>
        run key initial challenge process proof =
      runK key initial challenge process proof (fun value unread => pure (finish value, unread)) := by
  simp only [run]
  induction process generalizing proof with
  | done => simp [runK, postOutcome]
  | halt => simp [runK, postOutcome]
  | call operation continuation ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => simp [runK, postOutcome]
          | cons payload unread =>
              simp only [runK]
              cases Value.decode ty (.data payload) with
              | none => simp [postOutcome]
              | some value => exact ih value unread
      | send | observe | checkpoint => exact ih () proof
      | localService => simp [runK, postOutcome]
      | query history origin =>
          simp only [runK]
          split
          · rw [map_bind]
            congr 1
            funext answer
            cases answer with
            | stopped => simp [postOutcome]
            | returned value => exact ih value proof
          · simp [postOutcome]

theorem runK_mapOutcome {A R S : Type} (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F) (f : R → S)
    (process : PIR.Process (Domain.effects (Source.Structured.uniformCarriers F G)) A)
    (proof : Proof F G) (next : A → Proof F G → m (PIR.Outcome R × Proof F G)) :
    (fun result => (mapOutcome f result.1, result.2)) <$>
        runK key initial challenge process proof next =
      runK key initial challenge process proof
        (fun value unread => (fun result => (mapOutcome f result.1, result.2)) <$> next value unread) := by
  induction process generalizing proof with
  | done => rfl
  | halt => simp [runK, mapOutcome]
  | call operation continuation ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => simp [runK, mapOutcome]
          | cons payload unread =>
              simp only [runK]
              cases Value.decode ty (.data payload) with
              | none => simp [mapOutcome]
              | some value => exact ih value unread
      | send | observe | checkpoint => exact ih () proof
      | localService => simp [runK, mapOutcome]
      | query history origin =>
          simp only [runK]
          split
          · rw [map_bind]
            congr 1
            funext answer
            cases answer with
            | stopped => simp [mapOutcome]
            | returned value => exact ih value proof
          · simp [mapOutcome]

end Zkc.Construction.Uniform.DomainAdapter
