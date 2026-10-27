module

public import Zkc.Executable.DomainSuccess
public import Zkc.Source.Finite

@[expose] public section

/-! Success rules for the actual deterministic Domain Process handler. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type} (key : Origin → Origin) (initial : History F G) (oracle : History F G → F)

theorem Passes.mono {A : Type}
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (proof : Proof F G) (first second : A → Proof F G → Prop)
    (weaker : ∀ value unread, first value unread → second value unread)
    (passes : Passes key initial oracle process proof first) : Passes key initial oracle process proof second := by
  induction process generalizing proof with
  | done => exact weaker _ _ passes
  | halt => exact False.elim passes
  | call operation next ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => exact False.elim passes
          | cons payload unread =>
              cases decoded : Value.decode ty (.data payload) with
              | none => simp only [Passes, decoded] at passes
              | some value => simpa only [Passes, decoded] using ih value unread (by simpa only [Passes, decoded] using passes)
      | query history origin =>
          simp only [Passes] at passes ⊢
          obtain ⟨draw, passes⟩ := passes
          refine ⟨draw, ?_⟩
          cases reply : DomainAdapter.query (m := Id) key initial oracle history origin with
          | stopped reason => simp only [reply] at passes
          | returned value => simpa only [reply] using ih value proof (by simpa only [reply] using passes)
      | localService => exact False.elim passes
      | send | observe | checkpoint => exact ih () proof passes

theorem Passes.bind {A B : Type}
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (next : A → PIR.Process (Domain.effects (Structured.uniformCarriers F G)) B)
    (proof : Proof F G) (holds : B → Proof F G → Prop) :
    Passes key initial oracle (process.bind next) proof holds =
      Passes key initial oracle process proof (fun value unread => Passes key initial oracle (next value) unread holds) := by
  induction process generalizing proof with
  | done => rfl
  | halt => rfl
  | call operation continuation ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => rfl
          | cons payload unread =>
              cases decoded : Value.decode ty (.data payload) <;> simp [Passes, PIR.Process.bind, decoded, ih]
      | query history origin =>
          simp only [PIR.Process.bind, Passes]
          cases reply : DomainAdapter.query (m := Id) key initial oracle history origin <;> simp [ih]
      | send | observe | checkpoint => exact ih () proof
      | localService => rfl

/-- A proof-stream invariant composes an arbitrary ordered fold, including
zero trips. Success of each actual step must be constructed by the caller. -/
theorem Passes.fold {A S : Type}
    (step : S → A → PIR.Process (Domain.effects (Structured.uniformCarriers F G)) S)
    (invariant : List A → S → Proof F G → Prop)
    (next : ∀ item rest state proof, invariant (item :: rest) state proof →
      Passes key initial oracle (step state item) proof (fun state unread => invariant rest state unread)) :
    ∀ items state proof, invariant items state proof →
      Passes key initial oracle (Finite.fold step items state) proof
        (fun state unread => invariant [] state unread) := by
  intro items
  induction items with
  | nil => intro state proof valid; exact valid
  | cons item rest ih =>
      intro state proof valid
      rw [Finite.fold, Passes.bind]
      exact Passes.mono key initial oracle _ _ _ _ (fun state unread valid => ih state unread valid)
        (next item rest state proof valid)

/-- Administrative checkpoints do not change deterministic success or unread
messages. The projection preserves every other actual operation. -/
theorem Passes.forgetCheckpoints {A : Type}
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (proof : Proof F G) (holds : A → Proof F G → Prop) :
    Passes key initial oracle (process.interpret Original.forgetCheckpoints) proof holds =
      Passes key initial oracle process proof holds := by
  induction process generalizing proof with
  | done => rfl
  | halt => rfl
  | call operation next ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => rfl
          | cons payload unread =>
              cases decoded : Value.decode ty (.data payload) <;>
                simp [PIR.Process.interpret, Original.forgetCheckpoints, PIR.Process.bind, Passes, decoded, ih]
      | query history origin =>
          simp only [PIR.Process.interpret, Original.forgetCheckpoints, PIR.Process.bind, Passes]
          cases reply : DomainAdapter.query (m := Id) key initial oracle history origin <;> simp [ih]
      | send | observe | checkpoint =>
          simpa only [PIR.Process.interpret, Original.forgetCheckpoints, PIR.Process.bind, Passes] using ih () proof
      | localService => rfl

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A successful schema-checked participant supplies success of its canonical
Code observation at the same returned references. Both use Domain.evaluate. -/
theorem Passes.participant_observation (program : Structured.Program) (context : Context)
    (artifact : Participant) (env : Environment F G) (proof : Proof F G)
    (holds : Environment F G → Proof F G → Prop)
    (passes : Passes key initial oracle
      (((Domain.participant (Structured.ringModel F G) program context artifact env).bind
        (fun result => .done result.values)).interpret Original.forgetCheckpoints) proof holds) :
    Passes key initial oracle (observation program context artifact.instructions artifact.returned env) proof holds := by
  rw [Passes.forgetCheckpoints] at passes
  unfold observation
  rw [Passes.forgetCheckpoints]
  simp only [Domain.participant, PIR.Process.bind, Passes] at passes
  by_cases sorted : Domain.sortsMatch artifact.inputs env = true
  · simp only [sorted, ite_true, PIR.Process.bind_assoc, Passes.bind] at passes
    unfold outcome
    rw [Passes.bind]
    apply Passes.mono key initial oracle _ _ _ _ ?_ passes
    intro final unread valid
    unfold readback
    cases readEq : Domain.read final artifact.returned with
    | none => simp only [readEq, Passes] at valid
    | some returned =>
        simp only [readEq, Passes] at valid ⊢
        split at valid
        · exact valid
        · exact False.elim valid
  · simp only [sorted, Bool.false_eq_true, ite_false, PIR.Process.bind, Passes] at passes

end Zkc.Executable.DomainVM
