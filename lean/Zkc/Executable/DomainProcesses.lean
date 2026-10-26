module

public import Zkc.Executable.Observations
public import Zkc.Construction.Uniform.DomainHandler

@[expose] public section

/-! Continuation laws over the canonical open Process. These proofs quantify
over all replies, including malformed proof heads and stopped oracle replies.
They do not inspect constructed Instructions. -/
set_option autoImplicit false

namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source
open Zkc.Construction.Uniform
variable {F G : Type} {m : Type → Type} [Monad m]

/-- Every continuation reached after consuming the supplied proof, for all
typed action replies. Stops impose no continuation obligation. Query replies
are universally quantified; a mapped-handler refusal can only remove an
obligation. This predicate carries no numerical relation-validity premise. -/
def Continues {A : Type} :
    PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A → Proof F G →
      (A → Proof F G → Prop) → Prop
  | .done value, proof, holds => holds value proof
  | .halt _, _, _ => True
  | .call (.receive ty ..) next, proof, holds =>
      match proof with
      | [] => True
      | payload :: unread =>
          match Value.decode ty (.data payload) with
          | some value => Continues (next value) unread holds
          | none => True
  | .call (.query ..) next, proof, holds => ∀ reply, Continues (next reply) proof holds
  | .call (.localService ..) _, _, _ => True
  | .call (.send ..) next, proof, holds |
    .call (.observe ..) next, proof, holds |
    .call (.checkpoint ..) next, proof, holds => Continues (next ()) proof holds

theorem Continues.mono {A : Type}
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (proof : Proof F G) (first second : A → Proof F G → Prop)
    (implies : ∀ value unread, first value unread → second value unread)
    (holds : Continues process proof first) : Continues process proof second := by
  induction process generalizing proof with
  | done => exact implies _ _ holds
  | halt => trivial
  | call operation next ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => trivial
          | cons payload unread =>
              cases decoded : Value.decode ty (.data payload) with
              | none => simp only [Continues, decoded]
              | some value =>
                  simpa only [Continues, decoded] using
                    ih value unread (by simpa only [Continues, decoded] using holds)
      | send | observe | checkpoint => exact ih () proof holds
      | localService => trivial
      | query => exact fun reply => ih reply proof (holds reply)

/-- Handler congruence at the complete reached state, including the unread
proof. It is independent of the construction instruction vocabulary. -/
theorem runK_congr_continues {A R : Type} (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (proof : Proof F G) (property : A → Proof F G → Prop)
    (holds : Continues process proof property)
    (next next' : A → Proof F G → m (PIR.Outcome R × Proof F G))
    (agree : ∀ value unread, property value unread → next value unread = next' value unread) :
    DomainAdapter.runK key initial challenge process proof next =
      DomainAdapter.runK key initial challenge process proof next' := by
  induction process generalizing proof with
  | done value => exact agree value proof holds
  | halt => rfl
  | call operation continuation ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => rfl
          | cons payload unread =>
              simp only [DomainAdapter.runK]
              cases decoded : Value.decode ty (.data payload) with
              | none => rfl
              | some value => exact ih value unread (by simpa only [Continues, decoded] using holds)
      | send | observe | checkpoint => exact ih () proof holds
      | localService => rfl
      | query history origin =>
          simp only [DomainAdapter.runK]
          split
          · congr 1
            funext answer
            cases answer with
            | stopped => rfl
            | returned value => exact ih value proof (holds value)
          · rfl

/-- Pruning a continuation preserves the exact preceding oracle actions. -/
theorem runK_prunes {A R : Type} (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (proof : Proof F G)
    (next next' : A → Proof F G → m (PIR.Outcome R × Proof F G))
    (continues : ∀ value unread, Prunes Stopped (next value unread) (next' value unread)) :
    Prunes Stopped (DomainAdapter.runK key initial challenge process proof next)
      (DomainAdapter.runK key initial challenge process proof next') := by
  induction process generalizing proof with
  | done value => exact continues value proof
  | halt => exact .refl _
  | call operation continuation ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => exact .refl _
          | cons payload unread =>
              simp only [DomainAdapter.runK]
              cases Value.decode ty (.data payload) with
              | none => exact .refl _
              | some value => exact ih value unread
      | send | observe | checkpoint => exact ih () proof
      | localService => exact .refl _
      | query history origin =>
          simp only [DomainAdapter.runK]
          split
          · apply Prunes.bind
            intro answer
            cases answer with
            | stopped => exact .refl _
            | returned value => exact ih value proof
          · exact .refl _

/-- A sufficient postcondition only needs to hold at values the Process can
actually yield. This includes every typed reply, without an honest-input or
relation-validity restriction. -/
theorem runK_congr {A R : Type} (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (property : A → Prop) (yields : PIR.Yields property process)
    (next next' : A → Proof F G → m (PIR.Outcome R × Proof F G))
    (agree : ∀ value unread, property value → next value unread = next' value unread)
    (proof : Proof F G) :
    DomainAdapter.runK key initial challenge process proof next =
      DomainAdapter.runK key initial challenge process proof next' :=
  DomainAdapter.runK_congr_yields key initial challenge process property yields next next' agree proof

end Zkc.Executable.DomainVM
