import ZkcSecurity.ProgramLogic.Transcript.Typed
import TestsSecurity.Counterexamples.Support

/-! An averaged round-by-round certificate offered at import.

A validator receives one bit, then draws a challenge; the residual after the
draw depends on the absorbed bit: after the bit `1` every answer leaves the
doomed set, after the bit `0` none does. Averaged over a uniform bit, the escape
probability is `1 / 2` (`averaged_escape`), yet the per-prefix local obligation
of a typed certificate fails at that error (`perPrefix_fails`): after the bit `1`
it is one (`escape_after_one`). The import format admits worst-case, per-prefix
errors only; an averaged bound does not give the step the soundness theorems
consume.
-/

namespace TestsSecurity.Counterexamples.Imports
open OracleComp ZkcSecurity.FiatShamir
open TestsSecurity.Counterexamples
open scoped ENNReal

inductive Op where
  | message
  | draw

abbrev signature : PIR.Signature where
  Op := Op
  Reply
    | .message => Fin 2
    | .draw => Bool

inductive Event where
  | message (bit : Fin 2)
  | draw
  deriving DecidableEq

abbrev Raw : Event → Type := fun _ => Fin 2

def recoverMessage : Event → Option (Fin 2)
  | .message bit => some bit
  | .draw => none

/-- The draw reads its raw bit as a Boolean. -/
def absorb : Typed.Interface signature Event (Fin 2) Raw
  | .message => .receive Event.message recoverMessage
  | .draw => .query .draw fun raw => some (decide (raw = 1))

/-- After the bit `bit`, draw and return whether the bit was `1`. -/
def drawing (bit : Fin 2) : PIR.Process signature Bool := .call Op.draw fun _ => .done (decide (bit = 1))

def validator : PIR.Process signature Bool := .call Op.message drawing

def accepts (accepted : Bool) : Prop := accepted = true

/-- Before the bit, before the draw, a rejecting result and every stop. -/
def doomed (process : PIR.Process signature Bool) : Prop :=
  process = validator ∨ (∃ bit, process = drawing bit) ∨ process = .done false ∨
    ∃ stop, process = .halt stop

/-- The escape probability of the draw after the absorbed bit. -/
noncomputable def escape (bit : Fin 2) : ENNReal :=
  Pr{let raw ← $ᵗ (Fin 2)}[∃ value, some (decide (raw = 1)) = some value ∧
    ¬ doomed (.done (decide (bit = 1)))]

theorem done_true_not_doomed : ¬ doomed (.done true) := by
  rintro (same | ⟨_, same⟩ | same | ⟨_, same⟩) <;> cases same

theorem escape_after_one : escape 1 = 1 := by
  unfold escape
  exact (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr fun _ =>
    ⟨_, rfl, by simpa using done_true_not_doomed⟩

theorem escape_after_zero : escape 0 = 0 := by
  unfold escape
  refine prEvent_eq_zero_of_forall_not _ _ fun _ ⟨_, _, outside⟩ => outside ?_
  exact Or.inr (Or.inr (Or.inl rfl))

/-- Averaged over a uniform bit, the draw escapes with probability `1 / 2`. -/
theorem averaged_escape : (escape 0 + escape 1) / 2 = 1 / 2 := by
  rw [escape_after_zero, escape_after_one, zero_add]

/-- The per-prefix obligation fails at error `1 / 2`. -/
theorem perPrefix_fails : ¬ Typed.Step absorb doomed accepts (fun _ => 1 / 2) (drawing 1) := by
  intro step
  change escape 1 ≤ 1 / 2 at step
  rw [escape_after_one] at step
  exact absurd step (by rw [not_le]; numerals)

end TestsSecurity.Counterexamples.Imports
