import ZkcSecurity.FiatShamir.Typed
import TestsSecurity.Counterexamples.Support

/-! An averaged round-by-round certificate offered at import.

A validator receives one bit, then draws a challenge whose decoding depends on
the absorbed prefix: after the bit `1` every answer leaves the doomed set, after
the bit `0` none does. Averaged over a uniform bit, the escape probability is
`1 / 2` (`averaged_escape`), yet the per-prefix local obligation of a typed
certificate fails at that error (`perPrefix_fails`): after the bit `1` it is one
(`escape_after_one`). The import format admits worst-case, per-prefix errors
only; an averaged bound does not give the step the soundness theorems consume.
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

abbrev Raw : List Event → Type := fun _ => Fin 2

def recoverMessage : Event → Option (Fin 2)
  | .message bit => some bit
  | .draw => none

/-- After the bit `1` the decoded value accepts; otherwise it rejects. -/
def decodeAfter (preceding : List Event) (_raw : Fin 2) : Option Bool :=
  if preceding = [.message 1] then some true else some false

def absorb : Typed.Interface signature Event (Fin 2) Raw
  | .message => .receive Event.message recoverMessage
  | .draw => .query .draw decodeAfter

def drawing : PIR.Proc signature Bool := .call Op.draw fun accepted => .done accepted

def validator : PIR.Proc signature Bool := .call Op.message fun _ => drawing

def accepts (accepted : Bool) : Prop := accepted = true

/-- Before the bit, before the draw, a rejecting result and every stop. -/
def doomed (process : PIR.Proc signature Bool) : Prop :=
  process = validator ∨ process = drawing ∨ process = .done false ∨ ∃ stop, process = .halt stop

/-- The escape probability of the draw after an absorbed prefix. -/
noncomputable def escape (preceding : List Event) : ENNReal :=
  Pr{let raw ← $ᵗ (Fin 2)}[∃ value, decodeAfter preceding raw = some value ∧
    ¬ doomed (.done value)]

theorem done_true_not_doomed : ¬ doomed (.done true) := by
  rintro (same | same | same | ⟨_, same⟩) <;> cases same

theorem escape_after_one : escape [.message 1] = 1 := by
  unfold escape
  exact (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr fun _ =>
    ⟨true, by simp [decodeAfter], done_true_not_doomed⟩

theorem escape_after_zero : escape [.message 0] = 0 := by
  unfold escape
  refine prEvent_eq_zero_of_forall_not _ _ fun _ ⟨value, decoded, outside⟩ => outside ?_
  have rejecting : decodeAfter [.message 0] 0 = some false := by decide
  rw [show decodeAfter [.message 0] = fun _ => some false from funext fun _ => rejecting] at decoded
  cases Option.some.inj decoded
  exact Or.inr (Or.inr (Or.inl rfl))

/-- Averaged over a uniform bit, the draw escapes with probability `1 / 2`. -/
theorem averaged_escape : (escape [.message 0] + escape [.message 1]) / 2 = 1 / 2 := by
  rw [escape_after_zero, escape_after_one, zero_add]

/-- The per-prefix obligation fails at error `1 / 2`. -/
theorem perPrefix_fails : ¬ Typed.Step absorb doomed accepts (fun _ => 1 / 2) drawing := by
  intro step
  have bound := step [.message 1]
  change escape [.message 1] ≤ 1 / 2 at bound
  rw [escape_after_one] at bound
  exact absurd bound (by rw [not_le]; numerals)

end TestsSecurity.Counterexamples.Imports
