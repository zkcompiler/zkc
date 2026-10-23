import ZkcSecurity.Obligations.Derivation
import Tests.Obligations

set_option autoImplicit false
noncomputable section
namespace TestsSecurity.Obligations
open OracleComp OracleSpec Zkc.Transcript Zkc.Obligations
open ZkcSecurity.Obligations

theorem bit_escape (history : List Unit) :
    boundedEscape (Raw := fun _ : Unit => Bool) (fun _ _ => (2 : ENNReal)⁻¹)
      history () (fun bit => bit = true) := by
  change Pr{let bit ← $ᵗ Bool}[bit = true] ≤ (2 : ENNReal)⁻¹
  rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_bool, Nat.cast_ofNat]

/-- Nonzero local escape, with an actual probability proof. -/
def query_derived (history : List Unit) :
    Derivation Tests.Obligations.queryBit (boundedEscape (fun _ _ => (2 : ENNReal)⁻¹))
      (fun reached value => reached = history ++ [()] ∧ value = false)
      history Tests.Obligations.echo := by
  refine .query rfl (fun bit => bit = true) (bit_escape history) ?_
  intro raw value decoded outside
  cases decoded
  cases raw with
  | false => exact .done ⟨rfl, rfl⟩
  | true => exact (outside rfl).elim

example (history : List Unit) :
    (reduction Tests.Obligations.queryBit
      (fun reached value => reached = history ++ [()] ∧ value = false)
      (fun _ _ => (2 : ENNReal)⁻¹)).doomed history Tests.Obligations.echo :=
  derived_doomed (query_derived history)

example (history : List Unit) :
    (chargedCapability Tests.Obligations.queryBit
      (fun reached value => reached = history ++ [()] ∧ value = false)
      (fun _ _ => (2 : ENNReal)⁻¹)).Export (history, Tests.Obligations.echo) :=
  exportCapability (query_derived history)

/-- The guard/call/loop slice is interpreted through the general boundary. -/
example (allowed : Bool) (count : Nat) (history : List Nat) (state : Nat × Nat)
    (charge : List Nat → Nat → ENNReal) :
    (reduction Tests.Obligations.sendInterface
      (fun reached result => result.1 = state.1 + count + 1 ∧ result.2 = state.2 ∧
        reached.length = history.length + count + 1) charge).doomed history
      (Tests.Obligations.slice allowed count state) :=
  interpret (fun _ _ _ impossible => impossible.elim)
    (Tests.Obligations.slice_derived allowed count history state)

/-- A canonical bad event with probability one cannot be charged at zero. -/
theorem invalid_probability_refused (history : List Unit) :
    ¬ boundedEscape (Raw := fun _ : Unit => Bool) (fun _ _ => 0) history () (fun _ => True) := by
  change ¬ Pr{let _ ← $ᵗ Bool}[True] ≤ (0 : ENNReal)
  rw [prEvent_true_eq_one]
  exact not_le_of_gt (by simp)

/-- No proof object can conceal that invalid escape by choosing a different cut. -/
theorem invalid_query_refused :
    ¬ Nonempty (Derivation Tests.Obligations.queryBit (boundedEscape (fun _ _ => 0))
      (fun _ _ => False) [] Tests.Obligations.echo) := by
  rintro ⟨derivation⟩
  have reading := derived_doomed derivation
  change Pr{let raw ← $ᵗ Bool}[∃ value, some raw = some value ∧ ¬ False] ≤ (0 : ENNReal) at reading
  have total : Pr{let raw ← $ᵗ Bool}[∃ value, some raw = some value ∧ ¬ False] = 1 :=
    (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr fun raw => ⟨raw, rfl, id⟩
  rw [total] at reading
  exact (not_le_of_gt (by simp : (0 : ENNReal) < 1)) reading

/- Soundness of an always-stopping process is vacuous; successful acceptance
still fails. This is deliberately not a completeness consumer. -/
example (history : List Unit) :
    Nonempty (Derivation Tests.Obligations.queryBit (boundedEscape (fun _ _ => 0))
      (fun _ (_ : Bool) => False) history (.halt .reject)) := ⟨.halt .reject⟩

example : ¬ Accepted (fun _ : Bool => True) (.stopped .reject) := fun accepted => accepted

end TestsSecurity.Obligations

#print axioms ZkcSecurity.Obligations.interpret
#print axioms ZkcSecurity.Obligations.nonempty_iff_reduction
#print axioms ZkcSecurity.Obligations.exportCapability
#print axioms TestsSecurity.Obligations.query_derived
