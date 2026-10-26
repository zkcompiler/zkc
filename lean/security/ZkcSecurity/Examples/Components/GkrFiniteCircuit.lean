module

public import ZkcSecurity.Examples.Components.GkrCallerRealization
public import Zkc.Protocols.Gkr.Circuit
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The two-wire, two-layer arithmetic circuit behind the selected gate trial:
inputs (3,5), intermediate wires (8,15), and outputs (120,30). The operational
list realization is connected to the independent circuit evaluator below. -/
set_option autoImplicit false
namespace ZkcSecurity.Examples.Components.GkrFiniteCircuit
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Protocols.Gkr

variable {F : Type} [Field F]

def inputTable : Table F 1 := fun bits => if bits 0 then 5 else 3

def addWiring (layer : Nat) : Wiring F 1 := fun bits =>
  if layer = 0 then (if bits 0 && bits 1 && bits 2 then 1 else 0)
  else (if !bits 0 && !bits 1 && bits 2 then 1 else 0)

def mulWiring (layer : Nat) : Wiring F 1 := fun bits =>
  if layer = 0 then (if !bits 0 && !bits 1 && bits 2 then 1 else 0)
  else (if bits 0 && !bits 1 && bits 2 then 1 else 0)

theorem lower_layer : layer (addWiring (F := F) 1) (mulWiring 1) inputTable =
    GkrCallerRealization.below := by
  funext bits
  cases h : bits 0 <;>
    norm_num [layer, gates, sumTable, productTable, booleanSum, half,
      Quadratic.point, front, back, inputTable, addWiring, mulWiring,
      GkrCallerRealization.below, h] <;>
    norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]

theorem outputs : values (addWiring (F := F)) mulWiring inputTable 2 0 =
    (fun bits => if bits 0 then 30 else 120) := by
  rw [values_succ, show values (addWiring (F := F)) mulWiring inputTable 1 1 =
    GkrCallerRealization.below from lower_layer]
  funext bits
  cases h : bits 0 <;>
    norm_num [layer, gates, sumTable, productTable, booleanSum, half,
      Quadratic.point, front, back, addWiring, mulWiring,
      GkrCallerRealization.below, h] <;>
    norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]

/-- At every field point, not only at the Boolean cube, the actual circuit's
output extension is the total used by the selected four-factor reference. -/
theorem reference_total (rho : F) :
    extension 1 (values addWiring mulWiring inputTable 2 0) (fun _ => rho) =
      GkrRoundsReference.total (GkrCallerRealization.reference rho) := by
  rw [outputs, GkrCallerRealization.total_eq]
  norm_num [extension, Fin.cons]
  ring

/-- The inactive wire factor stays independent at both actual active-variable
stages, including after an arbitrary first field challenge. -/
theorem active_independence (rho : F) :
    GkrRoundsReference.independent (GkrCallerRealization.reference rho) ∧
      ∀ challenge, GkrRoundsReference.independent
        (GkrRoundsReference.restrict (GkrCallerRealization.reference rho) challenge) := by
  have admissible := (GkrCallerRealization.represented rho).2.1
  exact ⟨admissible.1, fun challenge => (admissible.2 challenge).1⟩

theorem degree_two (rho : F) :
    ((GkrRoundsReference.data F).polynomial (GkrCallerRealization.reference rho)).natDegree ≤ 2 :=
  GkrRoundsReference.laws.degree_le _ (GkrCallerRealization.represented rho).2.1

end ZkcSecurity.Examples.Components.GkrFiniteCircuit
