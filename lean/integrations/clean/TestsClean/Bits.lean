import ZkcClean.Specification
import TestsClean.KoalaBear
import Clean.Gadgets.Bits

/-! Main control: upstream `Gadgets.toBits 4` as a flat AIR component over
KoalaBear. It has four bit outputs, nested Boolean and Equality subcircuits, a
`forEach` loop and the constants 0, 1, 2, 4, 8 and -1.

Source-side evaluations use `constraintsHold_iff_flatten`, which involves
neither the exporter nor the zkc relation. zkc-side evaluations use the imported
constraints. Both are kernel evaluations (`decide +kernel`).
-/

set_option autoImplicit false

namespace TestsClean.Bits

open ZkcClean Zkc.Relation

def component : Air.Flat.Component KoalaBear := ⟨Gadgets.toBits 4 (by norm_num)⟩

/-- `-1` in its canonical KoalaBear presentation. -/
abbrev minusOne : Nat := koalaBear - 1

def booleanity (column : Nat) : Term :=
  .mul (.column column) (.add (.column column) (.mul (.constant minusOne) (.constant 1)))

def recomposition (one two : Nat) (weightTwo : Nat) : Term :=
  .add (.column 0) (.mul (.constant minusOne)
    (.add (.add (.add (.add (.constant 0) (.mul (.column one) (.constant 1)))
      (.mul (.column two) (.constant weightTwo))) (.mul (.column 3) (.constant 4)))
      (.mul (.column 4) (.constant 8))))

/-- The exact exported relation: x = b1 + 2 b2 + 4 b3 + 8 b4, each bᵢ Boolean. -/
def artifact : Artifact :=
  { fieldSize := koalaBear, width := 5,
    assertions := [booleanity 1, booleanity 2, booleanity 3, booleanity 4,
      recomposition 1 2 2] }

theorem exported : exportComponent component = .ok artifact := by decide +kernel

def constraints : List (AIR.Constraint KoalaBear 0 artifact.width) :=
  (artifact.decode KoalaBear).getD []

theorem decoded : artifact.decode KoalaBear = some constraints := by
  have admitted : (artifact.decode KoalaBear).isSome = true := by decide +kernel
  obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.mp admitted
  simp only [constraints, hcs, Option.getD_some]

/-- Theorem (2) for this component, for every trace and every prover data. -/
theorem correspondence {height : Nat} (trace : Fin (height + 1) → Fin 5 → KoalaBear)
    (data : ProverData KoalaBear) :
    (AIR.family constraints height).holds noPublic trace ↔
      ∀ row, component.operations.ConstraintsHold (rowEnvironment (trace row) data) :=
  holds_iff exported decoded noPublic trace data

/-- Theorem (3) for this component: the upstream specification per row. -/
theorem specification {height : Nat} (trace : Fin (height + 1) → Fin 5 → KoalaBear)
    (holds : (AIR.family constraints height).holds noPublic trace)
    (row : Fin (height + 1)) (data : ProverData KoalaBear) :
    component.Spec (rowEnvironment (trace row) data) :=
  row_spec exported decoded noPublic trace holds row data trivial

theorem lookupFree : FlatOperation.lookups (flatten component.operations) = [] :=
  List.eq_nil_of_length_eq_zero (by decide +kernel)

/-! Honest and invalid rows. -/

def six : Fin 5 → KoalaBear := ![6, 0, 1, 1, 0]
def thirteen : Fin 5 → KoalaBear := ![13, 1, 0, 1, 1]
def fifteen : Fin 5 → KoalaBear := ![15, 1, 1, 1, 1]
/-- The bits recompose to 7, not 6. -/
def wrongBit : Fin 5 → KoalaBear := ![6, 1, 1, 1, 0]
/-- -2 + 2·1 = 0, but -2 is not a bit. -/
def nonBoolean : Fin 5 → KoalaBear := ![0, -2, 1, 0, 0]
/-- No four bits recompose to 16. -/
def sixteen : Fin 5 → KoalaBear := ![16, 0, 0, 0, 0]

def honestTrace : Fin 3 → Fin 5 → KoalaBear := ![six, thirteen, fifteen]
def invalidTrace : Fin 3 → Fin 5 → KoalaBear := ![six, wrongBit, fifteen]

theorem honest_zkc : (AIR.family constraints 2).holds noPublic honestTrace := by
  change ∀ c ∈ constraints, c.Holds noPublic honestTrace
  unfold AIR.Constraint.Holds
  decide +kernel

theorem honest_clean :
    ∀ row, component.operations.ConstraintsHold (rowEnvironment (honestTrace row) noData) := by
  intro row
  rw [constraintsHold_iff_flatten lookupFree]
  revert row
  decide +kernel

theorem invalid_zkc : ¬ (AIR.family constraints 2).holds noPublic invalidTrace := by
  change ¬ ∀ c ∈ constraints, c.Holds noPublic invalidTrace
  unfold AIR.Constraint.Holds
  decide +kernel

theorem invalid_clean :
    ¬ component.operations.ConstraintsHold (rowEnvironment (invalidTrace 1) noData) := by
  rw [constraintsHold_iff_flatten lookupFree]
  decide +kernel

/-- Each single invalid row is rejected by both evaluations. -/
theorem invalid_rows_agree :
    (¬ (AIR.family constraints 0).holds noPublic (fun _ => nonBoolean) ∧
      ¬ component.operations.ConstraintsHold (rowEnvironment nonBoolean noData)) ∧
    (¬ (AIR.family constraints 0).holds noPublic (fun _ => sixteen) ∧
      ¬ component.operations.ConstraintsHold (rowEnvironment sixteen noData)) := by
  simp only [constraintsHold_iff_flatten lookupFree]
  change (¬ (∀ c ∈ constraints, c.Holds noPublic fun _ => nonBoolean) ∧ _) ∧
    (¬ (∀ c ∈ constraints, c.Holds noPublic fun _ => sixteen) ∧ _)
  unfold AIR.Constraint.Holds
  decide +kernel

/-! Mutated artifacts. Each is well formed for import, but its identity differs
from the export and the correspondence fails on a concrete trace. -/

def alteredConstant : Artifact :=
  { artifact with assertions := [booleanity 1, booleanity 2, booleanity 3, booleanity 4,
      recomposition 1 2 3] }

def alteredIndex : Artifact :=
  { artifact with assertions := [booleanity 1, booleanity 2, booleanity 3, booleanity 4,
      recomposition 2 2 2] }

def deletedAssertion : Artifact :=
  { artifact with assertions := [booleanity 2, booleanity 3, booleanity 4,
      recomposition 1 2 2] }

theorem mutations_distinct :
    alteredConstant ≠ artifact ∧ alteredIndex ≠ artifact ∧ deletedAssertion ≠ artifact ∧
    exportComponent component ≠ .ok alteredConstant ∧
    exportComponent component ≠ .ok alteredIndex ∧
    exportComponent component ≠ .ok deletedAssertion := by
  rw [exported]
  decide +kernel

def alteredConstantConstraints : List (AIR.Constraint KoalaBear 0 5) :=
  (alteredConstant.decode KoalaBear).getD []
def alteredIndexConstraints : List (AIR.Constraint KoalaBear 0 5) :=
  (alteredIndex.decode KoalaBear).getD []
def deletedAssertionConstraints : List (AIR.Constraint KoalaBear 0 5) :=
  (deletedAssertion.decode KoalaBear).getD []

theorem mutations_admitted :
    (alteredConstant.decode KoalaBear).isSome ∧ (alteredIndex.decode KoalaBear).isSome ∧
    (deletedAssertion.decode KoalaBear).isSome := by
  decide +kernel

/-- Correspondence of a candidate import with the component on all one-row traces. -/
def Corresponds (candidate : List (AIR.Constraint KoalaBear 0 5)) : Prop :=
  ∀ trace : Fin 1 → Fin 5 → KoalaBear,
    (AIR.family candidate 0).holds noPublic trace ↔
      ∀ row, component.operations.ConstraintsHold (rowEnvironment (trace row) noData)

theorem exported_corresponds : Corresponds constraints :=
  fun trace => correspondence trace noData

theorem six_clean : component.operations.ConstraintsHold (rowEnvironment six noData) := by
  rw [constraintsHold_iff_flatten lookupFree]
  decide +kernel

/-- Weight 3 instead of 2 rejects the honest decomposition of 6. -/
theorem alteredConstant_refuted : ¬ Corresponds alteredConstantConstraints := by
  intro h
  have accepted := (h fun _ => six).mpr fun _ => six_clean
  revert accepted
  change ¬ ∀ c ∈ alteredConstantConstraints, c.Holds noPublic fun _ => six
  unfold AIR.Constraint.Holds
  decide +kernel

/-- Reading b2 in place of b1 rejects the honest decomposition of 6. -/
theorem alteredIndex_refuted : ¬ Corresponds alteredIndexConstraints := by
  intro h
  have accepted := (h fun _ => six).mpr fun _ => six_clean
  revert accepted
  change ¬ ∀ c ∈ alteredIndexConstraints, c.Holds noPublic fun _ => six
  unfold AIR.Constraint.Holds
  decide +kernel

/-- Without booleanity of b1, the non-Boolean decomposition of 0 is accepted. -/
theorem deletedAssertion_refuted : ¬ Corresponds deletedAssertionConstraints := by
  intro h
  have accepted : (AIR.family deletedAssertionConstraints 0).holds noPublic fun _ => nonBoolean := by
    change ∀ c ∈ deletedAssertionConstraints, c.Holds noPublic fun _ => nonBoolean
    unfold AIR.Constraint.Holds
    decide +kernel
  have rejected : ¬ component.operations.ConstraintsHold (rowEnvironment nonBoolean noData) := by
    rw [constraintsHold_iff_flatten lookupFree]
    decide +kernel
  exact rejected ((h fun _ => nonBoolean).mp accepted 0)

end TestsClean.Bits
