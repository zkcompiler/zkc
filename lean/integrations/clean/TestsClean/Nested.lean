import ZkcClean.Specification
import TestsClean.KoalaBear
import Clean.Gadgets.IsEqual

/-! Nested positive control: upstream `Gadgets.IsEqual` over pairs. Its four
assertions sit three subcircuit levels deep (component body, `IsZero`,
`IsZeroField`) and are produced by a `foldlRange` loop; the component's own
operation list has no shallow assertion at all.
-/

set_option autoImplicit false

namespace TestsClean.Nested

open ZkcClean Zkc.Relation

def component : Air.Flat.Component KoalaBear :=
  ⟨(Gadgets.IsEqual.circuit (F := KoalaBear) (α := fields 2)).isGeneralFormalCircuit⟩

abbrev minusOne : Nat := koalaBear - 1

/-- `b - (1 - (x - y) z) = 0` for the difference of one coordinate pair. -/
def inverseRelation (x y z b : Nat) : Term :=
  .add (.column b) (.mul (.constant minusOne) (.add (.constant 1) (.mul (.constant minusOne)
    (.mul (.add (.column x) (.mul (.constant minusOne) (.column y))) (.column z)))))

/-- `b (x - y) - 0 = 0`. -/
def zeroProduct (x y b : Nat) : Term :=
  .add (.mul (.column b) (.add (.column x) (.mul (.constant minusOne) (.column y))))
    (.mul (.constant minusOne) (.constant 0))

/-- Columns: inputs x₀ x₁ y₀ y₁, then (inverse, flag) per coordinate. -/
def artifact : Artifact :=
  { fieldSize := koalaBear, width := 8,
    assertions := [inverseRelation 0 2 4 5, zeroProduct 0 2 5,
      inverseRelation 1 3 6 7, zeroProduct 1 3 7] }

theorem exported : exportComponent component = .ok artifact := by decide +kernel

theorem nested_only : component.operations.shallowConstraints = [] :=
  List.eq_nil_of_length_eq_zero (by decide +kernel)

/-- Theorem (2) for this component, for every trace and every prover data. -/
theorem correspondence {cs : List (AIR.Constraint KoalaBear 0 artifact.width)}
    (decoded : artifact.decode KoalaBear = some cs) {height : Nat}
    (trace : Fin (height + 1) → Fin 8 → KoalaBear) (data : ProverData KoalaBear) :
    (AIR.family cs height).holds noPublic trace ↔
      ∀ row, component.operations.ConstraintsHold (rowEnvironment (trace row) data) :=
  holds_iff exported decoded noPublic trace data

end TestsClean.Nested
