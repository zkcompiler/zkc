import TestsClean.Control

/-! Kernel controls for the native comparison subjects.

The mutations that the control applies to the actual `toBits` export produce
exactly the artifacts that `TestsClean.Bits` refutes, so the native rows on
which a mutant disagrees with Clean (`six`, `non-boolean`) are the rows of those
kernel refutations. Emission refuses fields without an installed native identity
and artifacts that do not fit the native presentation or limits. The ring-tree
theorems are instantiated for the emitted subjects.
-/

set_option autoImplicit false

namespace TestsClean.Mutations

open ZkcClean Zkc.Relation

theorem mutants_are_refuted_artifacts :
    Control.toBitsMutations.map (fun mutation => mutation.2.apply Bits.artifact) =
      [some Bits.alteredConstant, some Bits.alteredIndex, some Bits.deletedAssertion] := by
  decide +kernel

/-- The same statement for whatever `exportComponent` returns. -/
theorem mutants_of_export {exported : Artifact}
    (h : exportComponent Bits.component = .ok exported) :
    Control.toBitsMutations.map (fun mutation => mutation.2.apply exported) =
      [some Bits.alteredConstant, some Bits.alteredIndex, some Bits.deletedAssertion] := by
  rw [Bits.exported] at h
  cases h
  exact mutants_are_refuted_artifacts

/-- Each mutant of the export is still admitted by import (formation), but is
not the export (identity); `TestsClean.Bits` refutes each correspondence. -/
theorem mutants_formed_not_identical :
    (Control.toBitsMutations.map fun mutation =>
      ((mutation.2.apply Bits.artifact).map fun mutant =>
        ((mutant.decode KoalaBear).isSome, decide (mutant = Bits.artifact)))) =
      [some (true, false), some (true, false), some (true, false)] := by
  decide +kernel

theorem mutation_refusals :
    (Mutation.constant 4 7 3).apply Bits.artifact = none ∧
    (Mutation.column 0 0 1).apply Bits.artifact = none ∧
    (Mutation.delete 5).apply Bits.artifact = none ∧
    (Mutation.constant 9 2 3).apply Bits.artifact = none := by
  decide +kernel

/-! Emission refusals. -/

def refused (presentation : PrimePresentation KoalaBear) (artifact : Artifact)
    (expected : EmissionRefusal) : Bool :=
  match admitArtifact presentation artifact with
  | .error refusal => refusal == expected
  | .ok () => false

/-- Same field, but an identity whose native modulus differs: refused, not
reinterpreted. -/
def otherIdentity : PrimePresentation KoalaBear :=
  { Control.presentation with identity := "bn254.fr" }

theorem emission_refusals :
    refused otherIdentity Bits.artifact (.unsupportedPresentation "bn254.fr" koalaBear) ∧
    refused Control.presentation { Bits.artifact with fieldSize := 7 } (.fieldSize koalaBear 7) ∧
    refused Control.presentation { Bits.artifact with assertions := [.constant koalaBear] }
      (.noncanonicalConstant koalaBear) ∧
    refused Control.presentation { Bits.artifact with assertions := [.column 5] }
      (.columnOutOfRange 5) ∧
    refused Control.presentation
      { Bits.artifact with
        assertions := [(List.range 64).foldl (fun t _ => .add t (.column 0)) (.column 0)] }
      (.limit "depth") := by
  decide +kernel

theorem emission_admitted :
    (admitArtifact Control.presentation Bits.artifact matches .ok ()) ∧
    (admitArtifact Control.presentation Nested.artifact matches .ok ()) := by
  decide +kernel

/-! The ring-tree laws for the emitted subjects. -/

theorem toBits_ring :
    List.Forall₂ (fun e (c : AIR.Constraint KoalaBear 0 Bits.artifact.width) => c.scope = .every ∧
        ∀ (statement : Fin 0 → KoalaBear) (read : Nat × Fin Bits.artifact.width → KoalaBear)
          (data : ProverData KoalaBear),
          c.expression.toRing.eval (Sum.elim statement read) =
            Expression.eval (rowEnvironment (fun column => read (0, column)) data) e)
      Bits.component.operations.constraints Bits.constraints :=
  component_ring Bits.exported Bits.decoded

theorem toBits_native :
    List.Forall₂ (fun e (t : Term) => ∀ (row : Fin 5 → KoalaBear) (data : ProverData KoalaBear),
        (t.ring KoalaBear).eval (columns row) = Expression.eval (rowEnvironment row data) e)
      Bits.component.operations.constraints Bits.artifact.assertions :=
  component_native_ring Control.presentation Bits.exported

theorem isEqual_native :
    List.Forall₂ (fun e (t : Term) => ∀ (row : Fin 8 → KoalaBear) (data : ProverData KoalaBear),
        (t.ring KoalaBear).eval (columns row) = Expression.eval (rowEnvironment row data) e)
      Nested.component.operations.constraints Nested.artifact.assertions :=
  component_native_ring Control.presentation Nested.exported

end TestsClean.Mutations
