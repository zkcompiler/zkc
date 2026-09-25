import Tests.RelationEncoding
import Tests.RelationSparse
import Zkc.Relation.Reference

set_option autoImplicit false

namespace Tests.RelationReference

open Zkc.Relation.Reference

private def matrix := Tests.RelationSparse.matrix
private def system := Tests.RelationEncoding.system
private def binding : Binding 4 2 := .ofLayout Tests.RelationEncoding.layout

example : product matrix #[1, 2, 3, 4] = .ok #[22, 11] := by decide +kernel
example : contraction matrix #[3, 11] = .ok #[(0, 6), (3, 15), (1, 77), (2, -11)] := by decide +kernel
example : weightedValue matrix #[3, 11] #[1, 2, 3, 4] = .ok 86 := by decide +kernel
example : pointValue (r := 1) (c := 2) matrix #[2] #[3, 4] = .ok 36 := by decide +kernel

example : checkAssignment system binding #[4, 8] #[1, 4, 8, 2] = .ok true := by decide +kernel
example : checkAssignment system binding #[4, 8] #[0, 0, 0, 0] = .ok false := by decide +kernel
example : checkAssignment system binding #[8, 4] #[1, 4, 8, 2] = .ok false := by decide +kernel
example : checkAssignment system (⟨0, #v[2, 1]⟩ : Binding 4 2) #[4, 8] #[1, 4, 8, 2] =
    .ok false := by decide +kernel
example : checkAssignment system binding #[4, 8] #[1, 4, 8, 3] = .ok false := by decide +kernel

-- Canonical source data is accepted without dense conversion.
example : (do
    let m ← admitMatrix 2 4 (F := ZMod 101) #[#[(0, 2), (3, 5)], #[(1, 7), (2, -1)]]
    product m #[1, 2, 3, 4]) = .ok #[22, 11] := by decide +kernel

example : (admitRow 4 (F := ZMod 101) #[(1, 7), (1, 8)]) = .error "relation-column-order" := by decide +kernel
example : (admitRow 4 (F := ZMod 101) #[(2, 7), (1, 8)]) = .error "relation-column-order" := by decide +kernel
example : (admitRow 4 (F := ZMod 101) #[(4, 7)]) = .error "relation-column-index" := by decide +kernel
example : (admitRow 4 (F := ZMod 101) #[(1, 0)]) = .error "relation-zero-coefficient" := by decide +kernel
example : (admitRow 1048577 (F := ZMod 101) #[]) = .error "relation-limit" := by decide +kernel
example : (admitMatrix 2 4 (F := ZMod 101) #[#[]]).map (fun _ => ()) =
    .error "relation-matrix-shape" := by decide +kernel
example : (admitMatrix 1048577 1 (F := ZMod 101) #[]).map (fun _ => ()) =
    .error "relation-limit" := by decide +kernel

example : (admitBinding 4 2 0 #[1, 2]).map (fun _ => ()) = .ok () := by
  simp [admitBinding, List.mergeSort, increasing, Zkc.Algebra.FiniteVectors.limit]
  decide +kernel
example : (admitBinding 4 2 0 #[2, 1]).map (fun _ => ()) = .ok () := by
  simp [admitBinding, List.mergeSort, increasing, Zkc.Algebra.FiniteVectors.limit]
  decide +kernel
example : (admitBinding 4 2 0 #[0, 2]).map (fun _ => ()) = .error "relation-binding-alias" := by
  simp [admitBinding, List.mergeSort, increasing, Zkc.Algebra.FiniteVectors.limit]
  decide +kernel
example : (admitBinding 4 2 0 #[1, 1]).map (fun _ => ()) = .error "relation-binding-alias" := by
  simp [admitBinding, List.mergeSort, increasing, Zkc.Algebra.FiniteVectors.limit]
  decide +kernel
example : (admitBinding 4 2 4 #[1, 2]).map (fun _ => ()) = .error "relation-one-index" := by
  simp [admitBinding, List.mergeSort, increasing, Zkc.Algebra.FiniteVectors.limit]
  decide +kernel
example : (admitBinding 4 2 0 #[1, 4]).map (fun _ => ()) = .error "relation-public-index" := by
  simp [admitBinding, List.mergeSort, increasing, Zkc.Algebra.FiniteVectors.limit]
  decide +kernel
example : (admitBinding 4 2 0 #[1]).map (fun _ => ()) = .error "relation-public-shape" := by decide +kernel
example : (admitBinding 1048577 2 0 #[1, 2]).map (fun _ => ()) = .error "relation-limit" := by decide +kernel

example : product matrix #[1, 2, 3] = .error "relation-assignment-shape" := by decide +kernel
example : contraction matrix #[3] = .error "relation-row-weights-shape" := by decide +kernel
example : weightedValue matrix #[3, 11] #[1] = .error "relation-column-weights-shape" := by decide +kernel
example : pointValue (r := 1) (c := 2) matrix #[] #[3, 4] = .error "relation-row-point-shape" := by decide +kernel
example : pointValue (r := 1) (c := 2) matrix #[2] #[3] = .error "relation-column-point-shape" := by decide +kernel
example : checkAssignment system binding #[4] #[1, 4, 8, 2] = .error "relation-public-shape" := by decide +kernel
example : checkAssignment system binding #[4, 8] #[1, 4, 8] = .error "relation-assignment-shape" := by decide +kernel

end Tests.RelationReference
