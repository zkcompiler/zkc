module

public import Zkc.Realization.RecordLookup

@[expose] public section

namespace Tests.RecordLookup
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization.RecordLookup

abbrev layout : Layout := ⟨7, .index⟩

def inputs (model : DomainModel) (tag slot : Nat) : Domain.Environment model.toCarriers :=
  [.data (.index tag), .data (.index slot), .data ⟨.sequence .index, rfl, [13, 29]⟩]

/-- The same lookup proof is reusable under every caller prefix. -/
noncomputable def placed (model : DomainModel) (caller : Domain.Environment model.toCarriers) :
    Original.Simulation Eq (fun _ frame ↦ caller ++ inputs model 7 1 <+: frame)
      (.done (caller ++ inputs model 7 1 ++
        [.data (.index 7), .data (.boolean true), .data (.index 29)]))
      ((spine layout ⟨caller.length + 3, caller.length, caller.length + 1,
        caller.length + 2, "record"⟩).block model (caller ++ inputs model 7 1)) := by
  have derived := simulation model layout rfl (caller ++ inputs model 7 1)
    caller.length (caller.length + 1) (caller.length + 2) "record" 1 [13, 29] 29
    (by simp [inputs]) (by simp [inputs]) (by simp [inputs]) rfl (by decide)
  simpa [inputs] using derived

example : (recognize (instructions layout ⟨13, 2, 4, 9, "record"⟩)).isSome = true := by
  decide +kernel

/-- A guard which reads a caller value instead of the comparison
is not this lookup, even if some particular frame would let it return. -/
example : (recognize ((instructions layout ⟨3, 0, 1, 2, "record"⟩).set 2
    ⟨.require "record", [1], [], []⟩)).isSome = false := by decide +kernel

/-- Constructor/slot swaps are rejected by actual semantics, not only by a
syntactic inequality between fragments. -/
example (model : DomainModel) (program : Program) (context : Context) :
    (Domain.evaluate model program context (instructions layout ⟨3, 0, 1, 2, "record"⟩)
      (inputs model 1 7)).interpret Original.forgetCheckpoints = .halt .refused := by
  rw [correspondence]
  rfl

/-- A correct constructor still cannot read beyond the stored records. -/
example (model : DomainModel) (program : Program) (context : Context) :
    (Domain.evaluate model program context (instructions layout ⟨3, 0, 1, 2, "record"⟩)
      (inputs model 7 2)).interpret Original.forgetCheckpoints = .halt .refused := by
  rw [correspondence]
  rfl

#print axioms Zkc.Realization.RecordLookup.simulation
#print axioms placed
end Tests.RecordLookup
