module

public import Zkc.Realization.QueryInitialize
public import Tests.OracleProcessData

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.QueryInitialize
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization
open OracleProcessData QueryInitialize

def types : List Ty := [.index, .boolean, .index]
def body := instructions "reference" 1 types
def returned := outputReferences 3 0 types
abbrev checked : Recognized body returned := ⟨"reference", 1, 3, 0, types, rfl, rfl⟩

theorem recognized : recognize 3 body returned = some checked := by kernel_rfl

def environment (constructor anchorInstance position : Nat) :
    Domain.Environment model.toCarriers :=
  [.data (.index position),
    .data ⟨CaptureLayout.referenceType "reference", rfl, (constructor, anchorInstance, ())⟩,
    .data (.index 999)]

/-- Caller data may have the same type as any header field. The checked body
still obtains the exact supplied constructor, instance and query position. -/
theorem complete_output (program : Program) (context : Context)
    (constructor anchorInstance position : Nat) :
    Nonempty (Original.Simulation Eq
      (fun _ frame ↦ environment constructor anchorInstance position <+: frame)
      (.done (initialState model constructor anchorInstance position types))
      ((Domain.evaluate model program context body
        (environment constructor anchorInstance position)).bind fun final ↦
          match Domain.read final returned with
          | some values => .done values
          | none => .halt .refused)) := by
  exact checked.output model program context (by
    intro type member
    simp [types] at member
    rcases member with rfl | rfl | rfl <;> rfl)
    (environment constructor anchorInstance position) rfl
    constructor anchorInstance position rfl rfl

/-- The recognizer rejects swapping two equal-typed reference coordinates. -/
theorem swapped_header_refused :
    recognize 3 body [4, 3, 0, 5, 5, 5, 5, 5, 6, 7, 8] = none := by decide +kernel

/-- Two index arenas are still separate ordered stores. -/
theorem swapped_arenas_refused :
    recognize 3 body [3, 4, 0, 5, 5, 5, 5, 5, 8, 7, 6] = none := by decide +kernel

theorem nonzero_phase_refused :
    recognize 3 (RecordProjection.instructions (referenceLayout "reference") 1
      (RecordProjection.allFields CaptureLayout.referenceFields) ++
        ⟨.execute (.indexConstant 1), [], [.data .index], []⟩ :: emptyInstructions types)
      returned = none := by decide +kernel

theorem root_state : initialState model 9 4 17 types =
    [.data (.index 9), .data (.index 4), .data (.index 17),
      .data (.index 0), .data (.index 0), .data (.index 0), .data (.index 0), .data (.index 0),
      .data ⟨.sequence .index, rfl, ([] : List Nat)⟩,
      .data ⟨.sequence .boolean, rfl, ([] : List Bool)⟩,
      .data ⟨.sequence .index, rfl, ([] : List Nat)⟩] := by kernel_rfl

#print axioms complete_output
#print axioms recognized
#print axioms swapped_header_refused
#print axioms swapped_arenas_refused
#print axioms nonzero_phase_refused
#print axioms root_state
end Tests.QueryInitialize
