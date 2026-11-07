module

public import Zkc.Realization.QueryFinish
public import Tests.OracleProcessData

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.QueryFinish
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization
open OracleProcessData QueryFinish

def placement : Placement := ⟨4, 0, 1, 3, 2, "completed", "root-kind"⟩
def body := instructions .index placement

abbrev checked : Recognized body [8] := ⟨.index, placement, rfl, rfl⟩

theorem recognized : recognize 4 body [8] = some checked := by kernel_rfl

def environment (phase kind slot : Nat) (answers : List Nat) :
    Domain.Environment model.toCarriers :=
  [.data (.index phase), .data (.index kind), .data (.index slot),
    .data ⟨.sequence .index, rfl, answers⟩]

/-- The same actual-body theorem covers success and all finish refusals.
No successful answer lookup or projected-output equation is a premise. -/
theorem complete_output (program : Program) (context : Context) (phase kind slot : Nat)
    (answers : List Nat) :
    Nonempty (Original.Simulation
      (fun (value : model.Value .index) (output : Domain.Environment model.toCarriers) ↦
        output = [.data ⟨.index, rfl, value⟩])
      (fun _ frame ↦ environment phase kind slot answers <+: frame)
      (answer model .index phase kind answers slot)
      ((Domain.evaluate model program context body (environment phase kind slot answers)).bind
        fun final ↦ match Domain.read final [8] with
        | some values => .done values
        | none => .halt .refused)) := by
  convert checked.output model program context rfl (environment phase kind slot answers) rfl
    phase kind slot answers rfl rfl rfl rfl using 1
  kernel_rfl

theorem returns_root_answer : answer model .index 3 0 [10, 20] 1 = .done (20 : Nat) := by
  simp [answer, RequiredIndices.Accepted, indexLimit]

/-- A present answer cannot authorize early completion or a different kind. -/
theorem early_finish_refused : answer model .index 1 0 [20] 0 = .halt .refused := by
  simp [answer, RequiredIndices.Accepted]

theorem wrong_kind_refused : answer model .index 3 1 [20] 0 = .halt .refused := by
  simp [answer, RequiredIndices.Accepted]

theorem missing_answer_refused : answer model .index 3 0 ([] : List Nat) 0 = .halt .refused := by
  simp [answer, RequiredIndices.Accepted]

/-- For an index-valued root, the phase constant is a same-typed result cell.
Returning it instead of the answer must fail checked installation. -/
theorem wrong_output_refused : recognize 4 body [4] = none := by decide +kernel

theorem early_guard_refused :
    recognize 4 (RequiredIndices.constantInstructions 4 0 1 "completed" ++
      RequiredIndices.constantInstructions 6 1 0 "root-kind" ++
      [⟨.execute (.sequenceAt .index), [3, 2], [.data .index], []⟩]) [8] = none := by
  decide +kernel

#print axioms complete_output
#print axioms recognized
#print axioms returns_root_answer
#print axioms early_finish_refused
#print axioms wrong_kind_refused
#print axioms missing_answer_refused
#print axioms wrong_output_refused
#print axioms early_guard_refused
end Tests.QueryFinish
