module

public import Zkc.Realization.QueryResumption

@[expose] public section
set_option autoImplicit false
namespace Tests.QueryResumption
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Realization QueryResumption

def placement (start : Nat) : Placement :=
  ⟨start, 6, 5, ⟨0, 1, 2, 3, 4⟩, ⟨10, 11, 12, 13, 14⟩, 8, 9,
    "phase", "kind", !["constructor", "instance", "position", "continuation", "frame"]⟩

def environment (model : DomainModel) (phase kind : Nat) (pending supplied : Coordinates)
    (answers : List Nat) (answer : Nat) : Domain.Environment model.toCarriers :=
  [.data (.index pending.constructor), .data (.index pending.anchorInstance),
   .data (.index pending.position), .data (.index pending.continuation),
   .data (.index pending.continuationInstance), .data (.index kind), .data (.index phase),
   .data (.index 0), .data ⟨.sequence .index, rfl, answers⟩, .data (.index answer),
   .data (.index supplied.constructor), .data (.index supplied.anchorInstance),
   .data (.index supplied.position), .data (.index supplied.continuation),
   .data (.index supplied.continuationInstance)]

/-- One common law serves this unrelated index-valued client under every
caller suffix. No coordinate or arena contents are fixed by the proof. -/
theorem actual (model : DomainModel) (program : Program) (context : Context)
    (phase kind : Nat) (pending supplied : Coordinates) (answers : List Nat) (answer : Nat)
    (suffix : Domain.Environment model.toCarriers) :
    let frame := environment model phase kind pending supplied answers answer ++ suffix
    Nonempty (Original.Simulation Eq (fun _ live ↦ frame <+: live)
      (resumed model .index rfl frame 0 phase kind pending supplied answers answer)
      (Domain.evaluate model program context
        (instructions .index 0 (placement frame.length)) frame)) := by
  dsimp only
  rw [correspondence]
  apply simulation model .index rfl 0 (by decide) _ _ rfl
  · exact Original.read_append rfl suffix
  · exact Original.read_append rfl suffix
  · exact (RequiredIndices.Readback.cons rfl rfl
      (.cons rfl rfl (.cons rfl rfl (.cons rfl rfl (.cons rfl rfl .nil))))).extended suffix
  · exact Original.read_append rfl suffix
  · exact Original.read_append rfl suffix

def pending : Coordinates := ⟨3, 5, 7, 11, 13⟩
def swapped : Coordinates := ⟨3, 5, 7, 13, 11⟩

theorem coordinates_distinct : ¬ RequiredIndices.Accepted (pairs pending swapped) := by
  intro accepted
  have same := (accepted_iff pending swapped).mp accepted
  have impossible : (11 : Nat) = 13 := congrArg Coordinates.continuation same.1
  contradiction

/-- A same-typed parent/instance swap is a semantic refusal, even when the
arena is already exhausted. Requirement failure occurs first. -/
theorem swapped_before_exhaustion (model : DomainModel)
    (frame : Domain.Environment model.toCarriers) (answers : List Nat) (answer : Nat) :
    resumed model .index rfl frame 0 2 0 pending swapped answers answer =
      .halt .refused := by
  simp only [resumed, ite_eq_right coordinates_distinct]
  norm_num [RequiredIndices.Accepted, indexLimit]

/-- The refusal is connected to the complete constructed instruction block,
with arbitrary answer contents and untouched caller suffix. -/
theorem actual_swap_refuses (model : DomainModel) (program : Program) (context : Context)
    (answers : List Nat) (answer : Nat) (suffix : Domain.Environment model.toCarriers) :
    let frame := environment model 2 0 pending swapped answers answer ++ suffix
    Nonempty (Original.Simulation Eq (fun _ live ↦ frame <+: live) (.halt .refused)
      (Domain.evaluate model program context
        (instructions .index 0 (placement frame.length)) frame)) := by
  simpa only [swapped_before_exhaustion] using
    actual model program context 2 0 pending swapped answers answer suffix

theorem invalid_self_comparison (model : DomainModel)
    (frame : Domain.Environment model.toCarriers) (answers : List Nat) (answer : Nat) :
    let invalid : Coordinates := { pending with position := indexLimit }
    resumed model .index rfl frame 0 2 0 invalid invalid answers answer = .halt .refused := by
  have refused : ¬ RequiredIndices.Accepted
      (pairs { pending with position := indexLimit } { pending with position := indexLimit }) := by
    rw [accepted_iff]
    simp [Coordinates.Bounded, Coordinates.values]
  dsimp only
  simp only [resumed, ite_eq_right refused]
  norm_num [RequiredIndices.Accepted, indexLimit]

theorem completed_phase_refused (model : DomainModel)
    (frame : Domain.Environment model.toCarriers) (answer : Nat) :
    resumed model .index rfl frame 0 3 0 pending pending [] answer = .halt .refused := by
  simp [resumed, RequiredIndices.Accepted]

theorem wrong_kind_refused (model : DomainModel)
    (frame : Domain.Environment model.toCarriers) (answer : Nat) :
    resumed model .index rfl frame 0 2 1 pending pending [] answer = .halt .refused := by
  simp [resumed, RequiredIndices.Accepted, indexLimit]

theorem admitted_exhaustion (model : DomainModel)
    (frame : Domain.Environment model.toCarriers) (answers : List Nat) (answer : Nat)
    (full : ¬ answers.length < indexLimit) :
    resumed model .index rfl frame 0 2 0 pending pending answers answer =
      .halt .exhausted := by
  simp only [resumed, ite_eq_right full]
  norm_num [RequiredIndices.Accepted, pairs, Coordinates.values, pending, indexLimit]

theorem accepted_answer (model : DomainModel) (frame : Domain.Environment model.toCarriers)
    (answer : Nat) :
    resumed model .index rfl frame 0 2 0 pending pending [31, 37] answer =
      .done (frame ++ checkResults 0 ++
        [.data (.index 2), .data ⟨.sequence .index, rfl, [31, 37, answer]⟩, .data (.index 1)]) := by
  simp [resumed, RequiredIndices.Accepted, pairs, Coordinates.values, pending,
    indexLimit, answerResults]

theorem full_body_recognized :
    (recognizeAt 15 (instructions .index 0 (placement 15))).isSome = true := by decide +kernel

-- A false association is not repaired by making every compared value share a type.
theorem wrong_comparison_rejected :
    (recognizeAt 15 ((instructions .index 0 (placement 15)).set 2
      ⟨.require "phase", [15], [], []⟩)).isNone = true := by decide +kernel

theorem wrong_append_arena_rejected :
    (recognizeAt 15 ((instructions .index 0 (placement 15)).set 17
      ⟨.execute (.sequenceAppend .index), [7, 9], [.data (.sequence .index)], []⟩)).isNone = true :=
  by decide +kernel

theorem wrong_return_phase_rejected :
    (recognizeAt 15 ((instructions .index 0 (placement 15)).set 18
      ⟨.execute (.indexConstant 2), [], [.data .index], []⟩)).isNone = true := by decide +kernel

#print axioms actual
#print axioms accepted_answer
#print axioms swapped_before_exhaustion
#print axioms invalid_self_comparison
#print axioms actual_swap_refuses
end Tests.QueryResumption
