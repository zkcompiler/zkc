module

public import Zkc.Construction.ConnectionLocalRangeProgress

@[expose] public section
set_option autoImplicit false
namespace Tests.LocalRangeCompletion
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ConnectionLocalRange

/-- A closed callback stores Request (two) and computes its actual continuation
comparison. The range's source state is related to the physical phase slot. -/
def region : InstructionRegion :=
  ⟨[.data .index, .data .index],
    [⟨.calculate (.indexConstant 2), [], [.data .index], []⟩,
     ⟨.execute .indexLess, [2, 2], [.data .boolean], []⟩], [3, 2]⟩

def step (carriers : Carriers) (_value _index : Nat) :
    PIR.Process (Domain.effects carriers) (Bool × Nat) := .done (false, 2)

def related (carriers : Carriers) (value : Nat) (frame : Domain.Environment carriers) : Prop :=
  frame = [.data (.index value)]

noncomputable def callback (model : DomainModel) (program : Program) (context : Context)
    (caller : Domain.Environment model.toCarriers) (value index : Nat) :
    Original.Simulation (Yield (related model.toCarriers) true [.data .index] region.yielded)
      (fun _ frame ↦ caller <+: frame) (step model.toCarriers value index)
      ((Domain.evaluate model program context region.instructions
        [.data (.index index), .data (.index value)]).interpret
          (Domain.withCallerFrame caller)) := by
  change Original.Simulation _ _ (.done (false, 2))
    (.call (.checkpoint (caller ++ [.data (.index index), .data (.index value)])) fun _ ↦
      .call (.checkpoint (caller ++
        [.data (.index index), .data (.index value), .data (.index 2)])) fun _ ↦
      .call (.checkpoint (caller ++
        [.data (.index index), .data (.index value), .data (.index 2)])) fun _ ↦
      .call (.checkpoint (caller ++
        [.data (.index index), .data (.index value), .data (.index 2),
          .data (.boolean false)])) fun _ ↦
        .done ([.data (.index index), .data (.index value), .data (.index 2),
          .data (.boolean false)] : Domain.Environment model.toCarriers))
  exact .checkpoint _ (List.prefix_append _ _) (.checkpoint _ (List.prefix_append _ _)
    (.checkpoint _ (List.prefix_append _ _) (.checkpoint _ (List.prefix_append _ _)
      (.done ⟨[.data (.index 2)], rfl, rfl⟩))))

/-- Completion reaches the actual carried phase and complete output layout,
at arbitrary caller suffixes and loop lower bounds. -/
noncomputable def actual (model : DomainModel) (program : Program) (context : Context)
    (lo hi initial : Nat) (nonempty : lo < hi)
    (suffix : Domain.Environment model.toCarriers) :
    let caller : Domain.Environment model.toCarriers :=
      [.data (.index lo), .data (.index hi), .data (.index initial)] ++ suffix
    Original.Simulation
      (fun value final ↦ value = 2 ∧ final = caller ++ [.data (.index 2)])
      (fun _ frame ↦ caller <+: frame)
      ((Finite.fold (gated (step model.toCarriers)) (List.range' lo (hi - lo))
        (true, initial)).bind fun result ↦ .done result.2)
      (Domain.executeRange program true 0 1 [2] [.data .index] region
        (Domain.evaluate model program context region.instructions) caller) := by
  dsimp only
  let caller : Domain.Environment model.toCarriers :=
    [.data (.index lo), .data (.index hi), .data (.index initial)] ++ suffix
  have body := simulation program true [.data .index] region
    (Domain.evaluate model program context region.instructions) (step model.toCarriers)
    (related model.toCarriers) (fun frame ↦ caller <+: frame) caller [] rfl
    (fun _ _ holds ↦ by rw [holds]; rfl)
    (fun value carried index holds ↦ by
      cases holds
      exact callback model program context caller value index)
    0 1 [2] lo hi rfl rfl initial [.data (.index initial)] rfl rfl rfl
  have progress : StepProgress (step model.toCarriers) (fun _ ↦ True) (fun _ ↦ 0) := by
    intro value index _
    exact ⟨trivial, by simp⟩
  apply completedSimulation progress (finished := fun value ↦ value = 2)
    (fun _ _ _ ↦ ⟨trivial, fun _ ↦ rfl⟩) (List.range' lo (hi - lo)) initial trivial
    (by simpa only [List.length_range'] using Nat.sub_pos_of_lt nonempty) body
  rintro value final _ phase ⟨carried, holds, output⟩
  refine ⟨phase, ?_⟩
  rw [output, holds, phase]

/-- Progress alone allows an early false flag at Return (one). The completion
condition cannot be inferred from this certificate or from a larger budget. -/
def premature (carriers : Carriers) (_value _index : Nat) :
    PIR.Process (Domain.effects carriers) (Bool × Nat) := .done (false, 1)

theorem premature_progress (carriers : Carriers) :
    StepProgress (premature carriers) (fun _ ↦ True) (fun _ ↦ 0) := by
  intro value index _
  exact ⟨trivial, by simp⟩

theorem premature_not_complete (carriers : Carriers) :
    ¬ PIR.Yields (fun value ↦ value = 2)
      ((Finite.fold (gated (premature carriers)) [4, 5, 6] (true, 0)).bind
        fun result ↦ .done result.2) := by
  simp [Finite.fold, gated, premature, PIR.Process.bind, PIR.Yields]

/-- A proved source property never permits connecting to a new target value. -/
theorem phase_swap_rejected (carriers : Carriers) :
    IsEmpty (Original.Simulation
      (fun (source target : Nat) ↦ source = 2 ∧ target = source)
      (fun (_ : PIR.Process (Domain.effects carriers) Nat) _ ↦ True)
      (.done 2) (.done 1)) := by
  constructor
  intro certificate
  cases certificate with
  | done equal => omega

#print axioms actual
#print axioms premature_not_complete
#print axioms phase_swap_rejected
#print axioms Original.Simulation.refineReturns
#print axioms fold_completed
end Tests.LocalRangeCompletion
