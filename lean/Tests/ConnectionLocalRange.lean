module

public import Zkc.Construction.ConnectionLocalRange

@[expose] public section
set_option autoImplicit false
namespace Tests.ConnectionLocalRange
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.ConnectionLocalRange

/-- The actual closed region exits on its first invocation and returns its
induction variable, rather than its incoming carry or captured value. -/
def region : InstructionRegion :=
  ⟨[.data .index, .data .index, .data .index],
    [⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩], [3, 0]⟩

def carry (model : DomainModel) (value : Nat)
    (frame : Domain.Environment model.toCarriers) : Prop :=
  frame = [.data (.index value)]

def step (model : DomainModel) (_ index : Nat) :
    PIR.Process (Domain.effects model.toCarriers) (Bool × Nat) := .done (false, index)

noncomputable def callback (model : DomainModel) (program : Program) (context : Context)
    (caller : Domain.Environment model.toCarriers) (captured value index : Nat) :
    Original.Simulation (Yield (carry model) true [.data .index] region.yielded)
      (fun _ frame ↦ caller <+: frame) (step model value index)
      ((Domain.evaluate model program context region.instructions
        [.data (.index index), .data (.index value), .data (.index captured)]).interpret
          (Domain.withCallerFrame caller)) := by
  change Original.Simulation _ _ (.done (false, index))
    (.call (.checkpoint (caller ++
      [.data (.index index), .data (.index value), .data (.index captured)])) fun _ ↦
      .call (.checkpoint (caller ++
        [.data (.index index), .data (.index value), .data (.index captured),
          .data (.boolean false)])) fun _ ↦
        .done ([.data (.index index), .data (.index value), .data (.index captured),
          .data (.boolean false)] : Domain.Environment model.toCarriers))
  exact .checkpoint _ (List.prefix_append _ _)
    (.checkpoint _ (List.prefix_append _ _) (.done ⟨[.data (.index index)], rfl, rfl⟩))

/-- Arbitrary caller suffixes and captures use the same body certificate.
The range theorem derives final projection and skips every later iteration. -/
noncomputable def actual (model : DomainModel) (program : Program) (context : Context)
    (lo hi initial captured : Nat) (suffix : Domain.Environment model.toCarriers) :
    let caller : Domain.Environment model.toCarriers :=
      [.data (.index lo), .data (.index hi), .data (.index initial),
        .data (.index captured)] ++ suffix
    Original.Simulation
      (fun value final ↦ final = caller ++ [.data (.index value)])
      (fun _ frame ↦ caller <+: frame)
      ((Finite.fold (gated (step model)) (List.range' lo (hi - lo)) (true, initial)).bind
        fun result ↦ .done result.2)
      (Domain.executeRange program true 0 1 [2, 3] [.data .index] region
        (Domain.evaluate model program context region.instructions) caller) := by
  dsimp only
  let caller : Domain.Environment model.toCarriers :=
    [.data (.index lo), .data (.index hi), .data (.index initial),
      .data (.index captured)] ++ suffix
  have proof := simulation program true [.data .index] region
    (Domain.evaluate model program context region.instructions) (step model) (carry model)
    (fun frame ↦ caller <+: frame) caller [.data (.index captured)] (by rfl)
    (fun _ _ related ↦ by rw [related]; rfl)
    (fun value carried index related ↦ by
      cases related
      exact callback model program context caller captured value index)
    0 1 [2, 3] lo hi rfl rfl initial [.data (.index initial)] rfl rfl rfl
  simpa only [carry, exists_eq_left] using proof

theorem first_iteration (model : DomainModel) (initial index : Nat) (rest : List Nat) :
    ((Finite.fold (gated (step model)) (index :: rest) (true, initial)).bind
      fun result ↦ .done result.2) = .done index := by
  simp only [Finite.fold, gated, step, ↓reduceIte, PIR.Process.bind, fold_inactive]

theorem empty_interval (model : DomainModel) (initial : Nat) :
    ((Finite.fold (gated (step model)) [] (true, initial)).bind
      fun result ↦ .done result.2) = .done initial := rfl

def refusingRegion : InstructionRegion :=
  {region with instructions := region.instructions ++ [⟨.require "stop", [3], [], []⟩]}

/-- A reached backend refusal propagates through the connected body and the
range. It is not reclassified as a false continuation or successful completion. -/
noncomputable def refuses (model : DomainModel) (program : Program) (context : Context)
    (initial captured : Nat) :
    let caller : Domain.Environment model.toCarriers :=
      [.data (.index 0), .data (.index 1), .data (.index initial), .data (.index captured)]
    Original.Simulation
      (fun value final ↦ final = caller ++ [.data (.index value)])
      (fun _ frame ↦ caller <+: frame) (.halt .refused)
      (Domain.executeRange program true 0 1 [2, 3] [.data .index] refusingRegion
        (Domain.evaluate model program context refusingRegion.instructions) caller) := by
  dsimp only
  let caller : Domain.Environment model.toCarriers :=
    [.data (.index 0), .data (.index 1), .data (.index initial), .data (.index captured)]
  let stopped := fun (_ _ : Nat) ↦
    (PIR.Process.halt .refused : PIR.Process (Domain.effects model.toCarriers) (Bool × Nat))
  have callback : ∀ value carried index, carry model value carried →
      Original.Simulation (Yield (carry model) true [.data .index] refusingRegion.yielded)
        (fun _ frame ↦ caller <+: frame) (stopped value index)
        ((Domain.evaluate model program context refusingRegion.instructions
          (.data (.index index) :: (carried ++ [.data (.index captured)]))).interpret
            (Domain.withCallerFrame caller)) := by
    intro value carried index related
    cases related
    change Original.Simulation _ _ (.halt .refused)
      (.call (.checkpoint (caller ++
        [.data (.index index), .data (.index value), .data (.index captured)])) fun _ ↦
        .call (.checkpoint (caller ++
          [.data (.index index), .data (.index value), .data (.index captured),
            .data (.boolean false)])) fun _ ↦
          .call (.checkpoint (caller ++
            [.data (.index index), .data (.index value), .data (.index captured),
              .data (.boolean false)])) fun _ ↦ .halt .refused)
    exact .checkpoint _ (List.prefix_append _ _)
      (.checkpoint _ (List.prefix_append _ _)
        (.checkpoint _ (List.prefix_append _ _) (.halt .refused)))
  have proof := simulation program true [.data .index] refusingRegion
    (Domain.evaluate model program context refusingRegion.instructions) stopped (carry model)
    (fun frame ↦ caller <+: frame) caller [.data (.index captured)] (by rfl)
    (fun _ _ related ↦ by rw [related]; rfl) callback
    0 1 [2, 3] 0 1 rfl rfl initial [.data (.index initial)] rfl rfl rfl
  simpa [caller, carry, stopped, gated, Finite.fold, PIR.Process.bind] using proof

/-- After early exit a later refused body is not run. This uses the same gate
as the actual local range, not an assumption that all callbacks succeed. -/
theorem skips_later_refusal (model : DomainModel) (items : List Nat) (value : Nat) :
    Finite.fold (gated (fun (_ _ : Nat) ↦
      (PIR.Process.halt .refused : PIR.Process (Domain.effects model.toCarriers) (Bool × Nat))))
      items (false, value) = .done (false, value) := fold_inactive _ _ _

/-- The yield must keep its flag; swapping two actual references is rejected
even when both references exist. -/
theorem swapped_yield (model : DomainModel) (value : Nat) :
    (Domain.read (carriers := model.toCarriers)
      [.data (.boolean false), .data (.index value)] [1, 0]).bind
        (Domain.rangeResult true [.data .index]) = none := rfl

theorem wrong_flag (model : DomainModel) (value : Nat) :
    ¬ Yield (carry model) true [.data .index] [0, 1] (false, value)
      [.data (.boolean true), .data (.index value)] := by
  rintro ⟨carried, read, _⟩
  have impossible : (true : Bool) = false := congrArg Prod.fst (Option.some.inj read)
  contradiction

/-- Region formation precedes zero-trip execution. An ill-typed yield does
not become admissible just because the loop's interval is empty. -/
theorem malformed_empty (model : DomainModel) (program : Program) (context : Context) :
    let malformed := {region with yielded := [0, 3]}
    Domain.executeRange (carriers := model.toCarriers) program true 0 0 [0, 0]
      [.data .index] malformed (Domain.evaluate model program context malformed.instructions)
      [.data (.index 0)] = .halt .refused := rfl

/-- The source callback only describes the active state. Its returned index
may leave that state, and the false flag then prevents every later call. -/
def activeStep (model : DomainModel) (initial value index : Nat) :
    PIR.Process (Domain.effects model.toCarriers) (Bool × Nat) :=
  if value = initial then .done (false, index) else .halt .reject

/-- The actual region may have behavior outside the source callback's entry
predicate. The gated range does not demand correspondence on those unused
states, but it still validates the complete region and its returned tuple. -/
noncomputable def active_actual (model : DomainModel) (program : Program) (context : Context)
    (lo hi initial captured : Nat) :
    let caller : Domain.Environment model.toCarriers :=
      [.data (.index lo), .data (.index hi), .data (.index initial), .data (.index captured)]
    Original.Simulation
      (fun value final ↦ final = caller ++ [.data (.index value)])
      (fun _ frame ↦ caller <+: frame)
      ((Finite.fold (gated (activeStep model initial)) (List.range' lo (hi - lo))
        (true, initial)).bind fun result ↦ .done result.2)
      (Domain.executeRange program true 0 1 [2, 3] [.data .index] region
        (Domain.evaluate model program context region.instructions) caller) := by
  dsimp only
  let caller : Domain.Environment model.toCarriers :=
    [.data (.index lo), .data (.index hi), .data (.index initial), .data (.index captured)]
  have proof := activeSimulation program true [.data .index] region
    (Domain.evaluate model program context region.instructions) (activeStep model initial)
    (carry model) (fun value ↦ value = initial)
    (fun frame ↦ caller <+: frame) caller [.data (.index captured)] rfl
    (fun _ _ related ↦ by rw [related]; rfl)
    (fun value carried index related enabled ↦ by
      cases related
      have connected := (callback model program context caller captured value index).refineReturns
        (property := fun result ↦ result.1 = false)
        (nextReturns := fun result frame ↦ Yield (carry model) true [.data .index]
          region.yielded result frame ∧ (result.1 = true → result.2 = initial))
        rfl (fun result frame inactive returned ↦
          ⟨returned, fun active ↦ False.elim (Bool.false_ne_true (inactive.symm.trans active))⟩)
      simp only [activeStep, enabled, ↓reduceIte]
      convert connected using 1
      · rfl
      · rw [enabled]
        rfl)
    0 1 [2, 3] lo hi rfl rfl initial [.data (.index initial)] rfl rfl rfl rfl
  simpa only [carry, exists_eq_left] using proof

theorem inactive_result_is_not_reentered (model : DomainModel) :
    (Finite.fold (gated (activeStep model 0)) [1, 2, 3] (true, 0)).bind
      (fun result ↦ .done result.2) = .done 1 := by
  simp only [Finite.fold, gated, activeStep, Bool.false_eq_true, ↓reduceIte, PIR.Process.bind]

#print axioms actual
#print axioms first_iteration
#print axioms refuses
#print axioms malformed_empty
#print axioms active_actual
#print axioms inactive_result_is_not_reentered

end Tests.ConnectionLocalRange
