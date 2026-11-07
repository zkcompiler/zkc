module

public import Zkc.Construction.ConnectionLocalBranch

@[expose] public section
set_option autoImplicit false
namespace Tests.ConnectionLocalBranch
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.ConnectionLocalBranch

def declared : List ValueSort := [.data .index, .data .index]

def yes : InstructionRegion := ⟨declared, [], [1, 0]⟩

def no : InstructionRegion :=
  ⟨declared,
    [⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩,
     ⟨.require "refuse-selected", [2], [], []⟩], [0, 1]⟩

def relation (model : DomainModel) (value : Nat × Nat)
    (results : Domain.Environment model.toCarriers) : Prop :=
  results = [.data (.index value.1), .data (.index value.2)]

noncomputable def actual (model : DomainModel) (program : Program) (context : Context)
    (left right : Nat) (condition : Bool) (suffix : Domain.Environment model.toCarriers) :
    let environment : Domain.Environment model.toCarriers :=
      [.data (.boolean condition), .data (.index left), .data (.index right)] ++ suffix
    Original.Simulation
      (fun value final ↦ final = environment ++
        [.data (.index value.1), .data (.index value.2)])
      (fun _ frame ↦ ArtifactBinding.Captures environment frame)
      (if condition then .done (right, left) else .halt .refused)
      (Domain.View.localBranch program 0 [1, 2] declared yes no
        (Domain.evaluate model program context yes.instructions)
        (Domain.evaluate model program context no.instructions) environment) := by
  dsimp only
  let captured : Domain.Environment model.toCarriers :=
    [.data (.index left), .data (.index right)]
  have yesConnected : Original.Simulation (Returns (relation model) declared yes.yielded)
      (fun _ frame ↦ ArtifactBinding.Captures captured frame)
      (.done (right, left))
      (Domain.evaluate model program context yes.instructions captured) :=
    .done ⟨[.data (.index right), .data (.index left)], rfl, rfl, rfl⟩
  have noConnected : Original.Simulation (Returns (relation model) declared no.yielded)
      (fun _ frame ↦ ArtifactBinding.Captures captured frame)
      (.halt .refused)
      (Domain.evaluate model program context no.instructions captured) := by
    change Original.Simulation _ _ (.halt .refused)
      (.call (.checkpoint captured) fun _ ↦
        .call (.checkpoint (captured ++ [.data (.boolean false)])) fun _ ↦
          .call (.checkpoint (captured ++ [.data (.boolean false)])) fun _ ↦ .halt .refused)
    exact .checkpoint _ (ArtifactBinding.captures_append _ [])
      (.checkpoint _ (ArtifactBinding.captures_append _ _)
        (.checkpoint _ (ArtifactBinding.captures_append _ _) (.halt .refused)))
  have connected := simulation program (.done (right, left)) (.halt .refused)
    (Domain.evaluate model program context yes.instructions)
    (Domain.evaluate model program context no.instructions) yes no (relation model)
    ([.data (.boolean condition), .data (.index left), .data (.index right)] ++ suffix)
    captured condition 0 [1, 2] declared rfl rfl rfl rfl rfl yesConnected noConnected
  cases condition <;> simpa only [Bool.false_eq_true, ↓reduceIte,
    PIR.Process.interpret, relation, exists_eq_left] using connected

/-- Both arms are formed before selection. A malformed dormant yield is
rejected even when the selected source arm and its outputs are valid. -/
theorem malformed_dormant (model : DomainModel) (program : Program) (context : Context) :
    let malformed := {no with yielded := [0]}
    Domain.View.localBranch program 0 [1, 2] declared yes malformed
      (Domain.evaluate model program context yes.instructions)
      (Domain.evaluate model program context malformed.instructions)
      [.data (.boolean true), .data (.index 10), .data (.index 20)] = .halt .refused := rfl

/-- The output relation retains order even though both elements have the
same physical sort. The branch's actual swap is not an identity projection. -/
theorem output_order (model : DomainModel) :
    ¬ Returns (relation model) declared yes.yielded (10, 20)
      [.data (.index 10), .data (.index 20)] := by
  rintro ⟨results, read, _, associated⟩
  have selected : results = [.data (.index 20), .data (.index 10)] :=
    (Option.some.inj read).symm
  rw [selected] at associated
  have impossible : (some 20 : Option Nat) = some 10 :=
    congrArg (fun (values : Domain.Environment model.toCarriers) ↦
      values.head?.bind fun value ↦ match value with
        | .data ⟨.index, _, number⟩ => some number
        | _ => none) associated
  contradiction

#print axioms actual
#print axioms malformed_dormant
#print axioms output_order
end Tests.ConnectionLocalBranch
