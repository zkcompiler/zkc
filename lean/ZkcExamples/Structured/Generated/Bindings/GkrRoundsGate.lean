module

public import ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks
public import Zkc.Protocols.AlgebraicRounds.Gate

@[expose] public section

/-! Generated actual-helper gate equations. This is not a full GKR theorem. -/
namespace ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings
open Zkc.Protocols.AlgebraicRounds
open ZkcExamples.Structured.Generated.Bindings.GkrRounds
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option smartUnfolding false
noncomputable section
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

abbrev valueDefinition : CheckedDefinition := payload.definitions.get ⟨31, by decide +kernel⟩

theorem value_body (add mul left right : F) :
    valueDefinition.body.component
      (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed)
      (Evaluation.componentOperation (.silent _) (helpers payload)) (((.cons (some add) (.cons (some mul) (.cons (some left) (.cons (some right) .nil)))) : Values (Component (assignment F G)) valueDefinition.inputs).get) =
      .done (.cons (some (Gate.value add mul left right)) .nil) := by
  kernel_rfl

theorem value_invoke (add mul left right : F) :
    invoke (helpers (F := F) (G := G) payload).components valueDefinition.helper (.cons (some add) (.cons (some mul) (.cons (some left) (.cons (some right) .nil)))) =
      .done (.cons (some (Gate.value add mul left right)) .nil) :=
  (helper_body payload valueDefinition (List.get_mem _ _) (.cons (some add) (.cons (some mul) (.cons (some left) (.cons (some right) .nil))))).trans
    (value_body add mul left right)

abbrev quadraticDefinition : CheckedDefinition := payload.definitions.get ⟨37, by decide +kernel⟩

theorem quadratic_body (a0 a1 m0 m1 l0 l1 r0 r1 : F) :
    quadraticDefinition.body.component
      (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed)
      (Evaluation.componentOperation (.silent _) (helpers payload)) (((.cons (some a0) (.cons (some a1) (.cons (some m0) (.cons (some m1) (.cons (some l0) (.cons (some l1) (.cons (some r0) (.cons (some r1) .nil)))))))) : Values (Component (assignment F G)) quadraticDefinition.inputs).get) =
      .done (.cons (some (Gate.quadratic a0 a1 m0 m1 l0 l1 r0 r1)) .nil) := by
  kernel_rfl

theorem quadratic_invoke (a0 a1 m0 m1 l0 l1 r0 r1 : F) :
    invoke (helpers (F := F) (G := G) payload).components quadraticDefinition.helper (.cons (some a0) (.cons (some a1) (.cons (some m0) (.cons (some m1) (.cons (some l0) (.cons (some l1) (.cons (some r0) (.cons (some r1) .nil)))))))) =
      .done (.cons (some (Gate.quadratic a0 a1 m0 m1 l0 l1 r0 r1)) .nil) :=
  (helper_body payload quadraticDefinition (List.get_mem _ _) (.cons (some a0) (.cons (some a1) (.cons (some m0) (.cons (some m1) (.cons (some l0) (.cons (some l1) (.cons (some r0) (.cons (some r1) .nil))))))))).trans
    (quadratic_body a0 a1 m0 m1 l0 l1 r0 r1)

end
end ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate
