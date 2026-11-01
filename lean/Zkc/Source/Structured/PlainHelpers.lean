module

public import Zkc.Source.Structured.OpenLaws

@[expose] public section

/-! Exact helper-body transport into a complete unit's silent participant
 tables. These laws depend only on the admitted definitions and their complete
 signatures, independently of any protocol or mathematical helper library. -/
set_option autoImplicit false
namespace Zkc.Source.Structured
open Zkc.Source

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The actual silent fold used by the complete unit's participant semantics. -/
abbrev plainHelpers (U : UnitPayload) :
    Evaluation.ComponentTables F G (participantInterface F G) :=
  U.definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩

/-- Closed interpretation retains each helper's actual captured definition prefix. -/
theorem closed_invoke_plain (U : UnitPayload) (helper : Helper)
    (arguments : Values (assignment F G) helper.inputs) :
    invoke (plainHelpers (F := F) (G := G) U).closed helper arguments =
      (invoke (closedMeanings (F := F) (G := G) U.definitions) helper arguments).interpret
        (closedLift (I := participantInterface F G)) := by
  simpa only [plainHelpers, Evaluation.ComponentTables.closed_fold] using
    (Evaluation.foldMeanings_closedLift (F := F) (G := G)
      (I := participantInterface F G) U.definitions helper arguments).symm

/-- A proved complete closed result is reusable at the participant table.
The unit and helper arguments are unchanged by the transport. -/
theorem closed_invoke_returned (U : UnitPayload) (helper : Helper)
    (arguments : Values (assignment F G) helper.inputs)
    (result : Values (assignment F G) helper.outputs)
    (equation : invoke (closedMeanings (F := F) (G := G) U.definitions)
      helper arguments = .done result) :
    invoke (plainHelpers (F := F) (G := G) U).closed helper arguments = .done result := by
  rw [closed_invoke_plain, equation]
  rfl

/-- Present input transport retains every result coordinate. This is a law
for present inputs; it makes no claim about missing optional coordinates. -/
theorem component_invoke_present (U : UnitPayload) (helper : Helper)
    (arguments : Values (assignment F G) helper.inputs) :
    invoke (plainHelpers (F := F) (G := G) U).components helper arguments.present =
      (invoke (plainHelpers (F := F) (G := G) U).closed helper arguments).bind
        (fun result => .done result.present) :=
  Evaluation.ComponentTables.adequate_fold (.silent _) ⟨[], []⟩
    Evaluation.ComponentTables.adequate_empty U.definitions helper arguments

/-- Compose the two established transports without repeating an interpretation
proof at each mathematical helper. -/
theorem component_invoke_returned (U : UnitPayload) (helper : Helper)
    (arguments : Values (assignment F G) helper.inputs)
    (result : Values (assignment F G) helper.outputs)
    (equation : invoke (closedMeanings (F := F) (G := G) U.definitions)
      helper arguments = .done result) :
    invoke (plainHelpers (F := F) (G := G) U).components helper arguments.present =
      .done result.present := by
  rw [component_invoke_present, closed_invoke_returned U helper arguments result equation]
  rfl

/-- Full-body association transports optional component evaluation as well. -/
theorem component_body_plain (U : UnitPayload) (helper : Helper)
    (body : Region dialect helper.inputs helper.outputs)
    (association : BodyIn U.definitions helper body)
    (arguments : Values (Component (assignment F G)) helper.inputs) :
    invoke (plainHelpers (F := F) (G := G) U).components helper arguments =
      body.component (Evaluation.meaning (.silent _) (plainHelpers U).closed)
        (Evaluation.componentOperation (.silent _) (plainHelpers U)) arguments.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := association
  calc
    _ = (invoke (U.tables F G).components helper arguments).interpret forgetSites :=
      ((Evaluation.ComponentTables.fold_forgetSites U.definitions).components helper arguments).symm
    _ = _ := by
      rw [U.component_body_view_as definition member helper signature body exactRaw arguments]
      exact Evaluation.component_interpret forgetSites observedSites_forgetSites
        (Evaluation.ComponentTables.fold_forgetSites U.definitions) body arguments.get

end Zkc.Source.Structured
