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
