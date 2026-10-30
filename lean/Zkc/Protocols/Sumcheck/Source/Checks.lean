module

public import Zkc.Protocols.Sumcheck.Source.Library
public import Zkc.Protocols.Multilinear.Source.MapPrefixContracts
public import Zkc.Source.Structured.BodyBindings

@[expose] public section

/-! Source helper dependencies for the terminal checker and honest producer.
Every association is complete helper identity, membership and raw body; no
caller supplies the intended checker result as a semantic premise. -/
set_option autoImplicit false
set_option maxRecDepth 50000
noncomputable section
namespace ZkcExamples.Structured.OriginalSumcheckLibrary
open Zkc.Source Zkc.Source.Structured

structure TerminalImplementation (definitions : List CheckedDefinition)
    (bindings : MultilinearPrefixBodies.Bindings) : Prop where
  first : ∃ collectBindings, MapFirstContracts.Bodies definitions collectBindings
  restriction : MapPrefixContracts.Bodies definitions bindings
  check : BodyIn definitions SumcheckHelperBodies.checkHelper SumcheckHelperBodies.checkBody
  checkTable : BodyIn definitions SumcheckHelperBodies.checkTableHelper
    (SumcheckHelperBodies.checkTableBody bindings)

/-- A coherent exact implementation exists in this source; private names do not
escape into the protocol-level theorem's interface. -/
def TerminalBodies (definitions : List CheckedDefinition) : Prop :=
  ∃ bindings, TerminalImplementation definitions bindings

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The original closed helper fold computes the existing restriction checker,
including false scalars and malformed shapes, under its actual index bounds. -/
theorem check_terminal (payload : UnitPayload) (bodies : TerminalBodies payload.definitions)
    (entries point : List F) (claim : F) (vectorBound : entries.length < indexLimit)
    (pointBound : point.length < indexLimit) :
    invoke (helpers (G := G) payload).closed SumcheckHelperBodies.checkHelper
      (SumcheckHelperLaws.checkInputs entries point claim) =
      .done (PrimitiveLibrary.boolResult (decide (PrimitiveLibrary.HasShape entries point.length 1 ∧
        (Zkc.Polynomial.Multilinear.restrictPrefixValues entries point).sum = claim))) := by
  obtain ⟨bindings, bodies⟩ := bodies
  obtain ⟨collectBindings, first⟩ := bodies.first
  rw [← (helpers_lift payload).closed, Zkc.Source.Structured.closed_invoke_plain]
  rw [(bodies.check.invoke payload.linked (SumcheckHelperLaws.checkInputs entries point claim)).trans
    (SumcheckHelperLaws.check_generic_body _
      (MapPrefixContracts.laws_of_bodies payload.linked bodies.restriction first)
      (fun xs rs scalar => bodies.checkTable.invoke payload.linked
        (SumcheckHelperLaws.checkInputs xs rs scalar))
      entries point claim vectorBound pointBound)]
  rfl

theorem check_present (payload : UnitPayload) (bodies : TerminalBodies payload.definitions)
    (self : Nat) (entries point : List F) (claim : F) (vectorBound : entries.length < indexLimit)
    (pointBound : point.length < indexLimit) :
    Participant.owned self self
      (invoke (helpers (G := G) payload).closed SumcheckHelperBodies.checkHelper)
      (.cons (some entries) (.cons (some point) (.cons (some claim) .nil))) =
      .done (.cons (some (decide (PrimitiveLibrary.HasShape entries point.length 1 ∧
        (Zkc.Polynomial.Multilinear.restrictPrefixValues entries point).sum = claim))) .nil) := by
  simp only [Participant.owned, ↓reduceIte, RoleFamily.sequence]
  change (invoke (helpers (G := G) payload).closed SumcheckHelperBodies.checkHelper
    (SumcheckHelperLaws.checkInputs entries point claim)).bind _ = _
  rw [check_terminal payload bodies entries point claim vectorBound pointBound]
  rfl

end ZkcExamples.Structured.OriginalSumcheckLibrary
