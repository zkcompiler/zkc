module

public import Zkc.Protocols.Sumcheck.Source.HelperLaws
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import Zkc.Source.Structured.OpenLaws

@[expose] public section

namespace ZkcExamples.Structured.SumcheckVerifierTerminal
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary SumcheckHelperBodies
open SumcheckHelperLaws
open Zkc.Polynomial Zkc.Polynomial.Multilinear

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Actual owned source work, with the original optional raw verifier vector. -/
def actualOwnedCheck (unit : UnitPayload) (self : Nat)
    (raw point : Option (List F)) (claim : Option F) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [.boolean]) :=
  Participant.owned self self (invoke (Zkc.Source.Structured.plainHelpers unit).closed checkHelper)
    (.cons raw (.cons point (.cons claim .nil)))

/-- Any missing operand is incomplete; present operands invoke the actual helper. -/
theorem terminal_optional (unit : UnitPayload) (self : Nat)
    (raw point : Option (List F)) (claim : Option F) :
    actualOwnedCheck (G := G) unit self raw point claim =
      match raw, point, claim with
      | some xs, some coordinates, some value =>
        ((invoke (closedMeanings unit.definitions) checkHelper
          (checkInputs xs coordinates value)).interpret
            (closedLift (I := participantInterface F G))).bind
          fun result => .done result.present
      | _, _, _ => .halt .incomplete := by
  cases raw <;> cases point <;> cases claim <;>
    simp only [actualOwnedCheck, Participant.owned, ↓reduceIte]
  all_goals try rfl
  rename_i xs point claim
  change (invoke (Zkc.Source.Structured.plainHelpers unit).closed checkHelper
    (checkInputs xs point claim)).bind _ = _
  rw [Zkc.Source.Structured.closed_invoke_plain]

end ZkcExamples.Structured.SumcheckVerifierTerminal
