module

public import Zkc.Verification.Installations.Sumcheck.Source.HelperLaws
public import Zkc.Verification.Installations.Sumcheck.Source.VerifierHelpers
public import Zkc.IR.Source.Structured.OpenLaws

@[expose] public section

namespace ZkcExamples.Structured.SumcheckVerifierTerminal
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary SumcheckHelperBodies
open SumcheckHelperLaws
open Zkc.Polynomial Zkc.Polynomial.Multilinear

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Actual owned helper invocation retains the optional local custody operand. -/
def ownedCheck (unit : UnitPayload) (self : Nat)
    (raw : Option (List F)) (custody : Option CustodyToken)
    (point : Option (List F)) (claim : Option F) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [.boolean]) :=
  Participant.owned self self (invoke (Zkc.Source.Structured.plainHelpers unit).closed checkHelper)
    (.cons raw (.cons custody (.cons point (.cons claim .nil))))

/-- Owned invocation requires every operand, including its nominal custody slot. -/
theorem ownedCheck_optional (unit : UnitPayload) (self : Nat)
    (raw : Option (List F)) (custody : Option CustodyToken)
    (point : Option (List F)) (claim : Option F) :
    ownedCheck (G := G) unit self raw custody point claim =
      match raw, custody, point, claim with
      | some xs, some token, some coordinates, some value =>
        ((invoke (closedMeanings unit.definitions) checkHelper
          (terminalInputs xs token coordinates value)).interpret
            (closedLift (I := participantInterface F G))).bind
          fun result => .done result.present
      | _, _, _, _ => .halt .incomplete := by
  cases raw <;> cases custody <;> cases point <;> cases claim <;>
    simp only [ownedCheck, Participant.owned, ↓reduceIte]
  all_goals try rfl
  rename_i xs token point claim
  change (invoke (Zkc.Source.Structured.plainHelpers unit).closed checkHelper
    (terminalInputs xs token point claim)).bind _ = _
  rw [Zkc.Source.Structured.closed_invoke_plain]

/-- Missing custody refuses the actual helper before its mathematical checker. -/
theorem ownedCheck_missing (unit : UnitPayload) (self : Nat)
    (raw point : Option (List F)) (claim : Option F) :
    ownedCheck (G := G) unit self raw none point claim = .halt .incomplete := by
  cases raw <;> cases point <;> cases claim <;>
    simp only [ownedCheck, Participant.owned, ↓reduceIte] <;> rfl

/-- Actual owned source work, with the optional raw vector and the closed successor custody token. -/
def actualOwnedCheck (unit : UnitPayload) (self : Nat)
    (raw point : Option (List F)) (claim : Option F) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [.boolean]) :=
  ownedCheck unit self raw (some 0) point claim

/-- Any missing operand is incomplete; present operands invoke the actual helper. -/
theorem terminal_optional (unit : UnitPayload) (self : Nat)
    (raw point : Option (List F)) (claim : Option F) :
    actualOwnedCheck (G := G) unit self raw point claim =
      match raw, point, claim with
      | some xs, some coordinates, some value =>
        ((invoke (closedMeanings unit.definitions) checkHelper
          (terminalInputs xs 0 coordinates value)).interpret
            (closedLift (I := participantInterface F G))).bind
          fun result => .done result.present
      | _, _, _ => .halt .incomplete := by
  cases raw <;> cases point <;> cases claim <;>
    simp only [actualOwnedCheck, ownedCheck, Participant.owned, ↓reduceIte]
  all_goals try rfl
  rename_i xs point claim
  change (invoke (Zkc.Source.Structured.plainHelpers unit).closed checkHelper
    (terminalInputs xs 0 point claim)).bind _ = _
  rw [Zkc.Source.Structured.closed_invoke_plain]

end ZkcExamples.Structured.SumcheckVerifierTerminal
