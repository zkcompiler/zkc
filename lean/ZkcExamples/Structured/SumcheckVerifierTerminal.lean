module

public import ZkcExamples.Structured.SumcheckSourceContracts
public import ZkcExamples.Structured.SumcheckVerifierHelpers
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

open SumcheckSourceViews (unit)

/-- The helper owner's complete actual-source decision, transported to owned work. -/
theorem terminal_decision (self : Nat) (xs point : List F) (claim : F) :
    actualOwnedCheck (G := G) unit self (some xs) (some point) (some claim) =
      if point.length < indexLimit then
        if point.length < 64 then
          if xs.length < indexLimit then
            .done (.cons (some (Zkc.Protocols.Sumcheck.Multilinear.check
              (n := 0 + point.length) xs
              (Quadratic.point point.length (coordinates point.length point) Fin.elim0) claim)) .nil)
          else .halt .exhausted
        else .done (.cons (some false) .nil)
      else .halt .exhausted := by
  rw [terminal_optional]
  dsimp only
  rw [SumcheckSourceContracts.check_all]
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

/-- Representable inputs expose the actual source shape and restricted-sum test. -/
theorem terminal_equation (self : Nat) (xs point : List F) (claim : F)
    (vectorBound : xs.length < indexLimit) (pointBound : point.length < indexLimit) :
    actualOwnedCheck (G := G) unit self (some xs) (some point) (some claim) =
      .done (.cons (some (decide (HasShape xs point.length 1 ∧
        (restrictPrefixValues xs point).sum = claim))) .nil) := by
  rw [terminal_optional]
  dsimp only
  rw [SumcheckSourceContracts.check_equation xs point claim vectorBound pointBound]
  rfl

/-- Representable input agrees with the independently defined mathematical checker. -/
theorem terminal_mathematical (self : Nat) (xs point : List F) (claim : F)
    (vectorBound : xs.length < indexLimit) (pointBound : point.length < indexLimit) :
    actualOwnedCheck (G := G) unit self (some xs) (some point) (some claim) =
      .done (.cons (some (Zkc.Protocols.Sumcheck.Multilinear.check
        (n := 0 + point.length) xs
        (Quadratic.point point.length (coordinates point.length point) Fin.elim0) claim)) .nil) := by
  rw [terminal_optional]
  dsimp only
  rw [SumcheckSourceContracts.check_mathematical xs point claim vectorBound pointBound]
  rfl

/-- Decoding plus raw representability supplies the point bound; no P input occurs. -/
theorem terminal_decoded (self : Nat) (xs point : List F) (claim : F)
    (table : Table F (0 + point.length))
    (decoded : ofList? (0 + point.length) xs = some table)
    (vectorBound : xs.length < indexLimit) :
    actualOwnedCheck (G := G) unit self (some xs) (some point) (some claim) =
      .done (.cons (some (decide (extension (0 + point.length) table
        (coordinates (0 + point.length) point) = claim))) .nil) := by
  rw [terminal_optional]
  dsimp only
  rw [SumcheckSourceContracts.check_mle xs point claim table decoded vectorBound]
  rfl

/-- The returned point length transports the decoded dimension without a new assumption. -/
theorem terminal_decoded_length (self count : Nat) (xs point : List F) (claim : F)
    (table : Table F count) (decoded : ofList? count xs = some table)
    (vectorBound : xs.length < indexLimit) (length : point.length = count) :
    actualOwnedCheck (G := G) unit self (some xs) (some point) (some claim) =
      .done (.cons (some (decide (extension count table (coordinates count point) = claim))) .nil) := by
  have dimension : 0 + point.length = count := by omega
  cases dimension
  exact terminal_decoded self xs point claim table decoded vectorBound

/-- A representable malformed vector returns false. -/
theorem terminal_malformed (self : Nat) (xs point : List F) (claim : F)
    (vectorBound : xs.length < indexLimit) (pointBound : point.length < indexLimit)
    (malformed : ¬ HasShape xs point.length 1) :
    actualOwnedCheck (G := G) unit self (some xs) (some point) (some claim) =
      .done (.cons (some false) .nil) := by
  rw [terminal_equation self xs point claim vectorBound pointBound]
  simp only [malformed, false_and, decide_false]

end ZkcExamples.Structured.SumcheckVerifierTerminal
