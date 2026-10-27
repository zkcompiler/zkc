module

public import ZkcSecurity.Realizations.Gkr.HonestHelpersLayout
public import ZkcSecurity.Examples.Components.GkrRoundsRealization
public import ZkcExamples.Structured.SumcheckVerifierHelpers

@[expose] public section

/-! The producer uses the same checked helper definitions as the existing
round realization. This transports its coefficient and restriction laws to
the actual source participant, without assuming any helper correctness. -/

namespace ZkcSecurity.Realizations.Gkr.HonestHelpers
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers
open Zkc.Polynomial.Multilinear
open ZkcSecurity.Examples.Components

set_option maxRecDepth 20000

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Only the reached round helper is compared. The complete current declaration
list includes new guards and is not identified with another export's list. -/
theorem round_message_table (args : Values (assignment F G) GkrSourceBodies.helper41Helper.inputs) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper41Helper args =
    invoke GkrRoundsHelpers.table GkrRoundsHelpers.roundMessageHelper args := by
  kernel_rfl

/-- Exact helper correspondence includes arbitrary restrictions and stops. -/
theorem round_restriction_table (args : Values (assignment F G) GkrSourceBodies.helper45Helper.inputs) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper45Helper args =
    invoke GkrRoundsHelpers.table GkrRoundsHelpers.gateRestrictionHelper args := by
  kernel_rfl

theorem round_coefficients {n : Nat} (raw : GkrRoundsRealization.RawState F)
    (state : GkrRoundsReference.State F (n + 1))
    (decoded : GkrRoundsRealization.Decodes raw state)
    (capacity : 2 ^ n < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper41Helper raw.values =
      .done (.cons (GkrRoundsReference.message state).constant
        (.cons (GkrRoundsReference.message state).linear
          (.cons (GkrRoundsReference.message state).quadratic .nil))) := by
  rw [round_message_table]
  exact GkrRoundsRealization.round_success raw state decoded capacity

/-- Every factor is updated at the supplied challenge. -/
theorem round_restriction {n : Nat} (raw : GkrRoundsRealization.RawState F)
    (state : GkrRoundsReference.State F (n + 1))
    (decoded : GkrRoundsRealization.Decodes raw state)
    (capacity : 2 ^ n < indexLimit) (challenge : F) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper45Helper (raw.values.append (.cons challenge .nil)) =
      .done (raw.restrict challenge).values := by
  rw [round_restriction_table]
  exact GkrRoundsRealization.fixGates_success raw state decoded capacity challenge

end ZkcSecurity.Realizations.Gkr.HonestHelpers
