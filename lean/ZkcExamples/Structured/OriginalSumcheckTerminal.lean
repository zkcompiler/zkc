module

public import ZkcExamples.Structured.OriginalSumcheckChecks
public import ZkcExamples.Structured.OriginalSumcheckRoots

@[expose] public section
/-! Source-instance controls for both retained roots. The reusable terminal
laws live in OriginalSumcheckChecks without a concrete-root import. -/
set_option autoImplicit false
set_option maxRecDepth 50000
noncomputable section

namespace ZkcExamples.Structured.OriginalSumcheckInstances
open Zkc.Source Zkc.Source.Structured

namespace Small

theorem first_bodies : MapFirstContracts.Bodies payload.definitions := by
  bind_structured_bodies

theorem prefix_bodies : MapPrefixContracts.Bodies payload.definitions := by
  bind_structured_bodies

theorem terminal_bodies : OriginalSumcheckLibrary.TerminalBodies payload.definitions where
  first := first_bodies
  restriction := prefix_bodies
  check := by bind_structured_bodies
  checkTable := by bind_structured_bodies

theorem producer_bodies : SumcheckUnitContracts.Bodies payload.definitions where
  first := first_bodies
  sums := by bind_structured_bodies
  empty := helpers_bound.empty
  append := helpers_bound.append
  values := helpers_bound.values
  width := helpers_bound.width
  «variables» := helpers_bound.«variables»

end Small

namespace Two

theorem first_bodies : MapFirstContracts.Bodies payload.definitions := by
  bind_structured_bodies

theorem prefix_bodies : MapPrefixContracts.Bodies payload.definitions := by
  bind_structured_bodies

theorem terminal_bodies : OriginalSumcheckLibrary.TerminalBodies payload.definitions where
  first := first_bodies
  restriction := prefix_bodies
  check := by bind_structured_bodies
  checkTable := by bind_structured_bodies

theorem producer_bodies : SumcheckUnitContracts.Bodies payload.definitions where
  first := first_bodies
  sums := by bind_structured_bodies
  empty := helpers_bound.empty
  append := helpers_bound.append
  values := helpers_bound.values
  width := helpers_bound.width
  «variables» := helpers_bound.«variables»

end Two

end ZkcExamples.Structured.OriginalSumcheckInstances

namespace ZkcExamples.Structured.OriginalSumcheckRoots.Two
open Zkc.Source Zkc.Source.Structured

def bothBody : Region dialect [.boolean, .boolean] [.boolean] :=
  .letOp .booleanAnd (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

theorem both_body : BodyIn payload.definitions bothHelper bothBody :=
  by bind_structured_bodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

set_option backward.isDefEq.respectTransparency false in
theorem both_present (left right : Bool) :
    combine (OriginalSumcheckLibrary.helpers (F := F) (G := G) payload)
      (.cons (some left) .nil) (.cons (some right) .nil) =
      .done (.cons (some (left && right)) .nil) := by
  change Participant.owned 0 0
    (invoke (OriginalSumcheckLibrary.helpers (F := F) (G := G) payload).closed bothHelper)
    (.cons (some left) (.cons (some right) .nil)) = _
  simp only [Participant.owned, ↓reduceIte]
  change (invoke (OriginalSumcheckLibrary.helpers (F := F) (G := G) payload).closed bothHelper
    (.cons left (.cons right .nil))).bind _ = _
  rw [← (OriginalSumcheckLibrary.helpers_lift payload).closed,
    SumcheckVerifierHelpers.closed_invoke_plain, both_body.invoke payload.linked]
  rfl

end ZkcExamples.Structured.OriginalSumcheckRoots.Two
