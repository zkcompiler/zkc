import Zkc.Construction.TransportReduction

open Zkc.Construction

-- A reflected nominal equality can occur inside the decision of a guard.
example {F : Type} [DecidableEq F] (value : F) :
    decide (Eq.rec (motive := fun (_ : String) _ => F) value
      (show "field" = "field" from Decidable.reflects_decide ("field" = "field")) = value) =
      true := by
  simp only [↓reduceTransport, decide_true]

-- The normalizer cannot identify different dependent carriers or erase a
-- transport whose equality is only a hypothesis.
example {α : Type} {family : α → Type} {left right : α}
    (same : left = right) (value : family left) : HEq (same ▸ value) value := by
  fail_if_success simp only [↓reduceTransport]
  exact eqRec_heq same value
