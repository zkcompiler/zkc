module

public import ZkcSecurityExamples.Gkr.HonestHelpersReadback
public import ZkcSecurityExamples.Gkr.HonestHelpersRounds

@[expose] public section

/-! Transport the proved closed helper equations to the exact table invoked
by the source producer's normal form. -/

namespace ZkcSecurity.Realizations.Gkr.HonestHelpers
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.Examples.Components

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem layout_plain {width : Nat} (add mul below point : List F)
    (a m : Table F (width + width + width)) (v : Table F width)
    (da : ofList? (width + width + width) add = some a)
    (dm : ofList? (width + width + width) mul = some m)
    (dv : ofList? width below = some v) (pointSize : point.length = width)
    (small : width + width + width < 64) :
    let state := GkrRoundsLayout.state
      (fixPrefix width a (coordinates width point)) (fixPrefix width m (coordinates width point)) v v
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper36Helper
      (CollectionGoals.Layout.Inputs.pack (Value := assignment F G) { add, mul, point, below, width }) =
        .done (CollectionGoals.Layout.encode (ringModel F G)
          { addValues := GkrRoundsLayout.encode state.add, mulValues := GkrRoundsLayout.encode state.mul,
            leftValues := GkrRoundsLayout.encode state.left, rightValues := GkrRoundsLayout.encode state.right }) :=
  closed_invoke_returned GkrSourceViews.unit _ _ _ (layout_encodes add mul below point a m v da dm dv pointSize small)

/-- The layout is observed through the current component table, with every
factor present. The mathematical factors are independent multilinear tables. -/
theorem layout_component {width : Nat} (add mul below point : List F)
    (a m : Table F (width + width + width)) (v : Table F width)
    (da : ofList? (width + width + width) add = some a)
    (dm : ofList? (width + width + width) mul = some m)
    (dv : ofList? width below = some v) (pointSize : point.length = width)
    (small : width + width + width < 64) :
    let state := GkrRoundsLayout.state
      (fixPrefix width a (coordinates width point)) (fixPrefix width m (coordinates width point)) v v
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
      GkrSourceBodies.helper36Helper
      (CollectionGoals.Layout.Inputs.pack (Value := Component (assignment F G))
        { add := some add, mul := some mul, point := some point, below := some below, width := some width }) =
      .done (CollectionGoals.Layout.encode (ringModel F G)
        { addValues := GkrRoundsLayout.encode state.add, mulValues := GkrRoundsLayout.encode state.mul,
          leftValues := GkrRoundsLayout.encode state.left, rightValues := GkrRoundsLayout.encode state.right }).present :=
  component_invoke_returned GkrSourceViews.unit _ _ _ (layout_encodes add mul below point a m v da dm dv pointSize small)

/-- The actual component invocation returns all three quadratic coefficients. -/
theorem round_coefficients_component {n : Nat} (raw : GkrRoundsRealization.RawState F)
    (state : GkrRoundsReference.State F (n + 1))
    (decoded : GkrRoundsRealization.Decodes raw state) (capacity : 2 ^ n < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
      GkrSourceBodies.helper41Helper raw.values.present =
      .done (CoefficientResults.pack (Value := Component (assignment F G))
        { constant := some (GkrRoundsReference.message state).constant,
          linear := some (GkrRoundsReference.message state).linear,
          quadratic := some (GkrRoundsReference.message state).quadratic }) := by
  rw [component_invoke_present, round_coefficients raw state decoded capacity]
  rfl

/-- The challenge restricts all four present factors in the actual component table. -/
theorem round_restriction_component {n : Nat} (raw : GkrRoundsRealization.RawState F)
    (state : GkrRoundsReference.State F (n + 1))
    (decoded : GkrRoundsRealization.Decodes raw state) (capacity : 2 ^ n < indexLimit)
    (challenge : F) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
      GkrSourceBodies.helper45Helper (RestrictionArguments.pack (Value := assignment F G)
        { add := raw.add, mul := raw.mul, left := raw.left, right := raw.right, challenge }).present =
      .done (raw.restrict challenge).values.present := by
  rw [component_invoke_present, round_restriction raw state decoded capacity challenge]
  rfl

theorem element_plain (xs : List F) (position : Nat)
    (xsBound : xs.length < indexLimit) (positionBound : position < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper57Helper (ReadbackGoals.Element.Inputs.pack (Value := assignment F G) { source := xs, position }) =
      .done (ReadbackGoals.Element.encode (ringModel F G) ⟨xs[position]?.getD 0⟩) :=
  closed_invoke_returned GkrSourceViews.unit _ _ _ (element_equation xs position xsBound positionBound)

theorem element_after_plain (xs : List F) (position : Nat)
    (xsBound : xs.length < indexLimit) (positionBound : position + 1 < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper70Helper (ReadbackGoals.Element.Inputs.pack (Value := assignment F G) { source := xs, position }) =
      .done (ReadbackGoals.After.encode (ringModel F G) ⟨xs[position + 1]?.getD 0⟩) :=
  closed_invoke_returned GkrSourceViews.unit _ _ _ (element_after_equation xs position xsBound positionBound)

/-- The actual optional-component readback returns a present field value. -/
theorem element_component (xs : List F) (position : Nat)
    (xsBound : xs.length < indexLimit) (positionBound : position < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
      GkrSourceBodies.helper57Helper (ReadbackGoals.Element.Inputs.pack (Value := Component (assignment F G))
        { source := some xs, position := some position }) =
      .done (ReadbackGoals.Element.encode (ringModel F G) ⟨xs[position]?.getD 0⟩).present :=
  component_invoke_returned GkrSourceViews.unit _ _ _ (element_equation xs position xsBound positionBound)

/-- The checked successor is retained before the readback scan. -/
theorem element_after_component (xs : List F) (position : Nat)
    (xsBound : xs.length < indexLimit) (positionBound : position + 1 < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
      GkrSourceBodies.helper70Helper (ReadbackGoals.Element.Inputs.pack (Value := Component (assignment F G))
        { source := some xs, position := some position }) =
      .done (ReadbackGoals.After.encode (ringModel F G) ⟨xs[position + 1]?.getD 0⟩).present :=
  component_invoke_returned GkrSourceViews.unit _ _ _ (element_after_equation xs position xsBound positionBound)

end ZkcSecurity.Realizations.Gkr.HonestHelpers
