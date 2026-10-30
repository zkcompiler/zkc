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

/-- Present arguments and results use the source component table itself. -/
theorem component_present (helper : Helper) (args : Values (assignment F G) helper.inputs) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components helper args.present =
      (invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed helper args).bind
        fun result => .done result.present :=
  Evaluation.ComponentTables.adequate_fold (.silent _) _
    Evaluation.ComponentTables.adequate_empty _ helper args

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
      (.cons add (.cons mul (.cons point (.cons below (.cons width .nil))))) =
        .done (.cons (GkrRoundsLayout.encode state.add)
          (.cons (GkrRoundsLayout.encode state.mul)
            (.cons (GkrRoundsLayout.encode state.left)
              (.cons (GkrRoundsLayout.encode state.right) .nil)))) := by
  rw [closed_invoke_plain]
  change (invoke (helpers (G := G)) GkrSourceBodies.helper36Helper _).interpret _ = _
  rw [layout_encodes add mul below point a m v da dm dv pointSize small]
  rfl

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
      (.cons (some add) (.cons (some mul) (.cons (some point)
        (.cons (some below) (.cons (some width) .nil))))) =
      .done (.cons (some (GkrRoundsLayout.encode state.add))
        (.cons (some (GkrRoundsLayout.encode state.mul))
          (.cons (some (GkrRoundsLayout.encode state.left))
            (.cons (some (GkrRoundsLayout.encode state.right)) .nil)))) := by
  change invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
    GkrSourceBodies.helper36Helper
    (Values.cons add (.cons mul (.cons point (.cons below (.cons width .nil))))).present = _
  rw [component_present GkrSourceBodies.helper36Helper
    (.cons add (.cons mul (.cons point (.cons below (.cons width .nil))))),
    layout_plain add mul below point a m v da dm dv pointSize small]
  rfl

/-- The actual component invocation returns all three quadratic coefficients. -/
theorem round_coefficients_component {n : Nat} (raw : GkrRoundsRealization.RawState F)
    (state : GkrRoundsReference.State F (n + 1))
    (decoded : GkrRoundsRealization.Decodes raw state) (capacity : 2 ^ n < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
      GkrSourceBodies.helper41Helper raw.values.present =
      .done (.cons (some (GkrRoundsReference.message state).constant)
        (.cons (some (GkrRoundsReference.message state).linear)
          (.cons (some (GkrRoundsReference.message state).quadratic) .nil))) := by
  rw [component_present, round_coefficients raw state decoded capacity]
  rfl

/-- The challenge restricts all four present factors in the actual component table. -/
theorem round_restriction_component {n : Nat} (raw : GkrRoundsRealization.RawState F)
    (state : GkrRoundsReference.State F (n + 1))
    (decoded : GkrRoundsRealization.Decodes raw state) (capacity : 2 ^ n < indexLimit)
    (challenge : F) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
      GkrSourceBodies.helper45Helper (raw.values.append (.cons challenge .nil)).present =
      .done (raw.restrict challenge).values.present := by
  rw [component_present, round_restriction raw state decoded capacity challenge]
  rfl

theorem element_plain (xs : List F) (position : Nat)
    (xsBound : xs.length < indexLimit) (positionBound : position < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper57Helper (.cons xs (.cons position .nil)) =
      .done (.cons (xs[position]?.getD 0) .nil) := by
  rw [closed_invoke_plain]
  change (invoke (helpers (G := G)) GkrSourceBodies.helper57Helper _).interpret _ = _
  rw [element_equation xs position xsBound positionBound]
  rfl

theorem element_after_plain (xs : List F) (position : Nat)
    (xsBound : xs.length < indexLimit) (positionBound : position + 1 < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper70Helper (.cons xs (.cons position .nil)) =
      .done (.cons (xs[position + 1]?.getD 0) .nil) := by
  rw [closed_invoke_plain]
  change (invoke (helpers (G := G)) GkrSourceBodies.helper70Helper _).interpret _ = _
  rw [element_after_equation xs position xsBound positionBound]
  rfl

/-- The actual optional-component readback returns a present field value. -/
theorem element_component (xs : List F) (position : Nat)
    (xsBound : xs.length < indexLimit) (positionBound : position < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
      GkrSourceBodies.helper57Helper (.cons (some xs) (.cons (some position) .nil)) =
      .done (.cons (some (xs[position]?.getD 0)) .nil) := by
  change invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
    GkrSourceBodies.helper57Helper (Values.cons xs (.cons position .nil)).present = _
  rw [component_present GkrSourceBodies.helper57Helper (.cons xs (.cons position .nil)),
    element_plain xs position xsBound positionBound]
  rfl

/-- The checked successor is retained before the readback scan. -/
theorem element_after_component (xs : List F) (position : Nat)
    (xsBound : xs.length < indexLimit) (positionBound : position + 1 < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
      GkrSourceBodies.helper70Helper (.cons (some xs) (.cons (some position) .nil)) =
      .done (.cons (some (xs[position + 1]?.getD 0)) .nil) := by
  change invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
    GkrSourceBodies.helper70Helper (Values.cons xs (.cons position .nil)).present = _
  rw [component_present GkrSourceBodies.helper70Helper (.cons xs (.cons position .nil)),
    element_after_plain xs position xsBound positionBound]
  rfl

end ZkcSecurity.Realizations.Gkr.HonestHelpers
