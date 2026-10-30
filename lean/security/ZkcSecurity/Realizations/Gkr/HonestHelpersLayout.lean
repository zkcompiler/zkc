module

public import ZkcSecurity.Bindings.Gkr.LayoutReadback
public import ZkcSecurity.Realizations.Gkr.HonestHelpers
public import ZkcSecurity.Examples.Components.GkrRoundsRealization

@[expose] public section

/-! The actual producer's four outputs realize the mathematical split-variable
layout. Tables are logical references; they are not extra participant inputs. -/

namespace ZkcSecurity.Realizations.Gkr.HonestHelpers
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceLaws
open ZkcExamples.Structured.PrimitiveLibrary
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.Examples.Components

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Arbitrary raw representations, off-cube points, and every payload field.
The source's u64 capacity and shape admission remain visible. -/
theorem layout_encodes {width : Nat} (add mul below point : List F)
    (a m : Table F (width + width + width)) (v : Table F width)
    (da : ofList? (width + width + width) add = some a)
    (dm : ofList? (width + width + width) mul = some m)
    (dv : ofList? width below = some v) (pointSize : point.length = width)
    (small : width + width + width < 64) :
    let state := GkrRoundsLayout.state
      (fixPrefix width a (coordinates width point)) (fixPrefix width m (coordinates width point)) v v
    invoke (helpers (G := G)) GkrSourceBodies.helper36Helper
      (.cons add (.cons mul (.cons point (.cons below (.cons width .nil))))) =
        .done (.cons (GkrRoundsLayout.encode state.add)
          (.cons (GkrRoundsLayout.encode state.mul)
            (.cons (GkrRoundsLayout.encode state.left)
              (.cons (GkrRoundsLayout.encode state.right) .nil)))) := by
  dsimp only
  have widthSmall : width < 64 := by omega
  have powerSmall : 2 ^ (width + width + width) < indexLimit :=
    Nat.pow_lt_pow_right (by decide) small
  have belowSmall : 2 ^ width < indexLimit := Nat.pow_lt_pow_right (by decide) widthSmall
  have shapeA : HasShape add (point.length + width + width) 1 := by
    simpa [HasShape, Nat.mod_one, pointSize, ofList?_length add a da] using small
  have shapeM : HasShape mul (point.length + width + width) 1 := by
    simpa [HasShape, Nat.mod_one, pointSize, ofList?_length mul m dm] using small
  rw [layout_equation add mul below point width widthSmall shapeA shapeM
    (by rwa [ofList?_length add a da]) (by rwa [ofList?_length mul m dm])
    (by rwa [ofList?_length below v dv]) (by rw [pointSize]; exact Nat.lt_trans small (by decide +kernel))]
  have pa := ofList?_restrictPrefixValues_of_length width add point a pointSize da
  have pm := ofList?_restrictPrefixValues_of_length width mul point m pointSize dm
  rw [← encode_of_decodes _ _ pa, ← encode_of_decodes _ _ pm, ← encode_of_decodes below v dv,
    ← GkrRoundsLayout.encode_replicate, ← GkrRoundsLayout.encode_tile]
  rfl

end ZkcSecurity.Realizations.Gkr.HonestHelpers
