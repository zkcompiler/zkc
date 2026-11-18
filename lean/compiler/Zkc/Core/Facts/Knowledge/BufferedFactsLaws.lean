module

public import Zkc.Core.Facts.Knowledge.BufferedFacts

@[expose] public section

namespace Zkc.Core.BodyAnalysis.BufferedFacts
open FactCheck (Known factDepth rangeIn)

private theorem read_flush (t : FactCheck.FactBuckets (Nat × Range)) (id : Nat) : ∀ ps,
    rangeIn id ((flush t ps).find id) =
      readRanges id (rangeIn id (t.find id)) ps
  | [] => rfl
  | (key,r) :: ps => by
    simp only [flush, readRanges]
    by_cases eq : key = id
    · subst key
      simp [FactCheck.FactBuckets.find_insert, rangeIn, read_flush t id ps]
    · rw [FactCheck.FactBuckets.find_insert]
      split <;> simp [rangeIn, eq, read_flush t id ps]

@[simp] theorem view_rangeOf (k : BufferedFacts) (id : Nat) :
    k.toKnown.rangeOf id = k.rangeOf id := read_flush _ _ _

@[simp] theorem view_pointOf (k : BufferedFacts) (id : Nat) :
    k.toKnown.pointOf id = k.pointOf id := by
  simp only [Known.pointOf, view_rangeOf, pointOf]
  cases k.rangeOf id with
  | none => rfl
  | some r => cases r with | mk lo hi => cases hi <;> rfl

@[simp] theorem view_addRange (k : BufferedFacts) (id : Nat) (r : Range) :
    (k.addRange id r).toKnown = k.toKnown.addRange id r := by
  unfold addRange
  split <;> rfl

@[simp] theorem view_addRange? (k : BufferedFacts) (id : Nat) (r : Option Range) :
    (k.addRange? id r).toKnown = k.toKnown.addRange? id r := by
  cases r <;> simp [addRange?, Known.addRange?]

@[simp] theorem view_addOrder (k : BufferedFacts) (a b : Nat) (strict loop : Bool) :
    (k.addOrder a b strict loop).toKnown = k.toKnown.addOrder a b strict loop := rfl

@[simp] theorem view_pushLess (k : BufferedFacts) (a b : Nat) :
    (k.pushLess a b).toKnown = k.toKnown.pushLess a b := by simp [pushLess, Known.pushLess]

@[simp] theorem view_pushLe (k : BufferedFacts) (a b : Nat) :
    (k.pushLe a b).toKnown = k.toKnown.pushLe a b := by simp [pushLe, Known.pushLe]

@[simp] theorem view_pushEqual (k : BufferedFacts) (a b : Nat) :
    (k.pushEqual a b).toKnown = k.toKnown.pushEqual a b := by simp [pushEqual, Known.pushEqual]

@[simp] theorem view_pushDifferent (k : BufferedFacts) (a b : Nat) :
    (k.pushDifferent a b).toKnown = k.toKnown.pushDifferent a b := by
  simp only [pushDifferent, Known.pushDifferent, view_rangeOf]
  split <;> split <;> simp

end Zkc.Core.BodyAnalysis.BufferedFacts
