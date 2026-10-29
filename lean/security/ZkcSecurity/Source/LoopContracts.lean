module

public import ZkcSecurity.Source.Pair
public import Zkc.Source.Structured.DomainParticipant
public import Zkc.Source.Structured.IterationObservations

@[expose] public section

/-! Typed paired contracts at the actual source repeat boundary. Independent
unary reference, No/escape, frame, handler and budget contracts remain owned by
RepeatedComponent; a paired invariant does not imply those laws. The existing
Pair judgment performs the relational induction. -/
set_option autoImplicit false
namespace ZkcSecurity.Source.LoopContracts
open Zkc.Source Zkc.Source.Structured

variable {carriers : Carriers} {scope : PairScope} {A B : Type}

structure Paired (left : A → Nat → PIR.Process (Occurrence.signature carriers) A)
    (right : B → Nat → PIR.Process (Occurrence.signature carriers) B) where
  invariant : Nat → A → B → Prop
  step : ∀ remaining index a b, invariant (remaining + 1) a b →
    Pair scope (invariant remaining) (left a index) (right b index)

theorem Paired.range
    {left : A → Nat → PIR.Process (Occurrence.signature carriers) A}
    {right : B → Nat → PIR.Process (Occurrence.signature carriers) B}
    (contract : Paired (scope := scope) left right) (count start : Nat) (a : A) (b : B)
    (initial : contract.invariant count a b) :
    Pair scope (contract.invariant 0)
      (Finite.fold left (List.range' start count) a)
      (Finite.fold right (List.range' start count) b) :=
  Pair.range contract.invariant left right contract.step count start a b initial

/-- Both actual repeats admit the same count. The contract is indexed by the
real masked callback, including iteration observations and the complete state.
Counts/roles/masks are checked separately from the mathematical invariant. -/
theorem repeat_pair (spec : RepeatSpec) (ctx : ProtocolContext) (roleP roleV : Nat)
    (capturesP capturesV : Values (Component carriers.Value) spec.captures)
    (bodyP bodyV : RegionFunction (Component carriers.Value) (Occurrence.signature carriers)
      (.index :: (spec.state ++ spec.captures), spec.state)) (site : String)
    (contract : Paired (scope := scope)
      (Repeat.stepOn spec ctx (ctx.roles roleP) capturesP bodyP
        (iterations := Occurrence.iterations) (site := site))
      (Repeat.stepOn spec ctx (ctx.roles roleV) capturesV bodyV
        (iterations := Occurrence.iterations) (site := site)))
    (count : Nat) (p v : Values (Component carriers.Value) spec.state)
    (activeP : (spec.roles.map ctx.roles).contains (ctx.roles roleP) = true)
    (activeV : (spec.roles.map ctx.roles).contains (ctx.roles roleV) = true)
    (bounded : count ≤ spec.maximum)
    (initial : contract.invariant count
      (maskValues (ctx.roles roleP) (ctx.mapScopes spec.stateScopes) p)
      (maskValues (ctx.roles roleV) (ctx.mapScopes spec.stateScopes) v)) :
    Pair scope (contract.invariant 0)
      (denoteRepeatOn spec ctx (ctx.roles roleP) (some count) p capturesP bodyP Occurrence.iterations site)
      (denoteRepeatOn spec ctx (ctx.roles roleV) (some count) v capturesV bodyV Occurrence.iterations site) := by
  simp only [denoteRepeatOn, activeP, activeV, bounded, ↓reduceIte, List.range_eq_range']
  exact contract.range count 0 _ _ initial

end ZkcSecurity.Source.LoopContracts
