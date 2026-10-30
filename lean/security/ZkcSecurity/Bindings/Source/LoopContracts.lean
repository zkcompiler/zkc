module

public import ZkcSecurity.Bindings.Source.Pair
public import Zkc.Source.Structured.DomainParticipant
public import Zkc.Source.Structured.IterationObservations
public import ZkcSecurity.Bindings.Source.OccurrenceProperties

@[expose] public section

/-! Typed paired contracts at the actual source repeat boundary. Independent
unary reference, No/escape, frame, handler and budget contracts remain owned by
RepeatedComponent; a paired invariant does not imply those laws. The existing
Pair judgment performs the relational induction. -/
set_option autoImplicit false
namespace ZkcSecurity.Source.LoopContracts
open Zkc.Source Zkc.Source.Structured

/-- A counted presentation is consumed through its checked zero/successor
laws. The No invariant includes the actual reached history, current index and
remaining count; it is independent of a paired, honest, or charged-cost contract. Stops never provide a next state. -/
def counted_no {I : PIR.Signature} {E P S : Type} {Raw : E → Type}
    {absorb : Zkc.Transcript.Interface I E P Raw}
    {escape : Zkc.Transcript.EscapeJudgment E Raw}
    (reference : Nat → Nat → S → PIR.Process I S)
    (step : S → Nat → PIR.Process I S)
    (zero : ∀ index state, reference index 0 state = .done state)
    (succ : ∀ index count state, reference index (count + 1) state =
      (step state index).bind (reference (index + 1) count))
    (invariant : List E → Nat → Nat → S → Prop)
    (preserves : ∀ remaining index state history, invariant history index (remaining + 1) state →
      Zkc.Obligations.Derivation absorb escape (fun reached => invariant reached (index + 1) remaining)
        history (step state index))
    (index count : Nat) (state : S) (history : List E) (initial : invariant history index count state) :
    Zkc.Obligations.Derivation absorb escape (fun reached => invariant reached (index + count) 0)
      history (reference index count state) := by
  induction count generalizing index state history with
  | zero => rw [zero]; exact .done initial
  | succ count ih =>
    rw [succ]
    apply (preserves count index state history initial).bind _
    intro reached next valid
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using ih (index + 1) next reached valid

/-- A pathwise uniform callback budget, quantified over every state and reached
history. The source's occurrence frames stay inside `step`. The recurrence is
checked independently from No, which may have a different invariant. -/
theorem counted_cost {I : PIR.Signature} {E P S : Type} {Raw : E → Type}
    {absorb : Zkc.Transcript.Interface I E P Raw} {charge : List E → E → ENNReal}
    (reference : Nat → Nat → S → PIR.Process I S)
    (step : S → Nat → PIR.Process I S)
    (zero : ∀ index state, reference index 0 state = .done state)
    (succ : ∀ index count state, reference index (count + 1) state =
      (step state index).bind (reference (index + 1) count))
    (price : ENNReal)
    (bounded : ∀ index state history,
      ZkcSecurity.FiatShamir.Typed.ChargedCostBound absorb charge (step state index) history price)
    (index count : Nat) (state : S) (history : List E) :
    ZkcSecurity.FiatShamir.Typed.ChargedCostBound absorb charge
      (reference index count state) history (count * price) := by
  induction count generalizing index state history with
  | zero => rw [zero]; trivial
  | succ count ih =>
    rw [succ]
    convert ZkcSecurity.FiatShamir.CostComposition.bind _ _ price (count * price)
      (bounded index state history) (fun next reached => ih (index + 1) next reached) using 1
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

variable {carriers : Carriers} {scope : PairScope} {A B : Type}

/-- A paired counted presentation preserves both complete states and actual
iteration coordinates. Its honest invariant is independent of No and cost. -/
theorem counted_pair
    (left : Nat → Nat → A → PIR.Process (Occurrence.signature carriers) A)
    (right : Nat → Nat → B → PIR.Process (Occurrence.signature carriers) B)
    (stepLeft : A → Nat → PIR.Process (Occurrence.signature carriers) A)
    (stepRight : B → Nat → PIR.Process (Occurrence.signature carriers) B)
    (zeroLeft : ∀ index state, left index 0 state = .done state)
    (zeroRight : ∀ index state, right index 0 state = .done state)
    (succLeft : ∀ index count state, left index (count + 1) state =
      (stepLeft state index).bind (left (index + 1) count))
    (succRight : ∀ index count state, right index (count + 1) state =
      (stepRight state index).bind (right (index + 1) count))
    (invariant : Nat → Nat → A → B → Prop)
    (preserves : ∀ remaining index a b, invariant index (remaining + 1) a b →
      Pair scope (invariant (index + 1) remaining) (stepLeft a index) (stepRight b index))
    (Final : A → B → Prop)
    (finish : ∀ index a b, invariant index 0 a b → Final a b)
    (index count : Nat) (a : A) (b : B) (initial : invariant index count a b) :
    Pair scope Final (left index count a) (right index count b) := by
  induction count generalizing index a b with
  | zero => rw [zeroLeft, zeroRight]; exact .done (finish index a b initial)
  | succ count ih =>
    rw [succLeft, succRight]
    exact (preserves count index a b initial).bind _ _
      (fun nextLeft nextRight valid => ih (index + 1) nextLeft nextRight valid)

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
