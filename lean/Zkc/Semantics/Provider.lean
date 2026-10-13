module

public import Zkc.Semantics.Cost

@[expose] public section

/-! Provider state, contextual observations and deterministic memoization.

The finite supply below is concrete data, not a probability distribution. These
laws do not assert independent samples or a random-oracle implementation.
-/

set_option autoImplicit false
namespace PIR.Provider

variable {I J : Signature} {S T U V E F O A : Type}

/-- Pair independent state cells without exposing either cell to the other handler. -/
def jointSignature (I J : Signature) : Signature where
  Op := I.Op ⊕ J.Op
  Reply op := match op with
    | .inl left => I.Reply left
    | .inr right => J.Reply right

def joint (left : Handler I S E) (right : Handler J T E) :
    Handler (jointSignature I J) (S × T) E
  | .inl op, (s, t) =>
    let result := left op s
    ⟨result.outcome, (result.state, t), result.events⟩
  | .inr op, (s, t) =>
    let result := right op t
    ⟨result.outcome, (s, result.state), result.events⟩

/-- Adaptive contexts may interleave both interfaces. Component simulations lift
to the joint state, including terminal stops. This product-state construction
requires genuinely separate state cells; it says nothing about independence of
randomness or two handlers that both mutate one shared cache. -/
theorem run_joint_related (first : S → U → Prop) (second : T → V → Prop)
    (leftView : E → List O) (rightView : F → List O)
    (left : Handler I S E) (right : Handler J T E)
    (left' : Handler I U F) (right' : Handler J V F)
    (leftLaw : HandlerRelated first leftView rightView left left')
    (rightLaw : HandlerRelated second leftView rightView right right')
    (program : Proc (jointSignature I J) A) (s : S × T) (t : U × V)
    (initial : first s.1 t.1 ∧ second s.2 t.2) :
    Related (fun s t => first s.1 t.1 ∧ second s.2 t.2) leftView rightView
      (program.run (joint left right) s) (program.run (joint left' right') t) := by
  apply PIR.run_related _ _ _ _ _ _ program s t initial
  intro op s t related
  cases op with
  | inl op =>
    have law := leftLaw op s.1 t.1 related.1
    exact ⟨law.outcome, ⟨law.state, related.2⟩, law.events⟩
  | inr op =>
    have law := rightLaw op s.2 t.2 related.2
    exact ⟨law.outcome, ⟨related.1, law.state⟩, law.events⟩

/-- An established event view can be erased or postprocessed, never silently
strengthened to reveal a provider cache, hidden event, or accounting ledger. -/
theorem related_coarsen {Q : Type} (relation : S → T → Prop)
    (left : E → List O) (right : F → List O) (view : O → List Q)
    (a : Execution S E A) (b : Execution T F A)
    (related : Related relation left right a b) :
    Related relation (fun e => observeEvents view (left e))
      (fun e => observeEvents view (right e)) a b := by
  refine ⟨related.outcome, related.state, ?_⟩
  have same := congrArg (observeEvents view) related.events
  simpa only [observeEvents, List.flatMap_assoc] using same

structure CacheState (Key Value : Type) where
  entries : Key → Option Value
  unused : List Value

variable {Key Value : Type} [DecidableEq Key]

abbrev cacheSignature (Key Value : Type) : Signature := ⟨Key, fun _ => Value⟩

def CacheState.fill (state : CacheState Key Value) (key : Key) (value : Value)
    (rest : List Value) : CacheState Key Value :=
  ⟨fun other => if other = key then some value else state.entries other, rest⟩

/-- Every entered query is an event, including cache hits and exhausted misses. -/
def cached : Handler (cacheSignature Key Value) (CacheState Key Value) Key :=
  fun key state => match state.entries key with
    | some value => ⟨.returned value, state, [key]⟩
    | none => match state.unused with
      | [] => ⟨.stopped .exhausted, state, [key]⟩
      | value :: rest => ⟨.returned value, state.fill key value rest, [key]⟩

/-- All calls count as queries; only absent keys count as attempted misses. -/
def queryCharge : Cost.Charge (cacheSignature Key Value) (CacheState Key Value) Key :=
  fun _ _ _ => 1

def missCharge : Cost.Charge (cacheSignature Key Value) (CacheState Key Value) Key :=
  fun key state _ => if (state.entries key).isNone then 1 else 0

@[simp] theorem cached_hit (state : CacheState Key Value) (key : Key) (value : Value)
    (hit : state.entries key = some value) :
    cached key state = ⟨.returned value, state, [key]⟩ := by simp [cached, hit]

@[simp] theorem cached_miss (state : CacheState Key Value) (key : Key)
    (value : Value) (rest : List Value) (miss : state.entries key = none)
    (supply : state.unused = value :: rest) :
    cached key state = ⟨.returned value, state.fill key value rest, [key]⟩ := by
  simp [cached, miss, supply]

theorem cached_exhausted (state : CacheState Key Value) (key : Key)
    (miss : state.entries key = none) (empty : state.unused = []) :
    cached key state = ⟨.stopped .exhausted, state, [key]⟩ := by simp [cached, miss, empty]

/-- A hit does not consume supply; a successful miss installs exactly its reply. -/
theorem cached_stores (state : CacheState Key Value) (key : Key) (value : Value)
    (returned : (cached key state).outcome = .returned value) :
    (cached key state).state.entries key = some value := by
  cases hit : state.entries key with
  | some old => simp [cached, hit] at returned ⊢; exact returned
  | none =>
    cases supply : state.unused with
    | nil => simp [cached, hit, supply] at returned
    | cons old rest =>
      simp [cached, hit, supply] at returned
      simp [cached, hit, supply, CacheState.fill, returned]

theorem cached_preserves_other (state : CacheState Key Value) (key other : Key)
    (distinct : other ≠ key) :
    (cached key state).state.entries other = state.entries other := by
  cases hit : state.entries key with
  | some value => simp [cached, hit]
  | none => cases supply : state.unused <;> simp [cached, hit, supply, CacheState.fill, distinct]

/-- Repeated-key consistency holds in every successful state, including a cache
already populated by an earlier session. The second call still emits its query. -/
theorem cached_repeat (state : CacheState Key Value) (key : Key) (value : Value)
    (returned : (cached key state).outcome = .returned value) :
    cached key (cached key state).state =
      ⟨.returned value, (cached key state).state, [key]⟩ :=
  cached_hit _ _ _ (cached_stores state key value returned)

end PIR.Provider
