import Zkc.Semantics.Interpretation
import Zkc.Modules.Preparation

/-! Immutable preparation in a context with stateful external operations.

Preparation changes only its cache. External calls retain their actual reply,
stopped post-state and events, and cannot inspect that cache. The preserved
observation hides accounting; no timing or cache-visible scheduling claim follows.
-/

set_option autoImplicit false

namespace PIR.Preparation

inductive Op (K : Type) (I : Signature) where
  | prepare : K → Op K I
  | external : I.Op → Op K I

def signature (K V : Type) (I : Signature) : Signature :=
  ⟨Op K I, fun op => match op with
    | .prepare _ => V
    | .external call => I.Reply call⟩

inductive Event (E : Type) where
  | visible : E → Event E
  | charge : Nat → Nat → Nat → Event E
  deriving DecidableEq, Repr

variable {K V S E A : Type} {I : Signature}

def view : Event E → List E
  | .visible e => [e]
  | .charge _ _ _ => []

def work : List (Event E) → Nat
  | [] => 0
  | .visible _ :: tail => work tail
  | .charge n _ _ :: tail => n + work tail

def saved : List (Event E) → Nat
  | [] => 0
  | .visible _ :: tail => saved tail
  | .charge _ n _ :: tail => n + saved tail

def overhead : List (Event E) → Nat
  | [] => 0
  | .visible _ :: tail => overhead tail
  | .charge _ _ n :: tail => n + overhead tail

open Zkc.Modules.Preparation

def handler [DecidableEq K] (provider : Provider K V)
    (prices : Prices K V) (mode : Mode) (external : Handler I S E) :
    Handler (signature K V I) (Cache K V × S) (Event E)
  | .prepare key, (cache, state) =>
      let result := acquire provider prices mode cache key
      ⟨.returned result.value, (result.cache, state),
        [.charge result.work result.saved result.overhead]⟩
  | .external call, (cache, state) =>
      let result := external call state
      ⟨result.outcome, (cache, result.state), result.events.map Event.visible⟩

def StateRel (provider : Provider K V)
    (left right : Cache K V × S) : Prop :=
  Valid provider left.1 ∧ Valid provider right.1 ∧ left.2 = right.2

theorem handlers_related [DecidableEq K] (provider : Provider K V)
    (prices : Prices K V) (external : Handler I S E) :
    HandlerRelated (StateRel provider) view view
      (handler provider prices .direct external) (handler provider prices .memo external) := by
  rintro op ⟨left, s⟩ ⟨right, t⟩ ⟨hl, hr, same⟩
  dsimp at same
  subst t
  cases op with
  | prepare key =>
      have hd := acquire_law provider prices .direct left key hl
      have hm := acquire_law provider prices .memo right key hr
      refine ⟨?_, ⟨hd.2.1, hm.2.1, rfl⟩, rfl⟩
      change Outcome.returned _ = Outcome.returned _
      rw [hd.1, hm.1]
  | external call => exact ⟨rfl, ⟨hl, hr, rfl⟩, rfl⟩

/-- Uniform over finite value-adaptive contexts, including failing external
operations. Initial caches can differ but must both implement this provider. -/
theorem contextual_memo [DecidableEq K] (provider : Provider K V)
    (prices : Prices K V) (external : Handler I S E)
    (program : Proc (signature K V I) A) (left right : Cache K V × S)
    (valid : StateRel provider left right) :
    Related (StateRel provider) view view
      (program.run (handler provider prices .direct external) left)
      (program.run (handler provider prices .memo external) right) :=
  run_related _ _ _ _ _ (handlers_related provider prices external) program left right valid

/-- Caller-visible state, outcome and ordered protocol events survive reuse. -/
theorem contextual_observation [DecidableEq K] (provider : Provider K V)
    (prices : Prices K V) (external : Handler I S E)
    (program : Proc (signature K V I) A) (state : S) :
    let direct := program.run (handler provider prices .direct external) (empty, state)
    let memo := program.run (handler provider prices .memo external) (empty, state)
    (direct.outcome, direct.state.2, observeEvents view direct.events) =
      (memo.outcome, memo.state.2, observeEvents view memo.events) := by
  apply related_observer (StateRel provider) view view Prod.snd Prod.snd
  · exact fun _ _ h => h.2.2
  · exact contextual_memo provider prices external program _ _
      ⟨Zkc.Modules.ImmutableCache.empty_valid provider,
        Zkc.Modules.ImmutableCache.empty_valid provider, rfl⟩

/-- An external operation keeps its dependent reply and actual operation meaning. -/
def externalCalls : OperationInterpretation I (signature K V I) :=
  fun op => .call (.external op) .done

/-- Resolve preparation to its immutable value, retaining every external call. -/
def resolve (provider : Provider K V) : OperationInterpretation (signature K V I) I
  | .prepare key => .done (provider key).1
  | .external op => .call op .done

/-- Forget the private cache only while it implements the selected provider. -/
def Represents (provider : Provider K V) (state : S) (prepared : Cache K V × S) : Prop :=
  Valid provider prepared.1 ∧ state = prepared.2

theorem observe_visible (events : List E) :
    observeEvents view (events.map Event.visible) = events := by
  induction events with
  | nil => rfl
  | cons event events ih => simpa [observeEvents, view] using congrArg (List.cons event) ih

/-- The prepared implementation realizes the immutable reference for any
admitted cache and either policy. The reference has no cache or accounting. -/
theorem resolved_execution [DecidableEq K] (provider : Provider K V)
    (prices : Prices K V) (mode : Mode) (external : Handler I S E)
    (program : Proc (signature K V I) A) (cache : Cache K V) (state : S)
    (valid : Valid provider cache) :
    Related (Represents provider) (fun event => [event]) view
      ((program.interpret (resolve provider)).run external state)
      (program.run (handler provider prices mode external) (cache, state)) := by
  rw [Proc.run_interpret]
  apply run_related (Represents provider) (fun event => [event]) view
  · rintro op s ⟨c, t⟩ ⟨hc, same⟩
    dsimp at same
    subst t
    cases op with
    | prepare key =>
        have law := acquire_law provider prices mode c key hc
        exact ⟨congrArg Outcome.returned law.1.symm, ⟨law.2.1, rfl⟩, rfl⟩
    | external op =>
        simp only [resolve, Proc.run, handler]
        cases external op s with
        | mk outcome state events =>
            cases outcome <;> refine ⟨rfl, ⟨hc, rfl⟩, ?_⟩ <;>
              simpa [Execution.follow, observeEvents] using (observe_visible events).symm
  · exact ⟨valid, rfl⟩

end PIR.Preparation
