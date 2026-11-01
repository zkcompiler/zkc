module

public import Zkc.Source.Structured.LoopPresentation

@[expose] public section

/-! Ordered observed loops and their interpretations. The only loop engine is
`Finite.fold`; callback equations, not honest replies, justify transport. -/

set_option autoImplicit false

namespace Zkc.Source.Structured.ObservedLoop
open Zkc.Source

variable {I J : PIR.Signature} {A S : Type}

/-- Keep each reached item's actual index and both observation boundaries. -/
def fold (observations : IterationObservations I) (site : String) (index : A → Nat)
    (step : S → A → PIR.Process I S) (items : List A) (initial : S) : PIR.Process I S :=
  Finite.fold (fun state item => observations.within site (index item) (step state item)) items initial

/-- Interpretation commutes with the single observed presentation, including
empty loops, nested callbacks and callbacks that stop before their leave. -/
theorem interpret (operations : PIR.OperationInterpretation I J)
    {left : IterationObservations I} {right : IterationObservations J}
    (same : IterationObservations.Interprets operations left right)
    (site : String) (index : A → Nat) (step : S → A → PIR.Process I S)
    (items : List A) (initial : S) :
    (fold left site index step items initial).interpret operations =
      fold right site index (fun state item => (step state item).interpret operations) items initial := by
  unfold fold
  rw [Finite.interpret_fold]
  exact Finite.fold_congr _ _ (fun _ _ => IterationObservations.within_interpret operations same _ _ _) _ _

def counted (observations : IterationObservations I) (site : String)
    (step : S → Nat → PIR.Process I S) (start count : Nat) (initial : S) : PIR.Process I S :=
  fold observations site id step (List.range' start count) initial

@[simp] theorem counted_zero (observations : IterationObservations I) (site : String)
    (step : S → Nat → PIR.Process I S) (start : Nat) (initial : S) :
    counted observations site step start 0 initial = .done initial := rfl

theorem counted_succ (observations : IterationObservations I) (site : String)
    (step : S → Nat → PIR.Process I S) (start count : Nat) (initial : S) :
    counted observations site step start (count + 1) initial =
      (observations.within site start (step initial start)).bind
        (counted observations site step (start + 1) count) := by
  simp only [counted, fold, List.range'_succ, Finite.fold, id_eq]
  rfl

/-- Reuse a reference's existing zero/successor equations. No new recursive
interpreter or loop-wide correspondence premise is needed. -/
theorem counted_eq (observations : IterationObservations I) (site : String)
    (step : S → Nat → PIR.Process I S)
    (reference : Nat → Nat → S → PIR.Process I S)
    (zero : ∀ index state, reference index 0 state = .done state)
    (succ : ∀ index count state, reference index (count + 1) state =
      (observations.within site index (step state index)).bind (reference (index + 1) count))
    (start count : Nat) (initial : S) :
    counted observations site step start count initial = reference start count initial :=
  LoopPresentation.foldCounted _ reference zero succ start count initial

/-- A pointwise interpretation square and the reference equations suffice for
the complete loop. Stops and arbitrary replies are part of that square. -/
theorem interpret_counted (operations : PIR.OperationInterpretation I J)
    {left : IterationObservations I} {right : IterationObservations J}
    (same : IterationObservations.Interprets operations left right)
    (site : String) (step : S → Nat → PIR.Process I S) (target : S → Nat → PIR.Process J S)
    (equation : ∀ state index, (step state index).interpret operations = target state index)
    (reference : Nat → Nat → S → PIR.Process J S)
    (zero : ∀ index state, reference index 0 state = .done state)
    (succ : ∀ index count state, reference index (count + 1) state =
      (right.within site index (target state index)).bind (reference (index + 1) count))
    (start count : Nat) (initial : S) :
    (counted left site step start count initial).interpret operations = reference start count initial := by
  rw [counted, interpret operations same]
  simp only [equation]
  exact counted_eq right site target reference zero succ start count initial

/-- An index-independent mathematical reference may retain its own signature.
Prove its callback square once; repeated interpretation is library plumbing. -/
theorem interpret_repeated {K : PIR.Signature} (operations : PIR.OperationInterpretation I J)
    {observations : IterationObservations I}
    (same : IterationObservations.Interprets operations observations .silent)
    (site : String) (step : S → PIR.Process I S) (reference : S → PIR.Process K S)
    (target : PIR.OperationInterpretation K J)
    (equation : ∀ state, (step state).interpret operations = (reference state).interpret target)
    (start count : Nat) (initial : S) :
    (counted observations site (fun state _ => step state) start count initial).interpret operations =
      (PIR.repeatN count reference initial).interpret target :=
  interpret_counted operations same site _ (fun state _ => (reference state).interpret target)
    (fun state _ => equation state) (fun _ count state => (PIR.repeatN count reference state).interpret target)
    (fun _ _ => rfl) (fun _ _ _ => by
      simp only [IterationObservations.silent_within, PIR.repeatN, PIR.Process.interpret_bind])
    start count initial

/-- A list traversal uses the same presentation, with indices in source order. -/
def forEach (observations : IterationObservations I) (site : String)
    (step : S → A → Nat → PIR.Process I S) (start : Nat) (items : List A) (initial : S) : PIR.Process I S :=
  fold observations site Prod.snd (fun state item => step state item.1 item.2) (items.zipIdx start) initial

@[simp] theorem forEach_nil (observations : IterationObservations I) (site : String)
    (step : S → A → Nat → PIR.Process I S) (start : Nat) (initial : S) :
    forEach observations site step start [] initial = .done initial := rfl

theorem forEach_cons (observations : IterationObservations I) (site : String)
    (step : S → A → Nat → PIR.Process I S) (start : Nat) (item : A) (rest : List A) (initial : S) :
    forEach observations site step start (item :: rest) initial =
      (observations.within site start (step initial item start)).bind
        (forEach observations site step (start + 1) rest) := by
  simp only [forEach, fold, List.zipIdx_cons, Finite.fold]
  rfl

theorem forEach_eq (observations : IterationObservations I) (site : String)
    (step : S → A → Nat → PIR.Process I S)
    (reference : Nat → List A → S → PIR.Process I S)
    (nil : ∀ index state, reference index [] state = .done state)
    (cons : ∀ index item rest state, reference index (item :: rest) state =
      (observations.within site index (step state item index)).bind (reference (index + 1) rest))
    (start : Nat) (items : List A) (initial : S) :
    forEach observations site step start items initial = reference start items initial := by
  induction items generalizing start initial with
  | nil => exact (nil start initial).symm
  | cons item rest ih =>
    rw [forEach_cons, cons]
    apply congrArg (PIR.Process.bind _)
    funext next
    exact ih (start + 1) next

theorem interpret_forEach (operations : PIR.OperationInterpretation I J)
    {left : IterationObservations I} {right : IterationObservations J}
    (same : IterationObservations.Interprets operations left right)
    (site : String) (step : S → A → Nat → PIR.Process I S)
    (target : S → A → Nat → PIR.Process J S)
    (equation : ∀ state item index, (step state item index).interpret operations = target state item index)
    (reference : Nat → List A → S → PIR.Process J S)
    (nil : ∀ index state, reference index [] state = .done state)
    (cons : ∀ index item rest state, reference index (item :: rest) state =
      (right.within site index (target state item index)).bind (reference (index + 1) rest))
    (start : Nat) (items : List A) (initial : S) :
    (forEach left site step start items initial).interpret operations = reference start items initial := by
  rw [forEach, interpret operations same]
  simp only [equation]
  exact forEach_eq right site target reference nil cons start items initial

/-- Package a shrinking logical state without changing the uniform fold engine. -/
def decrement {State : Nat → Type}
    (step : (remaining : Nat) → State (remaining + 1) → Nat → PIR.Process I (State remaining))
    (state : Sigma State) (index : Nat) : PIR.Process I (Sigma State) :=
  match state with
  | ⟨0, value⟩ => .done ⟨0, value⟩
  | ⟨remaining + 1, value⟩ => (step remaining value index).bind fun next => .done ⟨remaining, next⟩

/-- Only the zero-dimensional result is a terminal value. The mismatch branch
is unreachable when the fold starts at its trip count, as `descending_eq`
proves from the reference's dependent zero/successor equations. -/
def finish {State : Nat → Type} : Sigma State → PIR.Process I (State 0)
  | ⟨0, value⟩ => .done value
  | ⟨_ + 1, _⟩ => .halt .refused

def descending {State : Nat → Type} (observations : IterationObservations I) (site : String)
    (step : (remaining : Nat) → State (remaining + 1) → Nat → PIR.Process I (State remaining))
    (start count : Nat) (initial : State count) : PIR.Process I (State 0) :=
  (counted observations site (decrement step) start count ⟨count, initial⟩).bind finish

@[simp] theorem descending_zero {State : Nat → Type}
    (observations : IterationObservations I) (site : String)
    (step : (remaining : Nat) → State (remaining + 1) → Nat → PIR.Process I (State remaining))
    (start : Nat) (initial : State 0) :
    descending observations site step start 0 initial = .done initial := rfl

theorem descending_succ {State : Nat → Type}
    (observations : IterationObservations I) (site : String)
    (step : (remaining : Nat) → State (remaining + 1) → Nat → PIR.Process I (State remaining))
    (start count : Nat) (initial : State (count + 1)) :
    descending observations site step start (count + 1) initial =
      (observations.within site start (step count initial start)).bind
        (descending observations site step (start + 1) count) := by
  simp only [descending, counted_succ, decrement, IterationObservations.within_eq,
    PIR.Process.bind_assoc, PIR.Process.bind]

theorem descending_eq {State : Nat → Type}
    (observations : IterationObservations I) (site : String)
    (step : (remaining : Nat) → State (remaining + 1) → Nat → PIR.Process I (State remaining))
    (reference : (start count : Nat) → State count → PIR.Process I (State 0))
    (zero : ∀ index state, reference index 0 state = .done state)
    (succ : ∀ index count state, reference index (count + 1) state =
      (observations.within site index (step count state index)).bind (reference (index + 1) count))
    (start count : Nat) (initial : State count) :
    descending observations site step start count initial = reference start count initial := by
  induction count generalizing start with
  | zero => exact (zero start initial).symm
  | succ count ih =>
    rw [descending_succ, succ]
    apply congrArg (PIR.Process.bind _)
    funext next
    exact ih (start + 1) next

/-- The same fold interpretation transports shrinking ghost state. The logical
dimension is retained; no decoding, admissibility or honest-reply premise is added. -/
theorem descending_interpret {State : Nat → Type}
    (operations : PIR.OperationInterpretation I J)
    {left : IterationObservations I} {right : IterationObservations J}
    (same : IterationObservations.Interprets operations left right) (site : String)
    (step : (remaining : Nat) → State (remaining + 1) → Nat → PIR.Process I (State remaining))
    (start count : Nat) (initial : State count) :
    (descending left site step start count initial).interpret operations =
      descending right site (fun remaining state index => (step remaining state index).interpret operations)
        start count initial := by
  have square (state : Sigma State) (index : Nat) :
      (decrement step state index).interpret operations =
        decrement (fun remaining state index => (step remaining state index).interpret operations) state index := by
    rcases state with ⟨remaining, value⟩
    cases remaining <;> simp only [decrement, PIR.Process.interpret_bind, PIR.Process.interpret]
  simp only [descending, PIR.Process.interpret_bind, counted, interpret operations same, square]
  apply congrArg (PIR.Process.bind _)
  funext state
  rcases state with ⟨remaining, value⟩
  cases remaining <;> rfl

end Zkc.Source.Structured.ObservedLoop
