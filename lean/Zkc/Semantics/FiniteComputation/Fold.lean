import Zkc.Semantics.FiniteComputation.Domain

/-! Total and failure-aware ordered folds. Item, body result and accumulator
are independent types. Local callbacks have only `Except String` outcomes:
there is no implicit protocol effect, mutable store, trace or resource budget.
Materialization and streaming are separate operations; their equality requires
explicit hypotheses about which callbacks can fail. -/

set_option autoImplicit false

namespace Zkc.FiniteComputation

variable {α β σ ρ : Type}

namespace Total

/-- Selected results in enumeration order; rejected items do not enter `body`. -/
def collect (items : List α) (keep : α → Bool) (body : α → β) : List β :=
  (items.filter keep).map body

/-- An ordered fold makes no associativity or commutativity assumption. -/
def fold (items : List α) (keep : α → Bool) (body : α → β)
    (step : σ → β → σ) (initial : σ) : σ :=
  (collect items keep body).foldl step initial

/-- Folding adjacent chunks retains order and the intermediate state. -/
theorem fold_append (xs ys : List α) (keep : α → Bool) (body : α → β)
    (step : σ → β → σ) (initial : σ) :
    fold (xs ++ ys) keep body step initial =
      fold ys keep body step (fold xs keep body step initial) := by
  simp [fold, collect, List.filter_append, List.foldl_append]

end Total

namespace Local

/-- Evaluate the predicate first and invoke the body only on `true`. -/
def select (keep : α → Except String Bool) (body : α → Except String β)
    (item : α) : Except String (Option β) := do
  if ← keep item then return some (← body item) else return none

/-- Materialize selected body results, stopping at the first predicate/body error. -/
def collect (items : List α) (keep : α → Except String Bool)
    (body : α → Except String β) : Except String (List β) :=
  items.filterMapM (select keep body)

/-- Interleave selection, body execution and accumulator updates left to right. -/
def fold (items : List α) (keep : α → Except String Bool)
    (body : α → Except String β) (step : σ → β → Except String σ)
    (initial : σ) : Except String σ :=
  items.foldlM (fun state item => do
    match ← select keep body item with
    | none => return state
    | some value => step state value) initial

/-- An ordinary reducer is invoked once, after all selected results are ready.
Its result type can differ from both the item and the mapped result types. -/
def materialize (items : List α) (keep : α → Except String Bool)
    (body : α → Except String β) (reducer : List β → Except String ρ) : Except String ρ := do
  reducer (← collect items keep body)

/-- Domain admission precedes all predicate, body and update calls, including
zero-trip folds. Eager arguments and captures must already have been evaluated. -/
def runFold (domain : Domain α) (keep : α → Except String Bool)
    (body : α → Except String β) (step : σ → β → Except String σ)
    (initial : σ) : Except String σ := do
  fold (← domain.enumerate) keep body step initial

/-- Dependent traversal enters an inner computation on each reached outer item.
`inner` includes that lexical entry's operand evaluation and admission. -/
def nestedFold (outer : List α) (inner : α → Except String (List β))
    (step : σ → α → β → Except String σ) (initial : σ) : Except String σ :=
  outer.foldlM (fun state item => do
    (← inner item).foldlM (fun state value => step state item value) state) initial

/-- A rejected item cannot cause a body failure. -/
theorem select_false (keep : α → Except String Bool) (body : α → Except String β)
    (item : α) (skip : keep item = .ok false) : select keep body item = .ok none := by
  simp [select, skip, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A predicate failure takes precedence over any body behavior. -/
theorem select_error (keep : α → Except String Bool) (body : α → Except String β)
    (item : α) (code : String) (failed : keep item = .error code) :
    select keep body item = .error code := by
  simp [select, failed, Bind.bind, Except.bind]

/-- Ordered chunking preserves both successful state and the first failure. -/
theorem fold_append (xs ys : List α) (keep : α → Except String Bool)
    (body : α → Except String β) (step : σ → β → Except String σ) (initial : σ) :
    fold (xs ++ ys) keep body step initial = (do
      let middle ← fold xs keep body step initial
      fold ys keep body step middle) := by
  simp [fold, List.foldlM_append]

/-- Once a prefix stops, no suffix can replace its error with another outcome. -/
theorem fold_prefix_error (xs ys : List α) (keep : α → Except String Bool)
    (body : α → Except String β) (step : σ → β → Except String σ)
    (initial : σ) (code : String) (failed : fold xs keep body step initial = .error code) :
    fold (xs ++ ys) keep body step initial = .error code := by
  rw [fold_append, failed]
  rfl

/-- Admission failure is independent of the callbacks, even if all items would
be filtered out or every callback ignores its input. -/
theorem runFold_error (domain : Domain α) (keep : α → Except String Bool)
    (body : α → Except String β) (step : σ → β → Except String σ)
    (initial : σ) (code : String) (failed : domain.enumerate = .error code) :
    runFold domain keep body step initial = .error code := by
  simp [runFold, failed, Bind.bind, Except.bind]

/-- An empty outer domain does not enter an inner domain. -/
@[simp] theorem nestedFold_nil (inner : α → Except String (List β))
    (step : σ → α → β → Except String σ) (initial : σ) :
    nestedFold [] inner step initial = .ok initial := rfl

/-- Total callbacks embed into Local collection without introducing failures. -/
theorem collect_total (items : List α) (keep : α → Bool) (body : α → β) :
    collect items (fun item => .ok (keep item)) (fun item => .ok (body item)) =
      .ok (Total.collect items keep body) := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    simp only [collect] at ih
    simp only [collect, List.filterMapM_cons]
    cases h : keep item <;>
      simp [select, h, Bind.bind, Except.bind, Pure.pure, Except.pure,
        ih, Total.collect]

/-- Total list-fold semantics and ordered Local execution agree at this
abstract boundary. No native representation or no-effect inference is assumed. -/
theorem fold_total (items : List α) (keep : α → Bool) (body : α → β)
    (step : σ → β → σ) (initial : σ) :
    fold items (fun item => .ok (keep item)) (fun item => .ok (body item))
      (fun state value => .ok (step state value)) initial =
      .ok (Total.fold items keep body step initial) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih =>
    cases h : keep item <;> simp [fold, select, Total.fold, Total.collect, h, fold] at ih ⊢
    all_goals apply ih

/-- Streaming is sound for a total, effect-free update even if predicates or
bodies fail. The statement preserves the exact first error, not just successes. -/
theorem materialize_total_step (items : List α) (keep : α → Except String Bool)
    (body : α → Except String β) (step : σ → β → σ) (initial : σ) :
    materialize items keep body (fun values => .ok (values.foldl step initial)) =
      fold items keep body (fun state value => .ok (step state value)) initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih =>
    unfold materialize collect fold at ih ⊢
    simp only [List.filterMapM_cons, List.foldlM_cons]
    cases select keep body item with
    | error code => simp [Bind.bind, Except.bind]
    | ok selected =>
      cases selected with
      | none =>
        simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at ih ⊢
        exact ih initial
      | some value =>
        simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at ih ⊢
        rw [← ih (step initial value)]
        cases items.filterMapM (select keep body) <;> rfl

/-- Total selection can be materialized before an update that may fail. All
body/predicate results exist, so moving those pure computations changes no error. -/
theorem fold_total_selection (items : List α) (keep : α → Bool) (body : α → β)
    (step : σ → β → Except String σ) (initial : σ) :
    fold items (fun item => .ok (keep item)) (fun item => .ok (body item)) step initial =
      (Total.collect items keep body).foldlM step initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih =>
    cases h : keep item <;>
      simp [fold, select, Total.collect, h, Bind.bind, Except.bind, Pure.pure, Except.pure] at ih ⊢
    · exact ih initial
    · cases step initial (body item) <;> simp_all

/-- This second sufficient condition permits a failing update, but requires
both the predicate and body to be total and effect-free. -/
theorem materialize_total_selection (items : List α) (keep : α → Bool) (body : α → β)
    (step : σ → β → Except String σ) (initial : σ) :
    materialize items (fun item => .ok (keep item)) (fun item => .ok (body item))
      (fun values => values.foldlM step initial) =
      fold items (fun item => .ok (keep item)) (fun item => .ok (body item)) step initial := by
  rw [materialize, collect_total, fold_total_selection]
  rfl

/-- A successful admission plus total callbacks yields the total value. Dynamic
zip length equality must be established by admission before this applies. -/
theorem runFold_total (domain : Domain α) (items : List α)
    (admitted : domain.enumerate = .ok items) (keep : α → Bool) (body : α → β)
    (step : σ → β → σ) (initial : σ) :
    runFold domain (fun item => .ok (keep item)) (fun item => .ok (body item))
      (fun state value => .ok (step state value)) initial =
      .ok (Total.fold items keep body step initial) := by
  unfold runFold
  rw [admitted]
  exact fold_total items keep body step initial

/-- When every inner enumeration is total, nested traversal equals a fold over
its lexicographic flattening, retaining update failures and outer bindings.
This does not authorize hoisting a possibly failing inner admission. -/
theorem nestedFold_total_inner (outer : List α) (inner : α → List β)
    (step : σ → α → β → Except String σ) (initial : σ) :
    nestedFold outer (fun item => .ok (inner item)) step initial =
      (outer.flatMap fun item => (inner item).map fun value => (item, value)).foldlM
        (fun state pair => step state pair.1 pair.2) initial := by
  induction outer generalizing initial with
  | nil => rfl
  | cons item outer ih =>
    simp only [nestedFold, List.foldlM_cons, List.flatMap_cons, List.foldlM_append,
      List.foldlM_map, Bind.bind, Except.bind] at ih ⊢
    cases (inner item).foldlM (fun state value => step state item value) initial with
    | error code => rfl
    | ok state => exact ih state

/-- A materialized reducer has no opportunity to run after a body failure. -/
theorem materialize_error (items : List α) (keep : α → Except String Bool)
    (body : α → Except String β) (reducer : List β → Except String ρ)
    (code : String) (failed : collect items keep body = .error code) :
    materialize items keep body reducer = .error code := by
  simp [materialize, failed, Bind.bind, Except.bind]

end Local
end Zkc.FiniteComputation
