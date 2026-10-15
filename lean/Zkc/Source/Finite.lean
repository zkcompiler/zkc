module

public import Zkc.Semantics.ExactRefinement
public import Zkc.Semantics.Interpretation
public import Zkc.Semantics.Interaction

@[expose] public section

/-! Independent ordered finite computations.

Domain admission is performed before iteration, including unused constructors and
all product factors. This model isolates the admission-to-fold boundary; it is
not a decoder or correspondence theorem for native finite operations. Eager
operand evaluation, shape provenance and capacity policies remain caller duties.
-/

set_option autoImplicit false

namespace Zkc.Source.Finite

open PIR (Outcome Proc Stop Signature)

/-- Sequence a checked computation without replacing its first stopping reason. -/
def continueWith {A B : Type} (first : Outcome A) (next : A → Outcome B) : Outcome B :=
  match first with
  | .returned value => next value
  | .stopped reason => .stopped reason

/-- An evaluated admission tree. `before` retains an otherwise unused definition.
Checks represent already evaluated domain conditions; they do not emit events. -/
inductive Domain : Type → Type 1 where
  | elements {A : Type} (items : List A) : Domain A
  | check {A : Type} (passed : Bool) (reason : Stop) (next : Domain A) : Domain A
  | before {A B : Type} (first : Domain B) (next : Domain A) : Domain A
  | zip {A B : Type} (left : Domain A) (right : Domain B) : Domain (A × B)
  | product {A B : Type} (left : Domain A) (right : Domain B) : Domain (A × B)

/-- Domain constructors execute left to right. An empty product factor does not
skip admission of later factors; zip checks equality after admitting both sides. -/
def Domain.admit {A : Type} : Domain A → Outcome (List A)
  | .elements items => .returned items
  | .check passed reason next => if passed then next.admit else .stopped reason
  | .before first next => continueWith first.admit fun _ => next.admit
  | .zip left right => continueWith left.admit fun xs =>
      continueWith right.admit fun ys =>
        if xs.length = ys.length then .returned (xs.zip ys) else .stopped .refused
  | .product left right => continueWith left.admit fun xs =>
      continueWith right.admit fun ys =>
        .returned (xs.flatMap fun x => ys.map fun y => (x, y))

/-- An ordered loop can stop or interact at every reached item. -/
def fold {I : Signature} {A S : Type} (step : S → A → Proc I S) :
    List A → S → Proc I S
  | [], initial => .done initial
  | item :: rest, initial => (step initial item).bind fun state => fold step rest state

/-- Keep checked admission in front of an open computation. -/
def admitThen {I : Signature} {A B : Type} (admission : Outcome A)
    (next : A → Proc I B) : Proc I B :=
  match admission with
  | .stopped reason => .halt reason
  | .returned value => next value

/-- Admission occurs even for zero trips. Captures are explicit parameters of
`step`; its state parameter is the current accumulator at each reached item. -/
def execute {I : Signature} {A S : Type} (domain : Domain A)
    (step : S → A → Proc I S) (initial : S) : Proc I S :=
  admitThen domain.admit fun items => fold step items initial

/-- Pointwise operation translation commutes with every reached loop callback. -/
theorem interpret_fold {I J : Signature} {A S : Type}
    (operations : PIR.OperationInterpretation I J) (step : S → A → Proc I S)
    (items : List A) (initial : S) :
    (fold step items initial).interpret operations =
      fold (fun state item => (step state item).interpret operations) items initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih => simp only [fold, Proc.interpret_bind, ih]

/-- Translation retains the admission stop before any translated action. -/
theorem interpret_admitThen {I J : Signature} {A B : Type}
    (operations : PIR.OperationInterpretation I J) (admission : Outcome A)
    (next : A → Proc I B) :
    (admitThen admission next).interpret operations =
      admitThen admission (fun value => (next value).interpret operations) := by
  cases admission <;> rfl

theorem interpret_execute {I J : Signature} {A S : Type}
    (operations : PIR.OperationInterpretation I J) (domain : Domain A)
    (step : S → A → Proc I S) (initial : S) :
    (execute domain step initial).interpret operations =
      execute domain (fun state item => (step state item).interpret operations) initial := by
  simp only [execute, interpret_admitThen, interpret_fold]

/-- Under a pointwise total callback law, ordered execution is the mathematical
fold. This sufficient law quantifies over all states and all items, including
unreachable ones. `fold_total_on` below permits a restricted law. -/
theorem fold_total {I : Signature} {A S : Type}
    (step : S → A → Proc I S) (total : S → A → S)
    (law : ∀ state item, step state item = .done (total state item))
    (items : List A) (initial : S) :
    fold step items initial = .done (items.foldl total initial) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih => simp only [fold, law, Proc.bind, List.foldl_cons, ih]

/-- An admitted domain and a total callback justify the pure fold denotation.
This conditional theorem does not erase failed admission on other inputs. -/
theorem execute_total {I : Signature} {A S : Type}
    (domain : Domain A) (items : List A) (admitted : domain.admit = .returned items)
    (step : S → A → Proc I S) (total : S → A → S)
    (law : ∀ state item, step state item = .done (total state item)) (initial : S) :
    execute domain step initial = .done (items.foldl total initial) := by
  simp only [execute, admitted, admitThen]
  exact fold_total step total law items initial

/-- Reuse a checked pure equation only after retaining the same admission.
Both paths preserve the same stop on failure, for any open suffix and handler. -/
theorem execute_replace {I : Signature} {A S B : Type}
    (domain : Domain A) (step : S → A → Proc I S) (total : S → A → S)
    (law : ∀ state item, step state item = .done (total state item))
    (candidate : List A → S → S)
    (same : ∀ items state, items.foldl total state = candidate items state)
    (initial : S) (next : S → Proc I B) :
    PIR.ExactRefinement ((execute domain step initial).bind next)
      ((admitThen domain.admit fun items =>
        Proc.done (candidate items initial)).bind next) := by
  refine ⟨?_⟩
  cases admitted : domain.admit with
  | stopped reason => simp only [execute, admitted, admitThen]
  | returned items => rw [execute_total domain items admitted step total law, same]
                      simp only [admitThen]

/-- Pointwise equality of an effectful transition lifts through the entire loop.
No purity, fixed replies or honest-message assumptions are required. -/
theorem fold_congr {I : Signature} {A S : Type} (left right : S → A → Proc I S)
    (same : ∀ state item, left state item = right state item)
    (items : List A) (initial : S) : fold left items initial = fold right items initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
      simp only [fold, same]
      congr 1
      funext state
      exact ih state

/-- Successful product admission exposes the exact factors and enumeration. -/
theorem Domain.admit_product_returned {A B : Type} (left : Domain A) (right : Domain B)
    (items : List (A × B)) :
    (Domain.product left right).admit = .returned items ↔
      ∃ xs ys, left.admit = .returned xs ∧ right.admit = .returned ys ∧
        items = xs.flatMap (fun x => ys.map fun y => (x, y)) := by
  cases hl : left.admit <;> cases hr : right.admit <;>
    simp [Domain.admit, continueWith, hl, hr, eq_comm]

/-- Both factors are admitted before strict zip checks their lengths. -/
theorem Domain.admit_zip_returned {A B : Type} (left : Domain A) (right : Domain B)
    (items : List (A × B)) :
    (Domain.zip left right).admit = .returned items ↔
      ∃ xs ys, left.admit = .returned xs ∧ right.admit = .returned ys ∧
        xs.length = ys.length ∧ items = xs.zip ys := by
  cases hl : left.admit <;> cases hr : right.admit <;>
    simp [Domain.admit, continueWith, hl, hr, eq_comm]
  split <;> simp_all [eq_comm]

/-- A failed left factor stops before the right factor is admitted. -/
theorem Domain.admit_product_left_stop {A B : Type} (left : Domain A) (right : Domain B)
    (reason : Stop) (failed : left.admit = .stopped reason) :
    (Domain.product left right).admit = .stopped reason := by
  simp [Domain.admit, continueWith, failed]

/-- A failed right factor is retained even when the admitted left list is empty. -/
theorem Domain.admit_product_right_stop {A B : Type} (left : Domain A) (right : Domain B)
    (xs : List A) (reason : Stop) (admitted : left.admit = .returned xs)
    (failed : right.admit = .stopped reason) :
    (Domain.product left right).admit = .stopped reason := by
  simp [Domain.admit, continueWith, admitted, failed]

theorem Domain.admit_zip_right_stop {A B : Type} (left : Domain A) (right : Domain B)
    (xs : List A) (reason : Stop) (admitted : left.admit = .returned xs)
    (failed : right.admit = .stopped reason) :
    (Domain.zip left right).admit = .stopped reason := by
  simp [Domain.admit, continueWith, admitted, failed]

/-- An unused admission retains its stop before the returned domain is considered. -/
theorem Domain.admit_before_stop {A B : Type} (first : Domain B) (next : Domain A)
    (reason : Stop) (failed : first.admit = .stopped reason) :
    (Domain.before first next).admit = .stopped reason := by
  simp [Domain.admit, continueWith, failed]

theorem Domain.admit_check_false {A : Type} (reason : Stop) (next : Domain A) :
    (Domain.check false reason next).admit = .stopped reason := rfl

theorem Domain.admit_zip_left_stop {A B : Type} (left : Domain A) (right : Domain B)
    (reason : Stop) (failed : left.admit = .stopped reason) :
    (Domain.zip left right).admit = .stopped reason := by
  simp [Domain.admit, continueWith, failed]

/-- A length mismatch is considered only after both factors have succeeded. -/
theorem Domain.admit_zip_mismatch {A B : Type} (left : Domain A) (right : Domain B)
    (xs : List A) (ys : List B) (hl : left.admit = .returned xs)
    (hr : right.admit = .returned ys) (mismatch : xs.length ≠ ys.length) :
    (Domain.zip left right).admit = .stopped .refused := by
  simp [Domain.admit, continueWith, hl, hr, mismatch]

theorem Domain.admit_before_returned {A B : Type} (first : Domain B) (next : Domain A)
    (items : List A) :
    (Domain.before first next).admit = .returned items ↔
      ∃ ignored, first.admit = .returned ignored ∧ next.admit = .returned items := by
  cases h : first.admit <;> simp [Domain.admit, continueWith, h]

/-- Totality need only hold on admitted items and invariant-preserving states. -/
theorem fold_total_on {I : Signature} {A S : Type}
    (step : S → A → Proc I S) (total : S → A → S) (valid : S → Prop)
    (items : List A) (initial : S) (start : valid initial)
    (law : ∀ state item, item ∈ items → valid state →
      step state item = .done (total state item) ∧ valid (total state item)) :
    fold step items initial = .done (items.foldl total initial) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
      obtain ⟨head, preserved⟩ := law initial item (by simp) start
      simp only [fold, head, Proc.bind, List.foldl_cons]
      exact ih _ preserved (fun state value member stateValid =>
        law state value (by simp [member]) stateValid)

/-- A useful equation may depend on the exact admitted list and initial state.
Its totality premise is restricted to admitted items and a preserved invariant. -/
theorem execute_replace_on {I : Signature} {A S B : Type}
    (domain : Domain A) (step : S → A → Proc I S) (total : S → A → S)
    (valid : S → Prop) (initial : S) (start : valid initial)
    (law : ∀ items, domain.admit = .returned items →
      ∀ state item, item ∈ items → valid state →
        step state item = .done (total state item) ∧ valid (total state item))
    (candidate : List A → S)
    (same : ∀ items, domain.admit = .returned items →
      items.foldl total initial = candidate items)
    (next : S → Proc I B) :
    PIR.ExactRefinement ((execute domain step initial).bind next)
      ((admitThen domain.admit fun items => Proc.done (candidate items)).bind next) := by
  refine ⟨?_⟩
  cases admitted : domain.admit with
  | stopped reason => simp only [execute, admitted, admitThen]
  | returned items =>
      simp only [execute, admitted, admitThen]
      rw [fold_total_on step total valid items initial start (law items admitted),
        same items admitted]

/-- Embed a closed stopping computation into the existing open process model. -/
def toProc {I : Signature} {A : Type} : Outcome A → Proc I A
  | .returned value => .done value
  | .stopped reason => .halt reason

/-- Closed Local iteration retains the first failing callback. -/
def foldChecked {A S : Type} (step : S → A → Outcome S) : List A → S → Outcome S
  | [], initial => .returned initial
  | item :: rest, initial => continueWith (step initial item) (foldChecked step rest)

/-- Closed Local folds are a specialization of open folds, without assuming totality. -/
theorem fold_checked {I : Signature} {A S : Type} (step : S → A → Outcome S)
    (items : List A) (initial : S) :
    fold (fun state item => toProc (I := I) (step state item)) items initial =
      toProc (foldChecked step items initial) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
      cases h : step initial item with
      | stopped reason => simp only [fold, foldChecked, h, toProc, continueWith, Proc.bind]
      | returned state =>
          simp only [fold, foldChecked, h, toProc, continueWith, Proc.bind]
          exact ih state

/-- Concatenation preserves sequencing, including replies and early stops. -/
theorem fold_append {I : Signature} {A S : Type} (step : S → A → Proc I S)
    (first rest : List A) (initial : S) :
    fold step (first ++ rest) initial = (fold step first initial).bind (fold step rest) := by
  induction first generalizing initial with
  | nil => rfl
  | cons item tail ih =>
      simp only [List.cons_append, fold, ih, Proc.bind_assoc]

theorem fold_map {I : Signature} {A B S : Type} (step : S → B → Proc I S)
    (map : A → B) (items : List A) (initial : S) :
    fold step (items.map map) initial = fold (fun state item => step state (map item)) items initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih => simp only [List.map_cons, fold, ih]

theorem fold_flatMap {I : Signature} {A B S : Type} (step : S → B → Proc I S)
    (map : A → List B) (items : List A) (initial : S) :
    fold step (items.flatMap map) initial =
      fold (fun state item => fold step (map item) state) items initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.flatMap_cons, fold_append, fold]
      congr 1
      funext state
      exact ih state

/-- Hoisted admission of both factors is essential even for an empty outer list. -/
theorem execute_product {I : Signature} {A B S : Type}
    (left : Domain A) (right : Domain B) (step : S → A × B → Proc I S) (initial : S) :
    execute (.product left right) step initial =
      admitThen left.admit fun xs => admitThen right.admit fun ys =>
        fold (fun state x => fold (fun state y => step state (x, y)) ys state) xs initial := by
  cases hl : left.admit <;> cases hr : right.admit <;>
    simp [execute, Domain.admit, continueWith, admitThen, hl, hr, fold_flatMap, fold_map]

/-- The fold reuses the existing fixed-trip interaction semantics. -/
theorem fold_replicate {I : Signature} {S : Type} (step : S → Proc I S)
    (count : Nat) (initial : S) :
    fold (fun state (_ : Unit) => step state) (List.replicate count ()) initial =
      PIR.repeatN count step initial := by
  induction count generalizing initial with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, fold, PIR.repeatN, ih]

end Zkc.Source.Finite
