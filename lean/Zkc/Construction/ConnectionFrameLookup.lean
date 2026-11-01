module

public import Zkc.Construction.ConnectionCertificate

@[expose] public section

/-! Exact finite lookup laws. No interpretation of a cell or process is used. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionFrameLookup
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame

theorem calculationCells_length {scope : Scope} {types : List Ty}
    (values : Values (Comp [] scope) types) :
    (ConnectionComputation.cells values).length = types.length := by
  induction values with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih


theorem map_some {α β : Type} (f : α → β) (xs : List α) (i : Nat) (a : α)
    (found : xs[i]? = some a) : (xs.map f)[i]? = some (f a) := by
  rw [List.getElem?_map, found]; rfl

theorem append_left {α : Type} (xs ys : List α) (i : Nat) (a : α)
    (bound : i < xs.length) (found : xs[i]? = some a) :
    (xs ++ ys)[i]? = some a := (List.getElem?_append_left bound).trans found

theorem append_right {α : Type} (xs ys : List α) (i j : Nat) (a : α)
    (bound : xs.length ≤ i) (offset : i - xs.length = j) (found : ys[j]? = some a) :
    (xs ++ ys)[i]? = some a := by
  rw [List.getElem?_append_right bound, offset]; exact found

theorem set_self {α : Type} (xs : List α) (i j : Nat) (a : α)
    (same : i = j) (bound : i < xs.length) : (xs.set j a)[i]? = some a := by
  subst j; exact List.getElem?_set_self bound

theorem set_other {α : Type} (xs : List α) (i j : Nat) (a b : α)
    (different : j ≠ i) (found : xs[i]? = some b) : (xs.set j a)[i]? = some b :=
  (List.getElem?_set_ne different).trans found

theorem cons_zero {α : Type} (a : α) (xs : List α) (i : Nat) (same : i = 0) :
    (a :: xs)[i]? = some a := by subst i; rfl

theorem cons_next {α : Type} (a : α) (xs : List α) (i j : Nat) (b : α)
    (same : i = j + 1) (found : xs[j]? = some b) : (a :: xs)[i]? = some b := by
  subst i; exact found

theorem receive_length {scope : Scope} (xs : Layout scope) (ty : Ty) :
    (ConnectionCertificate.receiveLayout xs ty).length = xs.length + 1 := by
  simp only [ConnectionCertificate.receiveLayout, List.length_append, List.length_map,
    List.length_cons, List.length_nil]

theorem tuple_length {scope : Scope} (xs : Layout scope) (types : List Ty) :
    (ConnectionComputation.tupleLayout xs types).length = xs.length + types.length := by
  simp only [ConnectionComputation.tupleLayout, List.length_append, List.length_map,
    calculationCells_length]

theorem results_length {scope : Scope} (xs : Layout scope) (types : List Ty) :
    (ConnectionComputation.resultsLayout xs types).length = xs.length + types.length := by
  simp only [ConnectionComputation.resultsLayout, List.length_append, List.length_map,
    calculationCells_length]

theorem guard_length {scope : Scope} {xs : Layout scope} {ty : Ty}
    {equality : Equality ty} {left right : Term [] scope ty} {reference : Nat}
    (read : ConnectionCertificate.GuardReadback xs equality left right reference) :
    read.refine.length = xs.length := by
  exact List.length_set

theorem observed_length {scope : Scope} (xs : Layout scope) (suite : String) :
    (observedLayout xs suite).length = xs.length + 1 := by
  simp only [observedLayout, List.length_append, List.length_map, List.length_cons, List.length_nil]

theorem query_length {scope : Scope} (xs : Layout scope) (field suite : String) :
    (queryLayout xs field suite).length = xs.length + 2 := by
  simp only [queryLayout, List.length_append, List.length_map, List.length_cons, List.length_nil]

theorem observed_receive_length {scope : Scope} (xs : Layout scope) (ty : Ty) (suite : String) :
    (observedReceiveLayout xs ty suite).length = xs.length + 2 := by
  simp only [observedReceiveLayout, List.length_append, List.length_map, List.length_cons, List.length_nil]

theorem delivery_length {scope : Scope} (xs : Layout scope) (field suite : String) :
    (deliveryLayout xs field suite).length = xs.length + 3 := by
  simp only [deliveryLayout, List.length_append, List.length_map, List.length_cons, List.length_nil]

theorem projectedLayout_length {scope : Scope} (context : Context) (role : Nat)
    (scopes : List (List Nat)) (layout : Layout scope) (types : List Ty) :
    (projectedLayout context role scopes layout types).length = layout.length + 1 +
      (roleCells role scopes (projectedState (scope := scope) role scopes types)).length +
      (profileCells (scope := RepeatScope types scope) context).length := by
  simp only [projectedLayout, List.length_append, List.length_map, List.length_cons, List.length_nil]

theorem projectedExitLayout_length {scope : Scope} (context : Context) (role : Nat)
    (scopes : List (List Nat)) (layout : Layout scope) (types : List Ty) :
    (projectedExitLayout context role scopes layout types).length = layout.length +
      (roleCells role scopes (calleeOutputs (Δ := scope) role scopes (Operands.identity types))).length +
      (profileCells (scope := .tuple types :: scope) context).length := by
  simp only [projectedExitLayout, List.length_append, List.length_map]


end Zkc.Construction.ConnectionFrameLookup
