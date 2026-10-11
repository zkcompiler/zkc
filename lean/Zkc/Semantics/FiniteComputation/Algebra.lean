import Zkc.Semantics.FiniteComputation.Fold
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Monoidal laws for total ordered folds. Associativity permits adjacent
chunking; a homomorphism permits transport. Permutation requires commutativity.
These laws do not remove domain admission, authorize a failing reducer, or
establish any native kernel's representation and resource obligations. -/

set_option autoImplicit false

namespace Zkc.FiniteComputation

variable {α β M N : Type}

/-- The product of mapped terms in list order, including repeated positions. -/
@[to_additive sumMap /-- The sum of mapped terms in list order, including repeated positions. -/]
def productMap [Monoid M] (items : List α) (body : α → M) : M :=
  (items.map body).prod

/-- The ordinary ordered fold realizes a mapped product with its supplied
initial state. Only monoid laws, not commutativity, are needed. -/
@[to_additive sumMap_fold /-- The ordinary ordered fold realizes a mapped sum with its supplied
initial state. Only additive monoid laws, not commutativity, are needed. -/]
theorem productMap_fold [Monoid M] (items : List α) (body : α → M) (initial : M) :
    Total.fold items (fun _ => true) body (· * ·) initial = initial * productMap items body := by
  induction items generalizing initial with
  | nil => simp [Total.fold, Total.collect, productMap]
  | cons item items ih =>
    simpa [Total.fold, Total.collect, productMap, mul_assoc] using ih (initial * body item)

/-- Chunking is valid when chunks remain in their original order. -/
@[to_additive sumMap_append /-- Chunking is valid when chunks remain in their original order. -/]
theorem productMap_append [Monoid M] (xs ys : List α) (body : α → M) :
    productMap (xs ++ ys) body = productMap xs body * productMap ys body := by
  simp [productMap, List.prod_append]

/-- Mapping before folding can be composed into the total body. -/
@[to_additive sumMap_map /-- Mapping before folding can be composed into the total body. -/]
theorem productMap_map [Monoid M] (items : List α) (f : α → β) (body : β → M) :
    productMap (items.map f) body = productMap items (body ∘ f) := by
  simp [productMap, List.map_map]

/-- Nested traversal can be flattened in outer-then-inner order without a
commutativity assumption. The inner enumeration may depend on the outer item. -/
@[to_additive sumMap_flatMap /-- Nested traversal can be flattened in outer-then-inner order without a
commutativity assumption. The inner enumeration may depend on the outer item. -/]
theorem productMap_flatMap [Monoid M] (items : List α) (inner : α → List β) (body : β → M) :
    productMap (items.flatMap inner) body = productMap items (fun item => productMap (inner item) body) := by
  induction items with
  | nil => simp [productMap]
  | cons item items ih =>
    rw [List.flatMap_cons, productMap_append, ih]
    rfl

/-- An explicit monoid homomorphism transports a total fold. An arbitrary
callback does not supply this law. -/
@[to_additive sumMap_hom /-- An explicit additive monoid homomorphism transports a total fold. An arbitrary
callback does not supply this law. -/]
theorem productMap_hom [Monoid M] [Monoid N] (items : List α) (body : α → M) (f : M →* N) :
    f (productMap items body) = productMap items (fun item => f (body item)) := by
  simp [productMap, map_list_prod, List.map_map, Function.comp_def]

/-- Reordering requires commutativity in addition to the ordinary monoid laws.
`List.Perm` retains multiplicities, unlike converting values to a finite set. -/
@[to_additive sumMap_perm /-- Reordering requires commutativity in addition to the ordinary additive
monoid laws. `List.Perm` retains multiplicities. -/]
theorem productMap_perm [CommMonoid M] (xs ys : List α) (body : α → M) (order : xs.Perm ys) :
    productMap xs body = productMap ys body :=
  (order.map body).prod_eq

/-- A Local computation with total arithmetic can stream an additive fold
without changing a predicate/body failure. Admission remains the caller's job. -/
theorem materialize_sum [AddMonoid M] (items : List α) (keep : α → Except String Bool)
    (body : α → Except String M) :
    Local.materialize items keep body (fun values => .ok values.sum) =
      Local.fold items keep body (fun state value => .ok (state + value)) 0 := by
  simpa only [List.sum_eq_foldl] using Local.materialize_total_step items keep body (· + ·) 0

end Zkc.FiniteComputation
