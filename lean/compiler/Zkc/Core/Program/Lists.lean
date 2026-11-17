module

@[expose] public section

/-!
Lists by type: the position of an item in a list, and lists of values of types.

A position (`Member`) names an item of a list: a call names a definition among the headers
before its caller by one. A list of values of types (`HList`) has one value of each type of a
list, of the type at its place. Nothing here is about a dialect or the vocabulary.
-/

namespace Zkc.Core

/-! ## Positions in a list -/

/-- An item of a list with its place: the definition among the headers before a caller that a
call names. -/
inductive Member {α : Type} : List α → α → Type where
  | head {a : α} {rest : List α} : Member (a :: rest) a
  | tail {a b : α} {rest : List α} : Member rest a → Member (b :: rest) a

section
variable {T : Type}

/-- The position, from the front. -/
def Member.index {Γ : List T} {a : T} : Member Γ a → Nat
  | .head => 0
  | .tail x => x.index + 1

/-- The item at a position. -/
def Member.atIndex : (Γ : List T) → Nat → Option ((t : T) × Member Γ t)
  | [], _ => none
  | t :: _, 0 => some ⟨t, .head⟩
  | _ :: Γ, n + 1 => (Member.atIndex Γ n).map fun found => ⟨found.1, .tail found.2⟩

/-- The item at the position of an item is that item, at that position. -/
theorem Member.atIndex_index : ∀ {Γ : List T} {a : T} (x : Member Γ a),
    Member.atIndex Γ x.index = some ⟨a, x⟩
  | _ :: _, _, .head => rfl
  | _ :: _, _, .tail x => by
      simp only [Member.index, Member.atIndex, Member.atIndex_index x, Option.map_some]

/-- The position of an item found at a position is that position. -/
theorem Member.index_of_atIndex :
    ∀ {Γ : List T} {n : Nat} {a : T} {x : Member Γ a},
      Member.atIndex Γ n = some ⟨a, x⟩ → x.index = n
  | [], _, _, _, found => nomatch found
  | _ :: _, 0, _, _, found => by
      simp only [Member.atIndex, Option.some.injEq] at found
      cases found
      rfl
  | _ :: Γ, n + 1, _, _, found => by
      simp only [Member.atIndex, Option.map_eq_some_iff] at found
      obtain ⟨⟨_, y⟩, located, same⟩ := found
      cases same
      simp only [Member.index, Member.index_of_atIndex located]

end

/-! ## Lists of values of types -/

/-- A list of values of types: one value of each type of a list, of the type at its place. -/
inductive HList {α : Type} (V : α → Type) : List α → Type where
  | nil : HList V []
  | cons {a : α} {rest : List α} : V a → HList V rest → HList V (a :: rest)

/-- Every value of a list satisfies a predicate of its type. -/
def HList.All {α : Type} {V : α → Type} (P : ∀ a, V a → Prop) :
    {items : List α} → HList V items → Prop
  | [], .nil => True
  | _ :: _, .cons v rest => P _ v ∧ rest.All P

/-- The values of two lists, one after the other. -/
def HList.append {α : Type} {V : α → Type} :
    {as bs : List α} → HList V as → HList V bs → HList V (as ++ bs)
  | [], _, .nil, ys => ys
  | _ :: _, _, .cons x xs, ys => .cons x (xs.append ys)

/-- The values of a list that is two lists, as the values of each. -/
def HList.split {α : Type} {V : α → Type} :
    (as : List α) → {bs : List α} → HList V (as ++ bs) → HList V as × HList V bs
  | [], _, ys => (.nil, ys)
  | _ :: as, _, .cons x rest => let parts := HList.split as rest; (.cons x parts.1, parts.2)

/-- The values of a list that is two lists, split and put together, are the values. -/
theorem split_append {α : Type} {F : α → Type} :
    ∀ (as : List α) {bs : List α} (xs : HList F (as ++ bs)),
      (HList.split as xs).1.append (HList.split as xs).2 = xs
  | [], _, _ => rfl
  | _ :: as, _, .cons x rest => by
      simp only [HList.split, HList.append, split_append as rest]

/-- Every value of a list with a first value satisfies a predicate exactly when the first does
and every other does. -/
theorem HList.all_cons {α : Type} {F : α → Type} {P : ∀ a, F a → Prop} {a : α} {rest : List α}
    {v : F a} {vs : HList F rest} : (HList.cons v vs).All P ↔ P a v ∧ vs.All P := Iff.rfl

/-- A list of values of one type is that one value. -/
theorem HList.one {α : Type} {F : α → Type} {a : α} :
    ∀ (vs : HList F [a]), ∃ v, vs = .cons v .nil
  | .cons v .nil => ⟨v, rfl⟩

/-- A list of values of two types is those two values. -/
theorem HList.two {α : Type} {F : α → Type} {a b : α} :
    ∀ (vs : HList F [a, b]), ∃ u v, vs = .cons u (.cons v .nil)
  | .cons u (.cons v .nil) => ⟨u, v, rfl⟩

/-- A list of values of three types is those three values. -/
theorem HList.three {α : Type} {F : α → Type} {a b c : α} :
    ∀ (vs : HList F [a, b, c]), ∃ u v w, vs = .cons u (.cons v (.cons w .nil))
  | .cons u (.cons v (.cons w .nil)) => ⟨u, v, w, rfl⟩

end Zkc.Core
