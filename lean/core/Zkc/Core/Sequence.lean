module

public section

/-! A sequence with logarithmic access that the kernel and compiled code evaluate alike.

A `Sequence` is a binary random-access list: complete binary trees of increasing size,
the most recently pushed value first. `push` is constant time amortized, `get?` is
logarithmic, and a value pushed recently is found in a small tree. Every function is
structurally recursive on the trees, so the kernel reduces it without well-founded
recursion, and arithmetic is on `Nat` literals, which the kernel computes natively.

The sequence is specified by `toList`: `push` is `cons` and `get?` is the list's lookup.
-/

set_option autoImplicit false

namespace Zkc.Source

/-- A binary tree of values. A node records the number of its leaves. -/
inductive Tree (α : Type) where
  | leaf (value : α)
  | node (size : Nat) (left right : Tree α)

namespace Tree

variable {α : Type}

def size : Tree α → Nat
  | leaf _ => 1
  | node size _ _ => size

def toList : Tree α → List α
  | leaf value => [value]
  | node _ left right => left.toList ++ right.toList

/-- The value at a position, counted from the left. -/
def get? : Tree α → Nat → Option α
  | leaf value, 0 => some value
  | leaf _, _ + 1 => none
  | node _ left right, index =>
      cond (Nat.blt index left.size) (left.get? index) (right.get? (index - left.size))

/-- Every node records the number of its leaves. -/
def Formed : Tree α → Prop
  | leaf _ => True
  | node size left right => size = left.size + right.size ∧ left.Formed ∧ right.Formed

theorem size_eq : ∀ (tree : Tree α), tree.Formed → tree.size = tree.toList.length
  | leaf _, _ => rfl
  | node _ left right, ⟨sized, leftFormed, rightFormed⟩ => by
      show _ = (left.toList ++ right.toList).length
      rw [List.length_append, ← size_eq left leftFormed, ← size_eq right rightFormed]
      exact sized

theorem get?_eq : ∀ (tree : Tree α), tree.Formed → ∀ (index : Nat),
    tree.get? index = tree.toList[index]?
  | leaf _, _, 0 => rfl
  | leaf _, _, _ + 1 => rfl
  | node _ left right, ⟨_, leftFormed, rightFormed⟩, index => by
      show cond (Nat.blt index left.size) _ _ = (left.toList ++ right.toList)[index]?
      rw [size_eq left leftFormed]
      cases inLeft : Nat.blt index left.toList.length with
      | true =>
          have bound : index < left.toList.length := Nat.blt_eq.mp inLeft
          simp only [Bool.cond_true, get?_eq left leftFormed, List.getElem?_append_left bound]
      | false =>
          have bound : left.toList.length ≤ index := by
            apply Nat.le_of_not_lt
            intro below
            rw [Nat.blt_eq.mpr below] at inLeft
            cases inLeft
          simp only [Bool.cond_false, get?_eq right rightFormed, List.getElem?_append_right bound]

end Tree

/-- Add a tree before trees that are not smaller, merging trees of equal size. -/
def pushTree {α : Type} : Tree α → List (Tree α) → List (Tree α)
  | tree, [] => [tree]
  | tree, first :: rest =>
      cond (Nat.beq tree.size first.size)
        (pushTree (.node (tree.size + first.size) tree first) rest) (tree :: first :: rest)

/-- The value at a position of the concatenation of the trees. -/
def getTrees? {α : Type} : List (Tree α) → Nat → Option α
  | [], _ => none
  | tree :: rest, index =>
      cond (Nat.blt index tree.size) (tree.get? index) (getTrees? rest (index - tree.size))

theorem flatMap_pushTree {α : Type} : ∀ (trees : List (Tree α)) (tree : Tree α),
    (pushTree tree trees).flatMap Tree.toList = tree.toList ++ trees.flatMap Tree.toList
  | [], tree => by simp [pushTree]
  | first :: rest, tree => by
      cases same : Nat.beq tree.size first.size with
      | true =>
          simp only [pushTree, same, Bool.cond_true, flatMap_pushTree rest, Tree.toList,
            List.flatMap_cons, List.append_assoc]
      | false => simp only [pushTree, same, Bool.cond_false, List.flatMap_cons]

theorem formed_pushTree {α : Type} : ∀ (trees : List (Tree α)) (tree : Tree α),
    tree.Formed → (∀ other ∈ trees, other.Formed) → ∀ other ∈ pushTree tree trees, other.Formed
  | [], tree, formed, _ => by
      intro other member
      simp only [pushTree, List.mem_singleton] at member
      exact member ▸ formed
  | first :: rest, tree, formed, restFormed => by
      cases same : Nat.beq tree.size first.size with
      | true =>
          simp only [pushTree, same, Bool.cond_true]
          exact formed_pushTree rest _
            ⟨rfl, formed, restFormed first List.mem_cons_self⟩
            fun other member => restFormed other (List.mem_cons_of_mem _ member)
      | false =>
          simp only [pushTree, same, Bool.cond_false]
          intro other member
          rcases List.mem_cons.mp member with rfl | later
          · exact formed
          · exact restFormed other later

theorem getTrees?_eq {α : Type} : ∀ (trees : List (Tree α)), (∀ tree ∈ trees, tree.Formed) →
    ∀ (index : Nat), getTrees? trees index = (trees.flatMap Tree.toList)[index]?
  | [], _, _ => rfl
  | tree :: rest, formed, index => by
      have treeFormed := formed tree List.mem_cons_self
      have restFormed : ∀ other ∈ rest, other.Formed :=
        fun other member => formed other (List.mem_cons_of_mem _ member)
      show cond (Nat.blt index tree.size) _ _ = _
      rw [List.flatMap_cons, Tree.size_eq tree treeFormed]
      cases inFirst : Nat.blt index tree.toList.length with
      | true =>
          have bound : index < tree.toList.length := Nat.blt_eq.mp inFirst
          simp only [Bool.cond_true, Tree.get?_eq tree treeFormed, List.getElem?_append_left bound]
      | false =>
          have bound : tree.toList.length ≤ index := by
            apply Nat.le_of_not_lt
            intro below
            rw [Nat.blt_eq.mpr below] at inFirst
            cases inFirst
          simp only [Bool.cond_false, getTrees?_eq rest restFormed, List.getElem?_append_right bound]

/-- A sequence of values, the most recently pushed first. -/
structure Sequence (α : Type) where
  trees : List (Tree α)
  formed : ∀ tree ∈ trees, tree.Formed

namespace Sequence

variable {α : Type}

@[expose] def empty : Sequence α := ⟨[], fun _ member => nomatch member⟩

def push (sequence : Sequence α) (value : α) : Sequence α :=
  ⟨pushTree (.leaf value) sequence.trees,
    formed_pushTree sequence.trees (.leaf value) trivial sequence.formed⟩

/-- The value at a position: position zero is the most recently pushed value. -/
def get? (sequence : Sequence α) (index : Nat) : Option α := getTrees? sequence.trees index

/-- The values, the most recently pushed first. -/
@[expose] def toList (sequence : Sequence α) : List α := sequence.trees.flatMap Tree.toList

@[simp] theorem toList_empty : (empty : Sequence α).toList = [] := rfl

@[simp] theorem toList_push (sequence : Sequence α) (value : α) :
    (sequence.push value).toList = value :: sequence.toList :=
  flatMap_pushTree sequence.trees (.leaf value)

theorem get?_eq (sequence : Sequence α) (index : Nat) :
    sequence.get? index = sequence.toList[index]? :=
  getTrees?_eq sequence.trees sequence.formed index

end Sequence

end Zkc.Source
