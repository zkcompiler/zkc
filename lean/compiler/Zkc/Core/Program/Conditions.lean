module

public import Zkc.Core.Program.Term

@[expose] public section

/-!
The decision of distinct addresses, with what failed: an address that is not an instruction's
own. Linear use is decided where it is defined (`Linear.lean`).
-/

namespace Zkc.Core

/-! ## Items placed by the bits of a natural -/

/-- Items placed by the low bits of a natural that each has: a binary tree whose leaves, at a
fixed depth, hold the items whose naturals agree on those bits. Placing or finding an item
costs the depth, whatever the naturals are; items that agree on every bit of the depth share a
leaf, where they are compared whole. -/
inductive BitTree (α : Type) where
  | leaf (items : List α)
  | node (zero one : BitTree α)

namespace BitTree
variable {α : Type}

/-- The depth of the trees of the decisions here: 64 bits. -/
abbrev depth : Nat := 64

/-- The items at the leaf that the low `d` bits of `bits` lead to. -/
def find : (d : Nat) → Nat → BitTree α → List α
  | 0, _, .leaf items => items
  | 0, _, .node .. => []
  | _ + 1, _, .leaf _ => []
  | d + 1, bits, .node zero one =>
      cond (Nat.beq (bits % 2) 0) (find d (bits / 2) zero) (find d (bits / 2) one)

/-- The tree with an item placed by the low `d` bits of `bits`. -/
def insert : (d : Nat) → Nat → α → BitTree α → BitTree α
  | 0, _, a, .leaf items => .leaf (a :: items)
  | 0, _, a, .node .. => .leaf [a]
  | d + 1, bits, a, .leaf _ =>
      cond (Nat.beq (bits % 2) 0) (.node (insert d (bits / 2) a (.leaf [])) (.leaf []))
        (.node (.leaf []) (insert d (bits / 2) a (.leaf [])))
  | d + 1, bits, a, .node zero one =>
      cond (Nat.beq (bits % 2) 0) (.node (insert d (bits / 2) a zero) one)
        (.node zero (insert d (bits / 2) a one))

theorem find_empty : ∀ (d bits : Nat), find d bits (.leaf [] : BitTree α) = []
  | 0, _ => rfl
  | _ + 1, _ => rfl

theorem find_insert : ∀ (d bits : Nat) (a : α) (t : BitTree α),
    find d bits (insert d bits a t) = a :: find d bits t
  | 0, _, _, .leaf _ => rfl
  | 0, _, _, .node .. => rfl
  | d + 1, bits, a, .leaf _ => by
      cases parity : Nat.beq (bits % 2) 0 <;>
        simp only [insert, find, parity, Bool.cond_true, Bool.cond_false, find_insert d,
          find_empty]
  | d + 1, bits, a, .node zero one => by
      cases parity : Nat.beq (bits % 2) 0 <;>
        simp only [insert, find, parity, Bool.cond_true, Bool.cond_false, find_insert d]

theorem mem_find_insert : ∀ (d bits bits' : Nat) (a x : α) (t : BitTree α),
    x ∈ find d bits' (insert d bits a t) → x ∈ find d bits' t ∨ x = a
  | 0, _, _, _, _, .leaf _, found => by
      simp only [insert, find, List.mem_cons] at found ⊢
      exact found.symm
  | 0, _, _, _, _, .node .., found => by
      simp only [insert, find, List.mem_cons, List.not_mem_nil, or_false] at found ⊢
      exact Or.inr found
  | d + 1, bits, bits', a, x, .leaf _, found => by
      right
      cases parity : Nat.beq (bits % 2) 0 <;> cases parity' : Nat.beq (bits' % 2) 0 <;>
        simp only [insert, find, parity, parity', Bool.cond_true, Bool.cond_false] at found
      all_goals first
        | exact (mem_find_insert d _ _ a x _ found).resolve_left (by simp [find_empty])
        | simp [find_empty] at found
  | d + 1, bits, bits', a, x, .node zero one, found => by
      cases parity : Nat.beq (bits % 2) 0 <;> cases parity' : Nat.beq (bits' % 2) 0 <;>
        simp only [insert, find, parity, parity', Bool.cond_true, Bool.cond_false] at found ⊢
      all_goals first
        | exact mem_find_insert d _ _ a x _ found
        | exact Or.inl found

theorem mem_find_insert_of_mem : ∀ (d bits bits' : Nat) (a x : α) (t : BitTree α),
    x ∈ find d bits' t → x ∈ find d bits' (insert d bits a t)
  | 0, _, _, _, _, .leaf _, found => List.mem_cons_of_mem _ found
  | 0, _, _, _, _, .node .., found => nomatch found
  | _ + 1, _, _, _, _, .leaf _, found => nomatch found
  | d + 1, bits, bits', a, x, .node zero one, found => by
      cases parity : Nat.beq (bits % 2) 0 <;> cases parity' : Nat.beq (bits' % 2) 0 <;>
        simp only [insert, find, parity, parity', Bool.cond_true, Bool.cond_false] at found ⊢
      all_goals first
        | exact mem_find_insert_of_mem d _ _ a x _ found
        | exact found

variable (keyOf : α → Nat)

/-- A tree holds exactly the items `seen`: each is at the leaf of its natural, and no other item
is in it. -/
def Holds (t : BitTree α) (seen : List α) : Prop :=
  (∀ bits x, x ∈ find depth bits t → x ∈ seen) ∧ ∀ x, x ∈ seen → x ∈ find depth (keyOf x) t

theorem holds_empty : Holds keyOf (.leaf []) [] :=
  ⟨fun _ _ found => by simp [find_empty] at found, fun _ seen => nomatch seen⟩

theorem holds_insert {t : BitTree α} {seen : List α} (a : α) (holds : Holds keyOf t seen) :
    Holds keyOf (insert depth (keyOf a) a t) (a :: seen) := by
  refine ⟨fun bits x found => ?_, fun x seenX => ?_⟩
  · cases mem_find_insert depth (keyOf a) bits a x t found with
    | inl before => exact List.mem_cons_of_mem _ (holds.1 bits x before)
    | inr same => exact same ▸ List.mem_cons_self
  · cases seenX with
    | head => rw [find_insert]; exact List.mem_cons_self
    | tail _ before => exact mem_find_insert_of_mem depth (keyOf a) _ a x t (holds.2 x before)

variable [DecidableEq α]

/-- The tree with the items of a list placed by their naturals, in order; or the first item
that is in the tree already when it comes. -/
def addAll : BitTree α → List α → Except α (BitTree α)
  | t, [] => .ok t
  | t, a :: rest =>
      if a ∈ find depth (keyOf a) t then .error a else addAll (insert depth (keyOf a) a t) rest

theorem addAll_spec : ∀ (t : BitTree α) (seen items : List α), Holds keyOf t seen →
    match addAll keyOf t items with
    | .ok t' => (items.Nodup ∧ ∀ a, a ∈ items → a ∉ seen) ∧ Holds keyOf t' (items.reverse ++ seen)
    | .error _ => ¬ (items.Nodup ∧ ∀ a, a ∈ items → a ∉ seen)
  | t, seen, [], holds => by
      simp only [addAll]
      exact ⟨⟨List.nodup_nil, fun _ none => nomatch none⟩, holds⟩
  | t, seen, a :: rest, holds => by
      by_cases present : a ∈ find depth (keyOf a) t
      · simp only [addAll, present, ↓reduceIte]
        exact fun ⟨_, fresh⟩ => fresh a List.mem_cons_self (holds.1 _ a present)
      · have unseen : a ∉ seen := fun seenA => present (holds.2 a seenA)
        have next := addAll_spec (insert depth (keyOf a) a t) (a :: seen) rest
          (holds_insert keyOf a holds)
        simp only [addAll, present, ↓reduceIte]
        split at next
        · rename_i t' added
          refine ⟨⟨List.nodup_cons.mpr ⟨fun inRest => next.1.2 a inRest List.mem_cons_self,
            next.1.1⟩, fun b inItems => ?_⟩, ?_⟩
          · cases inItems with
            | head => exact unseen
            | tail _ inRest => exact fun seenB => next.1.2 b inRest (List.mem_cons_of_mem _ seenB)
          · simpa [List.reverse_cons, List.append_assoc] using next.2
        · rename_i repeated added
          exact fun ⟨distinct, fresh⟩ => next ⟨(List.nodup_cons.mp distinct).2,
            fun b inRest seenB => match seenB with
              | .head _ => (List.nodup_cons.mp distinct).1 inRest
              | .tail _ seenB => fresh b (List.mem_cons_of_mem _ inRest) seenB⟩

end BitTree

section
variable {D : Dialect}

/-- The address at which the decision of distinct addresses fails: one that two instructions
have (the second, in the order of the addresses), or else the address of an instruction whose
key is the key of a block. It places each address once by the bits of its key. -/
def Term.repeatedAddress {Γ outs : List D.Ty} (t : Term D Γ outs) :
    Option (List (Key × Nat) × Key) :=
  match BitTree.addAll (fun address : List (Key × Nat) × Key => address.2.number) (.leaf [])
      (t.addresses []) with
  | .error address => some address
  | .ok placed =>
      t.blockKeys.findSome? fun key =>
        (BitTree.find BitTree.depth key.number placed).find? fun address => address.2 == key

theorem Term.repeatedAddress_eq_none {Γ outs : List D.Ty} (t : Term D Γ outs) :
    t.repeatedAddress = none ↔ t.Distinct := by
  have spec := BitTree.addAll_spec (fun address : List (Key × Nat) × Key => address.2.number)
    (.leaf []) [] (t.addresses []) (BitTree.holds_empty _)
  unfold Term.repeatedAddress Term.Distinct
  split at spec
  · rename_i placed added
    rw [added]
    obtain ⟨⟨distinct, _⟩, holds⟩ := spec
    simp only [List.findSome?_eq_none_iff, List.find?_eq_none, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq, List.append_nil] at holds ⊢
    constructor
    · intro none
      refine ⟨distinct, fun key inBlocks address inAddresses same => ?_⟩
      exact none key inBlocks address (same ▸ holds.2 address (List.mem_reverse.mpr inAddresses))
        same
    · intro ⟨_, apart⟩ key inBlocks address found same
      exact apart key inBlocks address (List.mem_reverse.mp (holds.1 _ address found)) same
  · rename_i repeated added
    rw [added]
    simp only [reduceCtorEq, false_iff, Bool.and_eq_true, decide_eq_true_eq, not_and]
    exact fun distinct _ => spec ⟨distinct, fun _ _ none => nomatch none⟩

end

end Zkc.Core
