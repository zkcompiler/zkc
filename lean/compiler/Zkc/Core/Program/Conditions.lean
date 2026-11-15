module

public import Zkc.Core.Program.Term

@[expose] public section

/-!
The decisions of the conditions of a body, with what failed: an address that is not an
instruction's own, and a value of a linear type that is not used once, with where.
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

/-- A value of a linear type that is not used once: the blocks and the instruction that bind
it (no instruction for an input of the body), its position among the values bound there, and
how often it is used. -/
structure Misuse where
  blocks : List (Key × Nat)
  instruction : Option Key
  position : Nat
  found : Nat
deriving DecidableEq

variable (linear : D.Ty → Bool)

/-! ## Linear use, counted for the values of linear type only -/

/-- The number of values of linear type among types. -/
def linearCount : List D.Ty → Nat
  | [] => 0
  | τ :: types => cond (linear τ) (linearCount types + 1) (linearCount types)

/-- The counts of the values of linear type among those of types, in order. -/
def keepLinear : List D.Ty → List Nat → List Nat
  | τ :: types, c :: counts =>
      cond (linear τ) (c :: keepLinear types counts) (keepLinear types counts)
  | _, _ => []

theorem linearCount_append : ∀ (items Γ : List D.Ty),
    linearCount linear (items ++ Γ) = linearCount linear items + linearCount linear Γ
  | [], _ => (Nat.zero_add _).symm
  | τ :: items, Γ => by
      cases mark : linear τ <;>
        simp only [List.cons_append, linearCount, mark, Bool.cond_true, Bool.cond_false,
          linearCount_append items Γ, Nat.add_right_comm]

theorem length_keepLinear : ∀ (items : List D.Ty) (v : List Nat), items.length ≤ v.length →
    (keepLinear linear items v).length = linearCount linear items
  | [], _, _ => by cases ‹List Nat› <;> rfl
  | τ :: items, [], short => nomatch short
  | τ :: items, _ :: v, long => by
      have rest := length_keepLinear items v (Nat.le_of_succ_le_succ long)
      cases mark : linear τ <;>
        simp only [keepLinear, linearCount, mark, Bool.cond_true, Bool.cond_false, List.length_cons,
          rest]

theorem keepLinear_append : ∀ (items Γ : List D.Ty) (v : List Nat), items.length ≤ v.length →
    keepLinear linear (items ++ Γ) v =
      keepLinear linear items v ++ keepLinear linear Γ (v.drop items.length)
  | [], Γ, v, _ => by cases v <;> rfl
  | τ :: items, Γ, [], short => nomatch short
  | τ :: items, Γ, c :: v, long => by
      have rest := keepLinear_append items Γ v (Nat.le_of_succ_le_succ long)
      cases mark : linear τ <;>
        simp only [List.cons_append, keepLinear, mark, Bool.cond_true, Bool.cond_false, rest,
          List.length_cons, List.drop_succ_cons, List.cons_append]

theorem keepLinear_replicate : ∀ (Γ : List D.Ty),
    keepLinear linear Γ (List.replicate Γ.length 0) = List.replicate (linearCount linear Γ) 0
  | [] => rfl
  | τ :: Γ => by
      cases mark : linear τ <;>
        simp only [List.length_cons, List.replicate_succ, keepLinear, linearCount, mark,
          Bool.cond_true, Bool.cond_false, keepLinear_replicate Γ]

theorem keepLinear_zipWith (f : Nat → Nat → Nat) : ∀ (Γ : List D.Ty) (a b : List Nat),
    Γ.length ≤ a.length → Γ.length ≤ b.length →
    keepLinear linear Γ (List.zipWith f a b) =
      List.zipWith f (keepLinear linear Γ a) (keepLinear linear Γ b)
  | [], _, _, _, _ => by simp [keepLinear]
  | _ :: _, [], _, short, _ => nomatch short
  | _ :: _, _ :: _, [], _, short => nomatch short
  | τ :: Γ, x :: a, y :: b, longA, longB => by
      have rest := keepLinear_zipWith f Γ a b (Nat.le_of_succ_le_succ longA)
        (Nat.le_of_succ_le_succ longB)
      cases mark : linear τ <;>
        simp only [List.zipWith_cons_cons, keepLinear, mark, Bool.cond_true, Bool.cond_false, rest]

/-- The position among the types of the first value of linear type whose count is not one,
with its count, reading the counts of the values of linear type in order. -/
def misuseAmong : (items : List D.Ty) → List Nat → Option (Nat × Nat)
  | [], _ => none
  | τ :: items, counts =>
      cond (linear τ)
        (match counts with
          | c :: counts =>
              cond (Nat.beq c 1) ((misuseAmong items counts).map fun m => (m.1 + 1, m.2))
                (some (0, c))
          | [] => some (0, 0))
        ((misuseAmong items counts).map fun m => (m.1 + 1, m.2))

theorem misuseAmong_eq_none : ∀ (items : List D.Ty) (v more : List Nat), items.length ≤ v.length →
    (misuseAmong linear items (keepLinear linear items v ++ more) = none ↔
      boundOnce linear items v = true)
  | [], _, _, _ => by simp [misuseAmong, boundOnce]
  | _ :: _, [], _, short => nomatch short
  | τ :: items, c :: v, more, long => by
      have rest := misuseAmong_eq_none items v more (Nat.le_of_succ_le_succ long)
      simp only [boundOnce, List.zip_cons_cons, List.all_cons] at rest ⊢
      cases mark : linear τ
      · simp only [keepLinear, mark, Bool.cond_false, misuseAmong, Option.map_eq_none_iff, rest,
          Bool.not_false, Bool.true_or, Bool.true_and]
      · cases one : Nat.beq c 1
        · have differ : c ≠ 1 := Nat.ne_of_beq_eq_false one
          simp only [keepLinear, mark, Bool.cond_true, List.cons_append, misuseAmong, one,
            Bool.cond_false, reduceCtorEq, Bool.not_true, Bool.false_or,
            Bool.and_eq_true, beq_iff_eq, differ, false_and]
        · have same : (c == 1) = true := beq_iff_eq.mpr (Nat.eq_of_beq_eq_true one)
          simp only [keepLinear, mark, Bool.cond_true, List.cons_append, misuseAmong, one,
            Option.map_eq_none_iff, rest, Bool.not_true, Bool.false_or, same, Bool.true_and]

theorem unusedLinear_iff : ∀ (Γ : List D.Ty) (v : List Nat), Γ.length ≤ v.length →
    (unusedLinear linear Γ v = true ↔ (keepLinear linear Γ v).all (Nat.beq · 0) = true)
  | [], _, _ => by simp [unusedLinear, keepLinear]
  | _ :: _, [], short => nomatch short
  | τ :: Γ, c :: v, long => by
      have rest := unusedLinear_iff Γ v (Nat.le_of_succ_le_succ long)
      simp only [unusedLinear, List.zip_cons_cons, List.all_cons] at rest ⊢
      cases mark : linear τ <;>
        simp only [keepLinear, mark, Bool.cond_true, Bool.cond_false, List.all_cons, rest,
          Bool.not_false, Bool.not_true, Bool.true_or, Bool.false_or, Bool.true_and,
          Bool.and_eq_true, beq_iff_eq, Nat.beq_eq]

theorem agreeLinear_iff : ∀ (Γ : List D.Ty) (a b : List Nat), Γ.length ≤ a.length →
    Γ.length ≤ b.length →
    (agreeLinear linear Γ a b = true ↔ keepLinear linear Γ a = keepLinear linear Γ b)
  | [], _, _, _, _ => by simp [agreeLinear, keepLinear]
  | _ :: _, [], _, short, _ => nomatch short
  | _ :: _, _ :: _, [], _, short => nomatch short
  | τ :: Γ, x :: a, y :: b, longA, longB => by
      have rest := agreeLinear_iff Γ a b (Nat.le_of_succ_le_succ longA)
        (Nat.le_of_succ_le_succ longB)
      simp only [agreeLinear, List.zip_cons_cons, List.all_cons] at rest ⊢
      cases mark : linear τ <;>
        simp only [keepLinear, mark, Bool.cond_true, Bool.cond_false, rest, Bool.not_false,
          Bool.not_true, Bool.true_or, Bool.false_or, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
          List.cons.injEq]

/-- A list of `width` counts, one at a position and none elsewhere. -/
def oneAt : Nat → Nat → List Nat
  | _, 0 => []
  | 0, width + 1 => 1 :: List.replicate width 0
  | position + 1, width + 1 => 0 :: oneAt position width

/-- The position of a variable among the values of linear type of its context, the innermost
first. -/
def Var.linearIndex : {Γ : List D.Ty} → {a : D.Ty} → Var Γ a → Nat
  | _, _, .head => 0
  | b :: _, _, .tail x => cond (linear b) (Var.linearIndex x + 1) (Var.linearIndex x)

/-- One use of a variable, counted for the `width` values of linear type of its context: it
walks the variable only when its type is linear. -/
def Var.linearUses (width : Nat) {Γ : List D.Ty} {a : D.Ty} (x : Var Γ a) : List Nat :=
  cond (linear a) (oneAt (Var.linearIndex linear x) width) (List.replicate width 0)

/-- The uses of a list of variables, counted for the values of linear type. -/
def HList.linearUses (width : Nat) {Γ : List D.Ty} :
    {items : List D.Ty} → HList (Var Γ) items → List Nat
  | [], .nil => List.replicate width 0
  | _ :: _, .cons x rest => addUses (Var.linearUses linear width x) (HList.linearUses width rest)

/-- The use of the count of a loop, counted for the values of linear type. -/
def Times.linearUses (width : Nat) {w : D.Who} {Γ : List D.Ty} : Times D w Γ → List Nat
  | .fixed _ => List.replicate width 0
  | .value count _ => Var.linearUses linear width count

omit linear in
theorem length_varUses {α : Type} : ∀ {Γ : List α} {a : α} (x : Var Γ a),
    (Var.uses x).length = Γ.length
  | _ :: _, _, .head => by simp [Var.uses]
  | _ :: _, _, .tail x => by simp [Var.uses, length_varUses x]

omit linear in
theorem length_hlistUses {α : Type} {Γ : List α} : ∀ {items : List α} (xs : HList (Var Γ) items),
    (HList.uses xs).length = Γ.length
  | [], .nil => by simp [HList.uses]
  | _ :: _, .cons x rest => by
      simp [HList.uses, addUses, List.length_zipWith, length_varUses, length_hlistUses rest]

omit linear in
theorem length_timesUses {w : D.Who} {Γ : List D.Ty} : ∀ (times : Times D w Γ),
    (Times.uses times).length = Γ.length
  | .fixed _ => by simp [Times.uses]
  | .value count _ => length_varUses count

theorem keepLinear_varUses : ∀ {Γ : List D.Ty} {a : D.Ty} (x : Var Γ a),
    keepLinear linear Γ (Var.uses x) = Var.linearUses linear (linearCount linear Γ) x
  | a :: rest, _, .head => by
      cases mark : linear a <;>
        simp only [Var.uses, keepLinear, linearCount, mark, Bool.cond_true, Bool.cond_false,
          keepLinear_replicate, Var.linearUses, Var.linearIndex, oneAt]
  | b :: rest, a, .tail x => by
      have rest := keepLinear_varUses x
      simp only [Var.linearUses] at rest
      cases markB : linear b <;> cases markA : linear a <;>
        simp only [Var.uses, keepLinear, linearCount, markB, markA, Bool.cond_true,
          Bool.cond_false, rest, Var.linearUses, Var.linearIndex, oneAt, List.replicate_succ]

theorem keepLinear_hlistUses {Γ : List D.Ty} : ∀ {items : List D.Ty} (xs : HList (Var Γ) items),
    keepLinear linear Γ (HList.uses xs) = HList.linearUses linear (linearCount linear Γ) xs
  | [], .nil => keepLinear_replicate linear Γ
  | _ :: _, .cons x rest => by
      simp only [HList.uses, addUses, HList.linearUses]
      rw [keepLinear_zipWith linear _ Γ _ _ (Nat.le_of_eq (length_varUses x).symm)
        (Nat.le_of_eq (length_hlistUses rest).symm), keepLinear_varUses, keepLinear_hlistUses rest]

theorem keepLinear_timesUses {w : D.Who} {Γ : List D.Ty} : ∀ (times : Times D w Γ),
    keepLinear linear Γ (Times.uses times) = Times.linearUses linear (linearCount linear Γ) times
  | .fixed _ => keepLinear_replicate linear Γ
  | .value count _ => keepLinear_varUses linear count

/-- The position in a context of the first value of linear type whose counts differ between
two regions, with its count in the second. -/
def firstDifference : (Γ : List D.Ty) → List Nat → List Nat → Nat × Nat
  | [], _, _ => (0, 0)
  | τ :: Γ, first, second =>
      cond (linear τ)
        (match first, second with
          | a :: first, b :: second =>
              cond (Nat.beq a b)
                (let found := firstDifference Γ first second; (found.1 + 1, found.2)) (0, b)
          | _, _ => (0, 0))
        (let found := firstDifference Γ first second; (found.1 + 1, found.2))

/-- The position in a context of the first value of linear type that is used, with its
count. -/
def firstUsed : (Γ : List D.Ty) → List Nat → Nat × Nat
  | [], _ => (0, 0)
  | τ :: Γ, counts =>
      cond (linear τ)
        (match counts with
          | c :: counts =>
              cond (Nat.beq c 0) (let found := firstUsed Γ counts; (found.1 + 1, found.2)) (0, c)
          | [] => (0, 0))
        (let found := firstUsed Γ counts; (found.1 + 1, found.2))

/-- What the arms of a case analysis use of the values around it, counted for the values of
linear type: when every arm uses each of them as often as the first, what any arm uses. -/
def joinArms (Γ : List D.Ty) (blocks : List (Key × Nat)) (key : Key) (width : Nat) :
    List (List Nat) → Except Misuse (List Nat)
  | [] => .ok (List.replicate width 0)
  | first :: others =>
      if others.all (fun other => decide (first = other)) then .ok (others.foldl joinUses first)
      else
        let found := firstDifference linear Γ first
          ((others.find? fun other => !decide (first = other)).getD first)
        .error ⟨blocks, some key, found.1, found.2⟩

mutual
  /-- What `Term.uses` counts, for the values of linear type only, in a context with `width`
  values of linear type; or else the first value of linear type that is not used once, with
  where: at the instruction that binds it (its position among the values that the instruction
  binds), or at a choice, a case analysis or a loop whose regions use a value from around it
  as they may not (its position in the context there). -/
  def Term.linearUses (blocks : List (Key × Nat)) (width : Nat) :
      {Γ outs : List D.Ty} → Term D Γ outs → Except Misuse (List Nat)
    | _, _, .ret xs => .ok (HList.linearUses linear width xs)
    | _, _, .op (res := res) key _ args rest =>
        match Term.linearUses blocks (linearCount linear res + width) rest with
        | .error misuse => .error misuse
        | .ok inner =>
            match misuseAmong linear res inner with
            | some found => .error ⟨blocks, some key, found.1, found.2⟩
            | none =>
                .ok (addUses (inner.drop (linearCount linear res))
                  (HList.linearUses linear width args))
    | _, _, .guard _ _ c _ _ rest =>
        match Term.linearUses blocks width rest with
        | .error misuse => .error misuse
        | .ok inner => .ok (addUses inner (Var.linearUses linear width c))
    | Γ, _, .choose (mid := mid) key _ c _ _ onTrue onFalse rest =>
        match Term.linearUses blocks width onTrue with
        | .error misuse => .error misuse
        | .ok whenTrue =>
            match Term.linearUses blocks width onFalse with
            | .error misuse => .error misuse
            | .ok whenFalse =>
                match Term.linearUses blocks (linearCount linear mid + width) rest with
                | .error misuse => .error misuse
                | .ok inner =>
                    if whenTrue = whenFalse then
                      match misuseAmong linear mid inner with
                      | some found => .error ⟨blocks, some key, found.1, found.2⟩
                      | none =>
                          .ok (addUses (addUses (joinUses whenTrue whenFalse)
                            (inner.drop (linearCount linear mid))) (Var.linearUses linear width c))
                    else
                      let found := firstDifference linear Γ whenTrue whenFalse
                      .error ⟨blocks, some key, found.1, found.2⟩
    | Γ, _, .cases (mid := mid) (payloads := payloads) key _ x _ _ arms rest =>
        match Arms.linearUses blocks key width 0 arms with
        | .error misuse => .error misuse
        | .ok armUses =>
            match Term.linearUses blocks (linearCount linear mid + width) rest with
            | .error misuse => .error misuse
            | .ok inner =>
                match joinArms linear Γ blocks key width armUses with
                | .error misuse => .error misuse
                | .ok outer =>
                    match misuseAmong linear mid inner with
                    | some found => .error ⟨blocks, some key, payloads.length + found.1, found.2⟩
                    | none =>
                        .ok (addUses (addUses outer (inner.drop (linearCount linear mid)))
                          (Var.linearUses linear width x))
    | Γ, _, .loop (carried := carried) (each := each) key w times _ init body rest =>
        match Term.linearUses blocks (linearCount linear (D.index w :: carried) + width) body with
        | .error misuse => .error misuse
        | .ok inBody =>
            match Term.linearUses blocks
                (linearCount linear (carried ++ each.map (D.collected times.size)) + width)
                rest with
            | .error misuse => .error misuse
            | .ok inner =>
                match misuseAmong linear (D.index w :: carried) inBody with
                | some found => .error ⟨blocks, some key, found.1, found.2⟩
                | none =>
                    if (inBody.drop (linearCount linear (D.index w :: carried))).all
                        (Nat.beq · 0) then
                      match misuseAmong linear (carried ++ each.map (D.collected times.size))
                          inner with
                      | some found =>
                          .error ⟨blocks, some key, carried.length + 1 + found.1, found.2⟩
                      | none =>
                          .ok (addUses
                            (addUses (inBody.drop (linearCount linear (D.index w :: carried)))
                              (inner.drop (linearCount linear
                                (carried ++ each.map (D.collected times.size)))))
                            (addUses (HList.linearUses linear width init)
                              (Times.linearUses linear width times)))
                    else
                      let found := firstUsed linear Γ
                        (inBody.drop (linearCount linear (D.index w :: carried)))
                      .error ⟨blocks, some key, found.1, found.2⟩
    | _, _, .block (mid := mid) key number body rest =>
        match Term.linearUses (blocks ++ [(key, number)]) width body with
        | .error misuse => .error misuse
        | .ok inBody =>
            match Term.linearUses blocks (linearCount linear mid + width) rest with
            | .error misuse => .error misuse
            | .ok inner =>
                match misuseAmong linear mid inner with
                | some found => .error ⟨blocks, some key, found.1, found.2⟩
                | none => .ok (addUses inBody (inner.drop (linearCount linear mid)))
    | _, _, .attempt (mid := mid) key w _ body rest =>
        match Term.linearUses blocks (linearCount linear [D.index w] + width) body with
        | .error misuse => .error misuse
        | .ok inBody =>
            match Term.linearUses blocks (linearCount linear mid + width) rest with
            | .error misuse => .error misuse
            | .ok inner =>
                match misuseAmong linear [D.index w] inBody with
                | some found => .error ⟨blocks, some key, found.1, found.2⟩
                | none =>
                    match misuseAmong linear mid inner with
                    | some found => .error ⟨blocks, some key, found.1 + 1, found.2⟩
                    | none =>
                        .ok (addUses (inBody.drop (linearCount linear [D.index w]))
                          (inner.drop (linearCount linear mid)))
  /-- What the arms of a case analysis use, each counted for the values of linear type around
  it; or the first arm (by its position from `index`) whose payload is linear and not used
  once. -/
  def Arms.linearUses (blocks : List (Key × Nat)) (key : Key) (width : Nat) (index : Nat) :
      {Γ mid payloads : List D.Ty} → Arms D Γ mid payloads → Except Misuse (List (List Nat))
    | _, _, _, .nil => .ok []
    | _, _, _, .cons (payload := payload) arm rest =>
        match Term.linearUses blocks (linearCount linear [payload] + width) arm with
        | .error misuse => .error misuse
        | .ok inArm =>
            match Arms.linearUses blocks key width (index + 1) rest with
            | .error misuse => .error misuse
            | .ok others =>
                match misuseAmong linear [payload] inArm with
                | some found => .error ⟨blocks, some key, index, found.2⟩
                | none => .ok (inArm.drop (linearCount linear [payload]) :: others)
end

theorem drop_keepLinear (items : List D.Ty) (v more : List Nat) (long : items.length ≤ v.length) :
    (keepLinear linear items v ++ more).drop (linearCount linear items) = more :=
  List.drop_left' (length_keepLinear linear items v long)

theorem misuseAmong_cases (items : List D.Ty) (v more : List Nat) (long : items.length ≤ v.length) :
    (boundOnce linear items v = true ∧
      misuseAmong linear items (keepLinear linear items v ++ more) = none) ∨
    (boundOnce linear items v = false ∧
      ∃ found, misuseAmong linear items (keepLinear linear items v ++ more) = some found) := by
  cases once : boundOnce linear items v
  · right
    refine ⟨rfl, ?_⟩
    cases decided : misuseAmong linear items (keepLinear linear items v ++ more) with
    | none =>
        have := (misuseAmong_eq_none linear items v more long).mp decided
        rw [once] at this
        cases this
    | some found => exact ⟨found, rfl⟩
  · exact Or.inl ⟨rfl, (misuseAmong_eq_none linear items v more long).mpr once⟩

theorem length_addUses (a b : List Nat) (n : Nat) (la : a.length = n) (lb : b.length = n) :
    (addUses a b).length = n := by
  simp [addUses, List.length_zipWith, la, lb]

theorem length_joinUses (a b : List Nat) (n : Nat) (la : a.length = n) (lb : b.length = n) :
    (joinUses a b).length = n := by
  simp [joinUses, List.length_zipWith, la, lb]

theorem keepLinear_addUses (Γ : List D.Ty) (a b : List Nat) (la : a.length = Γ.length)
    (lb : b.length = Γ.length) :
    keepLinear linear Γ (addUses a b) = addUses (keepLinear linear Γ a) (keepLinear linear Γ b) :=
  keepLinear_zipWith linear _ Γ a b (Nat.le_of_eq la.symm) (Nat.le_of_eq lb.symm)

theorem keepLinear_joinUses (Γ : List D.Ty) (a b : List Nat) (la : a.length = Γ.length)
    (lb : b.length = Γ.length) :
    keepLinear linear Γ (joinUses a b) = joinUses (keepLinear linear Γ a) (keepLinear linear Γ b) :=
  keepLinear_zipWith linear _ Γ a b (Nat.le_of_eq la.symm) (Nat.le_of_eq lb.symm)

theorem length_drop_of (items Γ : List D.Ty) (v : List Nat) (lv : v.length = (items ++ Γ).length) :
    (v.drop items.length).length = Γ.length := by
  simp [lv]

theorem long_of (items Γ : List D.Ty) (v : List Nat) (lv : v.length = (items ++ Γ).length) :
    items.length ≤ v.length := by
  simp [lv]

theorem keepLinear_foldl_joinUses (Γ : List D.Ty) : ∀ (others : List (List Nat)) (first : List Nat),
    first.length = Γ.length → (∀ v, v ∈ others → v.length = Γ.length) →
    keepLinear linear Γ (others.foldl joinUses first) =
        (others.map (keepLinear linear Γ)).foldl joinUses (keepLinear linear Γ first) ∧
      (others.foldl joinUses first).length = Γ.length
  | [], _, lf, _ => ⟨rfl, lf⟩
  | v :: others, first, lf, lo => by
      have lv := lo v List.mem_cons_self
      have rest := keepLinear_foldl_joinUses Γ others (joinUses first v)
        (length_joinUses first v _ lf lv) (fun w inOthers => lo w (List.mem_cons_of_mem _ inOthers))
      simp only [List.foldl_cons, List.map_cons]
      rw [rest.1, keepLinear_joinUses linear Γ first v lf lv]
      exact ⟨rfl, rest.2⟩

theorem all_agree_iff (Γ : List D.Ty) (first : List Nat) (lf : first.length = Γ.length) :
    ∀ (others : List (List Nat)), (∀ v, v ∈ others → v.length = Γ.length) →
    (others.all (agreeLinear linear Γ first) = true ↔
      (others.map (keepLinear linear Γ)).all
        (fun other => decide (keepLinear linear Γ first = other)) = true)
  | [], _ => by simp
  | v :: others, lo => by
      have lv := lo v List.mem_cons_self
      have rest := all_agree_iff Γ first lf others
        (fun w inOthers => lo w (List.mem_cons_of_mem _ inOthers))
      simp only [List.all_cons, List.map_cons, Bool.and_eq_true, decide_eq_true_eq, rest,
        agreeLinear_iff linear Γ first v (Nat.le_of_eq lf.symm) (Nat.le_of_eq lv.symm)]

mutual
  /-- The pass over the values of linear type counts what `Term.uses` counts, for those
  values, and fails where it fails. -/
  theorem Term.linearUses_spec : ∀ (blocks : List (Key × Nat)) {Γ outs : List D.Ty}
      (t : Term D Γ outs),
      match t.uses linear with
      | none => ∃ misuse, Term.linearUses linear blocks (linearCount linear Γ) t = .error misuse
      | some v => v.length = Γ.length ∧
          Term.linearUses linear blocks (linearCount linear Γ) t = .ok (keepLinear linear Γ v)
    | blocks, Γ, _, .ret xs => by
        simp only [Term.uses, Term.linearUses]
        exact ⟨length_hlistUses xs, by rw [keepLinear_hlistUses]⟩
    | blocks, Γ, _, .op (res := res) key o args rest => by
        have ih := Term.linearUses_spec blocks rest
        rw [linearCount_append] at ih
        cases found : rest.uses linear with
        | none =>
            rw [found] at ih
            obtain ⟨misuse, failed⟩ := ih
            simp only [Term.uses, found, Option.bind_eq_bind, Option.bind_none, Term.linearUses,
              failed]
            exact ⟨misuse, rfl⟩
        | some inner =>
            rw [found] at ih
            obtain ⟨length, kept⟩ := ih
            have long := long_of res Γ inner length
            rw [keepLinear_append linear res Γ inner long] at kept
            simp only [Term.uses, found, Option.bind_eq_bind, Option.bind_some, Term.linearUses,
              kept]
            rcases misuseAmong_cases linear res inner (keepLinear linear Γ (inner.drop res.length))
                long with ⟨once, none⟩ | ⟨twice, found, some⟩
            · simp only [once, ↓reduceIte, none,
                drop_keepLinear linear res inner (keepLinear linear Γ (inner.drop res.length)) long]
              have ld := length_drop_of res Γ inner length
              exact ⟨length_addUses _ _ _ ld (length_hlistUses args),
                by rw [keepLinear_addUses linear Γ _ _ ld (length_hlistUses args),
                  keepLinear_hlistUses]⟩
            · simp only [twice, Bool.false_eq_true, ↓reduceIte, some]
              exact ⟨_, rfl⟩
    | blocks, Γ, _, .guard key w c ok why rest => by
        have ih := Term.linearUses_spec blocks rest
        cases found : rest.uses linear with
        | none =>
            rw [found] at ih
            obtain ⟨misuse, failed⟩ := ih
            simp only [Term.uses, found, Option.bind_eq_bind, Option.bind_none, Term.linearUses,
              failed]
            exact ⟨misuse, rfl⟩
        | some inner =>
            rw [found] at ih
            obtain ⟨length, kept⟩ := ih
            simp only [Term.uses, found, Option.bind_eq_bind, Option.bind_some, Term.linearUses,
              kept]
            exact ⟨length_addUses _ _ _ length (length_varUses c),
              by rw [keepLinear_addUses linear Γ _ _ length (length_varUses c),
                keepLinear_varUses]⟩
    | blocks, Γ, _, .choose (mid := mid) key w c ok gives onTrue onFalse rest => by
        have ihTrue := Term.linearUses_spec blocks onTrue
        have ihFalse := Term.linearUses_spec blocks onFalse
        have ih := Term.linearUses_spec blocks rest
        rw [linearCount_append] at ih
        cases foundTrue : onTrue.uses linear with
        | none =>
            rw [foundTrue] at ihTrue
            obtain ⟨misuse, failed⟩ := ihTrue
            simp only [Term.uses, foundTrue, Option.bind_eq_bind, Option.bind_none,
              Term.linearUses, failed]
            exact ⟨misuse, rfl⟩
        | some whenTrue =>
        rw [foundTrue] at ihTrue
        obtain ⟨lengthTrue, keptTrue⟩ := ihTrue
        cases foundFalse : onFalse.uses linear with
        | none =>
            rw [foundFalse] at ihFalse
            obtain ⟨misuse, failed⟩ := ihFalse
            simp only [Term.uses, foundTrue, foundFalse, Option.bind_eq_bind, Option.bind_some,
              Option.bind_none, Term.linearUses, keptTrue, failed]
            exact ⟨misuse, rfl⟩
        | some whenFalse =>
        rw [foundFalse] at ihFalse
        obtain ⟨lengthFalse, keptFalse⟩ := ihFalse
        cases found : rest.uses linear with
        | none =>
            rw [found] at ih
            obtain ⟨misuse, failed⟩ := ih
            simp only [Term.uses, foundTrue, foundFalse, found, Option.bind_eq_bind,
              Option.bind_some, Option.bind_none, Term.linearUses, keptTrue, keptFalse, failed]
            exact ⟨misuse, rfl⟩
        | some inner =>
        rw [found] at ih
        obtain ⟨length, kept⟩ := ih
        have long := long_of mid Γ inner length
        rw [keepLinear_append linear mid Γ inner long] at kept
        simp only [Term.uses, foundTrue, foundFalse, found, Option.bind_eq_bind, Option.bind_some,
          Term.linearUses, keptTrue, keptFalse, kept]
        have agree := agreeLinear_iff linear Γ whenTrue whenFalse (Nat.le_of_eq lengthTrue.symm)
          (Nat.le_of_eq lengthFalse.symm)
        by_cases same : keepLinear linear Γ whenTrue = keepLinear linear Γ whenFalse
        · have agreed := agree.mpr same
          rcases misuseAmong_cases linear mid inner (keepLinear linear Γ (inner.drop mid.length))
              long with ⟨once, none⟩ | ⟨twice, foundMid, some⟩
          · simp only [agreed, once, and_self, ↓reduceIte, same, none,
              drop_keepLinear linear mid inner (keepLinear linear Γ (inner.drop mid.length)) long]
            have ld := length_drop_of mid Γ inner length
            have lj := length_joinUses _ _ _ lengthTrue lengthFalse
            refine ⟨length_addUses _ _ _ (length_addUses _ _ _ lj ld) (length_varUses c), ?_⟩
            rw [keepLinear_addUses linear Γ _ _ (length_addUses _ _ _ lj ld) (length_varUses c),
              keepLinear_addUses linear Γ _ _ lj ld,
              keepLinear_joinUses linear Γ _ _ lengthTrue lengthFalse, keepLinear_varUses, same]
          · simp only [agreed, twice, Bool.false_eq_true, and_false, ↓reduceIte, same, some]
            exact ⟨_, rfl⟩
        · have disagreed : ¬ agreeLinear linear Γ whenTrue whenFalse = true :=
            fun agreed => same (agree.mp agreed)
          simp only [disagreed, ↓reduceIte, same]
          exact ⟨_, rfl⟩
    | blocks, Γ, _, .cases (mid := mid) (payloads := payloads) key w x ok gives arms rest => by
        have ihArms := Arms.linearUses_spec blocks key 0 arms
        have ih := Term.linearUses_spec blocks rest
        rw [linearCount_append] at ih
        cases foundArms : Arms.uses linear arms with
        | none =>
            rw [foundArms] at ihArms
            obtain ⟨misuse, failed⟩ := ihArms
            simp only [Term.uses, foundArms, Option.bind_eq_bind, Option.bind_none,
              Term.linearUses, failed]
            exact ⟨misuse, rfl⟩
        | some vs =>
        rw [foundArms] at ihArms
        obtain ⟨lengthArms, keptArms⟩ := ihArms
        cases found : rest.uses linear with
        | none =>
            rw [found] at ih
            obtain ⟨misuse, failed⟩ := ih
            simp only [Term.uses, foundArms, found, Option.bind_eq_bind, Option.bind_some,
              Option.bind_none, Term.linearUses, keptArms, failed]
            exact ⟨misuse, rfl⟩
        | some inner =>
        rw [found] at ih
        obtain ⟨length, kept⟩ := ih
        have long := long_of mid Γ inner length
        rw [keepLinear_append linear mid Γ inner long] at kept
        have ld := length_drop_of mid Γ inner length
        simp only [Term.uses, foundArms, found, Option.bind_eq_bind, Option.bind_some,
          Term.linearUses, keptArms, kept]
        cases vs with
        | nil =>
            simp only [List.map_nil, joinArms]
            have lz : (List.replicate Γ.length 0).length = Γ.length := List.length_replicate
            rcases misuseAmong_cases linear mid inner (keepLinear linear Γ (inner.drop mid.length))
                long with ⟨once, none⟩ | ⟨twice, foundMid, some⟩
            · simp only [once, ↓reduceIte, none,
                drop_keepLinear linear mid inner (keepLinear linear Γ (inner.drop mid.length)) long]
              refine ⟨length_addUses _ _ _ (length_addUses _ _ _ lz ld) (length_varUses x), ?_⟩
              rw [keepLinear_addUses linear Γ _ _ (length_addUses _ _ _ lz ld) (length_varUses x),
                keepLinear_addUses linear Γ _ _ lz ld, keepLinear_replicate, keepLinear_varUses]
            · simp only [twice, Bool.false_eq_true, ↓reduceIte, some]
              exact ⟨_, rfl⟩
        | cons first others =>
            have lf := lengthArms first List.mem_cons_self
            have lo : ∀ v, v ∈ others → v.length = Γ.length :=
              fun v inOthers => lengthArms v (List.mem_cons_of_mem _ inOthers)
            have agree := all_agree_iff linear Γ first lf others lo
            simp only [List.map_cons, joinArms]
            by_cases agreed : others.all (agreeLinear linear Γ first) = true
            · have agreedKept := agree.mp agreed
              have folded := keepLinear_foldl_joinUses linear Γ others first lf lo
              simp only [agreed, ↓reduceIte, agreedKept]
              rcases misuseAmong_cases linear mid inner
                  (keepLinear linear Γ (inner.drop mid.length)) long
                with ⟨once, none⟩ | ⟨twice, foundMid, some⟩
              · simp only [once, ↓reduceIte, none, drop_keepLinear linear mid inner
                  (keepLinear linear Γ (inner.drop mid.length)) long]
                refine ⟨length_addUses _ _ _ (length_addUses _ _ _ folded.2 ld)
                  (length_varUses x), ?_⟩
                rw [keepLinear_addUses linear Γ _ _ (length_addUses _ _ _ folded.2 ld)
                    (length_varUses x),
                  keepLinear_addUses linear Γ _ _ folded.2 ld, folded.1, keepLinear_varUses]
              · simp only [twice, Bool.false_eq_true, ↓reduceIte, some]
                exact ⟨_, rfl⟩
            · have disagreed : ¬ (others.map (keepLinear linear Γ)).all
                  (fun other => decide (keepLinear linear Γ first = other)) = true :=
                fun agreedKept => agreed (agree.mpr agreedKept)
              simp only [agreed, disagreed, Option.bind_none]
              exact ⟨_, rfl⟩
    | blocks, Γ, _, .loop (carried := carried) (each := each) key w times gives init body rest => by
        have ihBody := Term.linearUses_spec blocks body
        have ih := Term.linearUses_spec blocks rest
        rw [linearCount_append] at ih
        have count : linearCount linear (D.index w :: (carried ++ Γ)) =
            linearCount linear (D.index w :: carried) + linearCount linear Γ :=
          linearCount_append linear (D.index w :: carried) Γ
        rw [count] at ihBody
        cases foundBody : body.uses linear with
        | none =>
            rw [foundBody] at ihBody
            obtain ⟨misuse, failed⟩ := ihBody
            simp only [Term.uses, foundBody, Option.bind_eq_bind, Option.bind_none,
              Term.linearUses, failed]
            exact ⟨misuse, rfl⟩
        | some inBody =>
        rw [foundBody] at ihBody
        obtain ⟨lengthBody, keptBody⟩ := ihBody
        have longBody : (D.index w :: carried).length ≤ inBody.length := by simp [lengthBody]
        have parts := keepLinear_append linear (D.index w :: carried) Γ inBody longBody
        simp only [List.cons_append, List.length_cons] at parts
        rw [parts] at keptBody
        cases found : rest.uses linear with
        | none =>
            rw [found] at ih
            obtain ⟨misuse, failed⟩ := ih
            simp only [Term.uses, foundBody, found, Option.bind_eq_bind, Option.bind_some,
              Option.bind_none, Term.linearUses, keptBody, failed]
            exact ⟨misuse, rfl⟩
        | some inner =>
        rw [found] at ih
        obtain ⟨length, kept⟩ := ih
        have long := long_of (carried ++ each.map (D.collected times.size)) Γ inner length
        rw [keepLinear_append linear _ Γ inner long] at kept
        have ld := length_drop_of (carried ++ each.map (D.collected times.size)) Γ inner length
        have outerLength : (inBody.drop (carried.length + 1)).length = Γ.length := by
          simp [lengthBody]
        simp only [Term.uses, foundBody, found, Option.bind_eq_bind, Option.bind_some,
          Term.linearUses, keptBody, kept]
        rcases misuseAmong_cases linear (D.index w :: carried) inBody
            (keepLinear linear Γ (inBody.drop (carried.length + 1))) longBody
          with ⟨onceBody, noneBody⟩ | ⟨twiceBody, foundBody', someBody⟩
        · have unused := unusedLinear_iff linear Γ (inBody.drop (carried.length + 1))
            (Nat.le_of_eq outerLength.symm)
          simp only [noneBody, drop_keepLinear linear (D.index w :: carried) inBody
            (keepLinear linear Γ (inBody.drop (carried.length + 1))) longBody]
          by_cases free : unusedLinear linear Γ (inBody.drop (carried.length + 1)) = true
          · have freeKept := unused.mp free
            rcases misuseAmong_cases linear (carried ++ each.map (D.collected times.size)) inner
                (keepLinear linear Γ
                  (inner.drop (carried ++ each.map (D.collected times.size)).length)) long
              with ⟨once, none⟩ | ⟨twice, foundMid, some⟩
            · simp only [onceBody, free, once, and_self, ↓reduceIte, freeKept, none,
                drop_keepLinear linear (carried ++ each.map (D.collected times.size)) inner
                  (keepLinear linear Γ
                    (inner.drop (carried ++ each.map (D.collected times.size)).length)) long]
              have lu := length_addUses _ _ _ (length_hlistUses init) (length_timesUses times)
              have lo := length_addUses _ _ _ outerLength ld
              refine ⟨length_addUses _ _ _ lo lu, ?_⟩
              rw [keepLinear_addUses linear Γ _ _ lo lu,
                keepLinear_addUses linear Γ _ _ outerLength ld,
                keepLinear_addUses linear Γ _ _ (length_hlistUses init) (length_timesUses times),
                keepLinear_hlistUses, keepLinear_timesUses]
            · simp only [onceBody, free, twice, Bool.false_eq_true, and_false, ↓reduceIte,
                freeKept, some]
              exact ⟨_, rfl⟩
          · have notKept : ¬ (keepLinear linear Γ (inBody.drop (carried.length + 1))).all
                (Nat.beq · 0) = true := fun freeKept => free (unused.mpr freeKept)
            simp only [onceBody, free, notKept]
            exact ⟨_, rfl⟩
        · simp only [twiceBody, Bool.false_eq_true, false_and, ↓reduceIte, someBody]
          exact ⟨_, rfl⟩
    | blocks, Γ, _, .block (mid := mid) key number body rest => by
        have ihBody := Term.linearUses_spec (blocks ++ [(key, number)]) body
        have ih := Term.linearUses_spec blocks rest
        rw [linearCount_append] at ih
        cases foundBody : body.uses linear with
        | none =>
            rw [foundBody] at ihBody
            obtain ⟨misuse, failed⟩ := ihBody
            simp only [Term.uses, foundBody, Option.bind_eq_bind, Option.bind_none,
              Term.linearUses, failed]
            exact ⟨misuse, rfl⟩
        | some inBody =>
        rw [foundBody] at ihBody
        obtain ⟨lengthBody, keptBody⟩ := ihBody
        cases found : rest.uses linear with
        | none =>
            rw [found] at ih
            obtain ⟨misuse, failed⟩ := ih
            simp only [Term.uses, foundBody, found, Option.bind_eq_bind, Option.bind_some,
              Option.bind_none, Term.linearUses, keptBody, failed]
            exact ⟨misuse, rfl⟩
        | some inner =>
        rw [found] at ih
        obtain ⟨length, kept⟩ := ih
        have long := long_of mid Γ inner length
        rw [keepLinear_append linear mid Γ inner long] at kept
        simp only [Term.uses, foundBody, found, Option.bind_eq_bind, Option.bind_some,
          Term.linearUses, keptBody, kept]
        rcases misuseAmong_cases linear mid inner (keepLinear linear Γ (inner.drop mid.length)) long
          with ⟨once, none⟩ | ⟨twice, foundMid, some⟩
        · simp only [once, ↓reduceIte, none,
            drop_keepLinear linear mid inner (keepLinear linear Γ (inner.drop mid.length)) long]
          have ld := length_drop_of mid Γ inner length
          exact ⟨length_addUses _ _ _ lengthBody ld,
            by rw [keepLinear_addUses linear Γ _ _ lengthBody ld]⟩
        · simp only [twice, Bool.false_eq_true, ↓reduceIte, some]
          exact ⟨_, rfl⟩
    | blocks, Γ, _, .attempt (mid := mid) key w owns body rest => by
        have ihBody := Term.linearUses_spec blocks body
        have ih := Term.linearUses_spec blocks rest
        rw [linearCount_append] at ih
        have count : linearCount linear (D.index w :: Γ) =
            linearCount linear [D.index w] + linearCount linear Γ :=
          linearCount_append linear [D.index w] Γ
        rw [count] at ihBody
        cases foundBody : body.uses linear with
        | none =>
            rw [foundBody] at ihBody
            obtain ⟨misuse, failed⟩ := ihBody
            simp only [Term.uses, foundBody, Option.bind_eq_bind, Option.bind_none,
              Term.linearUses, failed]
            exact ⟨misuse, rfl⟩
        | some inBody =>
        rw [foundBody] at ihBody
        obtain ⟨lengthBody, keptBody⟩ := ihBody
        have longBody : [D.index w].length ≤ inBody.length := by simp [lengthBody]
        have parts := keepLinear_append linear [D.index w] Γ inBody longBody
        simp only [List.singleton_append, List.length_singleton] at parts
        rw [parts] at keptBody
        cases found : rest.uses linear with
        | none =>
            rw [found] at ih
            obtain ⟨misuse, failed⟩ := ih
            simp only [Term.uses, foundBody, found, Option.bind_eq_bind, Option.bind_some,
              Option.bind_none, Term.linearUses, keptBody, failed]
            exact ⟨misuse, rfl⟩
        | some inner =>
        rw [found] at ih
        obtain ⟨length, kept⟩ := ih
        have long := long_of mid Γ inner length
        rw [keepLinear_append linear mid Γ inner long] at kept
        simp only [Term.uses, foundBody, found, Option.bind_eq_bind, Option.bind_some,
          Term.linearUses, keptBody, kept]
        rcases misuseAmong_cases linear [D.index w] inBody (keepLinear linear Γ (inBody.drop 1))
            longBody with ⟨onceBody, noneBody⟩ | ⟨twiceBody, foundBody', someBody⟩
        · rcases misuseAmong_cases linear mid inner (keepLinear linear Γ (inner.drop mid.length))
              long with ⟨once, none⟩ | ⟨twice, foundMid, some⟩
          · simp only [onceBody, once, and_self, ↓reduceIte, noneBody, none,
              drop_keepLinear linear [D.index w] inBody (keepLinear linear Γ (inBody.drop 1))
                longBody,
              drop_keepLinear linear mid inner (keepLinear linear Γ (inner.drop mid.length)) long]
            have ldBody : (inBody.drop 1).length = Γ.length := by simp [lengthBody]
            have ld := length_drop_of mid Γ inner length
            exact ⟨length_addUses _ _ _ ldBody ld,
              by rw [keepLinear_addUses linear Γ _ _ ldBody ld]⟩
          · simp only [onceBody, twice, Bool.false_eq_true, and_false, ↓reduceIte, noneBody, some]
            exact ⟨_, rfl⟩
        · simp only [twiceBody, Bool.false_eq_true, false_and, ↓reduceIte, someBody]
          exact ⟨_, rfl⟩
  theorem Arms.linearUses_spec : ∀ (blocks : List (Key × Nat)) (key : Key) (index : Nat)
      {Γ mid payloads : List D.Ty} (arms : Arms D Γ mid payloads),
      match Arms.uses linear arms with
      | none => ∃ misuse,
          Arms.linearUses linear blocks key (linearCount linear Γ) index arms = .error misuse
      | some vs => (∀ v, v ∈ vs → v.length = Γ.length) ∧
          Arms.linearUses linear blocks key (linearCount linear Γ) index arms =
            .ok (vs.map (keepLinear linear Γ))
    | blocks, key, index, Γ, _, _, .nil => by
        simp only [Arms.uses, Arms.linearUses, List.map_nil]
        exact ⟨fun _ none => (nomatch none), trivial⟩
    | blocks, key, index, Γ, _, _, .cons (payload := payload) arm rest => by
        have ihArm := Term.linearUses_spec blocks arm
        have ihRest := Arms.linearUses_spec blocks key (index + 1) rest
        have count : linearCount linear (payload :: Γ) =
            linearCount linear [payload] + linearCount linear Γ :=
          linearCount_append linear [payload] Γ
        rw [count] at ihArm
        cases foundArm : arm.uses linear with
        | none =>
            rw [foundArm] at ihArm
            obtain ⟨misuse, failed⟩ := ihArm
            simp only [Arms.uses, foundArm, Option.bind_eq_bind, Option.bind_none, Arms.linearUses,
              failed]
            exact ⟨misuse, rfl⟩
        | some inArm =>
        rw [foundArm] at ihArm
        obtain ⟨lengthArm, keptArm⟩ := ihArm
        have long : [payload].length ≤ inArm.length := by simp [lengthArm]
        have parts := keepLinear_append linear [payload] Γ inArm long
        simp only [List.singleton_append, List.length_singleton] at parts
        rw [parts] at keptArm
        cases foundRest : Arms.uses linear rest with
        | none =>
            rw [foundRest] at ihRest
            obtain ⟨misuse, failed⟩ := ihRest
            simp only [Arms.uses, foundArm, foundRest, Option.bind_eq_bind, Option.bind_some,
              Option.bind_none, Arms.linearUses, keptArm, failed]
            exact ⟨misuse, rfl⟩
        | some others =>
        rw [foundRest] at ihRest
        obtain ⟨lengthRest, keptRest⟩ := ihRest
        simp only [Arms.uses, foundArm, foundRest, Option.bind_eq_bind, Option.bind_some,
          Arms.linearUses, keptArm, keptRest]
        rcases misuseAmong_cases linear [payload] inArm (keepLinear linear Γ (inArm.drop 1)) long
          with ⟨once, none⟩ | ⟨twice, found, some⟩
        · simp only [once, ↓reduceIte, none,
            drop_keepLinear linear [payload] inArm (keepLinear linear Γ (inArm.drop 1)) long,
            List.map_cons]
          refine ⟨fun v inList => ?_, trivial⟩
          cases inList with
          | head => simp [lengthArm]
          | tail _ inOthers => exact lengthRest v inOthers
        · simp only [twice, Bool.false_eq_true, ↓reduceIte, some]
          exact ⟨_, rfl⟩
end


/-- The value of a linear type at which the decision of linear use fails: the first value of
linear type that is not used once, with where; nothing when every one is used once. -/
def Term.misuse {Γ outs : List D.Ty} (t : Term D Γ outs) : Option Misuse :=
  match Term.linearUses linear [] (linearCount linear Γ) t with
  | .error misuse => some misuse
  | .ok kept => (misuseAmong linear Γ kept).map fun found => ⟨[], none, found.1, found.2⟩

theorem Term.misuse_eq_none {Γ outs : List D.Ty} (t : Term D Γ outs) :
    t.misuse linear = none ↔ t.UsedOnce linear := by
  have spec := Term.linearUses_spec linear [] t
  unfold Term.misuse Term.UsedOnce
  cases found : t.uses linear with
  | none =>
      rw [found] at spec
      obtain ⟨misuse, failed⟩ := spec
      simp only [failed, reduceCtorEq, false_iff, not_exists, not_and]
      intro counts uses
      cases uses
  | some counts =>
      rw [found] at spec
      obtain ⟨length, kept⟩ := spec
      have decided := misuseAmong_eq_none linear Γ counts [] (Nat.le_of_eq length.symm)
      simp only [List.append_nil] at decided
      simp only [kept, Option.map_eq_none_iff, decided]
      constructor
      · intro once
        exact ⟨counts, rfl, once⟩
      · intro ⟨other, same, once⟩
        cases same
        exact once

end

end Zkc.Core
