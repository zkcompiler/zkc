module

public import Zkc.Core.Copies

public section

/-! The classes that the check of copies gives.

Facts of the check alone, without a side or a process: what `blocks` and the classes of ports
are, and that the check never hands out a class at or above its next class, never moves the
next class back, and returns as many copies as a region has outputs. The proof that the check
is sound reads them where no nested region runs for a side: a choice none of whose
participants is in the side, and a loop of no iteration.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The element of a mapped list at a position of the list. -/
theorem getD_map_of_getElem? {α β : Type} (f : α → β) (items : List α) {index : Nat} {item : α}
    (found : items[index]? = some item) (fallback : β) :
    (items.map f).getD index fallback = f item := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, found]


/-- Every level of the operands of an instruction is the level of a reference. -/
theorem numbers_levels {β : Type} {Δ : List β} (depth : Nat) :
    ∀ {types : List β} (operands : Operands Δ types) (level : Nat),
      level ∈ Scope.numbers depth operands →
        ∃ (entry : β) (reference : Var Δ entry), level = Scope.number depth reference
  | _, .nil, _, member => nomatch member
  | _, .cons reference rest, level, member => by
      cases member with
      | head => exact ⟨_, reference, rfl⟩
      | tail _ member => exact numbers_levels depth rest level member

/-- The operands of an instruction have one number each. -/
theorem numbers_count {β : Type} {Δ : List β} (depth : Nat) :
    ∀ {types : List β} (operands : Operands Δ types),
      (Scope.numbers depth operands).length = types.length
  | _, .nil => rfl
  | _, .cons _ rest => congrArg (· + 1) (numbers_count depth rest)

/-- The number of a reference is below the depth of its context. -/
theorem number_lt {β : Type} {Δ : List β} {entry : β} (reference : Var Δ entry) :
    Scope.number Δ.length reference < Δ.length := by
  have inside := (List.getElem?_eq_some_iff.mp reference.valid).1
  simp only [Scope.number, Scope.position]
  omega

/-! ## Supports -/

namespace Copies

theorem contains_withRole_self (support : List Nat) (role : Nat) :
    (withRole support role).contains role = true := by
  unfold withRole
  cases inside : support.contains role with
  | true => exact inside
  | false => simp

theorem contains_withRole {support : List Nat} {other : Nat} (role : Nat)
    (inside : support.contains other = true) : (withRole support role).contains other = true := by
  unfold withRole
  cases support.contains role with
  | true => exact inside
  | false =>
      simp only [Bool.cond_false, List.contains_cons, Bool.or_eq_true]
      exact .inr inside

theorem all_of_withRole {support : List Nat} {role : Nat} {side : Side}
    (inside : (withRole support role).all side = true) :
    support.all side = true ∧ side role = true := by
  unfold withRole at inside
  cases member : support.contains role with
  | true =>
      rw [member] at inside
      refine ⟨inside, ?_⟩
      have found : role ∈ support := by simpa using member
      exact List.all_eq_true.mp inside role found
  | false =>
      rw [member] at inside
      simp only [Bool.cond_false, List.all_cons, Bool.and_eq_true] at inside
      exact ⟨inside.2, inside.1⟩

theorem all_withRole {support : List Nat} {role : Nat} {side : Side}
    (inside : support.all side = true) (member : side role = true) :
    (withRole support role).all side = true := by
  unfold withRole
  cases support.contains role with
  | true => exact inside
  | false => simp only [Bool.cond_false, List.all_cons, member, inside, Bool.and_self]

/-- A role of a support that is inside the side is in the side. -/
theorem side_of_contains {support : List Nat} {role : Nat} {side : Side}
    (inside : support.all side = true) (member : support.contains role = true) :
    side role = true :=
  List.all_eq_true.mp inside role (by simpa using member)

theorem all_of_union {side : Side} : ∀ {second first : List Nat},
    (union first second).all side = true → first.all side = true ∧ second.all side = true
  | [], _, inside => ⟨inside, rfl⟩
  | role :: rest, first, inside => by
      have later := all_of_union (second := rest) (first := withRole first role) inside
      have parts := all_of_withRole later.1
      exact ⟨parts.1, by simp only [List.all_cons, parts.2, later.2, Bool.and_self]⟩

theorem contains_union_left {other : Nat} : ∀ {second first : List Nat},
    first.contains other = true → (union first second).contains other = true
  | [], _, inside => inside
  | role :: rest, _, inside =>
      contains_union_left (second := rest) (contains_withRole role inside)

end Copies

namespace Copies

/-! ## Classes by key

`blocks` gives the values of a list one class per key: two values have one class exactly when
their keys are equal, and every class is new. -/

theorem blocks_eq (state : State) (keys : List (List Nat)) :
    blocks state keys =
      ((keys.foldl blockStep ([], [], state.next)).2.1,
        { state with next := (keys.foldl blockStep ([], [], state.next)).2.2 }) := rfl

/-- What holds of `blocks` after the keys of a list: a class per key, each from `start` on and
below the next; a key has one class and a class one key; the class at a position is the class
of the key at that position. -/
structure BlocksInv (start : Nat) (done : List (List Nat))
    (found : List (List Nat × Nat) × List Nat × Nat) : Prop where
  length : found.2.1.length = done.length
  bounds : ∀ entry ∈ found.1, start ≤ entry.2 ∧ entry.2 < found.2.2
  keys : ∀ first ∈ found.1, ∀ second ∈ found.1, first.1 = second.1 → first = second
  classes : ∀ first ∈ found.1, ∀ second ∈ found.1, first.2 = second.2 → first = second
  listed : ∀ (index : Nat) (key : List Nat) (class_ : Nat), done[index]? = some key →
    found.2.1[index]? = some class_ → (key, class_) ∈ found.1
  grows : start ≤ found.2.2

theorem BlocksInv.start (start : Nat) : BlocksInv start [] ([], [], start) :=
  ⟨rfl, (fun _ member => nomatch member), (fun _ member => nomatch member),
    (fun _ member => nomatch member), (fun _ _ _ found => nomatch found), Nat.le_refl _⟩

theorem BlocksInv.step {start : Nat} {done : List (List Nat)}
    {found : List (List Nat × Nat) × List Nat × Nat} (inv : BlocksInv start done found)
    (key : List Nat) : BlocksInv start (done ++ [key]) (blockStep found key) := by
  unfold blockStep
  -- the class at a position of the keys so far, with one more key
  have listedAfter : ∀ (seen : List (List Nat × Nat)) (class_ : Nat),
      (∀ entry ∈ found.1, entry ∈ seen) → (key, class_) ∈ seen →
      ∀ (index : Nat) (other : List Nat) (at_ : Nat), (done ++ [key])[index]? = some other →
        (found.2.1 ++ [class_])[index]? = some at_ → (other, at_) ∈ seen := by
    intro seen class_ kept added index other at_ keyAt classAt
    by_cases earlier : index < done.length
    · rw [List.getElem?_append_left earlier] at keyAt
      rw [List.getElem?_append_left (inv.length ▸ earlier)] at classAt
      exact kept _ (inv.listed index other at_ keyAt classAt)
    · have beyond : done.length ≤ index := Nat.le_of_not_lt earlier
      rw [List.getElem?_append_right beyond] at keyAt
      rw [List.getElem?_append_right (inv.length ▸ beyond), inv.length] at classAt
      cases position : index - done.length with
      | zero =>
          rw [position] at keyAt classAt
          cases Option.some.inj keyAt
          cases Option.some.inj classAt
          exact added
      | succ _ =>
          rw [position] at keyAt
          cases keyAt
  split
  · rename_i entry seen
    have member := List.mem_of_find?_eq_some seen
    have decided := List.find?_some seen
    have same : entry.1 = key := eq_of_beq decided
    refine ⟨by simp [inv.length], inv.bounds, inv.keys, inv.classes, ?_, inv.grows⟩
    exact listedAfter found.1 entry.2 (fun _ inside => inside) (same ▸ member)
  · rename_i missing
    have absent : ∀ entry ∈ found.1, entry.1 ≠ key := by
      intro entry inside same
      have none := List.find?_eq_none.mp missing entry inside
      exact none (by simp [same])
    refine ⟨by simp [inv.length], ?_, ?_, ?_, ?_, Nat.le_succ_of_le inv.grows⟩
    · intro entry inside
      cases inside with
      | head => exact ⟨inv.grows, Nat.lt_succ_self _⟩
      | tail _ inside =>
          exact ⟨(inv.bounds entry inside).1, Nat.lt_succ_of_lt (inv.bounds entry inside).2⟩
    · intro first firstIn second secondIn same
      cases firstIn with
      | head =>
          cases secondIn with
          | head => rfl
          | tail _ secondIn => exact absurd same.symm (absent second secondIn)
      | tail _ firstIn =>
          cases secondIn with
          | head => exact absurd same (absent first firstIn)
          | tail _ secondIn => exact inv.keys first firstIn second secondIn same
    · intro first firstIn second secondIn same
      cases firstIn with
      | head =>
          cases secondIn with
          | head => rfl
          | tail _ secondIn =>
              exact absurd same (Nat.ne_of_gt (inv.bounds second secondIn).2)
      | tail _ firstIn =>
          cases secondIn with
          | head => exact absurd same (Nat.ne_of_lt (inv.bounds first firstIn).2)
          | tail _ secondIn => exact inv.classes first firstIn second secondIn same
    · exact listedAfter _ found.2.2 (fun _ inside => List.mem_cons_of_mem _ inside)
        (List.mem_cons_self ..)

theorem BlocksInv.fold {start : Nat} : ∀ (keys done : List (List Nat))
    (found : List (List Nat × Nat) × List Nat × Nat), BlocksInv start done found →
      BlocksInv start (done ++ keys) (keys.foldl blockStep found)
  | [], done, _, inv => by
      rw [List.append_nil]
      exact inv
  | key :: rest, done, found, inv => by
      have later := BlocksInv.fold rest (done ++ [key]) (blockStep found key) (inv.step key)
      rw [List.append_assoc] at later
      exact later

/-- The classes that `blocks` gives: one per key, from the state's next class on and below the
next class after; equal exactly when the keys are equal. -/
theorem blocks_spec (state : State) (keys : List (List Nat)) :
    (blocks state keys).1.length = keys.length ∧
    state.next ≤ (blocks state keys).2.next ∧
    (∀ (index : Nat) (class_ : Nat), (blocks state keys).1[index]? = some class_ →
      state.next ≤ class_ ∧ class_ < (blocks state keys).2.next) ∧
    ∀ (first second : Nat) (firstKey secondKey : List Nat) (firstClass secondClass : Nat),
      keys[first]? = some firstKey → keys[second]? = some secondKey →
      (blocks state keys).1[first]? = some firstClass →
      (blocks state keys).1[second]? = some secondClass →
        (firstClass = secondClass ↔ firstKey = secondKey) := by
  have inv := BlocksInv.fold keys [] ([], [], state.next) (BlocksInv.start state.next)
  rw [List.nil_append] at inv
  rw [blocks_eq]
  refine ⟨inv.length, inv.grows, fun index class_ classAt => ?_, ?_⟩
  · have inside : index < keys.length := by
      rw [← inv.length]
      exact (List.getElem?_eq_some_iff.mp classAt).1
    exact inv.bounds _ (inv.listed index keys[index] class_ (List.getElem?_eq_getElem inside)
      classAt)
  · intro first second firstKey secondKey firstClass secondClass firstAt secondAt firstIs secondIs
    have one := inv.listed first firstKey firstClass firstAt firstIs
    have two := inv.listed second secondKey secondClass secondAt secondIs
    constructor
    · intro same
      exact congrArg Prod.fst (inv.classes _ one _ two same)
    · intro same
      exact congrArg Prod.snd (inv.keys _ one _ two same)

/-- Two ports with one key are one port, or two copies of one agreement. -/
theorem portKey_same {ports : List Located} (agreements : List (Agreement ports))
    {first second : Nat} (same : portKey agreements first = portKey agreements second) :
    first = second ∨ ∃ agreement ∈ agreements,
      (∃ copy ∈ agreement.copies, copy.port.index = first) ∧
      (∃ copy ∈ agreement.copies, copy.port.index = second) := by
  have numbered : ∀ entry ∈ agreements.zip (List.range agreements.length),
      agreements[entry.2]? = some entry.1 := by
    intro entry inside
    obtain ⟨position, found⟩ := List.mem_iff_getElem?.mp inside
    obtain ⟨agreementAt, numberAt⟩ := List.getElem?_zip_eq_some.mp found
    obtain ⟨_, number⟩ := List.getElem?_eq_some_iff.mp numberAt
    rw [List.getElem_range] at number
    exact number ▸ agreementAt
  unfold portKey at same
  split at same
  · rename_i firstEntry firstFound
    split at same
    · rename_i secondEntry secondFound
      right
      have numbers : firstEntry.2 = secondEntry.2 := by simpa using same
      have firstAt := numbered _ (List.mem_of_find?_eq_some firstFound)
      have secondAt := numbered _ (List.mem_of_find?_eq_some secondFound)
      rw [numbers] at firstAt
      have agreements_ : firstEntry.1 = secondEntry.1 :=
        Option.some.inj (firstAt.symm.trans secondAt)
      have firstHas := List.find?_some firstFound
      have secondHas := List.find?_some secondFound
      rw [← agreements_] at secondHas
      obtain ⟨firstCopy, firstIn, firstIs⟩ := List.any_eq_true.mp firstHas
      obtain ⟨secondCopy, secondIn, secondIs⟩ := List.any_eq_true.mp secondHas
      exact ⟨firstEntry.1, List.mem_of_getElem? firstAt,
        ⟨firstCopy, firstIn, Nat.eq_of_beq_eq_true firstIs⟩,
        ⟨secondCopy, secondIn, Nat.eq_of_beq_eq_true secondIs⟩⟩
    · simp at same
  · split at same
    · simp at same
    · left
      simpa using same

/-- The classes of ports under agreements: one per port, each new; the state is otherwise
unchanged; two ports of one class are one port or two copies of one agreement. -/
theorem portClasses_spec {ports : List Located} (state : State)
    (agreements : List (Agreement ports)) :
    (portClasses state agreements).1.length = ports.length ∧
    state.next ≤ (portClasses state agreements).2.next ∧
    (portClasses state agreements).2.values = state.values ∧
    (portClasses state agreements).2.made = state.made ∧
    (∀ (index class_ : Nat), (portClasses state agreements).1[index]? = some class_ →
      state.next ≤ class_ ∧ class_ < (portClasses state agreements).2.next) ∧
    ∀ (first second class_ : Nat), (portClasses state agreements).1[first]? = some class_ →
      (portClasses state agreements).1[second]? = some class_ →
      first = second ∨ ∃ agreement ∈ agreements,
        (∃ copy ∈ agreement.copies, copy.port.index = first) ∧
        (∃ copy ∈ agreement.copies, copy.port.index = second) := by
  have spec := blocks_spec state ((List.range ports.length).map (portKey agreements))
  have counted : (portClasses state agreements).1.length = ports.length := by
    show (blocks state _).1.length = _
    rw [spec.1, List.length_map, List.length_range]
  have keyAt : ∀ position, position < ports.length →
      ((List.range ports.length).map (portKey agreements))[position]? =
        some (portKey agreements position) := by
    intro position below
    rw [List.getElem?_map, List.getElem?_range below]
    rfl
  refine ⟨counted, spec.2.1, rfl, rfl, spec.2.2.1, fun first second class_ firstIs secondIs => ?_⟩
  have firstBelow : first < ports.length :=
    counted ▸ (List.getElem?_eq_some_iff.mp firstIs).1
  have secondBelow : second < ports.length :=
    counted ▸ (List.getElem?_eq_some_iff.mp secondIs).1
  exact portKey_same agreements ((spec.2.2.2 first second _ _ class_ class_
    (keyAt first firstBelow) (keyAt second secondBelow) firstIs secondIs).mp rfl)

/-- An operation made gives classes from the next one on, or the classes of an earlier one:
the next class does not go back. -/
theorem numbered_next_le (state : State) (key : Raw.LocalStep) (count : Nat) :
    state.next ≤ (numbered state key count).2.next := by
  unfold numbered
  split
  · exact Nat.le_refl _
  · exact Nat.le_add_right _ _


/-! ## Bounds -/

/-- Every class that a state knows is below its next class. -/
@[expose] def State.Below (state : State) : Prop :=
  (∀ copy ∈ state.values, copy.class_ < state.next) ∧
    ∀ entry ∈ state.made, ∀ class_ ∈ entry.2, class_ < state.next

theorem State.Below.push {state : State} (below : state.Below) {copies : List Copy}
    (each : ∀ copy ∈ copies, copy.class_ < state.next) : (state.push copies).Below :=
  ⟨fun copy inside => (List.mem_append.mp inside).elim (below.1 copy) (each copy), below.2⟩

/-- The value at a level of a state that has it is one of the state's values. -/
theorem State.at_mem (state : State) {level : Nat} (inside : level < state.values.length) :
    state.at_ level ∈ state.values := by
  unfold State.at_
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]
  exact List.getElem_mem inside

/-- The copies at the operands of an instruction: one per operand, each of a class below the
next. -/
theorem operands_spec {Γ : List Located} (state : State) (depth : state.values.length = Γ.length)
    (below : ∀ copy ∈ state.values, copy.class_ < state.next) {types : List Located}
    (operands : Operands Γ types) :
    ((Scope.numbers state.values.length operands).map state.at_).length = types.length ∧
      ∀ copy ∈ (Scope.numbers state.values.length operands).map state.at_,
        copy.class_ < state.next := by
  refine ⟨by rw [List.length_map, numbers_count], fun copy inside => ?_⟩
  obtain ⟨level, listed, rfl⟩ := List.mem_map.mp inside
  obtain ⟨_, reference, rfl⟩ := numbers_levels _ operands level listed
  rw [depth]
  exact below _ (state.at_mem (depth ▸ number_lt reference))

/-- The classes of the results of a local operation: as many as asked, each below the next
class, in a state that keeps its values and its bounds. -/
theorem numbered_spec (state : State) (key : Raw.LocalStep) (count : Nat) (below : state.Below) :
    (numbered state key count).1.length = count ∧
    state.next ≤ (numbered state key count).2.next ∧
    (numbered state key count).2.values = state.values ∧
    (numbered state key count).2.Below ∧
    ∀ class_ ∈ (numbered state key count).1, class_ < (numbered state key count).2.next := by
  unfold numbered
  split
  · rename_i entry found
    have kept := List.find?_some found
    have sized := of_decide_eq_true (Bool.and_eq_true_iff.mp kept).2
    exact ⟨sized, Nat.le_refl _, rfl, below,
      below.2 entry (List.mem_of_find?_eq_some found)⟩
  · have ranged : ∀ class_ ∈ (List.range count).map (state.next + ·),
        class_ < state.next + count := by
      intro class_ inside
      obtain ⟨index, listed, rfl⟩ := List.mem_map.mp inside
      exact Nat.add_lt_add_left (List.mem_range.mp listed) _
    refine ⟨by simp [State.fresh], Nat.le_add_right _ _, rfl, ⟨fun copy inside =>
      Nat.lt_of_lt_of_le (below.1 copy inside) (Nat.le_add_right _ _), fun entry inside => ?_⟩,
      ranged⟩
    cases inside with
    | head => exact ranged
    | tail _ inside =>
        exact fun class_ member =>
          Nat.lt_of_lt_of_le (below.2 entry inside class_ member) (Nat.le_add_right _ _)

/-- What the check returns for a region, as classes: the next class is not below the start,
the results of the operations made are below it, and there are as many copies as outputs,
each of a class below it. -/
@[expose] def Returned.Below (start count : Nat) (returned : Returned) : Prop :=
  start ≤ returned.next ∧
    (∀ entry ∈ returned.made, ∀ class_ ∈ entry.2, class_ < returned.next) ∧
    ∀ copies, returned.copies = some copies →
      copies.length = count ∧ ∀ copy ∈ copies, copy.class_ < returned.next

/-! ### A choice -/

theorem choiceKeys_length (returning : List (List Copy)) (count : Nat) :
    (choiceKeys returning count).length = count := by
  unfold choiceKeys
  rw [List.length_map, List.length_range]

/-- The classes of the outputs of a choice: one per output, each a class of a key or a class
that an arm returns. -/
theorem choiceClasses_spec (returning : List (List Copy)) (made : List Nat) (count bound : Nat)
    (sized : made.length = count) (madeBelow : ∀ class_ ∈ made, class_ < bound)
    (each : ∀ copies ∈ returning, copies.length = count ∧ ∀ copy ∈ copies, copy.class_ < bound) :
    (choiceClasses returning made (choiceKeys returning count)).length = count ∧
      ∀ class_ ∈ choiceClasses returning made (choiceKeys returning count), class_ < bound := by
  cases returning with
  | nil => exact ⟨sized, madeBelow⟩
  | cons first rest =>
      refine ⟨by
        show ((made.zip (choiceKeys (first :: rest) count)).map _).length = _
        rw [List.length_map, List.length_zip, sized, choiceKeys_length, Nat.min_self],
        fun class_ inside => ?_⟩
      obtain ⟨entry, listed, rfl⟩ := List.mem_map.mp inside
      have madeIn := (List.of_mem_zip listed).1
      have keyIn := (List.of_mem_zip listed).2
      obtain ⟨position, ranged, keyed⟩ := List.mem_map.mp keyIn
      have inside : position < first.length := by
        rw [(each first (List.mem_cons_self ..)).1]
        exact List.mem_range.mp ranged
      have head : (first.getD position default).class_ < bound := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]
        exact (each first (List.mem_cons_self ..)).2 _ (List.getElem_mem inside)
      rw [← keyed]
      show cond _ (first.getD position default).class_ entry.1 < bound
      cases List.all _ _ with
      | true => exact head
      | false => exact madeBelow _ madeIn

theorem choiceResults_spec (returning : List (List Copy)) (classes : List Nat)
    (outputs : List Located) (sized : classes.length = outputs.length) :
    (choiceResults returning classes outputs).length = outputs.length ∧
      ∀ copy ∈ choiceResults returning classes outputs, copy.class_ ∈ classes := by
  unfold choiceResults
  refine ⟨by
    rw [List.length_map, List.length_zip, List.length_zip, List.length_range, sized, Nat.min_self,
      Nat.min_self], fun copy inside => ?_⟩
  obtain ⟨entry, listed, rfl⟩ := List.mem_map.mp inside
  exact (List.of_mem_zip (List.of_mem_zip listed).1).1

/-- The state after a choice: the values before it and one copy per output, every class below
the next, which is not below the next class after the arms. -/
theorem afterChoice_spec (state : State) (next : Nat) (returning : List (List Copy))
    (outputs : List Located) (below : state.Below) (grows : state.next ≤ next)
    (each : ∀ copies ∈ returning,
      copies.length = outputs.length ∧ ∀ copy ∈ copies, copy.class_ < next) :
    (afterChoice state next returning outputs).values.length =
        state.values.length + outputs.length ∧
      (afterChoice state next returning outputs).Below ∧
      next ≤ (afterChoice state next returning outputs).next := by
  have spec := blocks_spec { state with next := next } (choiceKeys returning outputs.length)
  have after : next ≤ (blocks { state with next := next }
      (choiceKeys returning outputs.length)).2.next := spec.2.1
  have classes := choiceClasses_spec returning
    (blocks { state with next := next } (choiceKeys returning outputs.length)).1 outputs.length
    (blocks { state with next := next } (choiceKeys returning outputs.length)).2.next
    (by rw [spec.1, choiceKeys_length])
    (fun class_ inside => by
      obtain ⟨index, _, found⟩ := List.getElem_of_mem inside
      exact (spec.2.2.1 index class_ (found ▸ List.getElem?_eq_getElem _)).2)
    (fun copies inside => ⟨(each copies inside).1, fun copy member =>
      Nat.lt_of_lt_of_le ((each copies inside).2 copy member) after⟩)
  have results := choiceResults_spec returning _ outputs classes.1
  refine ⟨?_, ⟨fun copy inside => ?_, fun entry inside class_ member => ?_⟩, after⟩
  · show (state.values ++ _).length = _
    rw [List.length_append, results.1]
  · rcases List.mem_append.mp inside with old | new
    · exact Nat.lt_of_lt_of_le (below.1 copy old) (Nat.le_trans grows after)
    · exact classes.2 _ (results.2 copy new)
  · exact Nat.lt_of_lt_of_le (below.2 entry inside class_ member) (Nat.le_trans grows after)

/-- The key of an output of a choice some arm of which returns. -/
theorem choiceKeys_at (first : List Copy) (rest : List (List Copy)) {count index : Nat}
    (below : index < count) :
    (choiceKeys (first :: rest) count)[index]? =
      some ((first :: rest).map fun copies => (copies.getD index default).class_) := by
  unfold choiceKeys
  rw [List.getElem?_map, List.getElem?_range below]
  rfl

/-- The class of an output is the class that every arm returns there, or the class of its
key. -/
theorem choiceClass_cases (class_ first : Nat) (rest : List Nat) :
    (choiceClass class_ (first :: rest) = first ∧ ∀ other ∈ first :: rest, other = first) ∨
      choiceClass class_ (first :: rest) = class_ := by
  show (cond (rest.all (Nat.beq · first)) first class_ = first ∧ _) ∨
    cond (rest.all (Nat.beq · first)) first class_ = class_
  cases same : rest.all (Nat.beq · first) with
  | false => exact Or.inr rfl
  | true =>
      refine Or.inl ⟨rfl, fun other inside => ?_⟩
      cases inside with
      | head => rfl
      | tail _ inside => exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp same other inside)

/-- The class of the output at a position is the class that every arm returns there, or the
class of its key. -/
theorem choiceClass_at (class_ : Nat) (first : List Copy) (rest : List (List Copy))
    (index : Nat) :
    (choiceClass class_ ((first :: rest).map fun copies => (copies.getD index default).class_) =
        (first.getD index default).class_ ∧
      ∀ copies ∈ first :: rest,
        (copies.getD index default).class_ = (first.getD index default).class_) ∨
      choiceClass class_ ((first :: rest).map fun copies => (copies.getD index default).class_) =
        class_ := by
  rcases choiceClass_cases class_ (first.getD index default).class_
      (rest.map fun copies => (copies.getD index default).class_) with ⟨constant, all⟩ | fresh
  · exact Or.inl ⟨constant, fun copies inside => all _ (List.mem_map_of_mem
      (f := fun copies : List Copy => (copies.getD index default).class_) inside)⟩
  · exact Or.inr fresh

/-- The class of the output at a position, when an arm returns: by its key, from the class
that the key has. -/
theorem choiceClasses_at (first : List Copy) (rest : List (List Copy)) (made : List Nat)
    {count index : Nat} (sized : made.length = count) (below : index < count) :
    ∃ class_, made[index]? = some class_ ∧
      (choiceClasses (first :: rest) made (choiceKeys (first :: rest) count))[index]? =
        some (choiceClass class_
          ((first :: rest).map fun copies => (copies.getD index default).class_)) := by
  have inside : index < made.length := sized ▸ below
  refine ⟨made[index], List.getElem?_eq_getElem inside, ?_⟩
  show ((made.zip (choiceKeys (first :: rest) count)).map _)[index]? = _
  rw [List.getElem?_map, List.getElem?_zip_eq_some
    (z := (made[index], (first :: rest).map fun copies => (copies.getD index default).class_))
    |>.mpr ⟨List.getElem?_eq_getElem inside, choiceKeys_at first rest below⟩]
  rfl

/-- The support of an output of a choice, as the union of the supports of what the arms
return at its position. -/
theorem choiceSupport_eq (returning : List (List Copy)) (holder position : Nat) :
    choiceSupport returning holder position =
      (returning.map fun copies => copies.getD position default).foldl
        (fun support copy => union support copy.support) [holder] := by
  unfold choiceSupport
  rw [List.foldl_map]

/-- The copy of the output at a position. -/
theorem choiceResults_at (returning : List (List Copy)) (classes : List Nat)
    (outputs : List Located) (sized : classes.length = outputs.length) {index : Nat}
    {located : Located} (found : outputs[index]? = some located) :
    ∃ class_, classes[index]? = some class_ ∧
      (choiceResults returning classes outputs).getD index default =
        ⟨class_, choiceSupport returning located.holder index⟩ := by
  have below : index < outputs.length := (List.getElem?_eq_some_iff.mp found).1
  have inside : index < classes.length := sized ▸ below
  exact ⟨classes[index], List.getElem?_eq_getElem inside,
    getD_map_of_getElem?
      (fun entry : (Nat × Located) × Nat =>
        (⟨entry.1.1, choiceSupport returning entry.1.2.holder entry.2⟩ : Copy))
      ((classes.zip outputs).zip (List.range outputs.length))
      (item := ((classes[index], located), index))
      (List.getElem?_zip_eq_some.mpr
        ⟨List.getElem?_zip_eq_some.mpr ⟨List.getElem?_eq_getElem inside, found⟩,
          List.getElem?_range below⟩) default⟩

/-- The state at the start of the arms of a choice: one value per input of every arm, and no
class at or above the next. -/
theorem choiceStart_spec (state : State) (below : state.Below) (participants : List Nat)
    (tag : ChoiceTag) (captures outputs : List Located) (operands : List Copy)
    (sized : operands.length = participants.length + captures.length)
    (bounded : ∀ copy ∈ operands, copy.class_ < state.next) :
    (∀ signature ∈ tag.regions participants captures outputs,
      (choiceOwn tag state.next (operands.take participants.length) ++
        operands.drop participants.length).length = signature.1.length) ∧
    (∀ copy ∈ choiceOwn tag state.next (operands.take participants.length) ++
        operands.drop participants.length, copy.class_ < state.next + 1) ∧
    ∀ entry ∈ state.made, ∀ class_ ∈ entry.2, class_ < state.next + 1 := by
  refine ⟨fun signature inside => ?_, fun copy inside => ?_, fun entry inside class_ member =>
    Nat.lt_succ_of_lt (below.2 entry inside class_ member)⟩
  · rw [List.length_append, List.length_drop, sized, Nat.add_sub_cancel_left]
    cases tag with
    | condition =>
        rw [List.eq_of_mem_replicate inside]
        exact Nat.zero_add _
    | arm count =>
        rw [List.eq_of_mem_replicate inside]
        exact Nat.zero_add _
    | alternative declaration alternatives =>
        obtain ⟨payload, _, rfl⟩ := List.mem_map.mp inside
        show ((List.take _ _).map _).length + _ = _
        rw [List.length_map, List.length_take, sized, List.length_append, List.length_map,
          Nat.min_eq_left (Nat.le_add_right _ _)]
  · rcases List.mem_append.mp inside with own | captured
    · cases tag with
      | condition => exact nomatch own
      | arm count => exact nomatch own
      | alternative declaration alternatives =>
          obtain ⟨_, _, rfl⟩ := List.mem_map.mp own
          exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (bounded copy (List.mem_of_mem_drop captured))

/-- What the arms of a choice return: one copy per output, each of a class below the next
class after the arms. -/
theorem choiceArms_spec (participants : List Nat) (tag : ChoiceTag)
    (captures outputs : List Located) (arms : List (Option (List Copy))) (after : Nat)
    (counted : arms.length = (tag.regions participants captures outputs).length)
    (each : ∀ (index : Nat) (copies : List Copy) (signature : List Located × List Located),
      arms[index]? = some (some copies) →
      (tag.regions participants captures outputs)[index]? = some signature →
        copies.length = signature.2.length ∧ ∀ copy ∈ copies, copy.class_ < after) :
    ∀ copies ∈ arms.filterMap id,
      copies.length = outputs.length ∧ ∀ copy ∈ copies, copy.class_ < after := by
  intro copies inside
  obtain ⟨arm, listed, same⟩ := List.mem_filterMap.mp inside
  cases same
  obtain ⟨position, ranged, found⟩ := List.getElem_of_mem listed
  have signed : position < (tag.regions participants captures outputs).length :=
    counted ▸ ranged
  have known := each position copies _ (found ▸ List.getElem?_eq_getElem ranged)
    (List.getElem?_eq_getElem signed)
  have output : ((tag.regions participants captures outputs)[position]).2 = outputs := by
    cases tag with
    | condition => exact congrArg Prod.snd (List.getElem_replicate ..)
    | arm count => exact congrArg Prod.snd (List.getElem_replicate ..)
    | alternative declaration alternatives =>
        show ((alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs))[position]).2 = outputs
        rw [List.getElem_map]
  rw [output] at known
  exact known

/-! ### A loop -/

/-- The operands of a loop after its counts: the carried values and the captures. -/
theorem loopOperands_spec (count : RepeatCount) (participants : List Nat)
    (carried captures : List Located) (operands : List Copy) (bound : Nat)
    (sized : operands.length = (count.operands participants ++ (carried ++ captures)).length)
    (bounded : ∀ copy ∈ operands, copy.class_ < bound) :
    (loopOperands count participants.length operands).2.length =
        carried.length + captures.length ∧
      ∀ copy ∈ (loopOperands count participants.length operands).2, copy.class_ < bound := by
  cases count with
  | «static» number =>
      refine ⟨?_, bounded⟩
      show operands.length = _
      rw [sized]
      show ([] ++ (carried ++ captures)).length = _
      rw [List.nil_append, List.length_append]
  | runtime maximum =>
      refine ⟨?_, fun copy inside => bounded copy (List.mem_of_mem_drop inside)⟩
      show (List.drop _ _).length = _
      rw [List.length_drop, sized]
      show (Located.ofRoles .nat participants ++ (carried ++ captures)).length - _ = _
      rw [List.length_append, List.length_map, List.length_append, Nat.add_sub_cancel_left]

/-- The operands of a loop after its counts, apart: as many as the carried values, and as many
as the captures. -/
theorem loopSplit_spec (carried captures : List Located) (rest : List Copy)
    (sized : rest.length = carried.length + captures.length) :
    (rest.take carried.length).length = carried.length ∧
      (rest.drop carried.length).length = captures.length :=
  ⟨by rw [List.length_take, sized, Nat.min_eq_left (Nat.le_add_right _ _)],
    by rw [List.length_drop, sized, Nat.add_sub_cancel_left]⟩

/-- The state at the start of the body of a loop: one value per input of the body, and no
class at or above the next. -/
theorem loopStart_spec (state : State) (below : state.Below) (participants : List Nat)
    (carried captures collected : List Located) (captured : List Copy)
    (capturedSized : captured.length = captures.length)
    (capturedBelow : ∀ copy ∈ captured, copy.class_ < state.next)
    (keys : List (List Nat)) (supports : List (List Nat)) (keyed : keys.length = carried.length)
    (supported : supports.length = carried.length) :
    (∀ signature ∈ [(Located.ofRoles .nat participants ++ (carried ++ captures),
        collected ++ carried)],
      (loopOwn participants state.next (blocks { state with next := state.next + 1 } keys).1
        supports ++ captured).length = signature.1.length) ∧
    (∀ copy ∈ loopOwn participants state.next
        (blocks { state with next := state.next + 1 } keys).1 supports ++ captured,
      copy.class_ < (blocks { state with next := state.next + 1 } keys).2.next) ∧
    (∀ entry ∈ state.made, ∀ class_ ∈ entry.2,
      class_ < (blocks { state with next := state.next + 1 } keys).2.next) ∧
    state.next + 1 ≤ (blocks { state with next := state.next + 1 } keys).2.next := by
  have spec := blocks_spec { state with next := state.next + 1 } keys
  refine ⟨fun signature inside => ?_, fun copy inside => ?_, fun entry inside class_ member =>
    Nat.lt_of_lt_of_le (below.2 entry inside class_ member) (Nat.le_trans (Nat.le_succ _) spec.2.1),
    spec.2.1⟩
  · cases List.mem_singleton.mp inside
    unfold loopOwn
    rw [List.length_append, List.length_append, List.length_map, List.length_map,
      List.length_zip, spec.1, keyed, supported, Nat.min_self, capturedSized, List.length_append,
      List.length_map, List.length_append, Nat.add_assoc]
  · rcases List.mem_append.mp inside with own | captured_
    · rcases List.mem_append.mp own with number | carriedCopy
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp number
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) spec.2.1
      · obtain ⟨entry, listed, rfl⟩ := List.mem_map.mp carriedCopy
        obtain ⟨position, _, found⟩ := List.getElem_of_mem (List.of_mem_zip listed).1
        exact (spec.2.2.1 position _ (found ▸ List.getElem?_eq_getElem _)).2
    · exact Nat.lt_of_lt_of_le (capturedBelow copy captured_)
        (Nat.le_trans (Nat.le_succ _) spec.2.1)

/-- The check of the body of a loop, from every state that the search for its partition
enters: the next class is not below the state's, and the body returns one copy per collected
entry and per carried value. `nested` is what the check of the nested regions gives. -/
theorem loopBody_checks (state : State) (below : state.Below) (participants : List Nat)
    (carried captures collected : List Located) (captured : List Copy)
    (capturedSized : captured.length = captures.length)
    (capturedBelow : ∀ copy ∈ captured, copy.class_ < state.next)
    (check : State → Except Refusal (List (Option (List Copy)) × Nat × List Requirement))
    (nested : ∀ (base : State) (result : List (Option (List Copy)) × Nat × List Requirement),
      check base = .ok result →
      (∀ signature ∈ [(Located.ofRoles .nat participants ++ (carried ++ captures),
          collected ++ carried)], base.values.length = signature.1.length) →
      (∀ copy ∈ base.values, copy.class_ < base.next) →
      (∀ entry ∈ base.made, ∀ class_ ∈ entry.2, class_ < base.next) →
        base.next ≤ result.2.1 ∧ result.1.length = 1 ∧
        ∀ (index : Nat) (copies : List Copy) (signature : List Located × List Located),
          result.1[index]? = some (some copies) →
          [(Located.ofRoles .nat participants ++ (carried ++ captures),
            collected ++ carried)][index]? = some signature →
            copies.length = signature.2.length ∧ ∀ copy ∈ copies, copy.class_ < result.2.1) :
    ∀ (keys : List (List Nat)) (supports : List (List Nat))
      (result : List (Option (List Copy)) × Nat × List Requirement),
      keys.length = carried.length → supports.length = carried.length →
      check { (blocks { state with next := state.next + 1 } keys).2 with
          values := loopOwn participants state.next
            (blocks { state with next := state.next + 1 } keys).1 supports ++ captured } =
        .ok result →
      state.next ≤ result.2.1 ∧
        ∀ returned, result.1.headD none = some returned →
          returned.length = collected.length + carried.length := by
  intro keys supports result keyed supported bodyChecked
  have start := loopStart_spec state below participants carried captures collected captured
    capturedSized capturedBelow keys supports keyed supported
  have body := nested _ result bodyChecked start.1 start.2.1 start.2.2.1
  refine ⟨Nat.le_trans (Nat.le_trans (Nat.le_succ _) start.2.2.2) body.1,
    fun returned found => ?_⟩
  cases arms : result.1 with
  | nil => rw [arms] at found; cases found
  | cons arm others =>
      rw [arms] at found
      cases found
      have known := body.2.2 0 returned _ (by rw [arms]; rfl) rfl
      rw [known.1, List.length_append]

/-- The partition that a loop settles on: the next class is not below the state's, and there
is one kept entry per carried value, when the check of the body, from every state that the
search enters, does not move the next class back and returns one copy per output. -/
theorem settle_classes (state : State) (participants : List Nat) (collected : Nat)
    (captured : List Copy) (unsettled : Refusal)
    (check : State → Except Refusal (List (Option (List Copy)) × Nat × List Requirement))
    (carried : Nat)
    (checks : ∀ (keys : List (List Nat)) (supports : List (List Nat))
      (result : List (Option (List Copy)) × Nat × List Requirement),
      keys.length = carried → supports.length = carried →
      check { (blocks { state with next := state.next + 1 } keys).2 with
          values := loopOwn participants state.next
            (blocks { state with next := state.next + 1 } keys).1 supports ++ captured } =
        .ok result →
      state.next ≤ result.2.1 ∧
        ∀ returned, result.1.headD none = some returned → returned.length = collected + carried) :
    ∀ (fuel : Nat) (keys : List (List Nat)) (supports : List (List Nat))
      (result : List Copy × List (Copy × Bool) × Nat × List Requirement),
      settle state participants collected captured unsettled check fuel keys supports =
        .ok result →
      keys.length = carried → supports.length = carried →
        state.next ≤ result.2.2.1 ∧ result.2.1.length = carried
  | 0, _, _, _, settled, _, _ => by
      rw [settle] at settled
      cases settled
  | fuel + 1, keys, supports, result, settled, keyed, supported => by
      have classed : (blocks { state with next := state.next + 1 } keys).1.length = carried :=
        (blocks_spec _ keys).1.trans keyed
      rw [settle] at settled
      dsimp only at settled
      split at settled
      · cases settled
      · rename_i bodies next inner bodyChecked
        have body := checks keys supports _ keyed supported bodyChecked
        split at settled
        · cases settled
          exact ⟨body.1, by
            show ((_ : List Nat).zip supports |>.map _).length = _
            rw [List.length_map, List.length_zip, classed, supported, Nat.min_self]⟩
        · rename_i returned found
          have sized := body.2 returned found
          have after : (returned.drop collected).length = carried := by
            rw [List.length_drop, sized, Nat.add_sub_cancel_left]
          split at settled
          · cases settled
            exact ⟨body.1, by
              show (((_ : List Nat).zip supports).zip (returned.drop collected) |>.map _).length = _
              rw [List.length_map, List.length_zip, List.length_zip, classed, supported, after,
                Nat.min_self, Nat.min_self]⟩
          · exact settle_classes state participants collected captured unsettled check carried
              checks fuel _ _ result settled
              (by rw [List.length_map, List.length_zip, keyed, after, Nat.min_self])
              (by rw [List.length_map, List.length_zip, supported, after, Nat.min_self])

/-- A role of the second support is in the union. -/
theorem contains_union_right {other : Nat} : ∀ {second first : List Nat},
    second.contains other = true → (union first second).contains other = true
  | [], _, inside => nomatch inside
  | role :: rest, first, inside => by
      show (union (withRole first role) rest).contains other = true
      by_cases same : other = role
      · rw [same]
        exact contains_union_left (contains_withRole_self first role)
      · refine contains_union_right (second := rest) ?_
        simpa [List.contains_cons, same] using inside

/-- A support that has the roles of its union with another contains the other. -/
theorem contains_of_sameRoles {old new : List Nat} (same : sameRoles old (union old new) = true)
    {role : Nat} (inside : new.contains role = true) : old.contains role = true := by
  unfold sameRoles at same
  have back := (Bool.and_eq_true_iff.mp same).2
  exact List.all_eq_true.mp back role (by simpa using contains_union_right (first := old) inside)

/-- What the search for the partition of a loop found: the keys and the supports that it
settled on, with the check of the body from them; from the keys and supports that it started
with, two carried values with one settled key had one key, and a settled support contains the
support at the start; and either the body returns nothing, or it returns the carried values
in classes that the settled keys already tell apart, each with a support inside the settled
one. -/
theorem settle_spec (state : State) (participants : List Nat) (collected : Nat)
    (captured : List Copy) (unsettled : Refusal)
    (check : State → Except Refusal (List (Option (List Copy)) × Nat × List Requirement))
    (carried : Nat)
    (checks : ∀ (keys : List (List Nat)) (supports : List (List Nat))
      (result : List (Option (List Copy)) × Nat × List Requirement),
      keys.length = carried → supports.length = carried →
      check { (blocks { state with next := state.next + 1 } keys).2 with
          values := loopOwn participants state.next
            (blocks { state with next := state.next + 1 } keys).1 supports ++ captured } =
        .ok result →
      state.next ≤ result.2.1 ∧
        ∀ returned, result.1.headD none = some returned → returned.length = collected + carried) :
    ∀ (fuel : Nat) (keys : List (List Nat)) (supports : List (List Nat))
      (result : List Copy × List (Copy × Bool) × Nat × List Requirement),
      settle state participants collected captured unsettled check fuel keys supports =
        .ok result →
      keys.length = carried → supports.length = carried →
      ∃ (settledKeys : List (List Nat)) (settledSupports : List (List Nat))
        (bodies : List (Option (List Copy))),
        settledKeys.length = carried ∧ settledSupports.length = carried ∧
        check { (blocks { state with next := state.next + 1 } settledKeys).2 with
            values := loopOwn participants state.next
              (blocks { state with next := state.next + 1 } settledKeys).1 settledSupports ++
                captured } = .ok (bodies, result.2.2.1, result.2.2.2) ∧
        (∀ (one two : Nat), one < carried → two < carried →
          settledKeys[one]? = settledKeys[two]? → keys[one]? = keys[two]?) ∧
        (∀ (index : Nat) (start settled : List Nat), supports[index]? = some start →
          settledSupports[index]? = some settled →
          ∀ role, start.contains role = true → settled.contains role = true) ∧
        ((bodies.headD none = none ∧ result.1 = [] ∧
            result.2.1 =
              ((blocks { state with next := state.next + 1 } settledKeys).1.zip
                settledSupports).map fun entry => (⟨entry.1, entry.2⟩, false)) ∨
          ∃ returned, bodies.headD none = some returned ∧
            result.1 = returned.take collected ∧
            result.2.1 =
              (((blocks { state with next := state.next + 1 } settledKeys).1.zip
                settledSupports).zip (returned.drop collected)).map
                  (fun entry => (⟨entry.1.1, entry.1.2⟩, Nat.beq entry.2.class_ entry.1.1)) ∧
            (blocks { state with next := state.next + 1 }
              ((settledKeys.zip (returned.drop collected)).map
                fun entry => entry.1 ++ [entry.2.class_])).1 =
              (blocks { state with next := state.next + 1 } settledKeys).1 ∧
            ((settledSupports.zip ((settledSupports.zip (returned.drop collected)).map
              fun entry => union entry.1 entry.2.support)).all
                fun entry => sameRoles entry.1 entry.2) = true)
  | 0, _, _, _, settled, _, _ => by
      rw [settle] at settled
      cases settled
  | fuel + 1, keys, supports, result, settled, keyed, supported => by
      rw [settle] at settled
      dsimp only at settled
      split at settled
      · cases settled
      · rename_i bodies next inner bodyChecked
        have same : ∀ (index : Nat) (start settled : List Nat), supports[index]? = some start →
            supports[index]? = some settled →
            ∀ role, start.contains role = true → settled.contains role = true := by
          intro index start settled startAt settledAt role inside
          cases Option.some.inj (startAt.symm.trans settledAt)
          exact inside
        split at settled
        · rename_i stopped
          cases settled
          exact ⟨keys, supports, bodies, keyed, supported, bodyChecked,
            fun _ _ _ _ equal => equal, same, Or.inl ⟨stopped, rfl, rfl⟩⟩
        · rename_i returned found
          have sized := (checks keys supports _ keyed supported bodyChecked).2 returned found
          have after : (returned.drop collected).length = carried := by
            rw [List.length_drop, sized, Nat.add_sub_cancel_left]
          split at settled
          · rename_i now
            cases settled
            have both := Bool.and_eq_true_iff.mp now
            exact ⟨keys, supports, bodies, keyed, supported, bodyChecked,
              fun _ _ _ _ equal => equal, same,
              Or.inr ⟨returned, found, rfl, rfl, eq_of_beq both.1, both.2⟩⟩
          · obtain ⟨settledKeys, settledSupports, others, keysSized, supportsSized, checked,
              keysFrom, supportsFrom, outcome⟩ :=
              settle_spec state participants collected captured unsettled check carried checks
                fuel _ _ result settled
                (by rw [List.length_map, List.length_zip, keyed, after, Nat.min_self])
                (by rw [List.length_map, List.length_zip, supported, after, Nat.min_self])
            refine ⟨settledKeys, settledSupports, others, keysSized, supportsSized, checked,
              fun one two oneBelow twoBelow equal => ?_,
              fun index start settled startAt settledAt role inside => ?_, outcome⟩
            · -- one refined key is one key: refinement appends one class to each
              have refinedAt : ∀ (index : Nat) (below : index < carried),
                  ((keys.zip (returned.drop collected)).map
                    fun entry => entry.1 ++ [entry.2.class_])[index]? =
                    some (keys[index]'(keyed ▸ below) ++
                      [((returned.drop collected)[index]'(after ▸ below)).class_]) := by
                intro index below
                rw [List.getElem?_map, List.getElem?_zip_eq_some
                  (z := (keys[index]'(keyed ▸ below), (returned.drop collected)[index]'(after ▸ below)))
                  |>.mpr ⟨List.getElem?_eq_getElem _, List.getElem?_eq_getElem _⟩]
                rfl
              have refined := keysFrom one two oneBelow twoBelow equal
              rw [refinedAt one oneBelow, refinedAt two twoBelow] at refined
              have keysEqual := List.append_inj_left' (Option.some.inj refined) rfl
              rw [List.getElem?_eq_getElem (keyed ▸ oneBelow),
                List.getElem?_eq_getElem (keyed ▸ twoBelow), keysEqual]
            · have below : index < carried :=
                supported ▸ (List.getElem?_eq_some_iff.mp startAt).1
              have widenedAt : ((supports.zip (returned.drop collected)).map
                  fun entry => union entry.1 entry.2.support)[index]? =
                  some (union start ((returned.drop collected)[index]'(after ▸ below)).support) := by
                rw [List.getElem?_map, List.getElem?_zip_eq_some
                  (z := (start, (returned.drop collected)[index]'(after ▸ below)))
                  |>.mpr ⟨startAt, List.getElem?_eq_getElem _⟩]
                rfl
              exact supportsFrom index _ settled widenedAt settledAt role
                (contains_union_left inside)

/-- The results of a loop: one copy per collected entry, then one per carried value. -/
theorem loopResults_length (collections finals : List Nat) (gathered : List Copy)
    (kept : List (Copy × Bool)) (initial : List Copy) (collected : List Located)
    (sized : collections.length = collected.length) (finalsSized : finals.length = kept.length)
    (keptSized : kept.length = initial.length) :
    (loopResults collections finals gathered kept initial collected).length =
      collected.length + initial.length := by
  unfold loopResults
  rw [List.length_append, List.length_map, List.length_map, List.length_zip, List.length_zip,
    List.length_zip, List.length_zip, List.length_range, sized, finalsSized, keptSized,
    Nat.min_self, Nat.min_self, Nat.min_self, Nat.min_self]

/-- The copy of the collection at a position. -/
theorem loopResults_collected (collections finals : List Nat) (gathered : List Copy)
    (kept : List (Copy × Bool)) (initial : List Copy) (collected : List Located)
    (sized : collections.length = collected.length) {position : Nat} {located : Located}
    (found : collected[position]? = some located) :
    ∃ class_, collections[position]? = some class_ ∧
      (loopResults collections finals gathered kept initial collected).getD position default =
        ⟨class_, withRole (gathered.getD position default).support located.holder⟩ := by
  have below : position < collected.length := (List.getElem?_eq_some_iff.mp found).1
  have inside : position < collections.length := sized ▸ below
  refine ⟨collections[position], List.getElem?_eq_getElem inside, ?_⟩
  have listed : ((collections.zip collected).zip (List.range collected.length))[position]? =
      some ((collections[position], located), position) :=
    List.getElem?_zip_eq_some.mpr
      ⟨List.getElem?_zip_eq_some.mpr ⟨List.getElem?_eq_getElem inside, found⟩,
        List.getElem?_range below⟩
  unfold loopResults
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by
    rw [List.length_map, List.length_zip, List.length_zip, List.length_range, sized, Nat.min_self,
      Nat.min_self]
    exact below), List.getElem?_map, listed]
  rfl

/-- The copy of the carried value at a position. -/
theorem loopResults_carried (collections finals : List Nat) (gathered : List Copy)
    (kept : List (Copy × Bool)) (initial : List Copy) (collected : List Located)
    (sized : collections.length = collected.length) (finalsSized : finals.length = kept.length)
    (keptSized : kept.length = initial.length) {position : Nat} {before : Copy}
    (found : initial[position]? = some before) :
    ∃ (class_ : Nat) (entry : Copy × Bool), finals[position]? = some class_ ∧
      kept[position]? = some entry ∧
      (loopResults collections finals gathered kept initial collected).getD
          (collected.length + position) default =
        ⟨cond entry.2 before.class_ class_, entry.1.support⟩ := by
  have below : position < initial.length := (List.getElem?_eq_some_iff.mp found).1
  have keptBelow : position < kept.length := keptSized ▸ below
  have finalsBelow : position < finals.length := finalsSized ▸ keptBelow
  refine ⟨finals[position], kept[position], List.getElem?_eq_getElem finalsBelow,
    List.getElem?_eq_getElem keptBelow, ?_⟩
  have listed : ((finals.zip kept).zip initial)[position]? =
      some ((finals[position], kept[position]), before) :=
    List.getElem?_zip_eq_some.mpr
      ⟨List.getElem?_zip_eq_some.mpr
        ⟨List.getElem?_eq_getElem finalsBelow, List.getElem?_eq_getElem keptBelow⟩, found⟩
  have first : (((collections.zip collected).zip (List.range collected.length)).map
      (fun entry =>
        (⟨entry.1.1, withRole (gathered.getD entry.2 default).support entry.1.2.holder⟩ :
          Copy))).length = collected.length := by
    rw [List.length_map, List.length_zip, List.length_zip, List.length_range, sized, Nat.min_self,
      Nat.min_self]
  unfold loopResults
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [first]; exact Nat.le_add_right _ _),
    first, Nat.add_sub_cancel_left, List.getElem?_map, listed]
  rfl

/-- The state after a loop: the values before it, one copy per collected entry and one per
carried value, every class below the next, which is not below the next class after the
body. -/
theorem afterLoop_spec (state : State) (next : Nat) (gathered : List Copy)
    (kept : List (Copy × Bool)) (initial : List Copy) (collected : List Located)
    (below : state.Below) (grows : state.next ≤ next) (keptCount : kept.length = initial.length)
    (initialBelow : ∀ copy ∈ initial, copy.class_ < state.next) :
    (afterLoop state next gathered kept initial collected).values.length =
        state.values.length + (collected.length + initial.length) ∧
      (afterLoop state next gathered kept initial collected).Below ∧
      next ≤ (afterLoop state next gathered kept initial collected).next := by
  have first := blocks_spec { state with next := next }
    ((List.range collected.length).map (collectionKey gathered collected))
  have second := blocks_spec
    (blocks { state with next := next }
      ((List.range collected.length).map (collectionKey gathered collected))).2
    (kept.map fun entry => [entry.1.class_])
  have after := Nat.le_trans first.2.1 second.2.1
  refine ⟨?_, ⟨fun copy inside => ?_, fun entry inside class_ member => ?_⟩, after⟩
  · show (state.values ++ (_ ++ _)).length = _
    rw [List.length_append, List.length_append, List.length_map, List.length_map,
      List.length_zip, List.length_zip, List.length_zip, List.length_zip, List.length_range,
      first.1, second.1, List.length_map, List.length_map, List.length_range, keptCount,
      Nat.min_self, Nat.min_self, Nat.min_self, Nat.min_self]
  · rcases List.mem_append.mp inside with old | new
    · exact Nat.lt_of_lt_of_le (below.1 copy old) (Nat.le_trans grows after)
    · rcases List.mem_append.mp new with collection | final
      · obtain ⟨entry, listed, rfl⟩ := List.mem_map.mp collection
        obtain ⟨index, _, found⟩ :=
          List.getElem_of_mem (List.of_mem_zip (List.of_mem_zip listed).1).1
        exact Nat.lt_of_lt_of_le
          (first.2.2.1 index _ (found ▸ List.getElem?_eq_getElem _)).2 second.2.1
      · obtain ⟨entry, listed, rfl⟩ := List.mem_map.mp final
        show cond entry.1.2.2 entry.2.class_ entry.1.1 < _
        cases entry.1.2.2 with
        | true =>
            exact Nat.lt_of_lt_of_le (initialBelow _ (List.of_mem_zip listed).2)
              (Nat.le_trans grows after)
        | false =>
            obtain ⟨index, _, found⟩ :=
              List.getElem_of_mem (List.of_mem_zip (List.of_mem_zip listed).1).1
            exact (second.2.2.1 index _ (found ▸ List.getElem?_eq_getElem _)).2
  · exact Nat.lt_of_lt_of_le (below.2 entry inside class_ member) (Nat.le_trans grows after)

/-! ### Regions -/

section Protocol

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

mutual
  /-- The classes of what the check returns for a region, from a state that has one value per
  entry of the context and knows no class at or above its next. -/
  theorem checkRegion_classes (summaries : List (List Requirement)) (roles : Nat) :
      ∀ {Γ out : List Located}
        (region : Region (ProtocolDialect operations functions protocols deployed) Γ out)
        (path : List Nat) (index : Nat) (state : State) (returned : Returned),
        checkRegion summaries roles path index state region = .ok returned →
        state.values.length = Γ.length → state.Below →
          returned.Below state.next out.length
    | _, _, .ret values, _, _, state, returned, checked, depth, below => by
        rw [checkRegion] at checked
        cases checked
        obtain ⟨counted, bounded⟩ := operands_spec state depth below.1 values
        exact ⟨Nat.le_refl _, below.2, fun copies found => by
          cases found
          exact ⟨counted, bounded⟩⟩
    | _, _, .stop _, _, _, state, returned, checked, _, below => by
        rw [checkRegion] at checked
        cases checked
        exact ⟨Nat.le_refl _, below.2, fun _ found => nomatch found⟩
    | Γ, out, .bind (mid := mid) body next, path, index, state, returned, checked, depth, below => by
        rw [checkRegion] at checked
        split at checked
        · cases checked
        · rename_i inner bodyChecked
          have first := checkRegion_classes summaries roles body _ _ state inner bodyChecked depth
            below
          have ranged : ∀ class_ ∈ (List.range mid.length).map (inner.next + ·),
              class_ < inner.next + mid.length := by
            intro class_ inside
            obtain ⟨position, listed, rfl⟩ := List.mem_map.mp inside
            exact Nat.add_lt_add_left (List.mem_range.mp listed) _
          have entered : ∀ copies : List Copy, copies.length = mid.length →
              (∀ copy ∈ copies, copy.class_ < inner.next + mid.length) →
              ∀ rest : Returned,
                checkRegion summaries roles path (index + 1)
                  (({ state with next := inner.next + mid.length, made := inner.made } :
                    State).push copies) next = .ok rest →
                Returned.Below state.next out.length rest := by
            intro copies sized bounded rest nextChecked
            have second := checkRegion_classes summaries roles next _ _ _ rest nextChecked
              (by
                show (state.values ++ copies).length = _
                rw [List.length_append, length_bindAll, depth, sized])
              ⟨fun copy inside => (List.mem_append.mp inside).elim
                  (fun old => Nat.lt_of_lt_of_le (below.1 copy old)
                    (Nat.le_trans first.1 (Nat.le_add_right _ _)))
                  (bounded copy),
                fun entry inside class_ member => Nat.lt_of_lt_of_le
                  (first.2.1 entry inside class_ member) (Nat.le_add_right _ _)⟩
            exact ⟨Nat.le_trans (Nat.le_trans first.1 (Nat.le_add_right _ _)) second.1,
              second.2.1, second.2.2⟩
          cases copiesOf : inner.copies with
          | none =>
              simp only [copiesOf, State.fresh] at checked
              split at checked
              · cases checked
              · rename_i rest nextChecked
                cases checked
                exact entered _ (by rw [List.length_map, List.length_map, List.length_range])
                  (fun copy inside => by
                    obtain ⟨class_, listed, rfl⟩ := List.mem_map.mp inside
                    exact ranged class_ listed) rest nextChecked
          | some copies =>
              simp only [copiesOf, State.fresh] at checked
              split at checked
              · cases checked
              · rename_i rest nextChecked
                cases checked
                have known := first.2.2 copies copiesOf
                exact entered copies known.1
                  (fun copy inside => Nat.lt_of_lt_of_le (known.2 copy inside)
                    (Nat.le_add_right _ _)) rest nextChecked
    | Γ, out, .letOp op arguments bodies next, path, index, state, returned, checked, depth,
        below => by
        obtain ⟨counted, bounded⟩ := operands_spec state depth below.1 arguments
        -- the rest of the region, from the state with the results of the instruction
        have continue_ : ∀ (entered : State) (requirements : List Requirement),
            (match checkRegion summaries roles path (index + 1) entered next with
              | .error refusal => (Except.error refusal : Except Refusal Returned)
              | .ok rest =>
                  Except.ok { rest with requirements := requirements ++ rest.requirements }) =
              Except.ok returned →
            entered.values.length = Γ.length + op.results.length → entered.Below →
            state.next ≤ entered.next → returned.Below state.next out.length := by
          intro entered requirements continued enteredDepth enteredBelow grows
          split at continued
          · cases continued
          · rename_i rest nextChecked
            cases continued
            have after := checkRegion_classes summaries roles next _ _ entered rest nextChecked
              (by rw [length_bindAll]; exact enteredDepth) enteredBelow
            exact ⟨Nat.le_trans grows after.1, after.2.1, after.2.2⟩
        -- the nested regions, read before the instruction is taken apart
        have regionsClasses := checkRegions_classes summaries roles bodies
        cases op with
        | exchange sender receiver site type =>
            rw [checkRegion] at checked
            cases arguments with
            | cons reference rest =>
            cases rest
            refine continue_ _ _ checked ?_ (below.push fun copy inside => ?_) (Nat.le_refl _)
            · show (state.values ++ [_]).length = _
              rw [List.length_append, depth]
              rfl
            · cases List.mem_singleton.mp inside
              show (state.at_ (Scope.number state.values.length reference)).class_ < _
              exact bounded (state.at_ (Scope.number state.values.length reference))
                (List.mem_cons_self ..)
        | sample owner site law populated =>
            rw [checkRegion] at checked
            simp only [State.fresh] at checked
            refine continue_ _ _ checked ?_ ?_ (Nat.le_succ _)
            · show (state.values ++ [_]).length = _
              rw [List.length_append, depth]
              rfl
            · refine State.Below.push (state := { state with next := state.next + 1 })
                ⟨fun copy inside => Nat.lt_succ_of_lt (below.1 copy inside),
                  fun entry inside class_ member =>
                    Nat.lt_succ_of_lt (below.2 entry inside class_ member)⟩ fun copy inside => ?_
              cases List.mem_singleton.mp inside
              exact Nat.lt_succ_self _
        | draw owner receivers site law populated =>
            rw [checkRegion] at checked
            simp only [State.fresh] at checked
            refine continue_ _ _ checked ?_ ?_ (Nat.le_succ _)
            · show (state.values ++ (_ :: List.map _ receivers)).length = _
              rw [List.length_append, depth, List.length_cons, List.length_map]
              show _ = Γ.length + ((Located.ofRoles _ receivers).length + 1)
              rw [List.length_map]
            · refine State.Below.push (state := { state with next := state.next + 1 })
                ⟨fun copy inside => Nat.lt_succ_of_lt (below.1 copy inside),
                  fun entry inside class_ member =>
                    Nat.lt_succ_of_lt (below.2 entry inside class_ member)⟩ fun copy inside => ?_
              cases inside with
              | head => exact Nat.lt_succ_self _
              | tail _ inside =>
                  obtain ⟨receiver, _, rfl⟩ := List.mem_map.mp inside
                  exact Nat.lt_succ_self _
        | «at» role local_ regions =>
            rw [checkRegion] at checked
            have spec := numbered_spec state
              (unelaborateLocalStep functions.length local_
                (((Scope.numbers state.values.length arguments).map state.at_).map (·.class_))
                (unelaborateLocalRegions functions.length regions)) local_.results.length below
            generalize numbered state _ _ = found at checked spec
            obtain ⟨classes, after⟩ := found
            dsimp only at checked spec
            refine continue_ _ _ checked ?_ (spec.2.2.2.1.push fun copy inside => ?_) spec.2.1
            · show (after.values ++ classes.map _).length = _
              rw [List.length_append, spec.2.2.1, depth, List.length_map, spec.1]
              show _ = Γ.length + (Located.atRole role local_.results).length
              rw [Located.atRole, List.length_map]
            · obtain ⟨class_, listed, rfl⟩ := List.mem_map.mp inside
              exact spec.2.2.2.2 class_ listed
        | @apply header callee roleMap site permitted =>
            rw [checkRegion] at checked
            split at checked
            · cases checked
            · generalize ported : portClasses state header.agreements.outputs = found at checked
              have spec := portClasses_spec state header.agreements.outputs
              rw [ported] at spec
              obtain ⟨classes, after⟩ := found
              dsimp only at checked spec
              have afterBelow : after.Below :=
                ⟨fun copy inside => Nat.lt_of_lt_of_le (below.1 copy (spec.2.2.1 ▸ inside))
                    spec.2.1,
                  fun entry inside class_ member => Nat.lt_of_lt_of_le
                    (below.2 entry (spec.2.2.2.1 ▸ inside) class_ member) spec.2.1⟩
              refine continue_ _ _ checked ?_ (afterBelow.push fun copy inside => ?_) spec.2.1
              · show (after.values ++ (classes.zip header.outputs).map _).length = _
                rw [List.length_append, spec.2.2.1, depth, List.length_map, List.length_zip,
                  spec.1, Nat.min_self]
                show _ = Γ.length + (header.outputs.map (Located.rename roleMap)).length
                rw [List.length_map]
              · obtain ⟨entry, listed, rfl⟩ := List.mem_map.mp inside
                obtain ⟨position, _, found⟩ := List.getElem_of_mem (List.of_mem_zip listed).1
                exact (spec.2.2.2.2.1 position _ (found ▸ List.getElem?_eq_getElem _)).2
        | choose participants tag captures outputs covered =>
            rw [checkRegion] at checked
            split at checked
            · cases checked
            · split at checked
              · cases checked
              · rename_i arms after inner armsChecked
                have sized : ((Scope.numbers state.values.length arguments).map state.at_).length =
                    participants.length + captures.length := by
                  rw [counted]
                  show (Located.ofRoles tag.type participants ++ captures).length = _
                  rw [List.length_append, List.length_map]
                have start := choiceStart_spec state below participants tag captures outputs _ sized
                  bounded
                have nested := regionsClasses _
                  { state with
                    next := state.next + 1
                    values := choiceOwn tag state.next
                        (((Scope.numbers state.values.length arguments).map state.at_).take
                          participants.length) ++
                      ((Scope.numbers state.values.length arguments).map state.at_).drop
                        participants.length } 0 (state.next + 1) _ armsChecked start.1 start.2.1
                  start.2.2
                have chosen := afterChoice_spec state after (arms.filterMap id) outputs below
                  (Nat.le_trans (Nat.le_succ _) nested.1)
                  (choiceArms_spec participants tag captures outputs arms after nested.2.1
                    nested.2.2)
                exact continue_ _ _ checked (by rw [chosen.1, depth]) chosen.2.1
                  (Nat.le_trans (Nat.le_trans (Nat.le_succ _) nested.1) chosen.2.2)
        | «repeat» participants count carried collected captures covered =>
            rw [checkRegion] at checked
            split at checked
            · cases checked
            · split at checked
              · cases checked
              · rename_i gathered kept after inner settled
                have rest := loopOperands_spec count participants carried captures _ state.next
                  counted bounded
                have sizes := loopSplit_spec carried captures _ rest.1
                have checks := loopBody_checks state below participants carried captures collected
                  _ sizes.2 (fun copy inside => rest.2 copy (List.mem_of_mem_drop inside))
                  (fun start => checkRegions summaries roles (path ++ [index]) (fun _ => start) 0
                    start.next bodies)
                  (fun base result bodyChecked => regionsClasses (path ++ [index]) base 0
                    base.next result bodyChecked)
                have loop := settle_classes state participants collected.length _ _ _
                  carried.length checks _ _ _ _ settled
                  (by rw [List.length_map, sizes.1])
                  (by rw [List.length_map, List.length_zip, sizes.1, Nat.min_self])
                have looped := afterLoop_spec state after gathered kept _ collected below loop.1
                  (loop.2.trans sizes.1.symm)
                  (fun copy inside => rest.2 copy (List.mem_of_mem_take inside))
                refine continue_ _ _ checked ?_ looped.2.1 (Nat.le_trans loop.1 looped.2.2)
                rw [looped.1, sizes.1, depth]
                show _ = Γ.length + (collectedSequencesAt count.size collected ++ carried).length
                rw [List.length_append, List.length_map]

  /-- The classes of what the check returns for nested regions, each from one state that has
  one value per input and knows no class at or above the next. -/
  theorem checkRegions_classes (summaries : List (List Requirement)) (roles : Nat) :
      ∀ {signatures : List (List Located × List Located)}
        (regions : Regions (ProtocolDialect operations functions protocols deployed) signatures)
        (path : List Nat) (base : State) (number next : Nat)
        (result : List (Option (List Copy)) × Nat × List Requirement),
        checkRegions summaries roles path (fun _ => base) number next regions = .ok result →
        (∀ signature ∈ signatures, base.values.length = signature.1.length) →
        (∀ copy ∈ base.values, copy.class_ < next) →
        (∀ entry ∈ base.made, ∀ class_ ∈ entry.2, class_ < next) →
          next ≤ result.2.1 ∧ result.1.length = signatures.length ∧
          ∀ (index : Nat) (copies : List Copy) (signature : List Located × List Located),
            result.1[index]? = some (some copies) → signatures[index]? = some signature →
              copies.length = signature.2.length ∧ ∀ copy ∈ copies, copy.class_ < result.2.1
    | _, .nil, _, _, _, _, _, checked, _, _, _ => by
        rw [checkRegions] at checked
        cases checked
        exact ⟨Nat.le_refl _, rfl, fun _ _ _ found => nomatch found⟩
    | _, .cons (inputs := inputs) (outputs := outputs) body tail, path, base, number, next,
        result, checked, sized, valuesBelow, madeBelow => by
        rw [checkRegions] at checked
        split at checked
        · cases checked
        · rename_i returned bodyChecked
          split at checked
          · cases checked
          · rename_i others after requirements tailChecked
            cases checked
            have first := checkRegion_classes summaries roles body _ 0 { base with next := next }
              returned bodyChecked
              (by
                rw [length_bindAll, List.length_nil, Nat.zero_add]
                exact sized (inputs, outputs) (List.mem_cons_self ..))
              ⟨valuesBelow, madeBelow⟩
            have rest := checkRegions_classes summaries roles tail path base (number + 1)
              returned.next _ tailChecked
              (fun signature inside => sized signature (List.mem_cons_of_mem _ inside))
              (fun copy inside => Nat.lt_of_lt_of_le (valuesBelow copy inside) first.1)
              (fun entry inside class_ member =>
                Nat.lt_of_lt_of_le (madeBelow entry inside class_ member) first.1)
            refine ⟨Nat.le_trans first.1 rest.1, congrArg (· + 1) rest.2.1,
              fun position copies signature found at_ => ?_⟩
            cases position with
            | zero =>
                cases Option.some.inj at_
                have here := first.2.2 copies (Option.some.inj found)
                exact ⟨here.1, fun copy inside => Nat.lt_of_lt_of_le (here.2 copy inside) rest.1⟩
            | succ position => exact rest.2.2 position copies signature found at_
end

end Protocol

end Copies

end Zkc.Core
