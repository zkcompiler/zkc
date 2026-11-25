module

public import Zkc.Core.Program.Identity

@[expose] public section

namespace Zkc.Subject.Coverage
open Zkc.Core

/-- Store bounded pages of definition numbers. A page number follows a binary path:
page zero is at the root and the children of page n correspond to paths with one
more bit. Large sparse keys allocate only a path and one bounded bitmap. -/
inductive Pending where
  | empty
  | node (bits : Nat) (odd even : Pending)

namespace Pending

/-- At most one kibibyte of bits in a page. -/
abbrev pageSize : Nat := 8192

/-- Little-endian bijective base two, with zero represented by the empty path. -/
def pathAux : Nat → Nat → List Bool
  | 0, _ | _ + 1, 0 => []
  | fuel + 1, n + 1 => (n % 2 == 1) :: pathAux fuel (n / 2)

def path (n : Nat) : List Bool := pathAux n n

private def page : List Bool → Nat
  | [] => 0
  | b :: bs => 2 * page bs + b.toNat + 1

private theorem page_path (n : Nat) : page (path n) = n := by
  have decode (fuel n : Nat) (enough : n ≤ fuel) : page (pathAux fuel n) = n := by
    induction fuel generalizing n with
    | zero =>
      obtain rfl : n = 0 := by omega
      rfl
    | succ fuel ih =>
      cases n with
      | zero => rfl
      | succ n =>
        rw [pathAux, page, ih _ (by omega)]
        cases b : (n % 2 == 1) <;> simp_all <;> omega
  exact decode n n (Nat.le_refl _)

@[inline] def bits : Pending → Nat
  | .empty => 0
  | .node word _ _ => word

@[inline] def child : Pending → Bool → Pending
  | .empty, _ => .empty
  | .node _ odd even, b => if b then even else odd

@[inline] def setBits (s : Pending) (word : Nat) : Pending :=
  match s with
  | .empty => .node word .empty .empty
  | .node _ odd even => .node word odd even

private theorem setBits_eq (s : Pending) (word : Nat) :
    s.setBits word = .node word (s.child false) (s.child true) := by cases s <;> rfl

def read (s : Pending) : List Bool → Nat
  | [] => s.bits
  | b :: bs => (s.child b).read bs

def modify (s : Pending) (f : Nat → Nat) : List Bool → Pending
  | [] => .node (f s.bits) (s.child false) (s.child true)
  | false :: bs => .node s.bits ((s.child false).modify f bs) (s.child true)
  | true :: bs => .node s.bits (s.child false) ((s.child true).modify f bs)

private theorem read_modify (s : Pending) (f : Nat → Nat) (a k : List Bool) :
    (s.modify f a).read k = if k = a then f (s.read k) else s.read k := by
  induction a generalizing s k with
  | nil => cases k with
    | nil => rfl
    | cons b bs => cases b <;> rfl
  | cons b bs ih =>
    cases k with
    | nil => cases b <;> rfl
    | cons c cs => cases b <;> cases c <;> simp [modify, read, child, ih]

@[inline] def contains (s : Pending) (k : Key) : Bool :=
  if k.number < pageSize then s.bits.testBit k.number
  else (s.read (path (k.number / pageSize))).testBit (k.number % pageSize)

@[inline] def insert (s : Pending) (k : Key) : Pending :=
  if k.number < pageSize then
    s.setBits (s.bits ||| (1 <<< k.number))
  else s.modify (· ||| (1 <<< (k.number % pageSize))) (path (k.number / pageSize))

/-- Discharge a key already known to be pending. -/
@[inline] def discharge (s : Pending) (k : Key) : Pending :=
  if k.number < pageSize then
    s.setBits (s.bits ^^^ (1 <<< k.number))
  else s.modify (· ^^^ (1 <<< (k.number % pageSize))) (path (k.number / pageSize))

private theorem contains_eq (s : Pending) (k : Key) :
    s.contains k = (s.read (path (k.number / pageSize))).testBit (k.number % pageSize) := by
  by_cases h : k.number < pageSize <;> simp [contains, h, Nat.div_eq_of_lt, Nat.mod_eq_of_lt, path, pathAux, read]

private theorem insert_eq (s : Pending) (k : Key) :
    s.insert k = s.modify (· ||| (1 <<< (k.number % pageSize))) (path (k.number / pageSize)) := by
  by_cases h : k.number < pageSize <;> simp [insert, h, Nat.div_eq_of_lt, Nat.mod_eq_of_lt, path, pathAux, modify, setBits_eq]

private theorem discharge_eq (s : Pending) (k : Key) :
    s.discharge k = s.modify (· ^^^ (1 <<< (k.number % pageSize))) (path (k.number / pageSize)) := by
  by_cases h : k.number < pageSize <;> simp [discharge, h, Nat.div_eq_of_lt, Nat.mod_eq_of_lt, path, pathAux, modify, setBits_eq]

def greater : Option Key → Option Key → Option Key
  | none, b => b
  | a, none => a
  | some a, some b => some (if a.number < b.number then b else a)

private theorem greater_none {a b : Option Key} : greater a b = none ↔ a = none ∧ b = none := by
  cases a <;> cases b <;> simp [greater]

/-- The largest outstanding number, independent of discovery order and page size. -/
def remainingFrom (base stride : Nat) : Pending → Option Key
  | .empty => none
  | .node word odd even =>
    let here := if word == 0 then none else some ⟨base * pageSize + word.log2⟩
    greater here (greater (odd.remainingFrom (base + stride) (2 * stride))
      (even.remainingFrom (base + 2 * stride) (2 * stride)))

def remaining (s : Pending) : Option Key := s.remainingFrom 0 1

private theorem read_empty (bs : List Bool) : empty.read bs = 0 := by
  induction bs with
  | nil => rfl
  | cons _ _ ih => exact ih

@[simp] theorem contains_empty (k : Key) : empty.contains k = false := by
  simp [contains_eq, read_empty]

private theorem key_eq {a k : Key} (p : path (k.number / pageSize) = path (a.number / pageSize))
    (i : k.number % pageSize = a.number % pageSize) : k = a := by
  have q := congrArg page p
  simp only [page_path] at q
  cases a; cases k
  congr 1
  exact (Nat.div_add_mod' _ _).symm.trans (by rw [q, i, Nat.div_add_mod'])

@[simp] theorem contains_insert (s : Pending) (a k : Key) :
    (s.insert a).contains k = true ↔ k = a ∨ s.contains k = true := by
  by_cases eq : k = a
  · subst k
    simp [insert_eq, contains_eq, read_modify, Nat.shiftLeft_eq]
  · by_cases p : path (k.number / pageSize) = path (a.number / pageSize)
    · have i := fun h => eq (key_eq p h)
      simp [insert_eq, contains_eq, read_modify, p, eq, Ne.symm i, Nat.shiftLeft_eq]
    · simp [insert_eq, contains_eq, read_modify, p, eq]

theorem contains_discharge (s : Pending) (a k : Key) (hit : s.contains a = true) :
    (s.discharge a).contains k = true ↔ k ≠ a ∧ s.contains k = true := by
  by_cases eq : k = a
  · subst k
    rw [contains_eq] at hit
    simp [discharge_eq, contains_eq, read_modify, hit, Nat.shiftLeft_eq]
  · by_cases p : path (k.number / pageSize) = path (a.number / pageSize)
    · have i := fun h => eq (key_eq p h)
      simp [discharge_eq, contains_eq, read_modify, p, eq, Ne.symm i, Nat.shiftLeft_eq]
    · simp [discharge_eq, contains_eq, read_modify, p, eq]

theorem contains_fold_insert (s : Pending) (keys : List Key) (k : Key) :
    (keys.foldl insert s).contains k = true ↔ k ∈ keys ∨ s.contains k = true := by
  induction keys generalizing s with
  | nil => simp
  | cons a keys ih => simp [ih, or_left_comm, or_assoc]

private theorem read_of_none (s : Pending) (base stride : Nat)
    (h : s.remainingFrom base stride = none) (bs : List Bool) : s.read bs = 0 := by
  induction s generalizing bs base stride with
  | empty => exact read_empty _
  | node word odd even left right =>
    by_cases zero : word = 0
    · simp [remainingFrom, greater_none, zero] at h
      cases bs with
      | nil => exact zero
      | cons b bs =>
        cases b
        · exact left _ _ h.1 _
        · exact right _ _ h.2 _
    · simp [remainingFrom, greater_none, zero] at h

theorem contains_of_remaining_none (s : Pending) (h : s.remaining = none) (k : Key) :
    s.contains k = false := by
  simp [contains_eq, read_of_none s 0 1 h]

end Pending
end Zkc.Subject.Coverage
