module

public import Std

@[expose] public section

/-! Exact explicit-table predicates and their finite evaluators. These model laws
are independent of field representation, native execution and lookup arguments.
The active flag is part of a query. Multiplicity is deliberately not consumed.
-/

set_option autoImplicit false
namespace PIR.Relation.Table

structure Query (A : Type) where
  active : Bool
  value : A
  deriving DecidableEq, Repr

variable {A : Type} [DecidableEq A]

def contains (table : List A) (value : A) : Bool :=
  table.foldl (fun found row => found || decide (row = value)) false

def Membership (table : List A) (queries : List (Query A)) : Prop :=
  ∀ query ∈ queries, query.active = true → query.value ∈ table

def membership (table : List A) (queries : List (Query A)) : Bool :=
  queries.foldl (fun valid query => valid && (!query.active || contains table query.value)) true

def IndexedRead (table : List A) (position : Nat) (value : A) : Prop :=
  table[position]? = some value

/-- A total scan, with a natural coordinate that cannot wrap. -/
def indexedReadFrom (table : List A) (coordinate position : Nat) (value : A) : Bool :=
  match table with
  | [] => false
  | row :: rest => (decide (coordinate = position) && decide (row = value)) ||
      indexedReadFrom rest (coordinate + 1) position value

def indexedRead (table : List A) (position : Nat) (value : A) : Bool :=
  indexedReadFrom table 0 position value

private theorem contains_acc (table : List A) (value : A) (found : Bool) :
    table.foldl (fun seen row => seen || decide (row = value)) found = true ↔
      found = true ∨ value ∈ table := by
  induction table generalizing found with
  | nil => simp
  | cons row rest ih =>
    simp only [List.foldl_cons, ih, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    rw [eq_comm (a := row) (b := value)]
    exact or_assoc

@[simp] theorem contains_exact (table : List A) (value : A) :
    contains table value = true ↔ value ∈ table := by
  simpa [contains] using contains_acc table value false

private theorem membership_acc (table : List A) (queries : List (Query A)) (valid : Bool) :
    queries.foldl (fun ok query => ok && (!query.active || contains table query.value)) valid = true ↔
      valid = true ∧ Membership table queries := by
  induction queries generalizing valid with
  | nil => simp [Membership]
  | cons query rest ih =>
    rw [List.foldl_cons, ih]
    cases active : query.active <;> simp [Membership, active, and_assoc]

@[simp] theorem membership_exact (table : List A) (queries : List (Query A)) :
    membership table queries = true ↔ Membership table queries := by
  simpa [membership] using membership_acc table queries true

private theorem indexedReadFrom_exact (table : List A) (coordinate position : Nat) (value : A) :
    indexedReadFrom table coordinate position value = true ↔
      ∃ offset, coordinate + offset = position ∧ table[offset]? = some value := by
  induction table generalizing coordinate with
  | nil => simp [indexedReadFrom]
  | cons row rest ih =>
    simp only [indexedReadFrom, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, ih]
    constructor
    · intro h
      rcases h with ⟨same, equal⟩ | ⟨offset, located, equal⟩
      · exact ⟨0, by simpa using same, by simpa using equal⟩
      · exact ⟨offset + 1, by omega, by simpa using equal⟩
    · rintro ⟨offset, located, equal⟩
      cases offset with
      | zero => exact Or.inl ⟨by simpa using located, by simpa using equal⟩
      | succ n => exact Or.inr ⟨n, by omega, by simpa using equal⟩

@[simp] theorem indexedRead_exact (table : List A) (position : Nat) (value : A) :
    indexedRead table position value = true ↔ IndexedRead table position value := by
  simp [indexedRead, indexedReadFrom_exact, IndexedRead]

/-- A duplicate active query does not require another table occurrence. -/
theorem duplicate_query (table : List A) (query : Query A) :
    membership table [query, query] = membership table [query] := by
  simp [membership, List.foldl_cons, List.foldl_nil]

/-- Dropping an active mask changes the predicate, including on empty tables. -/
theorem inactive_empty (value : A) : membership [] [⟨false, value⟩] = true := by
  simp [membership, contains]

theorem active_empty (value : A) : membership [] [⟨true, value⟩] = false := by
  simp [membership, contains]

end PIR.Relation.Table
