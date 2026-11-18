module

@[expose] public section

/-!
What an operation with a domain asks of an application, as data. The same requirement is what
an operation asks, what the check of facts decides, and what a refusal says when it is not
known. An operand of a requirement that applies a written operation names its operands by their
positions among the application's (`atPositions`). The positional format stores requirements on the inputs and on the inputs
followed by the results (`Summary`). A function header retains these original clauses as
`Requirement Empty`, alongside directly written assertions in `HeaderSummary`.
`Summary.lift` embeds the positional form into another dialect and `Summary.misplaced`
checks its positions. The meaning of positional requirements is in `Meaning/Requirement.lean`.
-/

namespace Zkc.Core

/-- What is known of a natural: it is at least `lo` and, when `hi` is there, at most `hi`. -/
structure Range where
  lo : Nat
  hi : Option Nat
deriving DecidableEq, Repr

/-- A natural is in a range. -/
def Range.Has (r : Range) (n : Nat) : Prop := r.lo ≤ n ∧ ∀ h, r.hi = some h → n ≤ h

/-- A value that a requirement speaks of: an operand of the application by its position, or the
first result of a written operation applied to operands of the application (a length, the truth
value of the row that decides a domain). -/
inductive Operand (Raw : Type) where
  | arg (position : Nat)
  | apply (written : Raw) (positions : List Nat)
deriving DecidableEq

/-- What an application must satisfy to be inside the domain of its operation. -/
inductive Requirement (Raw : Type) where
  /-- The first is at most the second. -/
  | le (first second : Operand Raw)
  /-- The first is less than the second. -/
  | lt (first second : Operand Raw)
  /-- The value is at least a number. -/
  | atLeast (value : Operand Raw) (number : Nat)
  /-- The value is below a number. -/
  | below (value : Operand Raw) (number : Nat)
  /-- The value is a number. -/
  | exactly (value : Operand Raw) (number : Nat)
  /-- The first less the second is a number. -/
  | difference (first second : Operand Raw) (number : Nat)
  /-- The value is true. -/
  | holds (value : Operand Raw)
  /-- The value has an upper bound. -/
  | bounded (value : Operand Raw)
deriving DecidableEq

/-- The values that a requirement names, in its order. -/
def Requirement.operands {Raw : Type} : Requirement Raw → List (Operand Raw)
  | .le t u => [t, u]
  | .lt t u => [t, u]
  | .atLeast t _ => [t]
  | .below t _ => [t]
  | .exactly t _ => [t]
  | .difference t u _ => [t, u]
  | .holds t => [t]
  | .bounded t => [t]

/-- What a call of a definition must establish of its operands, and what it may then take of
its operands and results: both in the language in which an operation states its domain, so
that the analysis decides the first at a call and learns the second. What it is for a definition
to satisfy one is in `Evidence/Summary.lean` (`Summary.Holds`). -/
structure Summary (Raw : Type) where
  /-- About the inputs, by position. -/
  requires : List (Requirement Raw)
  /-- About the inputs followed by the outputs, by position. -/
  ensures : List (Requirement Raw)
deriving DecidableEq

/-- Select the empty summary in the format expected by the caller. -/
class Summary.EmptyOf (S : Type) (Raw : outParam Type) where
  value : S

@[default_instance] instance {Raw : Type} : Summary.EmptyOf (Summary Raw) Raw := ⟨⟨[], []⟩⟩

/-- The summary with no requirement and no guarantee: a definition that has it is asked nothing
at a call and promises nothing beyond being assured. -/
def Summary.empty {Raw S : Type} [EmptyOf S Raw] : S := EmptyOf.value

/-! ## The summary of a function, by positions -/

/-- An operand over no written operation, as an operand over the written operations `Raw`: the
same position. There is no application to map. -/
def Operand.lift {Raw : Type} : Operand Empty → Operand Raw
  | .arg position => .arg position
  | .apply written _ => nomatch written

/-- A requirement over no written operation, as a requirement over the written operations `Raw`:
the same requirement on the same positions. -/
def Requirement.lift {Raw : Type} : Requirement Empty → Requirement Raw
  | .le first second => .le first.lift second.lift
  | .lt first second => .lt first.lift second.lift
  | .atLeast value number => .atLeast value.lift number
  | .below value number => .below value.lift number
  | .exactly value number => .exactly value.lift number
  | .difference first second number => .difference first.lift second.lift number
  | .holds value => .holds value.lift
  | .bounded value => .bounded value.lift

/-- Embed a positional summary into the written operations of a dialect while preserving its
requirements and guarantees. -/
def Summary.lift {Raw : Type} (summary : Summary Empty) : Summary Raw :=
  ⟨summary.requires.map Requirement.lift, summary.ensures.map Requirement.lift⟩

/-- The values that a lifted requirement names are those that it names, lifted. -/
theorem Requirement.operands_lift {Raw : Type} (requirement : Requirement Empty) :
    (requirement.lift (Raw := Raw)).operands = requirement.operands.map Operand.lift := by
  cases requirement <;> rfl

/-- A lifted requirement names operands by their positions only. -/
theorem Requirement.lift_positions {Raw : Type} (requirement : Requirement Empty) :
    ∀ operand, operand ∈ (requirement.lift (Raw := Raw)).operands →
      ∃ position, operand = .arg position := by
  intro operand listed
  rw [Requirement.operands_lift] at listed
  obtain ⟨original, -, rfl⟩ := List.mem_map.mp listed
  cases original with
  | arg position => exact ⟨position, rfl⟩
  | apply written _ => exact nomatch written

/-- Whether every position that a requirement names is below a count. -/
def Requirement.within (count : Nat) (requirement : Requirement Empty) : Bool :=
  requirement.operands.all fun
    | .arg position => decide (position < count)
    | .apply written _ => nomatch written

/-- The first requirement of a summary that names a position beyond the inputs, or else the first
guarantee that names a position beyond the inputs and the results, for a definition with as many
inputs and results; nothing when there is none. -/
def Summary.misplaced (inputs results : Nat) (summary : Summary Empty) :
    Option (Requirement Empty) :=
  match summary.requires.find? fun requirement => !requirement.within inputs with
  | some requirement => some requirement
  | none => summary.ensures.find? fun guarantee => !guarantee.within (inputs + results)

/-- The positions that a summary names are within the inputs, for a requirement, and within the
inputs followed by the results, for a guarantee: defined by its decision, which elaboration makes
of the summary of every function. -/
def Summary.InRange (inputs results : Nat) (summary : Summary Empty) : Prop :=
  summary.misplaced inputs results = none

/-! ## The items at positions -/

/-- The items at the positions, when every one is there: the operands of a written operation
that an operand of a requirement applies (`Operand.apply`). -/
def atPositions {α : Type} (xs : List α) : List Nat → Option (List α)
  | [] => some []
  | p :: ps =>
      match xs[p]?, atPositions xs ps with
      | some x, some rest => some (x :: rest)
      | _, _ => none

theorem atPositions_length {α : Type} {xs : List α} :
    ∀ {ps : List Nat} {ys : List α}, atPositions xs ps = some ys → ys.length = ps.length
  | [], ys, h => by simp only [atPositions, Option.some.injEq] at h; subst h; rfl
  | p :: ps, ys, h => by
      simp only [atPositions] at h
      split at h
      · next x rest e1 e2 =>
          cases h
          simp [atPositions_length e2]
      · cases h

theorem atPositions_mem {α : Type} {xs : List α} :
    ∀ {ps : List Nat} {ys : List α}, atPositions xs ps = some ys → ∀ y, y ∈ ys → y ∈ xs
  | [], ys, h, y, m => by simp only [atPositions, Option.some.injEq] at h; subst h; cases m
  | p :: ps, ys, h, y, m => by
      simp only [atPositions] at h
      split at h
      · next x rest e1 e2 =>
          cases h
          rcases List.mem_cons.mp m with rfl | m
          · exact List.mem_of_getElem? e1
          · exact atPositions_mem e2 y m
      · cases h

theorem atPositions_getElem {α : Type} {xs : List α} :
    ∀ {ps : List Nat} {ys : List α}, atPositions xs ps = some ys →
      ∀ (i p : Nat), ps[i]? = some p → ys[i]? = xs[p]?
  | [], ys, h, i, p, e => by simp at e
  | q :: ps, ys, h, i, p, e => by
      simp only [atPositions] at h
      split at h
      · next x rest e1 e2 =>
          cases h
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at e
              subst e
              simpa using e1.symm
          | succ i =>
              simp only [List.getElem?_cons_succ] at e ⊢
              exact atPositions_getElem e2 i p e
      · cases h

theorem atPositions_append {α : Type} (xs : List α) :
    ∀ (ps qs : List Nat), atPositions xs (ps ++ qs) =
      (atPositions xs ps).bind fun as => (atPositions xs qs).map fun bs => as ++ bs
  | [], qs => by simp [atPositions]
  | p :: ps, qs => by
      simp only [List.cons_append, atPositions, atPositions_append xs ps qs]
      cases xs[p]? <;> cases atPositions xs ps <;> simp
      cases atPositions xs qs <;> simp

theorem atPositions_range {α : Type} (xs : List α) :
    ∀ n, n ≤ xs.length → atPositions xs (List.range n) = some (xs.take n)
  | 0, _ => by simp [atPositions]
  | n + 1, le => by
      rw [List.range_succ, atPositions_append, atPositions_range xs n (by omega)]
      simp only [atPositions, List.getElem?_eq_getElem (by omega : n < xs.length),
        Option.bind_some, Option.map_some, Option.some.injEq]
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega : n < xs.length)]
      rfl

end Zkc.Core
