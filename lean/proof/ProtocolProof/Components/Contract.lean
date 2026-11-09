module

public import ProtocolProof.Semantics.Quantitative
public import ProtocolProof.Internal.Contract

/-! Public Process contracts reuse the checked backend calculus, including stopped branches. -/

public section
open PIR PFunctor MeasureTheory

namespace ProtocolProof
variable {I : Signature} {S L A B : Type}

@[expose] def UpperBound (spec : OperationSpec I S L) (program : Process I A)
    (post : Outcome A → (S × List L) → ENNReal) (bound : (S × List L) → ENNReal) : Prop :=
  Internal.UpperBound spec (Internal.encode program) post bound

@[expose] def LowerBound (spec : OperationSpec I S L) (program : Process I A)
    (post : Outcome A → (S × List L) → ENNReal) (bound : (S × List L) → ENNReal) : Prop :=
  Internal.LowerBound spec (Internal.encode program) post bound

variable {spec : OperationSpec I S L} {program : Process I A}
  {post post' : Outcome A → (S × List L) → ENNReal}
  {bound bound' : (S × List L) → ENNReal}

namespace UpperBound

theorem pure (value : A) (h : post (.returned value) ≤ bound) :
    UpperBound spec (.done value) post bound := h

theorem halt (reason : Stop) (h : post (.stopped reason) ≤ bound) :
    UpperBound spec (.halt reason) post bound := h

theorem operation (operation : I.Op) (post : Outcome (I.Reply operation) →
    (S × List L) → ENNReal) (h : spec operation post ≤ bound) :
    UpperBound spec (.call operation .done) post bound := by
  unfold UpperBound Internal.UpperBound
  rw [Internal.encode_operation]
  exact h

theorem bind (h : UpperBound spec program post bound) (mono : spec.Monotone)
    {next : A → Process I B} {reward : Outcome B → (S × List L) → ENNReal}
    (hnext : ∀ value, UpperBound spec (next value) reward (post (.returned value)))
    (hstop : ∀ reason, reward (.stopped reason) ≤ post (.stopped reason)) :
    UpperBound spec (program.bind next) reward bound := by
  unfold UpperBound
  rw [Internal.encode_bind]
  apply Internal.UpperBound.bind h mono
  intro outcome
  cases outcome with
  | returned value => exact hnext value
  | stopped reason => exact Internal.UpperBound.pure _ (hstop reason)

theorem consequence (h : UpperBound spec program post bound) (mono : spec.Monotone)
    (hpost : post' ≤ post) (hbound : bound ≤ bound') : UpperBound spec program post' bound' :=
  Internal.UpperBound.consequence h mono hpost hbound

theorem dite (condition : Prop) [Decidable condition]
    (yes : condition → Process I A) (no : ¬condition → Process I A)
    (hyes : ∀ h, UpperBound spec (yes h) post bound)
    (hno : ∀ h, UpperBound spec (no h) post bound) :
    UpperBound spec (if h : condition then yes h else no h) post bound := by
  split
  · exact hyes _
  · exact hno _

theorem ite (condition : Prop) [Decidable condition] (yes no : Process I A)
    (hyes : condition → UpperBound spec yes post bound)
    (hno : ¬condition → UpperBound spec no post bound) :
    UpperBound spec (if condition then yes else no) post bound :=
  dite condition (fun _ ↦ yes) (fun _ ↦ no) hyes hno

/-- A stop ends the loop; its invariant obligation cannot be omitted. -/
theorem iterate (mono : spec.Monotone) (body : Nat → A → Process I A)
    (invariant : Nat → Outcome A → (S × List L) → ENNReal) (count : Nat)
    (hstep : ∀ round, round < count → ∀ value,
      UpperBound spec (body round value) (invariant (round + 1))
        (invariant round (.returned value)))
    (hstop : ∀ round, round < count → ∀ reason,
      invariant (round + 1) (.stopped reason) ≤ invariant round (.stopped reason))
    (initial : A) :
    UpperBound spec ((List.range count).foldlM (fun value round ↦ body round value) initial)
      (invariant count) (invariant 0 (.returned initial)) := by
  induction count with
  | zero => exact pure initial le_rfl
  | succ count ih =>
      rw [List.range_succ, List.foldlM_append]
      apply (ih (fun round hround ↦ hstep round (Nat.lt_succ_of_lt hround))
        (fun round hround ↦ hstop round (Nat.lt_succ_of_lt hround))).bind mono
      · intro value
        simpa using hstep count (Nat.lt_succ_self count) value
      · exact hstop count (Nat.lt_succ_self count)

end UpperBound

namespace LowerBound

theorem pure (value : A) (h : bound ≤ post (.returned value)) :
    LowerBound spec (.done value) post bound := h

theorem halt (reason : Stop) (h : bound ≤ post (.stopped reason)) :
    LowerBound spec (.halt reason) post bound := h

theorem operation (operation : I.Op) (post : Outcome (I.Reply operation) →
    (S × List L) → ENNReal) (h : bound ≤ spec operation post) :
    LowerBound spec (.call operation .done) post bound := by
  unfold LowerBound Internal.LowerBound
  rw [Internal.encode_operation]
  exact h

theorem bind (h : LowerBound spec program post bound) (mono : spec.Monotone)
    {next : A → Process I B} {reward : Outcome B → (S × List L) → ENNReal}
    (hnext : ∀ value, LowerBound spec (next value) reward (post (.returned value)))
    (hstop : ∀ reason, post (.stopped reason) ≤ reward (.stopped reason)) :
    LowerBound spec (program.bind next) reward bound := by
  unfold LowerBound
  rw [Internal.encode_bind]
  apply Internal.LowerBound.bind h mono
  intro outcome
  cases outcome with
  | returned value => exact hnext value
  | stopped reason => exact Internal.LowerBound.pure _ (hstop reason)

theorem consequence (h : LowerBound spec program post bound) (mono : spec.Monotone)
    (hpost : post ≤ post') (hbound : bound' ≤ bound) : LowerBound spec program post' bound' :=
  Internal.LowerBound.consequence h mono hpost hbound

theorem dite (condition : Prop) [Decidable condition]
    (yes : condition → Process I A) (no : ¬condition → Process I A)
    (hyes : ∀ h, LowerBound spec (yes h) post bound)
    (hno : ∀ h, LowerBound spec (no h) post bound) :
    LowerBound spec (if h : condition then yes h else no h) post bound := by
  split
  · exact hyes _
  · exact hno _

theorem ite (condition : Prop) [Decidable condition] (yes no : Process I A)
    (hyes : condition → LowerBound spec yes post bound)
    (hno : ¬condition → LowerBound spec no post bound) :
    LowerBound spec (if condition then yes else no) post bound :=
  dite condition (fun _ ↦ yes) (fun _ ↦ no) hyes hno

/-- Lower contracts retain the reverse obligation on every stopped loop branch. -/
theorem iterate (mono : spec.Monotone) (body : Nat → A → Process I A)
    (invariant : Nat → Outcome A → (S × List L) → ENNReal) (count : Nat)
    (hstep : ∀ round, round < count → ∀ value,
      LowerBound spec (body round value) (invariant (round + 1))
        (invariant round (.returned value)))
    (hstop : ∀ round, round < count → ∀ reason,
      invariant round (.stopped reason) ≤ invariant (round + 1) (.stopped reason))
    (initial : A) :
    LowerBound spec ((List.range count).foldlM (fun value round ↦ body round value) initial)
      (invariant count) (invariant 0 (.returned initial)) := by
  induction count with
  | zero => exact pure initial le_rfl
  | succ count ih =>
      rw [List.range_succ, List.foldlM_append]
      apply (ih (fun round hround ↦ hstep round (Nat.lt_succ_of_lt hround))
        (fun round hround ↦ hstop round (Nat.lt_succ_of_lt hround))).bind mono
      · intro value
        simpa using hstep count (Nat.lt_succ_self count) value
      · exact hstop count (Nat.lt_succ_self count)

end LowerBound
end ProtocolProof
