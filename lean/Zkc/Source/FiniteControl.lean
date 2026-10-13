module

public import Zkc.Source.Region
public import Zkc.Semantics.InterpretationAdmission

@[expose] public section

/-! Compact runtime-selected finite control.

Bounds and one body are stored before selecting an environment. Denotation is a
finite `Proc`, consistent with `Region.iterate`; it is not a native runner or an
unbounded process. Terminal stops and ordinary bounded-loop completion differ.
-/

set_option autoImplicit false
namespace Zkc.Source.FiniteControl
open PIR

structure Range where
  lower : Nat
  upper : Nat
  deriving DecidableEq, Repr

def Range.count (range : Range) : Nat := range.upper - range.lower

def Range.index (range : Range) (offset : Fin range.count) : Nat := range.lower + offset.val

theorem Range.count_zero (range : Range) (inverted : range.upper ≤ range.lower) :
    range.count = 0 := Nat.sub_eq_zero_of_le inverted

theorem Range.index_bounds (range : Range) (offset : Fin range.count) :
    range.lower ≤ range.index offset ∧ range.index offset < range.upper := by
  have inside := offset.isLt
  simp only [Range.count, Range.index] at *
  omega

/-- Both magnitudes are checked, even for inverted intervals. The selected
maximum is a profile parameter, not a theorem about native work accounting. -/
def admitRange (maximum lower upper : Nat) : Option Range :=
  if lower ≤ maximum ∧ upper ≤ maximum then some ⟨lower, upper⟩ else none

theorem admitRange_some (maximum lower upper : Nat) (range : Range) :
    admitRange maximum lower upper = some range ↔
      lower ≤ maximum ∧ upper ≤ maximum ∧ range = ⟨lower, upper⟩ := by
  simp only [admitRange]
  split
  · rename_i bounds
    simp [bounds.1, bounds.2, eq_comm]
  · rename_i bounds
    constructor
    · intro impossible; cases impossible
    · rintro ⟨lo, hi, _⟩
      exact False.elim (bounds ⟨lo, hi⟩)

theorem admitted_count_bound (maximum lower upper : Nat) (range : Range)
    (accepted : admitRange maximum lower upper = some range) : range.count ≤ maximum := by
  obtain ⟨lo, hi, rfl⟩ := (admitRange_some maximum lower upper range).mp accepted
  simp only [Range.count]
  omega

variable {I : Signature} {A B S E Env : Type}

/-- One retained body is entered at successive indices. Handler stops propagate
through ordinary `Proc.bind`, retaining the actual state and event prefix. -/
def iterateFrom : Nat → Nat → (Nat → A → Proc I A) → A → Proc I A
  | 0, _, _, value => .done value
  | count + 1, index, body, value =>
    (body index value).bind (iterateFrom count (index + 1) body)

/-- Splitting an interval preserves the carried value and starts the suffix at
the next index. The equation holds even if a body stops before the split. -/
theorem iterateFrom_add (first second index : Nat) (body : Nat → A → Proc I A) (value : A) :
    iterateFrom (first + second) index body value =
      (iterateFrom first index body value).bind (iterateFrom second (index + first) body) := by
  induction first generalizing index value with
  | zero => simp [iterateFrom, Proc.bind]
  | succ first ih =>
    simp only [Nat.succ_add, iterateFrom, Proc.bind_assoc]
    congr 1
    funext next
    rw [ih]
    rw [show index + 1 + first = index + (first + 1) by omega]

/-- Only in-range body meanings affect an execution. This is a semantic index
bound, not merely a property of a separately constructed index list. -/
theorem iterateFrom_congr (count index : Nat) (left right : Nat → A → Proc I A)
    (value : A)
    (same : ∀ current value, index ≤ current ∧ current < index + count →
      left current value = right current value) :
    iterateFrom count index left value = iterateFrom count index right value := by
  induction count generalizing index value with
  | zero => rfl
  | succ count ih =>
    rw [iterateFrom, iterateFrom, same index value ⟨Nat.le_refl _, by omega⟩]
    congr 1
    funext next
    apply ih
    intro current value inside
    exact same current value (by omega)

/-- Index-insensitive iteration is exactly the existing finite repetition. -/
theorem iterateFrom_repeat (count index : Nat) (body : A → Proc I A) (value : A) :
    iterateFrom count index (fun _ => body) value = repeatN count body value := by
  induction count generalizing index value with
  | zero => rfl
  | succ count ih =>
    simp only [iterateFrom, repeatN]
    congr 1
    funext next
    exact ih (index + 1) next

theorem iterateFrom_within (count index maximum : Nat) (body : Nat → A → Proc I A)
    (bounded : ∀ index value, Within maximum (body index value)) (value : A) :
    Within (count * maximum) (iterateFrom count index body value) := by
  induction count generalizing index value with
  | zero => simp [iterateFrom, Within]
  | succ count ih =>
    simpa only [iterateFrom, Nat.succ_mul, Nat.add_comm] using
      Boundary.within_bind (body index value) (iterateFrom count (index + 1) body)
        maximum (count * maximum) (bounded index value) (ih (index + 1))

/-- Typed compact carrier: runtime selection evaluates the bounds once; the
body remains a single function, not a stored list of unrolled copies. -/
structure Loop (I : Signature) (Env A : Type) where
  bounds : Env → Range
  body : Env → Nat → A → Proc I A

def Loop.denote (loop : Loop I Env A) (env : Env) (initial : A) : Proc I A :=
  iterateFrom (loop.bounds env).count (loop.bounds env).lower (loop.body env) initial

theorem Loop.zero_trip (loop : Loop I Env A) (env : Env) (initial : A)
    (inverted : (loop.bounds env).upper ≤ (loop.bounds env).lower) :
    loop.denote env initial = .done initial := by
  simp only [Loop.denote, Range.count_zero _ inverted, iterateFrom]

theorem Loop.within (loop : Loop I Env A) (env : Env) (initial : A)
    (maximum : Nat) (bounded : ∀ index value, Within maximum (loop.body env index value)) :
    Within ((loop.bounds env).count * maximum) (loop.denote env initial) :=
  iterateFrom_within _ _ _ _ bounded initial

/-- Runtime-selected counts respect a public call budget when their admission
and each entered body supply the corresponding bounds. -/
theorem Loop.within_selected (loop : Loop I Env A) (env : Env) (initial : A)
    (limit maximum : Nat) (selected : (loop.bounds env).count ≤ limit)
    (bounded : ∀ index value, Within maximum (loop.body env index value)) :
    Within (limit * maximum) (loop.denote env initial) :=
  Boundary.within_mono _ _ _ (Nat.mul_le_mul_right maximum selected)
    (loop.within env initial maximum bounded)

/-- Existing phase admission composes across the actual indexed return edges.
Every returned carried value must preserve the invariant; stopping bodies have
no invented exit. -/
theorem iterateFrom_formed (protocol : Interaction I)
    (body : Nat → A → Proc I A) (invariant : Nat → A → protocol.Phase → Prop)
    (formed : ∀ index value phase, invariant index value phase →
      Conforms protocol (body index value) phase)
    (preserved : ∀ index value phase, invariant index value phase →
      Boundary.Returns protocol (invariant (index + 1)) (body index value) phase)
    (count index : Nat) (value : A) (phase : protocol.Phase)
    (initial : invariant index value phase) :
    Conforms protocol (iterateFrom count index body value) phase ∧
      Boundary.Returns protocol (invariant (index + count))
        (iterateFrom count index body value) phase := by
  induction count generalizing index value phase with
  | zero => exact ⟨trivial, initial⟩
  | succ count ih =>
    have exits := preserved index value phase initial
    have next := fun value phase (h : invariant (index + 1) value phase) =>
      ih (index + 1) value phase h
    have indexEq : index + 1 + count = index + (count + 1) := by omega
    simp only [indexEq] at next
    exact ⟨Boundary.conforms_bind protocol _ _ _ phase (formed index value phase initial)
      exits (fun value phase h => (next value phase h).1),
      Boundary.returns_bind protocol _ _ _ _ phase exits
        (fun value phase h => (next value phase h).2)⟩

/-- The selected count is the existing Region count, with no alternate meaning
for continuation or failure. Index-sensitive bodies use `Loop` directly. -/
theorem denote_region_iterate {language : Language}
    (meaning : Interpretation language I) {Γ ty acc}
    (count : Nat) (initial : Var Γ acc)
    (body : Region language (acc :: Γ) acc) (next : Region language (acc :: Γ) ty)
    (env : Environment meaning.Value Γ) (index : Nat) :
    (iterateFrom count index (fun _ value => body.denote meaning (env.push value))
      (env initial)).bind (fun value => next.denote meaning (env.push value)) =
        (Region.iterate count initial body next).denote meaning env := by
  rw [iterateFrom_repeat]
  rfl

/-- Normal loop completion carries a value and permits the surrounding suffix.
It is different from `Proc.halt`, which terminates the whole process. -/
inductive Step (A : Type) where
  | continue : A → Step A
  | finish : A → Step A

/-- A bounded condition is evaluated by the body on each entered iteration. -/
def iterateWhile : Nat → Nat → (Nat → A → Proc I (Step A)) → A → Proc I A
  | 0, _, _, value => .done value
  | count + 1, index, body, value =>
    (body index value).bind fun step => match step with
      | .finish result => .done result
      | .continue result => iterateWhile count (index + 1) body result

theorem iterateWhile_within (count index maximum : Nat)
    (body : Nat → A → Proc I (Step A))
    (bounded : ∀ index value, Within maximum (body index value)) (value : A) :
    Within (count * maximum) (iterateWhile count index body value) := by
  induction count generalizing index value with
  | zero => simp [iterateWhile, Within]
  | succ count ih =>
    simp only [iterateWhile, Nat.succ_mul, Nat.add_comm]
    apply Boundary.within_bind _ _ maximum (count * maximum) (bounded index value)
    intro step
    cases step with
    | finish result => cases count * maximum <;> trivial
    | «continue» result => exact ih (index + 1) result

/-- On normal completion the surrounding continuation receives the completed
value and actual residual state; unused iterations are never executed. -/
theorem iterateWhile_finish (handler : Handler I S E) (count index : Nat)
    (body : Nat → A → Proc I (Step A)) (initial result : A)
    (state residual : S) (events : List E)
    (finished : (body index initial).run handler state =
      ⟨.returned (.finish result), residual, events⟩) :
    (iterateWhile (count + 1) index body initial).run handler state =
      ⟨.returned result, residual, events⟩ := by
  rw [iterateWhile, PIR.run_bind, finished]
  simp [Execution.follow, Proc.run]

theorem iterateWhile_continue (handler : Handler I S E) (count index : Nat)
    (body : Nat → A → Proc I (Step A)) (initial result : A)
    (state residual : S) (events : List E)
    (continued : (body index initial).run handler state =
      ⟨.returned (.continue result), residual, events⟩) :
    (iterateWhile (count + 1) index body initial).run handler state =
      let rest := (iterateWhile count (index + 1) body result).run handler residual
      ⟨rest.outcome, rest.state, events ++ rest.events⟩ := by
  rw [iterateWhile, PIR.run_bind, continued]
  rfl

theorem iterateWhile_stopped (handler : Handler I S E) (count index : Nat)
    (body : Nat → A → Proc I (Step A)) (initial : A) (next : A → Proc I B)
    (state residual : S) (events : List E) (reason : Stop)
    (stopped : (body index initial).run handler state = ⟨.stopped reason, residual, events⟩) :
    ((iterateWhile (count + 1) index body initial).bind next).run handler state =
      ⟨.stopped reason, residual, events⟩ := by
  rw [iterateWhile, Proc.bind_assoc, PIR.run_bind, stopped]
  rfl

end Zkc.Source.FiniteControl
