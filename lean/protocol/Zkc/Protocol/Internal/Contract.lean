module

public import Zkc.Protocol.Internal.Quantitative

/-!
# Upper and lower contracts for stateful probabilistic programs

Contracts are inequalities over upstream `FreeM.wpFold`, with a potential on the complete private
state. Bind integrates the continuation's potential at the actual returned answer and state.
Local operation inequalities are sufficient for adequacy of every adaptive free program.

The rules apply to nonnegative rewards and arbitrary kernels. Event corollaries give unconditional
event masses, including under subprobability execution. Probability and completeness applications
must supply their own mass discipline. `closed_mass_one` supplies normalization from normalized
initial states and primitive operations. Explicit reject and abort values remain ordinary results.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe uA uB uS uX uY

namespace ProtocolProof.Internal

variable {P : PFunctor.{uA, uB}} {S : Type uS} {α : Type uX} {β : Type uY}

/-- The folded expected terminal reward is bounded above by an initial-state potential. -/
@[expose]
def UpperBound (spec : PFunctor.OpSpec P (S → ENNReal)) (program : PFunctor.FreeM P α)
    (post : α → S → ENNReal) (bound : S → ENNReal) : Prop :=
  PFunctor.FreeM.wpFold spec program post ≤ bound

/-- An initial-state potential is bounded above by the folded expected terminal reward. -/
@[expose]
def LowerBound (spec : PFunctor.OpSpec P (S → ENNReal)) (program : PFunctor.FreeM P α)
    (post : α → S → ENNReal) (bound : S → ENNReal) : Prop :=
  bound ≤ PFunctor.FreeM.wpFold spec program post

variable {spec : PFunctor.OpSpec P (S → ENNReal)}
variable {program : PFunctor.FreeM P α} {post post' : α → S → ENNReal}
variable {bound bound' : S → ENNReal}

namespace UpperBound

/-- A returned value satisfies exactly the pointwise terminal-reward obligation. -/
theorem pure (value : α) (h : post value ≤ bound) :
    UpperBound spec (pure value) post bound := h

/-- A primitive operation is discharged by its local continuation-potential specification. -/
theorem operation (a : P.A) (post : P.B a → S → ENNReal)
    (h : spec a post ≤ bound) : UpperBound spec (PFunctor.FreeM.lift a) post bound := h

/-- Sequential contracts compose through an answer-and-state dependent cut potential. -/
theorem bind (h : UpperBound spec program post bound) (hmono : spec.Monotone)
    {next : α → PFunctor.FreeM P β} {reward : β → S → ENNReal}
    (hnext : ∀ value, UpperBound spec (next value) reward (post value)) :
    UpperBound spec (program.bind next) reward bound := by
  unfold UpperBound at *
  rw [PFunctor.FreeM.wpFold_bind']
  exact (PFunctor.FreeM.wpFold_mono hmono program hnext).trans h

/-- Decreasing the reward and increasing the budget preserves an upper contract. -/
theorem consequence (h : UpperBound spec program post bound) (hmono : spec.Monotone)
    (hpost : post' ≤ post) (hbound : bound ≤ bound') :
    UpperBound spec program post' bound' :=
  (PFunctor.FreeM.wpFold_mono hmono program hpost).trans (h.trans hbound)

/-- A branch uses the contract of the selected branch, including its proof-dependent body. -/
theorem dite (condition : Prop) [Decidable condition]
    (yes : condition → PFunctor.FreeM P α) (no : ¬condition → PFunctor.FreeM P α)
    (hyes : ∀ h, UpperBound spec (yes h) post bound)
    (hno : ∀ h, UpperBound spec (no h) post bound) :
    UpperBound spec (if h : condition then yes h else no h) post bound := by
  split
  · exact hyes _
  · exact hno _

/-- Ordinary conditional composition is a specialization of the dependent branch rule. -/
theorem ite (condition : Prop) [Decidable condition] (yes no : PFunctor.FreeM P α)
    (hyes : condition → UpperBound spec yes post bound)
    (hno : ¬condition → UpperBound spec no post bound) :
    UpperBound spec (if condition then yes else no) post bound :=
  dite condition (fun _ ↦ yes) (fun _ ↦ no) hyes hno

/-- An indexed invariant composes any finite sequence of stateful, adaptive iteration bodies.

The accumulator may include explicit stopped outcomes, and a body may itself contain nested
iterations. The invariant depends on both the iteration index and the complete private state.
-/
theorem iterate (hmono : spec.Monotone) (body : Nat → α → PFunctor.FreeM P α)
    (invariant : Nat → α → S → ENNReal) (count : Nat)
    (hstep : ∀ round, round < count → ∀ value,
      UpperBound spec (body round value) (invariant (round + 1)) (invariant round value))
    (initial : α) :
    UpperBound spec
      ((List.range count).foldlM (fun value round ↦ body round value) initial)
      (invariant count) (invariant 0 initial) := by
  induction count with
  | zero => exact UpperBound.pure initial le_rfl
  | succ count ih =>
      rw [List.range_succ, List.foldlM_append]
      apply (ih (fun round hround ↦ hstep round (Nat.lt_succ_of_lt hround))).bind hmono
      intro value
      simpa using hstep count (Nat.lt_succ_self count) value

end UpperBound

namespace LowerBound

/-- A returned value satisfies exactly the pointwise terminal-reward obligation. -/
theorem pure (value : α) (h : bound ≤ post value) :
    LowerBound spec (pure value) post bound := h

/-- A primitive lower contract is a local lower expectation inequality. -/
theorem operation (a : P.A) (post : P.B a → S → ENNReal)
    (h : bound ≤ spec a post) : LowerBound spec (PFunctor.FreeM.lift a) post bound := h

/-- Lower continuation potentials compose in the same reached answer-and-state distribution. -/
theorem bind (h : LowerBound spec program post bound) (hmono : spec.Monotone)
    {next : α → PFunctor.FreeM P β} {reward : β → S → ENNReal}
    (hnext : ∀ value, LowerBound spec (next value) reward (post value)) :
    LowerBound spec (program.bind next) reward bound := by
  unfold LowerBound at *
  rw [PFunctor.FreeM.wpFold_bind']
  exact h.trans (PFunctor.FreeM.wpFold_mono hmono program hnext)

/-- Increasing the reward and decreasing the claimed lower potential preserves the contract. -/
theorem consequence (h : LowerBound spec program post bound) (hmono : spec.Monotone)
    (hpost : post ≤ post') (hbound : bound' ≤ bound) :
    LowerBound spec program post' bound' :=
  hbound.trans (h.trans (PFunctor.FreeM.wpFold_mono hmono program hpost))

/-- A lower contract follows the actual dependent branch. -/
theorem dite (condition : Prop) [Decidable condition]
    (yes : condition → PFunctor.FreeM P α) (no : ¬condition → PFunctor.FreeM P α)
    (hyes : ∀ h, LowerBound spec (yes h) post bound)
    (hno : ∀ h, LowerBound spec (no h) post bound) :
    LowerBound spec (if h : condition then yes h else no h) post bound := by
  split
  · exact hyes _
  · exact hno _

/-- An ordinary branch inherits the lower contract of its selected arm. -/
theorem ite (condition : Prop) [Decidable condition] (yes no : PFunctor.FreeM P α)
    (hyes : condition → LowerBound spec yes post bound)
    (hno : ¬condition → LowerBound spec no post bound) :
    LowerBound spec (if condition then yes else no) post bound :=
  dite condition (fun _ ↦ yes) (fun _ ↦ no) hyes hno

/-- Finite iteration preserves an iteration-, accumulator-, and private-state indexed lower
potential, including nested iterations and explicit stopped accumulator values. -/
theorem iterate (hmono : spec.Monotone) (body : Nat → α → PFunctor.FreeM P α)
    (invariant : Nat → α → S → ENNReal) (count : Nat)
    (hstep : ∀ round, round < count → ∀ value,
      LowerBound spec (body round value) (invariant (round + 1)) (invariant round value))
    (initial : α) :
    LowerBound spec
      ((List.range count).foldlM (fun value round ↦ body round value) initial)
      (invariant count) (invariant 0 initial) := by
  induction count with
  | zero => exact LowerBound.pure initial le_rfl
  | succ count ih =>
      rw [List.range_succ, List.foldlM_append]
      apply (ih (fun round hround ↦ hstep round (Nat.lt_succ_of_lt hround))).bind hmono
      intro value
      simpa using hstep count (Nat.lt_succ_self count) value

end LowerBound

section Adequacy

variable [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S]
variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
variable [MeasurableSpace α]

/-- Upper operation specifications bound every complete program's kernel expectation.

The only semantic premises concern individual operations, for every continuation potential.
Monotonicity of the exact expectation propagates the induction through adaptive continuations.
-/
theorem runExpectation_le_wpFold (handler : PFunctor.KernelHandler P S)
    (hlocal : ∀ a continuation, opExpectation handler a continuation ≤ spec a continuation)
    (program : PFunctor.FreeM P α) (post : α → S → ENNReal)
    (hpost : Measurable fun out : α × S ↦ post out.1 out.2) :
    runExpectation handler program post ≤ PFunctor.FreeM.wpFold spec program post := by
  rw [← wpFold_eq_runExpectation_of_measurable handler program post hpost]
  induction program with
  | pure value => exact le_rfl
  | lift_bind a next ih =>
      exact ((opExpectation_monotone handler) a ih).trans (hlocal a _)

/-- Lower operation specifications yield unconditional lower expectations for whole programs. -/
theorem wpFold_le_runExpectation (handler : PFunctor.KernelHandler P S)
    (hlocal : ∀ a continuation, spec a continuation ≤ opExpectation handler a continuation)
    (program : PFunctor.FreeM P α) (post : α → S → ENNReal)
    (hpost : Measurable fun out : α × S ↦ post out.1 out.2) :
    PFunctor.FreeM.wpFold spec program post ≤ runExpectation handler program post := by
  rw [← wpFold_eq_runExpectation_of_measurable handler program post hpost]
  induction program with
  | pure value => exact le_rfl
  | lift_bind a next ih =>
      exact (hlocal a _).trans ((opExpectation_monotone handler) a ih)

namespace UpperBound

/-- A composed upper contract is adequate when every operation spec is a local upper bound. -/
theorem adequate (h : UpperBound spec program post bound)
    (handler : PFunctor.KernelHandler P S)
    (hlocal : ∀ a continuation, opExpectation handler a continuation ≤ spec a continuation)
    (hpost : Measurable fun out : α × S ↦ post out.1 out.2) :
    runExpectation handler program post ≤ bound :=
  (runExpectation_le_wpFold handler hlocal program post hpost).trans h

/-- Integrating an adequate upper potential against the fixed initial law closes the bound. -/
theorem closed_expectation_le (h : UpperBound spec program post bound)
    (handler : PFunctor.KernelHandler P S)
    (hlocal : ∀ a continuation, opExpectation handler a continuation ≤ spec a continuation)
    (hpost : Measurable fun out : α × S ↦ post out.1 out.2)
    (initial : Measure S) {budget : ENNReal} (hbudget : (∫⁻ state, bound state ∂initial) ≤ budget) :
    (∫⁻ out, post out.1 out.2
      ∂initial.bind (PFunctor.FreeM.runKernel handler program)) ≤ budget := by
  rw [← lintegral_runExpectation handler program post hpost]
  exact (lintegral_mono (h.adequate handler hlocal hpost)).trans hbudget

/-- An indicator contract bounds actual event mass, with no conditioning on returned outcomes. -/
theorem closed_event_le (handler : PFunctor.KernelHandler P S)
    (hlocal : ∀ a continuation, opExpectation handler a continuation ≤ spec a continuation)
    (event : Set (α × S)) (hevent : MeasurableSet event)
    (h : UpperBound spec program (fun value state ↦ event.indicator 1 (value, state)) bound)
    (initial : Measure S) {budget : ENNReal} (hbudget : (∫⁻ state, bound state ∂initial) ≤ budget) :
    initial.bind (PFunctor.FreeM.runKernel handler program) event ≤ budget := by
  rw [← lintegral_runExpectation_indicator handler program event hevent initial]
  exact (lintegral_mono
    (h.adequate handler hlocal (measurable_const.indicator hevent))).trans hbudget

end UpperBound

namespace LowerBound

/-- A composed lower contract is adequate from per-operation lower bounds. -/
theorem adequate (h : LowerBound spec program post bound)
    (handler : PFunctor.KernelHandler P S)
    (hlocal : ∀ a continuation, spec a continuation ≤ opExpectation handler a continuation)
    (hpost : Measurable fun out : α × S ↦ post out.1 out.2) :
    bound ≤ runExpectation handler program post :=
  h.trans (wpFold_le_runExpectation handler hlocal program post hpost)

/-- A fixed initial lower potential gives a lower bound on the closed expected reward. -/
theorem le_closed_expectation (h : LowerBound spec program post bound)
    (handler : PFunctor.KernelHandler P S)
    (hlocal : ∀ a continuation, spec a continuation ≤ opExpectation handler a continuation)
    (hpost : Measurable fun out : α × S ↦ post out.1 out.2)
    (initial : Measure S) {budget : ENNReal} (hbudget : budget ≤ ∫⁻ state, bound state ∂initial) :
    budget ≤ ∫⁻ out, post out.1 out.2
      ∂initial.bind (PFunctor.FreeM.runKernel handler program) := by
  rw [← lintegral_runExpectation handler program post hpost]
  exact hbudget.trans (lintegral_mono (h.adequate handler hlocal hpost))

/-- A lower indicator contract proves unconditional accepting mass, including execution loss. -/
theorem le_closed_event (handler : PFunctor.KernelHandler P S)
    (hlocal : ∀ a continuation, spec a continuation ≤ opExpectation handler a continuation)
    (event : Set (α × S)) (hevent : MeasurableSet event)
    (h : LowerBound spec program (fun value state ↦ event.indicator 1 (value, state)) bound)
    (initial : Measure S) {budget : ENNReal} (hbudget : budget ≤ ∫⁻ state, bound state ∂initial) :
    budget ≤ initial.bind (PFunctor.FreeM.runKernel handler program) event := by
  rw [← lintegral_runExpectation_indicator handler program event hevent initial]
  exact hbudget.trans (lintegral_mono
    (h.adequate handler hlocal (measurable_const.indicator hevent)))

end LowerBound

end Adequacy

end ProtocolProof.Internal
