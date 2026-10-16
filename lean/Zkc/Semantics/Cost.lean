module

public import Zkc.Semantics.InterpretationAdmission

@[expose] public section

/-! Exact operation-sensitive accounting for finite executions.

The monitor charges entered operations, including operations that stop. A charge
may depend on the pre-state and actual result (for example, a cache miss).
It cannot inspect the accumulated counter. Counters are accounting state, not
attacker observations; callers must explicitly choose whether to expose them.
-/

set_option autoImplicit false
namespace PIR.Cost

variable {I J : Signature} {S E A B : Type}

abbrev Charge (I : Signature) (S E : Type) :=
  (op : I.Op) → S → Execution S E (I.Reply op) → Nat

/-- Instrument an actual handler; no call or stop is erased. -/
def handler (charge : Charge I S E) (backend : Handler I S E) :
    Handler I (S × Nat) E := fun op state =>
  let result := backend op state.1
  ⟨result.outcome, (result.state, state.2 + charge op state.1 result), result.events⟩

/-- The monitor has no effect on logical state, terminal outcome or events. -/
theorem run_related (charge : Charge I S E) (backend : Handler I S E)
    (program : Proc I A) (state : S) (initial : Nat) :
    Related (fun s t => s = t.1) (fun e => [e]) (fun e => [e])
      (program.run backend state) (program.run (handler charge backend) (state, initial)) := by
  apply PIR.run_related _ _ _ _ _ _ program state (state, initial) rfl
  intro op s t same
  subst s
  exact ⟨rfl, rfl, rfl⟩

/-- Changing the initial ledger adds exactly that amount even on inner stops. -/
theorem run_shift (charge : Charge I S E) (backend : Handler I S E)
    (program : Proc I A) (state : S) (initial extra : Nat) :
    program.run (handler charge backend) (state, initial + extra) =
      let result := program.run (handler charge backend) (state, initial)
      ⟨result.outcome, (result.state.1, result.state.2 + extra), result.events⟩ := by
  induction program generalizing state initial with
  | done value => rfl
  | halt why => rfl
  | call op next ih =>
    simp only [Proc.run, handler]
    cases h : backend op state with
    | mk outcome residual events =>
      cases outcome with
      | stopped why => simp [Execution.follow, Nat.add_assoc, Nat.add_comm]
      | returned value =>
        simp only [Execution.follow]
        rw [show initial + extra + charge op state ⟨.returned value, residual, events⟩ =
          (initial + charge op state ⟨.returned value, residual, events⟩) + extra by omega]
        rw [ih]

/-- Exact cost from a zero ledger. Repeated queries can be charged even when
cached, or a separately selected charge can count only misses. -/
def spent (charge : Charge I S E) (backend : Handler I S E)
    (program : Proc I A) (state : S) : Nat :=
  (program.run (handler charge backend) (state, 0)).state.2

theorem run_eq (charge : Charge I S E) (backend : Handler I S E)
    (program : Proc I A) (state : S) (initial : Nat) :
    program.run (handler charge backend) (state, initial) =
      let result := program.run backend state
      ⟨result.outcome, (result.state, initial + spent charge backend program state),
        result.events⟩ := by
  have related := run_related charge backend program state 0
  have shifted := run_shift charge backend program state 0 initial
  simp only [Nat.zero_add] at shifted
  rw [shifted]
  have events := related.events
  simp only [observeEvents, List.flatMap_singleton'] at events
  cases h : program.run (handler charge backend) (state, 0) with
  | mk outcome residual es =>
    rcases residual with ⟨s, count⟩
    simp only [h] at related events ⊢
    simp only [spent, h]
    have outcomeEq := related.outcome
    have stateEq := related.state
    dsimp at outcomeEq stateEq
    rw [outcomeEq, stateEq, events, Nat.add_comm count initial]

/-- Sequencing charges the actual suffix at the actual residual state. A stopped
prefix contributes its cost alone; the suffix has no execution or charge. -/
theorem spent_bind (charge : Charge I S E) (backend : Handler I S E)
    (program : Proc I A) (next : A → Proc I B) (state : S) :
    spent charge backend (program.bind next) state =
      spent charge backend program state +
        match (program.run backend state).outcome with
        | .stopped _ => 0
        | .returned value => spent charge backend (next value) (program.run backend state).state := by
  change ((program.bind next).run (handler charge backend) (state, 0)).state.2 = _
  rw [PIR.run_bind, run_eq]
  cases h : program.run backend state with
  | mk outcome residual events =>
    cases outcome with
    | stopped why => simp [Execution.follow]
    | returned value =>
      simp only [Execution.follow]
      rw [run_eq]
      simp only [Nat.zero_add]

/-- Charge one source operation for the actual complete expansion. This includes
multiple lower calls, state-dependent hits/misses, and partially executed stops. -/
def expansionCharge (operations : OperationInterpretation I J)
    (charge : Charge J S E) (backend : Handler J S E) : Charge I S E :=
  fun op state _ => spent charge backend (operations op) state

/-- The central accounting equation is derived from the concrete monitor and
staging laws. There is no assumed whole-program correspondence field. -/
theorem run_interpret (operations : OperationInterpretation I J)
    (charge : Charge J S E) (backend : Handler J S E)
    (program : Proc I A) (state : S × Nat) :
    (program.interpret operations).run (handler charge backend) state =
      program.run
        (handler (expansionCharge operations charge backend)
          (fun op s => (operations op).run backend s)) state := by
  rw [Proc.run_interpret]
  congr 1
  funext op s
  exact run_eq charge backend (operations op) s.1 s.2

theorem spent_interpret (operations : OperationInterpretation I J)
    (charge : Charge J S E) (backend : Handler J S E)
    (program : Proc I A) (state : S) :
    spent charge backend (program.interpret operations) state =
      spent (expansionCharge operations charge backend)
        (fun op s => (operations op).run backend s) program state := by
  unfold spent
  rw [run_interpret]

/-- Pointwise operation-cost domination lifts through every adaptive context,
without identifying cost with events or requiring successful termination. -/
theorem spent_mono (smaller larger : Charge I S E) (backend : Handler I S E)
    (bounded : ∀ op state, smaller op state (backend op state) ≤
      larger op state (backend op state)) (program : Proc I A) (state : S) :
    spent smaller backend program state ≤ spent larger backend program state := by
  have law : HandlerRelated (fun s t : S × Nat => s.1 = t.1 ∧ s.2 ≤ t.2)
      (fun e : E => [e]) (fun e => [e])
      (handler smaller backend) (handler larger backend) := by
    intro op s t related
    rcases s with ⟨s, a⟩
    rcases t with ⟨t, b⟩
    obtain ⟨same, le⟩ := related
    dsimp at same le
    subst t
    exact ⟨rfl, ⟨rfl, Nat.add_le_add le (bounded op s)⟩, rfl⟩
  exact (PIR.run_related _ _ _ _ _ law program (state, 0) (state, 0)
    ⟨rfl, Nat.le_refl 0⟩).state.2

/-- Heterogeneous source charges can bound heterogeneous expansions. The
premise is local to each operation at its actual input state; the whole-program
inequality, including early-stop behavior, is proved by transport. -/
theorem spent_interpret_le (operations : OperationInterpretation I J)
    (charge : Charge J S E) (backend : Handler J S E) (budget : Charge I S E)
    (bounded : ∀ op state, spent charge backend (operations op) state ≤
      budget op state ((operations op).run backend state))
    (program : Proc I A) (state : S) :
    spent charge backend (program.interpret operations) state ≤
      spent budget (fun op s => (operations op).run backend s) program state := by
  rw [spent_interpret]
  exact spent_mono _ budget _ bounded program state

/-- Reuse the existing uniform interface-call bound. Charging a stopped call is
included; unreachable continuations never consume ledger entries. -/
theorem run_bound (charge : Charge I S E) (backend : Handler I S E)
    (maximum : Nat) (bounded : ∀ op s, charge op s (backend op s) ≤ maximum)
    (program : Proc I A) (calls : Nat) (within : Within calls program)
    (state : S) (initial : Nat) :
    (program.run (handler charge backend) (state, initial)).state.2 ≤
      initial + calls * maximum := by
  induction program generalizing calls state initial with
  | done value => simp [Proc.run]
  | halt why => simp [Proc.run]
  | call op next ih =>
    cases calls with
    | zero => exact False.elim within
    | succ calls =>
      have stepBound := bounded op state
      simp only [Proc.run, handler]
      cases h : backend op state with
      | mk outcome residual events =>
        rw [h] at stepBound
        cases outcome with
        | stopped why => simp only [Execution.follow]; rw [Nat.succ_mul]; omega
        | returned value =>
          simp only [Execution.follow]
          have tailBound := ih value calls (within value) residual
            (initial + charge op state ⟨.returned value, residual, events⟩)
          rw [Nat.succ_mul]
          omega

theorem spent_bound (charge : Charge I S E) (backend : Handler I S E)
    (maximum : Nat) (bounded : ∀ op s, charge op s (backend op s) ≤ maximum)
    (program : Proc I A) (calls : Nat) (within : Within calls program) (state : S) :
    spent charge backend program state ≤ calls * maximum := by
  simpa only [spent, Nat.zero_add] using
    run_bound charge backend maximum bounded program calls within state 0

/-- A logical call budget transports through state-dependent expansion costs.
`maximum` bounds each actual expansion, not the cost of a fictitious single call. -/
theorem spent_interpret_bound (operations : OperationInterpretation I J)
    (charge : Charge J S E) (backend : Handler J S E) (maximum : Nat)
    (bounded : ∀ op s, spent charge backend (operations op) s ≤ maximum)
    (program : Proc I A) (calls : Nat) (within : Within calls program) (state : S) :
    spent charge backend (program.interpret operations) state ≤ calls * maximum := by
  rw [spent_interpret]
  exact spent_bound _ _ maximum bounded program calls within state

end PIR.Cost
