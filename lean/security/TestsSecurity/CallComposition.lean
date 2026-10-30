import ZkcSecurity.ProgramLogic.Oracle.Composition
import ZkcTools.DeclarationAudit

/-! Controls for acceptance composition at a call boundary. -/
namespace TestsSecurity.CallComposition

open OracleComp OracleSpec
open ZkcSecurity.VCVio.Execution ZkcSecurity.VCVio.Composition

/-- A terminal guard accepts exactly true and refuses false. -/
def guarded {I : PIR.Signature} (value : Bool) : PIR.Process I Bool :=
  if value then .done true else .halt .refused

theorem guarded_terminal {I : PIR.Signature} {S E : Type}
    (h : PIR.MonadHandler ProbComp I S E) (a : Bool) (state : S)
    (e : PIR.Execution S E Bool) (supported : e ∈ support ((guarded a).runM h state))
    (accepted : returnedSatisfies (· = true) e) : a = true := by
  cases a <;> simp_all [guarded, PIR.Process.runM, returnedSatisfies]

/-- No restrictions on the prefix, its effects, or its stopping behavior. -/
theorem arbitrary_prefix_bound {I : PIR.Signature} {S E : Type}
    (h : PIR.MonadHandler ProbComp I S E) (p : PIR.Process I Bool) (s : S) :
    mass (acceptance h (p.bind guarded) s (· = true)) ≤
      mass (acceptance h p s (· = true)) :=
  acceptance_bind_le h p guarded s _ _ (guarded_terminal h)

inductive Action where
  | prepare
  | inspect
  | draw

abbrev interface : PIR.Signature where
  Op := Action
  Reply _ := Bool

inductive Event where
  | prepared (state : Nat)
  | inspected (state : Nat)
  | drawn (bit : Fin 2)
  deriving DecidableEq, Repr

def handler : PIR.MonadHandler ProbComp interface Nat Event
  | .prepare, s => pure ⟨.returned false, s + 1, [.prepared s]⟩
  | .inspect, s => pure ⟨.returned (s != 0), s, [.inspected s]⟩
  | .draw, s => do
      let bit ← ($ᵗ Fin 2)
      pure ⟨if bit = 0 then .stopped .abort else .returned true, s + 1, [.drawn bit]⟩

def changingPrefix : PIR.Process interface Bool := .call .prepare .done

def stateSensitive (_ : Bool) : PIR.Process interface Bool := .call .inspect .done

def randomPrefix : PIR.Process interface Bool := .call .draw .done

/-- Refusal keeps the prefix's updated state and event. -/
theorem guard_refusal (s : Nat) :
    (changingPrefix.bind guarded).runM handler s =
      pure ⟨.stopped .refused, s + 1, [.prepared s]⟩ := by
  simp [changingPrefix, guarded, PIR.Process.bind, PIR.Process.runM, handler,
    PIR.Execution.followM]

theorem guard_refusal_mass (s : Nat) :
    mass (acceptance handler (changingPrefix.bind guarded) s (· = true)) = 0 := by
  simp [acceptance, guard_refusal, returnedSatisfies, mass]

/-- At the initial state, the terminal implication to False holds vacuously. -/
theorem initial_state_terminal (a : Bool) (e : PIR.Execution Nat Event Bool)
    (supported : e ∈ support ((stateSensitive a).runM handler 0)) :
    returnedSatisfies (· = true) e → False := by
  simp [stateSensitive, PIR.Process.runM, handler, PIR.Execution.followM] at supported
  subst e
  simp [returnedSatisfies]

theorem changed_state_accepts :
    (changingPrefix.bind stateSensitive).runM handler 0 =
      pure ⟨.returned true, 1, [.prepared 0, .inspected 1]⟩ := by
  simp [changingPrefix, stateSensitive, PIR.Process.bind, PIR.Process.runM,
    handler, PIR.Execution.followM]

/-- Checking the terminal implication only at the initial state gives a false bound. -/
theorem initial_state_is_insufficient :
    ¬ mass (acceptance handler (changingPrefix.bind stateSensitive) 0 (· = true)) ≤
      mass (acceptance handler changingPrefix 0 (fun _ => False)) := by
  unfold acceptance
  rw [changed_state_accepts]
  simp [changingPrefix, PIR.Process.runM,
    handler, PIR.Execution.followM, returnedSatisfies, mass]

/-- Even a pure prefix disproves the bound when its terminal premise is omitted. -/
theorem terminal_premise_is_necessary :
    ¬ mass (acceptance handler ((PIR.Process.done false).bind fun _ => .done true)
        0 (· = true)) ≤
      mass (acceptance handler (.done false) 0 (· = true)) := by
  simp [acceptance, PIR.Process.bind, PIR.Process.runM, returnedSatisfies, mass]

/-- The stopped prefix skips the state-reading continuation and its event. -/
theorem stopped_prefix (s : Nat) :
    ((PIR.Process.halt .abort).bind stateSensitive).runM handler s =
      pure ⟨.stopped .abort, s, []⟩ := rfl

theorem stopped_prefix_mass (s : Nat) :
    mass (acceptance handler ((PIR.Process.halt .abort).bind stateSensitive)
      s (· = true)) = 0 := by
  simp [acceptance, stopped_prefix, returnedSatisfies, mass]

/-- Half of the executions stop with the recorded draw; half pass the terminal.
The prefix's increment and event survive on both branches. -/
theorem random_call_exact (s : Nat) :
    (randomPrefix.bind guarded).runM handler s = (do
      let bit ← ($ᵗ Fin 2)
      pure ⟨if bit = 0 then .stopped .abort else .returned true,
        s + 1, [.drawn bit]⟩) := by
  simp only [randomPrefix, PIR.Process.bind, PIR.Process.runM, handler, bind_assoc]
  apply bind_congr
  intro bit
  by_cases zero : bit = 0 <;>
    simp [zero, PIR.Execution.followM, guarded, PIR.Process.runM]

theorem random_call_mass (s : Nat) :
    mass (acceptance handler (randomPrefix.bind guarded) s (· = true)) = 1 / 2 := by
  unfold acceptance
  rw [random_call_exact]
  simp only [bind_assoc, pure_bind]
  have observation (bit : Fin 2) :
      returnedSatisfies (· = true)
        (⟨if bit = 0 then .stopped .abort else .returned true,
          s + 1, [Event.drawn bit]⟩ : PIR.Execution Nat Event Bool) ↔ bit = 1 := by
    fin_cases bit <;> simp [returnedSatisfies]
  simp_rw [propext (observation _)]
  change Pr{let bit ← ($ᵗ Fin 2)}[bit = 1] = _
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  norm_num

theorem random_call_bound (s : Nat) :
    mass (acceptance handler (randomPrefix.bind guarded) s (· = true)) ≤
      mass (acceptance handler randomPrefix s (· = true)) :=
  arbitrary_prefix_bound handler randomPrefix s

end TestsSecurity.CallComposition

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`ZkcSecurity.ProgramLogic.Oracle.Composition]
    "CALL-PROBABILITY-LIBRARY-AUDIT-PASS" (exactModules := true)
