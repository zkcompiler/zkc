module

public import ZkcSecurity.VCVio.Execution

@[expose] public section

namespace TestsSecurity.CausalSumcheck.Execution

open OracleComp ZkcSecurity.VCVio.Execution
open scoped ENNReal

abbrev Interface : PIR.Signature where
  Op := Unit
  Reply _ := Unit

def work : PIR.Proc Interface Unit := .call () .done

def handler (stop : Bool) : PIR.MonadHandler ProbComp Interface Nat String := fun _ s =>
  pure ⟨if stop then .stopped .exhausted else .returned (), s + 1, ["trusted-work"]⟩

def calculation (value : Nat) : PIR.Proc Interface Nat := work.bind fun _ => .done value

/-- An effectful calculation followed by an arbitrary continuation uses the
same residual state and events. The returned value is not an ignored Unit. -/
theorem determined_context (stop : Bool) (value : Nat)
    (next : Nat → PIR.Proc Interface Nat) (s : Nat) :
    ((calculation value).bind next).runM (handler stop) s = (do
      let e ← work.runM (handler stop) s
      e.followM fun _ s => (next value).runM (handler stop) s) := by
  apply runM_bind_determined (handler stop) _ (work.runM (handler stop)) value
  intro s
  exact runM_determined_of_proc (handler stop) _ work value rfl s

/-- Exhaustion preserves the actual prefix and does not supply a fabricated value. -/
theorem determined_stop (value : Nat) (s : Nat) :
    (calculation value).runM (handler true) s =
      pure ⟨.stopped .exhausted, s + 1, ["trusted-work"]⟩ := by
  simp [calculation, work, handler, PIR.Proc.bind, PIR.Proc.runM, PIR.Execution.followM]

theorem determined_return (value : Nat) (s : Nat) :
    (calculation value).runM (handler false) s =
      pure ⟨.returned value, s + 1, ["trusted-work"]⟩ := by
  simp [calculation, work, handler, PIR.Proc.bind, PIR.Proc.runM, PIR.Execution.followM]

/-- The Proc-level law suffices for a conservative checker after any prefix. -/
theorem checker_from_proc (stop : Bool) (p : PIR.Proc Interface Nat) (s : Nat) :
    mass (checked (handler stop) p (fun a => work.bind fun _ => .done (decide (a = 0))) s) ≤
      mass (acceptance (handler stop) (attachWork p (fun _ => work)) s (fun a => a ≤ 1)) := by
  apply checked_le_of_proc (handler stop) p (fun _ => work) _ (fun a => decide (a = 0)) s
    (fun _ => rfl)
  intro a ha
  have : a = 0 := of_decide_eq_true ha
  omega

/-- This implementation consumes an additional hidden random draw. It has the
same Execution distribution, but does not have the same oracle-query cost. -/
def sampledHandler (stop : Bool) : PIR.MonadHandler ProbComp Interface Nat String := fun op s => do
  let _ ← ($ᵗ Bool)
  handler stop op s

theorem sampled_handler_law (stop : Bool) (op : Interface.Op) (s : Nat) :
    SameDist (sampledHandler stop op s) (handler stop op s) := by
  let : MeasurableSpace (PIR.Execution Nat String (Interface.Reply op)) := ⊤
  unfold SameDist sampledHandler
  exact OracleComp.evalDist_bind_const _ _

/-- Arbitrary continuations preserve the complete observed execution, including
the stopped prefix; no unfolding of the particular caller is needed. -/
theorem sampled_handler_context {A : Type} (stop : Bool)
    (process : PIR.Proc Interface A) (s : Nat) :
    SameDist (process.runM (sampledHandler stop) s) (process.runM (handler stop) s) :=
  runM_sameDist _ _ (sampled_handler_law stop) process s

end TestsSecurity.CausalSumcheck.Execution
