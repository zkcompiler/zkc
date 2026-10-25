import Zkc.Semantics.Execution
import Zkc.Semantics.MonadExecution
import ZkcTools.DeclarationAudit

/-! Standard monadic notation preserves the open tree, adversarial branches,
ordered effects and stopped prefixes of the process semantics. -/

namespace ProcessNotationTests
open PIR

abbrev channel : Signature := ⟨Unit, fun _ => Bool⟩

def receive : Process channel Bool := .call () .done

def verifier : Process channel Nat := do
  let proceed ← receive
  if proceed then
    let accepted ← receive
    return if accepted then 1 else 0
  else
    .halt .reject

/-- Equality includes every reply branch, not only an honest execution. -/
theorem verifier_tree : verifier =
    .call () (fun proceed => if proceed then
      .call () (fun accepted => .done (if accepted then 1 else 0))
    else .halt .reject) := rfl

def replies : Handler channel Nat Nat := fun _ state =>
  ⟨.returned (state == 0), state + 1, [state]⟩

theorem returned_false_trace : verifier.run replies 0 = ⟨.returned 0, 2, [0, 1]⟩ := rfl
theorem rejected_trace : verifier.run replies 1 = ⟨.stopped .reject, 2, [1]⟩ := rfl

/-- A stopped action does not run the suffix, and retains its reached event. -/
theorem stopped_suffix : ((do let _ ← verifier; receive) : Process channel Bool).run replies 1 =
    ⟨.stopped .reject, 2, [1]⟩ := rfl

def stoppedReply : Handler channel Nat Nat := fun _ state =>
  ⟨.stopped .abort, state + 1, [state]⟩

/-- A handler-produced stop also suppresses all reply-dependent continuation. -/
theorem handler_stopped_trace : verifier.run stoppedReply 0 =
    ⟨.stopped .abort, 1, [0]⟩ := rfl

/-- Generic monad simplification is available without unfolding the effect tree. -/
theorem standard_bind_pure (process : Process channel Nat) :
    (do let value ← process; pure value) = process := by simp

/-- Monadic notation also selects the existing outer-monad execution. -/
theorem monadic_execution : verifier.runM (m := Id) (fun op state => pure (replies op state)) 1 =
    (pure ⟨.stopped .reject, 2, [1]⟩ : Id (Execution Nat Nat Nat)) := rfl

run_cmd ZkcTools.DeclarationAudit.checkCurrent "PROCESS-NOTATION-AXIOM-PASS"

end ProcessNotationTests
