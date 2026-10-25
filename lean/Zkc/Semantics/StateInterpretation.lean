module

public import Zkc.Semantics.Interpretation

@[expose] public section

/-! State-threaded operation interpretation over the existing finite Process.
The state belongs to the interpretation (for example occurrence coordinates or
an ideal transcript); this does not replace the runtime handler's post-state.
Stopped processes keep their operation prefix and do not run a continuation. -/
set_option autoImplicit false
namespace PIR

abbrev StateOperationInterpretation (I J : Signature) (S : Type) :=
  (operation : I.Op) → S → Process J (I.Reply operation × S)

namespace Process
variable {I J : Signature} {S A B : Type}

def interpretState (operations : StateOperationInterpretation I J S) :
    Process I A → S → Process J (A × S)
  | .done value, state => .done (value, state)
  | .halt reason, _ => .halt reason
  | .call operation next, state =>
      (operations operation state).bind fun (reply, nextState) =>
        (next reply).interpretState operations nextState

/-- The continuation receives the actual state of the reached prefix. -/
theorem interpretState_bind (operations : StateOperationInterpretation I J S)
    (process : Process I A) (next : A → Process I B) (state : S) :
    (process.bind next).interpretState operations state =
      (process.interpretState operations state).bind fun (value, final) =>
        (next value).interpretState operations final := by
  induction process generalizing state with
  | done => rfl
  | halt => rfl
  | call operation continuation ih =>
    simp only [bind, interpretState, bind_assoc]
    congr 1
    funext result
    exact ih result.1 result.2

/-- A state-free interpretation embeds without changing that state. -/
theorem interpretState_constant (operations : OperationInterpretation I J)
    (process : Process I A) (state : S) :
    process.interpretState (fun operation current =>
      (operations operation).bind fun reply => .done (reply, current)) state =
        (process.interpret operations).bind (fun value => .done (value, state)) := by
  induction process generalizing state with
  | done => rfl
  | halt => rfl
  | call operation continuation ih =>
    simp only [interpretState, interpret, bind_assoc, bind]
    congr 1
    funext reply
    exact ih reply state

/-- Interpreting the target effects commutes with the stateful translation. -/
theorem interpretState_interchange {K : Signature}
    (operations : StateOperationInterpretation I J S)
    (target : OperationInterpretation J K) (process : Process I A) (state : S) :
    (process.interpretState operations state).interpret target =
      process.interpretState (fun operation current =>
        (operations operation current).interpret target) state := by
  induction process generalizing state with
  | done => rfl
  | halt => rfl
  | call operation continuation ih =>
    simp only [interpretState, interpret_bind]
    congr 1
    funext result
    exact ih result.1 result.2

end Process
end PIR
