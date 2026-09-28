import Zkc.Semantics.MonadExecution
import VCVio.OracleComp.SimSemantics.SimulateQ

/-! Structural correspondence with VCVio, preserving typed replies and terminal
outcomes. Handler simulation retains stopped state and preceding events. -/

set_option autoImplicit false

namespace ZkcArkLib.Mathematical

def signature (I : PIR.Signature) : OracleSpec I.Op := I.Reply

def encode {I : PIR.Signature} {A : Type} :
    PIR.Proc I A → OracleComp (signature I) (PIR.Outcome A)
  | .done a => .pure (.returned a)
  | .halt why => .pure (.stopped why)
  | .call op next => .liftBind op (fun reply => encode (next reply))

def decode {I : PIR.Signature} {A : Type} :
    OracleComp (signature I) (PIR.Outcome A) → PIR.Proc I A
  | .pure (.returned a) => .done a
  | .pure (.stopped why) => .halt why
  | .liftBind op next => .call op (fun reply => decode (next reply))

theorem decode_encode {I : PIR.Signature} {A : Type} (p : PIR.Proc I A) :
    decode (encode p) = p := by
  induction p with
  | done a => rfl
  | halt why => rfl
  | call op next ih =>
      change PIR.Proc.call op (fun reply => decode (encode (next reply))) = _
      exact congrArg (PIR.Proc.call op) (funext ih)

theorem encode_decode {I : PIR.Signature} {A : Type}
    (p : OracleComp (signature I) (PIR.Outcome A)) : encode (decode p) = p := by
  induction p using OracleComp.inductionOn with
  | pure result => cases result <;> rfl
  | query_bind op next ih =>
      change PFunctor.FreeM.liftBind op
        (fun reply => encode (decode (next reply))) = _
      exact congrArg (PFunctor.FreeM.liftBind (P := (signature I).toPFunctor) op) (funext ih)

def bindOutcome {I : PIR.Signature} {A B : Type}
    (p : OracleComp (signature I) (PIR.Outcome A))
    (next : A → OracleComp (signature I) (PIR.Outcome B)) :
    OracleComp (signature I) (PIR.Outcome B) :=
  p >>= fun result => match result with
    | .returned a => next a
    | .stopped why => pure (.stopped why)

theorem encode_bind {I : PIR.Signature} {A B : Type}
    (p : PIR.Proc I A) (next : A → PIR.Proc I B) :
    encode (p.bind next) = bindOutcome (encode p) (fun a => encode (next a)) := by
  induction p with
  | done a => rfl
  | halt why => rfl
  | call op rest ih =>
      change PFunctor.FreeM.liftBind (P := (signature I).toPFunctor) op
        (fun reply : I.Reply op => encode ((rest reply).bind next)) =
        PFunctor.FreeM.liftBind (P := (signature I).toPFunctor) op
        (fun reply : I.Reply op => bindOutcome (encode (rest reply)) (fun a => encode (next a)))
      exact congrArg (PFunctor.FreeM.liftBind (P := (signature I).toPFunctor) op) (funext ih)

/-- State and events live outside the stopping outcome, so failures retain both. -/
abbrev ExecutionM (S E A : Type) := S → PIR.Execution S E A

instance {S E : Type} : Monad (ExecutionM S E) where
  pure value state := ⟨.returned value, state, []⟩
  bind first next state := (first state).follow next

instance {S E : Type} : LawfulMonad (ExecutionM S E) := LawfulMonad.mk' _
  (by
    intro A first
    funext state
    change (first state).follow (fun value state => ⟨.returned value, state, []⟩) = first state
    cases first state with
    | mk outcome state events =>
        cases outcome <;> simp [PIR.Execution.follow])
  (by
    intro A B value next
    funext state
    change PIR.Execution.follow ⟨.returned value, state, []⟩ next = next value state
    simp [PIR.Execution.follow])
  (by
    intro A B C first next last
    funext state
    exact PIR.follow_assoc _ _ _)

def flatten {S E A : Type} (execution : PIR.Execution S E (PIR.Outcome A)) :
    PIR.Execution S E A :=
  ⟨match execution.outcome with
    | .returned outcome => outcome
    | .stopped reason => .stopped reason, execution.state, execution.events⟩

/-- Uses VCVio's actual simulator, with a stopping state-and-event implementation.
An Empty reply (e.g. a source stop) is legal because its handler may stop. It
cannot be supplied by a total answer function or an ordinary uniform sampler. -/
def simulate {I : PIR.Signature} {S E A : Type} (handler : PIR.Handler I S E)
    (program : OracleComp (signature I) (PIR.Outcome A)) (state : S) :
    PIR.Execution S E A :=
  flatten ((simulateQ (r := ExecutionM S E) handler program) state)

theorem simulate_encode {I : PIR.Signature} {S E A : Type}
    (handler : PIR.Handler I S E) (program : PIR.Proc I A) (state : S) :
    simulate handler (encode program) state = program.run handler state := by
  induction program generalizing state with
  | done value => rfl
  | halt reason => rfl
  | call op next ih =>
      change flatten ((handler op state).follow
        (fun reply state => simulateQ (r := ExecutionM S E) handler (encode (next reply)) state)) =
          (handler op state).follow (fun reply state => (next reply).run handler state)
      cases h : handler op state with
      | mk outcome state events =>
          cases outcome with
          | stopped reason => rfl
          | returned reply =>
              have same := ih reply state
              unfold simulate at same
              cases hs : simulateQ (r := ExecutionM S E) handler (encode (next reply)) state with
              | mk result final tail =>
                  rw [hs] at same
                  cases result <;> simp only [flatten] at same <;>
                    simp [PIR.Execution.follow, flatten, ← same, hs]

end ZkcArkLib.Mathematical
