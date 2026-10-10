import Zkc.Semantics.Interpretation
import Zkc.Semantics.Boundary

/-! Phase and uniform call-bound transport across operation interpretation.

An interpretation can expand one logical operation into several lower operations.
The phase relation records its legal entry and every returning exit. It does not
assert endpoint locality, resource independence or cryptographic security.
-/

set_option autoImplicit false

namespace PIR

variable {I J : Signature} {A : Type}

/-- The lower protocol must implement each enabled source operation, including
all returning phases. Stopping implementations have no returning obligation. -/
structure InterpretationAdmission (source : Interaction I) (target : Interaction J)
    (operations : OperationInterpretation I J) where
  phases : source.Phase → target.Phase → Prop
  operation : ∀ phase op, source.enabled phase op → ∀ lowerPhase,
    phases phase lowerPhase →
      Conforms target (operations op) lowerPhase ∧
      Boundary.Returns target
        (fun reply finalPhase => phases (source.advance phase op reply) finalPhase)
        (operations op) lowerPhase

namespace InterpretationAdmission

variable {source : Interaction I} {target : Interaction J}
  {operations : OperationInterpretation I J}

/-- Transport legality and the actual return relation together. A legal entry
alone would not justify the caller's continuation after an expanded operation. -/
theorem transport (admission : InterpretationAdmission source target operations)
    (program : Proc I A) (post : A → source.Phase → Prop)
    (phase : source.Phase) (lowerPhase : target.Phase)
    (formed : Conforms source program phase)
    (exits : Boundary.Returns source post program phase)
    (initial : admission.phases phase lowerPhase) :
    Conforms target (program.interpret operations) lowerPhase ∧
    Boundary.Returns target
      (fun value finalPhase => ∃ upperPhase,
        post value upperPhase ∧ admission.phases upperPhase finalPhase)
      (program.interpret operations) lowerPhase := by
  induction program generalizing phase lowerPhase with
  | done value => exact ⟨trivial, phase, exits, initial⟩
  | halt why => exact ⟨trivial, trivial⟩
  | call op next ih =>
    obtain ⟨body, returns⟩ := admission.operation phase op formed.1 lowerPhase initial
    exact ⟨Boundary.conforms_bind target _ _ _ lowerPhase body returns
      (fun reply finalPhase related =>
        (ih reply _ finalPhase (formed.2 reply) (exits reply) related).1),
      Boundary.returns_bind target _ _ _ _ lowerPhase returns
        (fun reply finalPhase related =>
          (ih reply _ finalPhase (formed.2 reply) (exits reply) related).2)⟩

end InterpretationAdmission

namespace Proc

/-- A uniform expansion bound scales the logical call budget. This counts
interface calls, not field operations, memory traffic or native running time. -/
theorem within_interpret (operations : OperationInterpretation I J)
    (operationBound : Nat) (bounded : ∀ op, Within operationBound (operations op))
    (program : Proc I A) (sourceBound : Nat) (source : Within sourceBound program) :
    Within (sourceBound * operationBound) (program.interpret operations) := by
  induction program generalizing sourceBound with
  | done => cases sourceBound * operationBound <;> trivial
  | halt => cases sourceBound * operationBound <;> trivial
  | call op next ih =>
    cases sourceBound with
    | zero => exact False.elim source
    | succ n =>
      simpa only [Proc.interpret, Nat.succ_mul, Nat.add_comm] using
        Boundary.within_bind (operations op) (fun reply => (next reply).interpret operations)
          operationBound (n * operationBound) (bounded op)
          (fun reply => ih reply n (source reply))

end Proc
end PIR
