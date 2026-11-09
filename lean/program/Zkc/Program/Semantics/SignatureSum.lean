module

public import Zkc.Program.Interpretation

@[expose] public section

/-! A dependent sum of existing process signatures, with the ordinary interpretation laws. -/

set_option autoImplicit false
namespace PIR.Signature

/-- The selected operation determines its reply without a common reply envelope. -/
abbrev sum (left right : PIR.Signature) : PIR.Signature where
  Op := Sum left.Op right.Op
  Reply
    | .inl operation => left.Reply operation
    | .inr operation => right.Reply operation

variable {I J K L : PIR.Signature} {A : Type}

def injectLeft : PIR.OperationInterpretation I (sum I J) :=
  fun operation ↦ .call (.inl operation) .done

def injectRight : PIR.OperationInterpretation J (sum I J) :=
  fun operation ↦ .call (.inr operation) .done

/-- Both arms use the same target process and its stopping behavior. -/
def interpretSum (left : PIR.OperationInterpretation I K)
    (right : PIR.OperationInterpretation J K) : PIR.OperationInterpretation (sum I J) K
  | .inl operation => left operation
  | .inr operation => right operation

@[simp] theorem interpret_injectLeft (left : PIR.OperationInterpretation I K)
    (right : PIR.OperationInterpretation J K) (source : PIR.Process I A) :
    (source.interpret injectLeft).interpret (interpretSum left right) = source.interpret left := by
  rw [PIR.Process.interpret_comp]
  congr 1
  funext operation
  exact PIR.Process.bind_done (left operation)

@[simp] theorem interpret_injectRight (left : PIR.OperationInterpretation I K)
    (right : PIR.OperationInterpretation J K) (source : PIR.Process J A) :
    (source.interpret injectRight).interpret (interpretSum left right) =
      source.interpret right := by
  rw [PIR.Process.interpret_comp]
  congr 1
  funext operation
  exact PIR.Process.bind_done (right operation)

theorem interpretSum_comp (left : PIR.OperationInterpretation I K)
    (right : PIR.OperationInterpretation J K) (next : PIR.OperationInterpretation K L)
    (source : PIR.Process (sum I J) A) :
    (source.interpret (interpretSum left right)).interpret next =
      source.interpret (interpretSum (fun op ↦ (left op).interpret next)
        (fun op ↦ (right op).interpret next)) := by
  rw [PIR.Process.interpret_comp]
  congr 1
  funext operation
  cases operation <;> rfl

end PIR.Signature
