import Zkc.Source.Program
import Zkc.Semantics.Interpretation

/-! Reinterpret structured source operations through a lower-level signature.
Values and source structure stay fixed; each operation can expand into a process.
-/

set_option autoImplicit false

namespace Zkc.Source

variable {language : Language} {I J : PIR.Signature}

abbrev Interpretation.translate (meaning : Interpretation language I)
    (operations : PIR.OperationInterpretation I J) : Interpretation language J where
  Value := meaning.Value
  condition := meaning.condition
  operation op args := (meaning.operation op args).interpret operations

theorem interpret_repeat {A : Type} (operations : PIR.OperationInterpretation I J)
    (count : Nat) (body : A → PIR.Proc I A) (value : A) :
    (PIR.repeatN count body value).interpret operations =
      PIR.repeatN count (fun a => (body a).interpret operations) value := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih => simp [PIR.repeatN, PIR.Proc.interpret_bind, ih]

theorem Program.denote_translate (meaning : Interpretation language I)
    (operations : PIR.OperationInterpretation I J) {Γ ty}
    (source : Program language Γ ty) (env : Environment meaning.Value Γ) :
    source.denote (meaning.translate operations) env =
      (source.denote meaning env).interpret operations := by
  induction source with
  | ret value => rfl
  | stop why => rfl
  | letOp op args next ih =>
    simp only [denote, Interpretation.translate, PIR.Proc.interpret_bind]
    congr 1
    funext value
    exact ih (env.push value)
  | branch condition yes no ihYes ihNo =>
    simp only [denote]
    change (if meaning.condition (env condition) then _ else _) = _
    split <;> simp_all
  | iterate count initial body next ihBody ihNext =>
    simp only [denote, PIR.Proc.interpret_bind, interpret_repeat]
    have bodySame :
        (fun value => body.denote (meaning.translate operations) (env.push value)) =
        (fun value => (body.denote meaning (env.push value)).interpret operations) := by
      funext value
      exact ihBody (env.push value)
    rw [bodySame]
    congr 1
    funext value
    exact ihNext (env.push value)

end Zkc.Source
