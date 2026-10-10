import Zkc.Protocols.Sumcheck.LocalProver.Code

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Protocols.Sumcheck.LocalProver

variable {F : Type} [Ring F] [DecidableEq F]

def evalFallback (fallback : Nat → F) (st : State F) (e : Expr) : F :=
  e.eval (fun | .inl i => st.inputs[i]?.getD (fallback i) | .inr i => st.regs i)

theorem eval_no_default (fallback : Nat → F) (st : State F) (e : Expr)
    (bound : ∀ i ∈ exprInputs e, i < st.inputs.length) :
    evalFallback fallback st e = eval st e := by
  apply Zkc.Source.Expressions.eval_agreement
  intro a ha
  cases a with
  | inl i =>
    have hi : i ∈ exprInputs e := List.mem_filterMap.mpr ⟨.inl i, ha, rfl⟩
    have hb := bound i hi
    simp [List.getElem?_eq_getElem hb]
  | inr i => rfl

/-- Operational execution preserves the captured vector even through local writes/coins. -/
theorem reaches_inputs (p : Code) (st : State F) (out : Cut F) (h : Reaches p st out) :
    Cut.inputs out = st.inputs := by
  induction h <;> simp_all [Cut.inputs,write,Zkc.Protocols.Sumcheck.LocalProver.coin,branch,boundary]


end Zkc.Protocols.Sumcheck.LocalProver
