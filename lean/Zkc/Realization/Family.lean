import Zkc.Source.Family
import Zkc.Realization.Simulation

/-! Relating actual ingress and the members it selects. Input configuration
types and representations may differ; neither member admission nor a matching
configuration name establishes the ingress correspondence used here. -/

set_option autoImplicit false
namespace Zkc.Realization.Family
open PIR
variable {I J : Signature} {C D Raw OtherRaw S T E F O A B : Type}
  {Inputs : C → Type} {OtherInputs : D → Type}

theorem run_relates
    (ingress : Raw → S → Execution S E (Sigma Inputs))
    (otherIngress : OtherRaw → T → Execution T F (Sigma OtherInputs))
    (member : (c : C) → Inputs c → Proc I A)
    (other : (d : D) → OtherInputs d → Proc J B)
    (left : Handler I S E) (right : Handler J T F)
    (states : S → T → Prop)
    (inputs : Sigma Inputs → S → Sigma OtherInputs → T → Prop)
    (results : A → S → B → T → Prop) (viewLeft : E → List O) (viewRight : F → List O)
    (raw : Raw) (s : S) (otherRaw : OtherRaw) (t : T)
    (selected : Execution.Relates states inputs viewLeft viewRight
      (ingress raw s) (otherIngress otherRaw t))
    (members : ∀ bound residual otherBound otherResidual,
      states residual otherResidual → inputs bound residual otherBound otherResidual →
      Execution.Relates states results viewLeft viewRight
        ((member bound.1 bound.2).run left residual)
        ((other otherBound.1 otherBound.2).run right otherResidual)) :
    Execution.Relates states results viewLeft viewRight
      (Zkc.Source.Family.run ingress member left raw s)
      (Zkc.Source.Family.run otherIngress other right otherRaw t) :=
  Execution.Relates.follow states inputs results viewLeft viewRight _ _ selected _ _ members

end Zkc.Realization.Family
