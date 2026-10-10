import Zkc.Semantics.Boundary

set_option autoImplicit false

namespace PIR

/-- An identified frontend interpretation. These functions have an actual
    definition for each frontend; the record does not inspect host code. -/
structure Frontend (I : Signature) (Role Result : Type) where
  Source : Type
  Binding : Type
  inputs : Source → Binding → Role → Prop
  elaborate : Source → Binding → Role → Option (Proc I Result)

structure EndpointContract {I : Signature} (P : Interaction I) (Result : Type) where
  initialPhase : P.Phase
  publicBound : Nat
  returned : Result → P.Phase → Prop

variable {I : Signature} {A : Type} {P : Interaction I}

/-- Every field concerns the same source, binding, actor and elaborated body.
    Public parameters are fixed by the chosen instance of F, P and C. -/
structure Admitted (F : Frontend I P.Role A) (C : EndpointContract P A)
    (src : F.Source) (binding : F.Binding) (actor : P.Role) (body : Proc I A) : Prop where
  actual : F.elaborate src binding actor = some body
  inputs : F.inputs src binding actor
  conforms : Conforms P body C.initialPhase
  bounded : Within C.publicBound body
  returned : Boundary.Returns P C.returned body C.initialPhase

theorem admitted_body_unique (F : Frontend I P.Role A) (C : EndpointContract P A)
    (src : F.Source) (binding : F.Binding) (actor : P.Role) (left right : Proc I A)
    (hl : Admitted F C src binding actor left) (hr : Admitted F C src binding actor right) :
    left = right := Option.some.inj (hl.actual.symm.trans hr.actual)

/-- The accepted body used by the consumer is the same body used by a complete
    execution relation. This does not prove the handler relation itself. -/
theorem admitted_execution_related {S T E G O : Type}
    (F : Frontend I P.Role A) (C : EndpointContract P A)
    (src : F.Source) (binding : F.Binding) (actor : P.Role) (left right : Proc I A)
    (hl : Admitted F C src binding actor left) (hr : Admitted F C src binding actor right)
    (R : S → T → Prop) (viewL : E → List O) (viewR : G → List O)
    (h : Handler I S E) (g : Handler I T G)
    (law : HandlerRelated R viewL viewR h g) (s : S) (t : T) (initial : R s t) :
    Related R viewL viewR (left.run h s) (right.run g t) := by
  have same := admitted_body_unique F C src binding actor left right hl hr
  subst right
  exact run_related R viewL viewR h g law left s t initial

end PIR
