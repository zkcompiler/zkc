module

public import Zkc.Semantics.StateInterpretation

@[expose] public section

/-! Operation support through every typed continuation of the existing process
semantics. This is a property of an effect tree, independent of cryptographic
interpretation, particular executions or chosen replies. -/
set_option autoImplicit false
namespace PIR

variable {I J : PIR.Signature} {A B S : Type}

/-- Every operation in the tree satisfies the predicate, on every typed reply. -/
def OperationSupport (allowed : I.Op → Prop) : PIR.Process I A → Prop
  | .done _ | .halt _ => True
  | .call operation next => allowed operation ∧ ∀ reply, OperationSupport allowed (next reply)

namespace OperationSupport
variable {allowed : I.Op → Prop} {other : J.Op → Prop}

theorem bind {source : PIR.Process I A} (supported : OperationSupport allowed source)
    (next : A → PIR.Process I B) (suffix : ∀ value, OperationSupport allowed (next value)) :
    OperationSupport allowed (source.bind next) := by
  induction source with
  | done value => exact suffix value
  | halt => trivial
  | call operation next ih => exact ⟨supported.1, fun reply => ih reply (supported.2 reply)⟩

theorem mono {source : PIR.Process I A} (supported : OperationSupport allowed source)
    {stronger : I.Op → Prop} (law : ∀ operation, allowed operation → stronger operation) :
    OperationSupport stronger source := by
  induction source with
  | done => trivial
  | halt => trivial
  | call operation next ih => exact ⟨law operation supported.1, fun reply => ih reply (supported.2 reply)⟩

theorem interpret (operations : PIR.OperationInterpretation I J)
    (laws : ∀ operation, allowed operation → OperationSupport other (operations operation))
    {source : PIR.Process I A} (supported : OperationSupport allowed source) :
    OperationSupport other (source.interpret operations) := by
  induction source with
  | done => trivial
  | halt => trivial
  | call operation next ih =>
    exact (laws operation supported.1).bind _ (fun reply => ih reply (supported.2 reply))

theorem interpretState (operations : PIR.StateOperationInterpretation I J S)
    (laws : ∀ operation state, allowed operation → OperationSupport other (operations operation state))
    {source : PIR.Process I A} (supported : OperationSupport allowed source) (state : S) :
    OperationSupport other (source.interpretState operations state) := by
  induction source generalizing state with
  | done => trivial
  | halt => trivial
  | call operation next ih =>
    exact (laws operation state supported.1).bind _ (fun result => ih result.1 (supported.2 result.1) result.2)

theorem closed (allowed : J.Op → Prop) (source : PIR.Process I A)
    (operations : PIR.OperationInterpretation I J) (empty : I.Op → False) :
    OperationSupport allowed (source.interpret operations) := by
  induction source with
  | done => trivial
  | halt => trivial
  | call operation => exact False.elim (empty operation)

end OperationSupport
end PIR
