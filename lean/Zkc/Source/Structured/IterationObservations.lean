module

public import Zkc.Source.Structured.Repeat

@[expose] public section

/-! Iteration boundaries are explicit internal observations. They carry the
qualified source repeat site and the actual reached index. A stopped body has
no closing observation: no continuation executes after a stop. Erasing both
observations recovers the original process, including every stopped prefix. -/
set_option autoImplicit false
namespace Zkc.Source.Structured

inductive IterationObservations (I : PIR.Signature) where
  | silent
  | observed (enter leave : String → Nat → PIR.Process I Unit)

namespace IterationObservations
variable {I J : PIR.Signature} {A : Type}

def enter : IterationObservations I → String → Nat → PIR.Process I Unit
  | .silent, _, _ => .done ()
  | .observed before _, site, index => before site index

def leave : IterationObservations I → String → Nat → PIR.Process I Unit
  | .silent, _, _ => .done ()
  | .observed _ after, site, index => after site index

def within (observations : IterationObservations I) (site : String) (index : Nat)
    (body : PIR.Process I A) : PIR.Process I A :=
  match observations with
  | .silent => body
  | .observed before after =>
    (before site index).bind fun _ => body.bind fun result =>
      (after site index).bind fun _ => .done result

@[simp] theorem silent_within (site : String) (index : Nat) (body : PIR.Process I A) :
    (silent (I := I)).within site index body = body := rfl

theorem within_eq (observations : IterationObservations I) (site : String) (index : Nat)
    (body : PIR.Process I A) :
    observations.within site index body =
      (observations.enter site index).bind fun _ => body.bind fun result =>
        (observations.leave site index).bind fun _ => .done result := by
  cases observations <;> simp [within, enter, leave, PIR.Process.bind, PIR.Process.bind_done]

structure Interprets (operations : PIR.OperationInterpretation I J)
    (left : IterationObservations I) (right : IterationObservations J) : Prop where
  enter : ∀ site index, (left.enter site index).interpret operations = right.enter site index
  leave : ∀ site index, (left.leave site index).interpret operations = right.leave site index

theorem silent_interpret (operations : PIR.OperationInterpretation I J) :
    Interprets operations silent silent := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem within_interpret (operations : PIR.OperationInterpretation I J)
    {left : IterationObservations I} {right : IterationObservations J}
    (same : Interprets operations left right) (site : String) (index : Nat)
    (body : PIR.Process I A) :
    (left.within site index body).interpret operations =
      right.within site index (body.interpret operations) := by
  simp only [within_eq, PIR.Process.interpret_bind, same.enter, same.leave, PIR.Process.interpret]

end IterationObservations
end Zkc.Source.Structured
