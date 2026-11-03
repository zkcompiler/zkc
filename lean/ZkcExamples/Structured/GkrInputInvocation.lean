module

public import ZkcExamples.Structured.Generated.Presentations.Gkr
public import Zkc.Protocols.Sumcheck.Source.HelperLaws

@[expose] public section

/-! The single-role terminal input protocol, with exact source input/output
masks. This binding includes absent inputs and all stopped helper executions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Structured.GkrInputInvocation
open Zkc.Source Zkc.Source.Structured Generated.Presentations.Gkr.Input

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem invoke (ctx : ProtocolContext)
    (values : Option (List F)) (custody : Option CustodyToken)
    (point : Option (List F)) (claim : Option F) :
    invokeProtocol (GkrSourceViews.unit.plainProtocolTable F G)
      GkrSourceBodies.inputSignature ctx (ctx.roles 0)
      (.cons values (.cons custody (.cons point (.cons claim .nil)))) =
      verifierProcess values custody point claim := by
  refine (verifier_invocation (F := F) (G := G) ctx
    (NormalForm.RosterDistinct.only ctx) (.cons values (.cons custody (.cons point (.cons claim .nil))))).trans ?_
  change (verifierProcess (F := F) (G := G) values custody point claim).bind
    (fun out => .done (.cons (out.get .here) .nil : Values (Component (assignment F G)) [.boolean])) =
      verifierProcess values custody point claim
  simp only [SumcheckHelperLaws.singleton_eta, PIR.Process.bind_done]

/-- An absent owned claim is incomplete even when its ordinary fields are
present. The local custody coordinate is not inferred from those fields. -/
theorem missing_custody (ctx : ProtocolContext) (values point : List F) (claim : F) :
    invokeProtocol (GkrSourceViews.unit.plainProtocolTable F G)
      GkrSourceBodies.inputSignature ctx (ctx.roles 0)
      (.cons (some values) (.cons none (.cons (some point) (.cons (some claim) .nil)))) =
      .halt .incomplete := by
  rw [invoke]
  rfl

end ZkcExamples.Structured.GkrInputInvocation
