module

public import ZkcExamples.Structured.Generated.Presentations.Gkr
public import ZkcExamples.Structured.SumcheckHelperLaws

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
    (values point : Option (List F)) (claim : Option F) :
    invokeProtocol (GkrSourceViews.unit.plainProtocolTable F G)
      GkrSourceBodies.sourceProtocol80Signature ctx (ctx.roles 0)
      (.cons values (.cons point (.cons claim .nil))) =
      verifierProcess values point claim := by
  refine (verifier_invocation (F := F) (G := G) ctx
    (NormalForm.RosterDistinct.only ctx) (.cons values (.cons point (.cons claim .nil)))).trans ?_
  change (verifierProcess (F := F) (G := G) values point claim).bind
    (fun out => .done (.cons (out.get .here) .nil : Values (Component (assignment F G)) [.boolean])) =
      verifierProcess values point claim
  simp only [SumcheckHelperLaws.singleton_eta, PIR.Process.bind_done]

end ZkcExamples.Structured.GkrInputInvocation
