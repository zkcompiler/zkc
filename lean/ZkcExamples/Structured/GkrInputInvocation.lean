module

public import ZkcExamples.Structured.GkrInputNormalForms

@[expose] public section

/-! The single-role terminal input protocol, with exact source input/output
masks. This binding includes absent inputs and all stopped helper executions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Structured.GkrInputInvocation
open Zkc.Source Zkc.Source.Structured GkrInputNormalForms SumcheckVerifierHelpers

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem invoke (ctx : ProtocolContext)
    (values point : Option (List F)) (claim : Option F) :
    invokeProtocol (GkrSourceViews.unit.plainProtocolTable F G)
      GkrSourceBodies.sourceProtocol80Signature ctx (ctx.roles 0)
      (.cons values (.cons point (.cons claim .nil))) =
      verifierProcess values point claim := by
  have view := protocol_invoke_body_view (.silent _) (participantActions F G)
    (plainHelpers (F := F) (G := G) GkrSourceViews.unit)
    GkrSourceViews.unit.protocols GkrSourceViews.unit.protocolsLinked
    GkrSourceViews.sourceProtocol80Definition GkrSourceViews.sourceProtocol80_member
    inputBody inputBody_raw ctx (ctx.roles 0)
    (.cons values (.cons point (.cons claim .nil)))
  have masked : maskValues (ctx.roles 0) (ctx.mapScopes [[0], [0], [0]])
      (.cons values (.cons point (.cons claim .nil)) :
        Values (Component (assignment F G)) inputInputs) =
      .cons values (.cons point (.cons claim .nil)) := by
    iterate 4 unfold maskValues
    simp [ProtocolContext.mapScopes, Participant.restrict]
  change _ = (inputFn ctx (ctx.roles 0)
    (maskValues (ctx.roles 0) (ctx.mapScopes [[0], [0], [0]])
      (.cons values (.cons point (.cons claim .nil))))).bind _ at view
  rw [masked, verifier_process ctx (ctx.roles 0) rfl] at view
  refine view.trans ?_
  have outputs (results : Values (Component (assignment F G)) [.boolean]) :
      maskValues (ctx.roles 0) (ctx.mapScopes
        GkrSourceViews.sourceProtocol80Definition.outputScopes) results = results := by
    cases results with | cons value rest =>
      cases rest
      change maskValues (ctx.roles 0) (ctx.mapScopes [[0]]) (.cons value .nil) = _
      iterate 2 unfold maskValues
      simp [ProtocolContext.mapScopes, Participant.restrict]
  simp only [outputs]
  change (verifierProcess (F := F) (G := G) values point claim).bind PIR.Process.done = _
  exact PIR.Process.bind_done _

end ZkcExamples.Structured.GkrInputInvocation
