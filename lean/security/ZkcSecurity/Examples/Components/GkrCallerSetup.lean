module

public import ZkcSecurity.Examples.Components.GkrCallerSource
public import Zkc.Source.TypedABI

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace ZkcSecurity.Examples.Components.GkrCallerSetup
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsCaller
open GkrCallerRealization GkrCallerSource

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The generated prefix of the actual producer layer callback, ending at the
left call's full arguments. No source AST or tuple positions are authored here.
The absent verifier claim/service match role 0's actual private scopes. -/
def setup (ctx : ProtocolContext) (rho : F) :=
  (protocol2Role0Callback1Setup (F := F) (G := G) ctx (some 0) (some [rho]) none none
    (some inputs) (some stackedAdd) (some stackedMul) (some 2) (some 1) (some 1) none).bind
      (fun frame => .done (protocol2Role0Callback1SetupInput frame))

/-- Source-computed four factors at the actual first-left call. These are
producer construction facts, never assumptions about adversarial messages. -/
theorem setup_input (ctx : ProtocolContext) (rho : F) :
    setup (G := G) ctx rho = .done
      (.cons (some (raw rho).add) (.cons (some (raw rho).mul)
        (.cons (some (raw rho).left) (.cons (some (raw rho).right)
          (.cons none (.cons none (.cons (some 1) (.cons none .nil)))))))) := by
  unfold setup protocol2Role0Callback1Setup
  conv_lhs =>
    arg 1; arg 1
    erw [owned_equation (ctx.roles 0) valuesBelowHelper _ _ (values_below (F := F) (G := G))]
  simp only [PIR.Process.bind]
  conv_lhs =>
    arg 1; arg 1
    erw [owned_equation (ctx.roles 0) selectBlockHelper _ _ (select_add (F := F) (G := G))]
  simp only [PIR.Process.bind]
  conv_lhs =>
    arg 1; arg 1
    erw [owned_equation (ctx.roles 0) selectBlockHelper _ _ (select_mul (F := F) (G := G))]
  simp only [PIR.Process.bind]
  conv_lhs =>
    arg 1; arg 1
    change Participant.owned (ctx.roles 0) (ctx.roles 0)
      (invoke (helpers (F := F) (G := G)
        ZkcExamples.Structured.Generated.Bindings.GkrRounds.payload).toOn.closed layerGatesHelper)
      (Values.present (.cons addBlock (.cons mulBlock (.cons [rho] (.cons [8, 15] (.cons 1 .nil))))))
    rw [owned_equation (F := F) (G := G) (ctx.roles 0) layerGatesHelper _ _
      (layer_gates (G := G) rho)]
  kernel_rfl

/-- Exact source occurrence identity agrees with the verifier's selected site. -/
theorem same_context (ctx : ProtocolContext) :
    protocol2Role0Callback1SetupContext ctx = firstLeftContext ctx := by
  rfl

end ZkcSecurity.Examples.Components.GkrCallerSetup
