import ZkcSecurity.Realizations.Gkr.HonestHelpersSource
import ZkcSecurity.Realizations.Gkr.HonestRound
import ZkcSecurity.Realizations.Gkr.HonestPackets
import ZkcSecurity.Examples.Components.GkrFiniteCircuit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace TestsSecurity.GkrHonestHelpers
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceLaws
open ZkcExamples.Structured.PrimitiveLibrary
open Zkc.Polynomial.Multilinear Zkc.Protocols.AlgebraicRounds
open ZkcSecurity.Examples.Components
open ZkcSecurity.Realizations.Gkr

def upperAdd : List ℚ := [0, 0, 0, 0, 0, 0, 0, 1]
def upperMul : List ℚ := [0, 1, 0, 0, 0, 0, 0, 0]

/-- Two mixed add/multiply layers: the independent evaluator gives
(3,5) -> (8,15) -> (120,30). This does not assert helper34 correctness. -/
theorem mixed_circuit :
    Zkc.Protocols.Gkr.values (GkrFiniteCircuit.addWiring (F := ℚ))
      GkrFiniteCircuit.mulWiring GkrFiniteCircuit.inputTable 2 0 =
        (fun bits => if bits 0 then 30 else 120) :=
  GkrFiniteCircuit.outputs

/-- Actual helper36 at every field point of the mixed circuit's upper layer.
The lower wire values here are explicit test data. -/
theorem upper_layout (rho : ℚ) :
    invoke (helpers (G := ℚ)) GkrSourceBodies.helper36Helper
      (.cons upperAdd (.cons upperMul (.cons [rho] (.cons [8, 15] (.cons 1 .nil))))) =
      .done (GkrCallerRealization.raw rho).values := by
  rw [HonestHelpers.layout_equation upperAdd upperMul [8, 15] [rho] 1 (by decide)
    (by norm_num [HasShape, upperAdd]) (by norm_num [HasShape, upperMul])
    (by norm_num [upperAdd, indexLimit]) (by norm_num [upperMul, indexLimit])
    (by norm_num [indexLimit]) (by norm_num [indexLimit])]
  simp [upperAdd, upperMul, restrictPrefixValues, restrictValues,
    GkrCallerRealization.raw, GkrRoundsRealization.RawState.values, sub_eq_add_neg]

theorem read_output :
    invoke (helpers (G := ℚ)) GkrSourceBodies.helper57Helper
      (.cons ([120, 30] : List ℚ) (.cons 1 .nil)) = .done (.cons 30 .nil) := by
  simpa using HonestHelpers.element_equation (G := ℚ) ([120, 30] : List ℚ) 1
    (by norm_num [indexLimit]) (by norm_num [indexLimit])

theorem changed_readback :
    invoke (helpers (G := ℚ)) GkrSourceBodies.helper57Helper
      (.cons ([120, 30] : List ℚ) (.cons 1 .nil)) ≠ .done (.cons 31 .nil) := by
  rw [read_output]
  intro wrong
  have value := congrArg (fun xs => xs.get .here) (PIR.Process.done.inj wrong)
  norm_num [Values.get] at value

theorem read_past_end :
    invoke (helpers (G := ℚ)) GkrSourceBodies.helper57Helper
      (.cons ([120, 30] : List ℚ) (.cons 2 .nil)) = .done (.cons 0 .nil) := by
  simpa using HonestHelpers.element_equation (G := ℚ) ([120, 30] : List ℚ) 2
    (by norm_num [indexLimit]) (by norm_num [indexLimit])

theorem line_packet (ctx : ProtocolContext) :
    GkrSourceCallbacks.proverCoefficientProcess (F := ℚ) (G := ℚ) ctx 0 (some [8, 7]) =
      .call (.send (ty := .field scalarDomain) (GkrSourceCallbacks.lineCoefficientSite ctx)
        (ctx.roles 1) 7) fun _ => .done () := by
  simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] using
    HonestPackets.line_coefficient (G := ℚ) ctx ([8, 7] : List ℚ) 0
    (by norm_num [indexLimit]) (by norm_num [indexLimit])

/-- A test delivery script for the existing runner; it retains all actions. -/
def handler : PIR.Handler (participantInterface ℚ ℚ) (List ℚ)
    (participantInterface ℚ ℚ).Op
  | action@(.send ..), state => ⟨.returned (), state, [action]⟩
  | action@(.query ..), state => ⟨.returned (0 : ℚ), state, [action]⟩
  | action@(.receive (.field _) _ _), state =>
    match state with
    | value :: rest => ⟨.returned value, rest, [action]⟩
    | [] => ⟨.stopped .refused, [], [action]⟩
  | action@(.receive _ _ _), state => ⟨.stopped .refused, state, [action]⟩

def events (ctx : ProtocolContext) : List (participantInterface ℚ ℚ).Op :=
  [.send (ty := .field scalarDomain)
      (GkrRoundsNormalForms.round0Site ctx) (ctx.roles 1) 120,
   .send (ty := .field scalarDomain)
      (GkrRoundsNormalForms.round1Site ctx) (ctx.roles 1) (-15),
   .send (ty := .field scalarDomain)
      (GkrRoundsNormalForms.round2Site ctx) (ctx.roles 1) (-105),
   .receive (.field scalarDomain)
      (GkrRoundsNormalForms.deliverySite ctx) (ctx.roles 1)]

theorem first_message : GkrRoundsReference.message (GkrCallerRealization.reference (0 : ℚ)) =
    ⟨120, -15, -105⟩ := by
  norm_num [GkrRoundsReference.message, GkrRoundsReference.pointMessage,
    GkrCallerRealization.reference, GkrCallerRealization.addTable, GkrCallerRealization.mulTable,
    GkrCallerRealization.below, GkrRoundsLayout.state, GkrRoundsLayout.replicate,
    GkrRoundsLayout.tile, GkrRoundsLayout.leading, GkrRoundsLayout.trailing,
    booleanSum, half, Gate.message, Gate.value, Gate.quadratic]

/-- Actual source round, exact suffix and all three ordered payloads. The
existing challenge prefix is retained in the returned point. -/
theorem round_run (ctx : ProtocolContext) (point suffix : List ℚ) :
    (GkrRoundsNormalForms.proverProcess (G := ℚ) ctx
      (some (GkrCallerRealization.raw 0).add) (some (GkrCallerRealization.raw 0).mul)
      (some (GkrCallerRealization.raw 0).left) (some (GkrCallerRealization.raw 0).right)
      (some point)).run handler (0 :: suffix) =
      ⟨.returned (HonestRound.result (GkrCallerRealization.raw 0) point 0), suffix, events ctx⟩ := by
  rw [HonestRound.run ctx _ (GkrCallerRealization.reference 0)
    (GkrCallerRealization.represented 0).1 (by norm_num [indexLimit]) point handler (0 :: suffix),
    first_message]
  rfl

/-- Exhausting the challenge script is failure, after the same emitted
coefficient packet. It cannot be counted as a successful producer round. -/
theorem missing_delivery (ctx : ProtocolContext) (point : List ℚ) :
    (GkrRoundsNormalForms.proverProcess (G := ℚ) ctx
      (some (GkrCallerRealization.raw 0).add) (some (GkrCallerRealization.raw 0).mul)
      (some (GkrCallerRealization.raw 0).left) (some (GkrCallerRealization.raw 0).right)
      (some point)).run handler [] = ⟨.stopped .refused, [], events ctx⟩ := by
  rw [HonestRound.run ctx _ (GkrCallerRealization.reference 0)
    (GkrCallerRealization.represented 0).1 (by norm_num [indexLimit]) point handler [], first_message]
  rfl

theorem changed_message :
    invoke (Zkc.Source.Structured.plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).closed
      GkrSourceBodies.helper41Helper (GkrCallerRealization.raw 0).values ≠
      .done (.cons 121 (.cons (-15) (.cons (-105) .nil))) := by
  rw [HonestHelpers.round_coefficients _ (GkrCallerRealization.reference 0)
    (GkrCallerRealization.represented 0).1 (by norm_num [indexLimit]), first_message]
  intro wrong
  have value := congrArg (fun xs => xs.get .here) (PIR.Process.done.inj wrong)
  norm_num [Values.get] at value

/-- The same source round consumer rejects a changed constant, retaining
the actual unread suffix and the three receive observations. -/
theorem changed_message_rejected (ctx : ProtocolContext) (point suffix : List ℚ) :
    (GkrRoundsNormalForms.verifierProcess (G := ℚ) ctx (some 83) (some point) (some 120)).run
      handler (121 :: (-15) :: (-105) :: suffix) =
      ⟨.stopped .reject, suffix,
        [.receive (.field scalarDomain) (GkrRoundsNormalForms.round0Site ctx) (ctx.roles 0),
         .receive (.field scalarDomain) (GkrRoundsNormalForms.round1Site ctx) (ctx.roles 0),
         .receive (.field scalarDomain) (GkrRoundsNormalForms.round2Site ctx) (ctx.roles 0)]⟩ := by
  norm_num [GkrRoundsNormalForms.verifierProcess, PIR.Process.run, handler, PIR.Execution.follow]

theorem malformed_round :
    invoke (Zkc.Source.Structured.plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).closed
      GkrSourceBodies.helper41Helper
      (.cons [] (.cons [0, 1] (.cons [1, 1] (.cons [1, 1] .nil)))) = .halt .refused := by
  rw [HonestHelpers.round_message_table, GkrRoundsProcesses.round_equation]
  rfl

#print axioms HonestHelpers.layout_encodes
#print axioms HonestHelpers.round_coefficients
#print axioms HonestHelpers.round_restriction
#print axioms HonestHelpers.element_equation
#print axioms HonestHelpers.element_after_equation
#print axioms HonestHelpers.layout_plain
#print axioms HonestRound.process
#print axioms HonestRound.run
#print axioms HonestPackets.output_point
#print axioms HonestPackets.line_coefficient
#print axioms round_run
#print axioms changed_message
#print axioms changed_readback
#print axioms changed_message_rejected
#print axioms malformed_round

end TestsSecurity.GkrHonestHelpers
