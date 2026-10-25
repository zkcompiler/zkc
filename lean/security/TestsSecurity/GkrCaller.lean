import ZkcSecurity.Examples.Components.GkrCallerSetup
import ZkcSecurity.Examples.Components.GkrCallerResidual
import Zkc.Source.Structured.ReplyScript

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 800000

namespace TestsSecurity.GkrCaller
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings Zkc.Source.Structured.NormalForm
open ZkcSecurity.Examples.Components
open GkrCallerRealization GkrCallerBinding
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsCaller

noncomputable section

/-- The two output controls differ at every possible output point. -/
example (rho : ℚ) : honestClaim rho = GkrRoundsReference.total (reference rho) :=
  honest_control rho
example (rho : ℚ) : wrongClaim rho ≠ GkrRoundsReference.total (reference rho) :=
  wrong_control rho

/-- The source setup and the actual call have the same selected occurrence. -/
example (ctx : ProtocolContext) (rho : ℚ) :
    GkrCallerSetup.setup (G := ℚ) ctx rho = .done
      (.cons (some (raw rho).add) (.cons (some (raw rho).mul)
        (.cons (some (raw rho).left) (.cons (some (raw rho).right)
          (.cons none (.cons (some 1) (.cons none .nil))))))) :=
  GkrCallerSetup.setup_input ctx rho

example : (firstLeftContext {}).applicationPrefix ≠
    (({} : ProtocolContext).enter "label_7269676874" [0, 1]).applicationPrefix := by decide +kernel

/-- Query and delivery stops retain the exact emitted prefix of the full caller. -/
def caller := invokeProtocol
  (ZkcExamples.Structured.Generated.Bindings.GkrRounds.payload.plainProtocolTable ℚ ℚ)
  ZkcExamples.Structured.Generated.Bindings.GkrRounds.definition1.signature {} 1
  (callerInput wrongOutputs 83)

def stopQuery : PIR.Handler (participantInterface ℚ ℚ) Unit (participantInterface ℚ ℚ).Op
  | action, state => ⟨.stopped .refused, state, [action]⟩

def stopDelivery : PIR.Handler (participantInterface ℚ ℚ) Unit (participantInterface ℚ ℚ).Op
  | action@(.query ..), state => ⟨.returned (2 : ℚ), state, [action]⟩
  | action, state => ⟨.stopped .exhausted, state, [action]⟩

theorem query_stop : (caller.run stopQuery ()).outcome = .stopped .refused ∧
    (caller.run stopQuery ()).events = [outputQuery {} 83] := by
  unfold caller
  exact ⟨rfl, rfl⟩

theorem delivery_stop : (caller.run stopDelivery ()).outcome = .stopped .exhausted ∧
    (caller.run stopDelivery ()).events = [outputQuery {} 83, outputDelivery {} (2 : ℚ)] := by
  unfold caller
  exact ⟨rfl, rfl⟩

/-- Residual outputs have exactly one point and all five private ports absent. -/
example (rho : ℚ) (output : leftReturn (F := ℚ) (G := ℚ))
    (residual : GkrRoundsResidual.NoReturn (n := 1) 83
      (GkrRoundsBinding.initial (raw rho) (reference rho) (wrongClaim rho)) output) :
    ∃ point scalar, output = GkrRoundsBinding.runtime (G := ℚ) point scalar ∧ point.length = 1 :=
  GkrRoundsResidual.noReturn_exact_point 83 (raw rho) (reference rho) (wrongClaim rho) output residual

#print axioms GkrCallerSetup.setup_input
#print axioms GkrCallerRealization.represented
#print axioms GkrCallerRealization.all_future
#print axioms GkrCallerBinding.caller_equation
#print axioms GkrCallerBinding.fixture_invocation
#print axioms GkrCallerResidual.first_left_invocation_conditional
#print axioms GkrCallerResidual.first_left_invocation_doomed
#print axioms query_stop
#print axioms delivery_stop

end
end TestsSecurity.GkrCaller
