import Zkc.Construction.OriginalCorrespondence
import Zkc.Construction.DomainRuntimeProjection
import Zkc.Source.KernelRfl
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option smartUnfolding false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Tests.SourceDeliverySchedule
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Original

private def model : DomainModel := ringModel (ZMod 5) (ZMod 5)

-- Admitted-source regressions from independent review: the construction
-- refuses repeated or delayed delivery, while preserving the original source.
private def snapshot : Snapshot where
  source := "sha256:0000000000000000000000000000000000000000000000000000000000000000"
  entry := "Root"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"Root", .protocol, .publicDef,
    [.service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr"],
    some ⟨["P", "V"], [["V"]], [["P", "V"], ["P", "V"]]⟩, [], some (.protocol ⟨"Root", []⟩),
    .block [
      .instruction (.draw "V" "bls12-381.fr") [0] [.field "bls12-381.fr"] [] "q",
      .instruction (.exchange "V" "P") [0] [.field "bls12-381.fr"] [] "d1",
      .instruction (.exchange "V" "P") [1] [.field "bls12-381.fr"] [] "d2"]
      (.ret [1, 0])⟩]
  contracts := [⟨"Root", []⟩]
  catalogue := admittedCatalogue

private def program : Program := (check snapshot).toOption.get (by decide +kernel)

private def context : Context :=
  ⟨"Root", ["P", "V"], 0, 1, 0, "random.bls12-381.fr/0",
    some (.draw "bls12-381.fr"), "suite", [("q", "d1"), ("q", "d2")]⟩
private def draw : Template :=
  ⟨"Root", [], ["query", "Root", "q", "input_0", "random.bls12-381.fr/0", "draw", "V"]⟩
private def message (site : String) : Template :=
  ⟨"Root", [], ["message", "Root", site, site, "V", "P"]⟩
private def routing (mode : Domain.Mode) : Routing :=
  ⟨snapshot, context, mode, 73, [message "d1", message "d2"], [draw],
    [⟨draw, message "d1"⟩, ⟨draw, message "d2"⟩], []⟩

example : SourceDelivery.checked snapshot context draw (message "d1") = true := by decide +kernel
example : SourceDelivery.checked snapshot context draw (message "d2") = false := by decide +kernel
example : SourceDelivery.resolve snapshot context "q" "d1" = some (draw, message "d1") := by decide +kernel
example : SourceDelivery.resolve snapshot context "q" "d2" = none := by decide +kernel

private def originalInputs (mode : Domain.Mode) :
    Values (Component model.Value) [.service "random.bls12-381.fr/0"] :=
  .cons (match mode with | .producer => none | .validator => some 73) .nil
private def constructed (mode : Domain.Mode) :=
  Original.participant model program (routing mode)
    (match mode with | .producer => 0 | .validator => 1) (originalInputs mode) {}

-- This is a deterministic, coherent keyed oracle: its answer is a function of
-- the key's history alone. Repeated identical keys always return the same value.
private def keyed : Domain.Oracle Id model.toCarriers Nat :=
  fun history event state =>
    match event with
    | .challenge origin =>
      if request : origin.request = some (.draw "bls12-381.fr") then
        (.returned (by simpa [Domain.Raw, request, model, Request.draw] using
          (history.length : ZMod 5)), state + 1)
      else (.stopped .refused, state)
    | .message _ _ | .publicBinding _ => (.returned (), state)

private def returned (first second : ZMod 5) :
    Values (Component model.Value) [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .cons (some first) (.cons (some second) .nil)

theorem repeated_draw_policy_refused :
    (mapExecution Prod.fst (Domain.run .producer keyed (constructed .producer) ⟨[], [], 0⟩)).outcome =
    .stopped .refused := by kernel_rfl
theorem shared_validator_returns :
    (mapExecution Prod.fst (Domain.run .validator keyed (constructed .validator) ⟨[], [], 0⟩)).outcome =
    .returned (returned 0 0) := by kernel_rfl
theorem shared_producer_queries :
    (Domain.run .producer keyed (constructed .producer) ⟨[], [], 0⟩).state.oracle = 0 := by kernel_rfl
theorem shared_validator_queries :
    (Domain.run .validator keyed (constructed .validator) ⟨[], [], 0⟩).state.oracle = 1 := by kernel_rfl

-- A prover message between draw and delivery invalidates the supported
-- synchronous construction, despite preserving the original SSA edge.
private def delayedSnapshot : Snapshot :=
  { snapshot with definitions := [.function ⟨"Root", .protocol, .publicDef,
    [.boolean, .service "random.bls12-381.fr/0"], [.field "bls12-381.fr"],
    some ⟨["P", "V"], [["P"], ["V"]], [["P", "V"]]⟩, [], some (.protocol ⟨"Root", []⟩),
    .block [
      .instruction (.draw "V" "bls12-381.fr") [1] [.field "bls12-381.fr"] [] "q",
      .instruction (.exchange "P" "V") [1] [.boolean] [] "m",
      .instruction (.exchange "V" "P") [1] [.field "bls12-381.fr"] [] "d"]
      (.ret [0])⟩] }
private def delayedProgram : Program := (check delayedSnapshot).toOption.get (by decide +kernel)
private def delayedContext : Context := { context with service := 1, draws := [("q", "d")] }
private def delayedDraw : Template :=
  ⟨"Root", [], ["query", "Root", "q", "input_1", "random.bls12-381.fr/0", "draw", "V"]⟩
private def proverMessage : Template := ⟨"Root", [], ["message", "Root", "m", "m", "P", "V"]⟩
private def delayedRouting (mode : Domain.Mode) : Routing :=
  ⟨delayedSnapshot, delayedContext, mode, 73, [proverMessage, message "d"], [delayedDraw],
    [⟨delayedDraw, message "d"⟩], []⟩
example : SourceDelivery.checked delayedSnapshot delayedContext delayedDraw (message "d") = false := by
  decide +kernel
private def delayedInputs (mode : Domain.Mode) :
    Values (Component model.Value) [.boolean, .service "random.bls12-381.fr/0"] :=
  match mode with
  | .producer => .cons (some true) (.cons none .nil)
  | .validator => .cons none (.cons (some 73) .nil)
private def delayed (mode : Domain.Mode) :=
  Original.participant model delayedProgram (delayedRouting mode)
    (match mode with | .producer => 0 | .validator => 1) (delayedInputs mode) {}
private def singleReturn (value : ZMod 5) : Values (Component model.Value) [.field "bls12-381.fr"] :=
  .cons (some value) .nil
theorem delayed_delivery_refused :
    (mapExecution Prod.fst (Domain.run .producer keyed (delayed .producer) ⟨[], [], 0⟩)).outcome =
    .stopped .refused := by kernel_rfl
theorem delayed_validator_returns : (mapExecution Prod.fst
    (Domain.run .validator keyed (delayed .validator) ⟨[], [.boolean true], 0⟩)).outcome =
    .returned (singleReturn 0) := by kernel_rfl


-- Even a correct source edge must belong to the fixed construction policy.
example : ({ routing .producer with context := { context with draws := [] } }).delivery
    [] "d1" "bls12-381.fr" 1 = none := by decide +kernel
example : (({ routing .producer with context := { context with draws := [("q", "d1")] } }).delivery
    [] "d1" "bls12-381.fr" 1).isSome = true := by decide +kernel

end Tests.SourceDeliverySchedule
