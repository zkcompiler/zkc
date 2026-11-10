module

public import Zkc.Tests.Verification.Construction.DrawPairSource
public import Mathlib.Algebra.Ring.Int.Defs

/-! A second author supplies a stateful service interpretation. Structural construction
uses the actual source, including the failing unselected arm and both ordered handles. -/

@[expose] public section
noncomputable section
set_option experimental.vcgen true
open PIR Zkc.Source Zkc.Source.Structured ProtocolProof Std.WP
namespace ActualSourceConstruction.DrawPair

bind_source_helper rejectValue from actual named "s12h61637475616c5f63616c6c7312h72656a6563745f76616c7565"
bind_source_protocol drawPair from actual named "s12h61637475616c5f63616c6c738h4472617750616972"

abbrev model := ringModel Int Int
abbrev State := Nat → Nat
abbrev Interface := participantInterfaceOn model.toCarriers

def advance (handle : Nat) (state : State) : State :=
  fun selected => if selected = handle then state selected + 1 else state selected

/-- A handle selects its own counter. Aliased handles therefore share state. -/
def specification : OperationSpec Interface State Nat := fun operation =>
  match operation with
  | .query _ operation arguments =>
    match operation with
    | .draw _ => fun post current =>
      let handle := arguments.get .here
      post (.returned (current.1 handle : Int)) (advance handle current.1, current.2 ++ [handle])
    | _ => fun post current => post (.stopped .refused) current
  | _ => fun post current => post (.stopped .refused) current

attribute [local construction_simp] specification OperationSpec.outcomePost List.append_assoc

theorem specification_monotone : specification.Monotone := by
  intro operation post next bound current
  cases operation with
  | send => exact bound _ _
  | receive => exact bound _ _
  | query site op args => cases op <;> exact bound _ _

abbrev logic : WPMonad (Process Interface)
    (Potential State Nat)ᵒᵈ (Stop → Potential State Nat)ᵒᵈ :=
  specification.toUpperWPMonad specification_monotone
abbrev lowerLogic : WPMonad (Process Interface)
    (Potential State Nat) (Stop → Potential State Nat) :=
  specification.toWPMonad specification_monotone
section Upper
attribute [local instance] logic

set_option maxHeartbeats 200000 in
/-- Both actual requests preserve their ordered handles, state updates and history. -/
theorem participant_law (enabled : Bool) (left right : Nat)
    (post : Values (Component model.Value) drawPair.signature.outputs → (Potential State Nat)ᵒᵈ)
    (stopped : (Stop → Potential State Nat)ᵒᵈ) :
    ⦃OrderDual.toDual (fun current => if enabled then
      OrderDual.ofDual (post (.cons (some (current.1 left : Int))
        (.cons (some (advance left current.1 right : Int)) .nil)))
        (advance right (advance left current.1), current.2 ++ [left, right])
      else OrderDual.ofDual stopped .reject current)⦄
      actual.program.participantOn model 0
        (.cons (some enabled) (.cons (some left) (.cons (some right) .nil)))
      ⦃post; stopped⦄ := by
  construct_region

end Upper

section Lower
attribute [local instance] lowerLogic

/-- The same actual effects also give the lower contract, without a dual interpretation. -/
theorem participant_lower_law (enabled : Bool) (left right : Nat)
    (post : Values (Component model.Value) drawPair.signature.outputs → Potential State Nat)
    (stopped : Stop → Potential State Nat) :
    @Triple _ _ _ _ _ _
      (actual.program.participantOn model 0
        (.cons (some enabled) (.cons (some left) (.cons (some right) .nil))))
      ((specification.toWPMonad specification_monotone).toWP _)
      (fun current => if enabled then
        post (.cons (some (current.1 left : Int))
          (.cons (some (advance left current.1 right : Int)) .nil))
          (advance right (advance left current.1), current.2 ++ [left, right])
        else stopped .reject current) post stopped := by
  construct_region

end Lower

#print axioms participant_lower_law
#print axioms participant_law
end ActualSourceConstruction.DrawPair
