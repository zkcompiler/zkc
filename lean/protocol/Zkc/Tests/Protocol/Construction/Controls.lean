module

import Zkc.Tests.Protocol.Construction.Pilot

set_option experimental.vcgen true

open PIR Zkc.Source ProtocolProof Std.WP
open ProtocolProofExamples.ConstructionPilot

namespace ProtocolProofExamples.ConstructionControls

attribute [local instance] proofLogic

example (reason : Stop) (post : Nat → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃OrderDual.toDual (OrderDual.ofDual stopped reason)⦄ (Process.halt reason : Process Service Nat) ⦃post; stopped⦄ := by
  construct_region

example (count x : Nat) (post : Nat → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃post x⦄ repeatN count (fun x => Process.done (I := Service) x) x ⦃post; stopped⦄ := by
  construct_region with_invariants [fun _ value => post value]

def selected : Region (scalarDialect language) [(), ()] [()] :=
  .letOp (.branch [()] ()) (.cons .here (.cons (.there .here) .nil))
    (.cons (.ret (.cons .here .nil)) (.cons (.stop .refused) .nil))
    (.ret (.cons .here .nil))

example (env : Environment meaning.Value [(), ()])
    (post : Values meaning.Value [()] → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃if meaning.condition (env .here) then post (.singleton (env (.there .here)))
      else OrderDual.toDual (OrderDual.ofDual stopped .refused)⦄
      selected.denote meaning.regionMeaning env ⦃post; stopped⦄ := by
  unfold selected
  construct_region

-- A choice can be well typed while its mathematical obligations are false.
example (count x : Nat) :
    ⦃OrderDual.toDual (fun _ : Unit × List Unit => (1 : ENNReal))⦄
      repeatN count (fun x => Process.done (I := Service) x) x
    ⦃fun _ => OrderDual.toDual (fun _ => (1 : ENNReal));
      OrderDual.toDual (fun _ _ => (0 : ENNReal))⦄ := by
  fail_if_success
    solve
    | construct_region with_invariants [fun _ _ =>
        OrderDual.toDual (fun _ => (0 : ENNReal))]
      all_goals simp
  construct_region with_invariants [fun _ _ =>
    OrderDual.toDual (fun _ => (1 : ENNReal))]

example (count x : Nat) (post : Nat → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃post x⦄ repeatN count (fun x => Process.done (I := Service) x) x ⦃post; stopped⦄ := by
  fail_if_success construct_region with_invariants [true]
  construct_region with_invariants [fun _ value => post value]

def swapped : Renaming [(), ()] [(), ()]
  | _, .here => .there .here
  | _, .there .here => .here

def inputs : Environment meaning.Value [(), ()] :=
  (Values.cons 9 (Values.cons 2 .nil)).get

example : ¬ UpperBound spec ((helper.rename swapped).denote meaning.regionMeaning inputs)
    (fun out _ => match out with
      | .returned values => if values.get .here = 7 then 0 else 1
      | .stopped _ => 0)
    (fun _ => 0) := by
  change ¬ ∀ _ : Unit × List Unit, (1 : ENNReal) ≤ 0
  simp

end ProtocolProofExamples.ConstructionControls
