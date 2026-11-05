import Zkc.Source.Structured.OracleEffects

set_option autoImplicit false
open Zkc.Source Zkc.Source.Structured

namespace Tests.OracleValues

private abbrev carriers : Carriers := uniformCarriers Nat Nat
private abbrev kind : OracleKind := .table .index none
private def anchor (iteration : Nat) : OracleAnchor :=
  ⟨⟨0, [.application 2 [1], .iteration 2 [3] iteration]⟩, .construction [5]⟩
private def reference (iteration rows : Nat) : OracleReference kind :=
  ⟨anchor iteration, .cons rows .nil⟩
private def view (iteration rows : Nat) : OracleDataView (.singleton kind) :=
  ⟨0, [1, 2], reference iteration rows⟩
private def sequenceView : OracleDataView (.sequence kind 3) :=
  ⟨0, [1, 2], [reference 0 0, reference 1 7, reference 0 0]⟩

/-- Ordinary round trips quantify over every current type and every carrier value. -/
theorem concrete_roundtrip (type : Ty) (value : carriers.Value type) :
    ProtocolValue.toConcrete (ProtocolValue.ofConcrete type value) = some value :=
  ProtocolValue.toConcrete_ofConcrete type value

/-- The empty sequence retains its full paired identity even with no element anchor. -/
example : (OracleLogicalSort.sequence kind 0).dataType = .sequence .indices := rfl
example : OracleLogicalSort.ofType (.indices) = none := rfl
example : OracleLogicalSort.ofType (.oracleSequence kind 3) = some (.sequence kind 3) := rfl
example : sequenceView.anchors carriers = [anchor 0, anchor 1, anchor 0] := rfl
example : (OracleLogicalSort.sequence kind 0).dataType =
    (OracleLogicalSort.sequence kind 3).dataType := rfl
example : (OracleLogicalSort.sequence kind 0).type ≠
    (OracleLogicalSort.sequence kind 3).type := by decide
example : (view 0 0).anchors carriers ≠ (view 1 0).anchors carriers := by
  change anchor 0 ≠ anchor 1
  decide

theorem wrong_holder : ¬ (view 0 0).SamePair { view 0 0 with holder := 1 } := by
  intro same
  have impossible : (0 : Nat) = 1 := same.1
  cases impossible

theorem empty_pair_identity :
    ¬ (⟨0, [1], []⟩ : OracleDataView (.sequence kind 0)).SamePair ⟨1, [1], []⟩ := by
  intro same
  have impossible : (0 : Nat) = 1 := same.1
  cases impossible

theorem wrong_anchor : ¬ (view 0 0).SamePair (view 1 0) := by
  intro same
  have impossible := same.anchors_eq carriers
  exact (by decide : anchor 0 ≠ anchor 1) impossible

theorem wrong_shape : ¬ (view 0 0).SamePair (view 0 1) := by
  intro same
  have impossible : (0 : Nat) = 1 :=
    congrArg (fun ref : OracleReference kind ↦ ref.shape.get .here) same.2.2
  cases impossible

theorem receiver_permutation :
    (view 0 0).SamePair { view 0 0 with receivers := [2, 1] } := by
  refine ⟨rfl, ?_, rfl⟩
  intro role
  simp [view, or_comm]

theorem wrong_receiver : ¬ (view 0 0).SamePair { view 0 0 with receivers := [1] } := by
  intro same
  have impossible := (same.2.1 2).mp (by decide)
  exact (by decide : (2 : Nat) ∉ [1]) impossible

theorem sequence_order :
    ¬ sequenceView.SamePair { sequenceView with
      references := [reference 1 7, reference 0 0, reference 0 0] } := by
  intro same
  have impossible := congrArg List.head? (same.anchors_eq carriers)
  exact (by decide : some (anchor 0) ≠ some (anchor 1)) impossible

theorem sequence_multiplicity :
    ¬ sequenceView.SamePair { sequenceView with references := [reference 0 0, reference 1 7] } := by
  intro same
  have impossible : (3 : Nat) = 2 := congrArg List.length (same.anchors_eq carriers)
  cases impossible

private abbrev dataType : Ty := (OracleLogicalSort.singleton kind).dataType
private abbrev fields : ProductFields := .cons dataType (.cons .index .nil)
private def record : ProtocolValue carriers (.product "Record" "Record" fields) :=
  .product "Record" "Record" fields
    (.cons (.deferred (view 0 0)) (.cons (ProtocolValue.ofConcrete .index 9) .nil))

theorem project_lazy : record.project .here = .deferred (view 0 0) := rfl
theorem project_concrete : record.project (.there .here) = ProtocolValue.ofConcrete .index 9 := rfl

theorem refuse_concrete_retraction :
    ProtocolValue.toConcrete (carriers := carriers) (.deferred (view 0 0)) = none :=
  ProtocolValue.toConcrete_deferred _

theorem refuse_record_retraction : record.toConcrete = none := by
  unfold record
  erw [ProtocolValue.toConcrete_product, ProtocolValue.toConcreteFields,
    ProtocolValue.toConcrete_deferred]
  rfl

private def nested : ProtocolValue carriers (.sequence (.product "Record" "Record" fields)) :=
  .sequence _ (.cons record (.cons record .nil))

private def demand : OracleDataDemandInterpretation carriers (oracleDataDemandInterface carriers) :=
  fun request ↦ .call request .done

private theorem materialize_record : ProtocolValue.materializeWith demand 0 record =
    .call ⟨0, .singleton kind, view 0 0⟩ (fun rows ↦ .done (rows, 9, ())) := by
  unfold record
  erw [ProtocolValue.materializeWith_product, ProtocolValue.materializeFieldsWith,
    ProtocolValue.materializeWith_deferred]
  simp only [demand, PIR.Process.bind]
  congr 1
  funext rows
  erw [ProtocolValue.materializeFieldsWith, ProtocolValue.materializeWith_ofConcrete,
    ProtocolValue.materializeFieldsWith]
  rfl

/-- Projection selects a demanded operand before traversal, so the other field stays deferred. -/
theorem selective_demand :
    ProtocolValue.materializeWith demand 0 (record.project (.there .here)) = .done 9 := by
  rw [project_concrete, ProtocolValue.materializeWith_ofConcrete]

theorem deferred_demand :
    ProtocolValue.materializeWith demand 0 (record.project .here) =
      .call ⟨0, .singleton kind, view 0 0⟩ .done := by
  rw [project_lazy, ProtocolValue.materializeWith_deferred]
  rfl

/-- This refusal policy supplies no virtual data semantics. It records each attempted demand and
retains the updated state at the first stop. A second element and a suffix never execute. -/
private def refusingHandler : PIR.Handler (oracleDataDemandInterface carriers) Nat Nat :=
  fun request state ↦ ⟨.stopped .refused, state + 1, [request.requester]⟩

theorem stopped_state :
    ((ProtocolValue.materializeWith demand 0 nested).bind fun _ ↦
      (.halt .abort : PIR.Process _ Unit)).run
      refusingHandler 4 = ⟨.stopped .refused, 5, [0]⟩ := by
  simp only [nested, ProtocolValue.materializeWith_sequence, ProtocolValue.materializeSequenceWith,
    materialize_record, PIR.Process.bind, PIR.Process.run,
    refusingHandler, PIR.Execution.follow]

private abbrev flagInterface : PIR.Signature := ⟨Unit, fun _ ↦ Bool⟩
private abbrev numberInterface : PIR.Signature := ⟨Unit, fun _ ↦ Nat⟩
private def flagProcess : PIR.Process flagInterface Bool := .call () .done
private def numberProcess : PIR.Process numberInterface Nat := .call () .done
private def mixedHandler : PIR.Handler (PIR.Signature.sum flagInterface numberInterface) Nat Nat :=
  fun operation state ↦ match operation with
    | .inl _ => ⟨.returned true, state + 1, [0]⟩
    | .inr _ => ⟨.returned 17, state + 1, [1]⟩

theorem dependent_left_reply :
    (flagProcess.interpret (PIR.Signature.injectLeft (J := numberInterface))).run
      mixedHandler 0 = ⟨.returned true, 1, [0]⟩ := rfl

theorem dependent_right_reply :
    (numberProcess.interpret (PIR.Signature.injectRight (I := flagInterface))).run
      mixedHandler 0 = ⟨.returned 17, 1, [1]⟩ := rfl

end Tests.OracleValues
