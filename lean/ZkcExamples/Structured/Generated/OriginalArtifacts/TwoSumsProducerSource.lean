module

public import ZkcExamples.Structured.Generated.Original.TwoSums
public import ZkcExamples.Structured.OriginalSumcheckProducerCalls

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Structured.Generated.OriginalArtifacts.TwoSumsProducerSource
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open OriginalSumcheckLibrary SumcheckVerifierBodies
open ZkcExamples.Structured.OriginalSumcheckProducerCalls
open ZkcExamples.Structured.OriginalSumcheckCalls
open ZkcExamples.Structured.Generated.Original.TwoSums
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

theorem root_lookup_self (self : Nat) (args : Values (Component (assignment F G)) root.inputs) :
    invokeProtocol (Occurrence.table (ringModel F G) payload) root.signature {} self args =
      root.denoteWithOn (ringModel F G) (.silent _) actions (helpers payload).toOn protocolPrefix1 Occurrence.iterations {} self args := by
  unfold Occurrence.table
  rw [← helpers_on, protocols_eq]
  simp only [List.foldl_cons, List.foldl_nil, extendProtocolTableOn]
  rw [invokeProtocol_cons_same]
  rfl

abbrev step0 (tables : Evaluation.ComponentTables F G (signature (F := F) (G := G))) (input0 : (Option (List F))) (input4 : (Option Nat)) : PIR.Process (signature (F := F) (G := G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index]) :=
  (Participant.owned 0 0 (invoke tables.closed sourceHelper8.helper) (.cons (input0) (.cons (input4) (.cons ((some (1))) .nil))))
abbrev step1 (protocols : ProtocolTable (assignment F G) (signature (F := F) (G := G))) (input4 : (Option Nat)) (_input5 : (Option Nat)) (out0 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index])) : PIR.Process (signature (F := F) (G := G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :=
  (invokeProtocol protocols sourceProtocol0.signature (ProtocolContext.enter {} "label_6c656674" [0, 1]) 0 (.cons ((out0).get .here) (.cons ((out0).get (.there .here)) (.cons ((out0).get (.there (.there .here))) (.cons (none) (.cons (none) (.cons (input4) (.cons (_input5) .nil))))))))
abbrev step1Realized (input4 : (Option Nat)) (_input5 : (Option Nat)) (out0 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index])) := (realizeProducerCall (G := G) payload maximum0 (ProtocolContext.enter {} "label_6c656674" [0, 1]) sourceProtocol0.outputScopes (.cons ((out0).get .here) (.cons ((out0).get (.there .here)) (.cons ((out0).get (.there (.there .here))) (.cons (none) (.cons (none) (.cons (input4) (.cons (_input5) .nil))))))))
theorem step1_binding (input4 : (Option Nat)) (_input5 : (Option Nat)) (out0 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index])) :
  (step1 protocolPrefix1 input4 _input5 out0) = (step1Realized (G := G) input4 _input5 out0) := by
  unfold step1 protocolPrefix1 protocolPrefix0 extendProtocolTableOn
  rw [invokeProtocol_cons_same]
  unfold CheckedProtocol.denoteWithOn
  rw [sourceProtocol0_body]
  rfl
abbrev step2 (tables : Evaluation.ComponentTables F G (signature (F := F) (G := G))) (input1 : (Option (List F))) (input4 : (Option Nat)) : PIR.Process (signature (F := F) (G := G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index]) :=
  (Participant.owned 0 0 (invoke tables.closed sourceHelper8.helper) (.cons (input1) (.cons (input4) (.cons ((some (1))) .nil))))
abbrev step3 (protocols : ProtocolTable (assignment F G) (signature (F := F) (G := G))) (input4 : (Option Nat)) (_input5 : (Option Nat)) (out2 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index])) : PIR.Process (signature (F := F) (G := G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :=
  (invokeProtocol protocols sourceProtocol0.signature (ProtocolContext.enter {} "label_7269676874" [0, 1]) 0 (.cons ((out2).get .here) (.cons ((out2).get (.there .here)) (.cons ((out2).get (.there (.there .here))) (.cons (none) (.cons (none) (.cons (input4) (.cons (_input5) .nil))))))))
abbrev step3Realized (input4 : (Option Nat)) (_input5 : (Option Nat)) (out2 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index])) := (realizeProducerCall (G := G) payload maximum0 (ProtocolContext.enter {} "label_7269676874" [0, 1]) sourceProtocol0.outputScopes (.cons ((out2).get .here) (.cons ((out2).get (.there .here)) (.cons ((out2).get (.there (.there .here))) (.cons (none) (.cons (none) (.cons (input4) (.cons (_input5) .nil))))))))
theorem step3_binding (input4 : (Option Nat)) (_input5 : (Option Nat)) (out2 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index])) :
  (step3 protocolPrefix1 input4 _input5 out2) = (step3Realized (G := G) input4 _input5 out2) := by
  unfold step3 protocolPrefix1 protocolPrefix0 extendProtocolTableOn
  rw [invokeProtocol_cons_same]
  unfold CheckedProtocol.denoteWithOn
  rw [sourceProtocol0_body]
  rfl
abbrev step4 (tables : Evaluation.ComponentTables F G (signature (F := F) (G := G)))  : PIR.Process (signature (F := F) (G := G)) (Values (Component (assignment F G)) [.boolean]) :=
  (invoke tables.components sourceHelper25.helper (.cons (none) (.cons (none) .nil)))

def process (tables : Evaluation.ComponentTables F G (signature (F := F) (G := G)))
    (protocols : ProtocolTable (assignment F G) (signature (F := F) (G := G))) (input0 : (Option (List F))) (input1 : (Option (List F))) (_input2 : (Option F)) (_input3 : (Option F)) (input4 : (Option Nat)) (_input5 : (Option Nat)) : PIR.Process (signature (F := F) (G := G)) (Values (Component (assignment F G)) root.outputs) :=
  (step0 tables input0 input4).bind fun out0 =>
  (step1 protocols input4 _input5 out0).bind fun _out1 =>
  (step2 tables input1 input4).bind fun out2 =>
  (step3 protocols input4 _input5 out2).bind fun _out3 =>
  (step4 tables).bind fun out4 =>
  .done (.cons ((out4).get .here) .nil)

theorem body_binding (tables : Evaluation.ComponentTables F G (signature (F := F) (G := G)))
    (protocols : ProtocolTable (assignment F G) (signature (F := F) (G := G))) (input0 : (Option (List F))) (input1 : (Option (List F))) (_input2 : (Option F)) (_input3 : (Option F)) (input4 : (Option Nat)) (_input5 : (Option Nat)) :
    sourceBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) actions tables.toOn 0 protocols {} Occurrence.iterations)
      ((.cons input0 (.cons input1 (.cons _input2 (.cons _input3 (.cons input4 (.cons _input5 .nil)))))) : Values (Component (assignment F G)) root.inputs).get = process tables protocols input0 input1 _input2 _input3 input4 _input5 := by
  derive_process

abbrev realized (input0 : (Option (List F))) (input1 : (Option (List F))) (_input2 : (Option F)) (_input3 : (Option F)) (input4 : (Option Nat)) (_input5 : (Option Nat)) : PIR.Process (signature (F := F) (G := G)) (Values (Component (assignment F G)) root.outputs) :=
  let tables := helpers (F := F) (G := G) payload
  (step0 tables input0 input4).bind fun out0 =>
  (step1Realized (G := G) input4 _input5 out0).bind fun _out1 =>
  (step2 tables input1 input4).bind fun out2 =>
  (step3Realized (G := G) input4 _input5 out2).bind fun _out3 =>
  (step4 tables).bind fun out4 =>
  .done (.cons ((out4).get .here) .nil)

theorem realization_binding (input0 : (Option (List F))) (input1 : (Option (List F))) (_input2 : (Option F)) (_input3 : (Option F)) (input4 : (Option Nat)) (_input5 : (Option Nat)) :
    process (helpers (F := F) (G := G) payload) protocolPrefix1 input0 input1 _input2 _input3 input4 _input5 = realized (G := G) input0 input1 _input2 _input3 input4 _input5 := by
  unfold process realized
  apply congrArg₂ PIR.Process.bind
  · rfl
  · funext out0
    apply congrArg₂ PIR.Process.bind
    · exact (step1_binding (G := G) input4 _input5 out0)
    · funext out1
      apply congrArg₂ PIR.Process.bind
      · rfl
      · funext out2
        apply congrArg₂ PIR.Process.bind
        · exact (step3_binding (G := G) input4 _input5 out2)
        · funext out3
          apply congrArg₂ PIR.Process.bind
          · rfl
          · funext out4
            rfl

theorem participant_binding (input0 : (Option (List F))) (input1 : (Option (List F))) (input4 : (Option Nat)) :
    Occurrence.participant (ringModel F G) imported.program 0 ((.cons input0 (.cons input1 (.cons none (.cons none (.cons input4 (.cons none .nil))))))) =
      (realized (G := G) input0 input1 none none input4 none).bind (fun out => .done (maskValues 0 root.outputScopes out)) := by
  change invokeProtocol (Occurrence.table (ringModel F G) payload) root.signature {} 0 ((.cons input0 (.cons input1 (.cons none (.cons none (.cons input4 (.cons none .nil))))))) = _
  rw [root_lookup_self (F := F) (G := G)]
  unfold CheckedProtocol.denoteWithOn
  change (root.body.denote (participantMeaningWithOn (ringModel F G) (.silent _) actions (helpers payload).toOn 0 protocolPrefix1 {} Occurrence.iterations)
    ((.cons input0 (.cons input1 (.cons none (.cons none (.cons input4 (.cons none .nil)))))) : Values (Component (assignment F G)) root.inputs).get).bind _ = _
  rw [root_body, body_binding, realization_binding, ProtocolContext.mapScopes_root]

end ZkcExamples.Structured.Generated.OriginalArtifacts.TwoSumsProducerSource
