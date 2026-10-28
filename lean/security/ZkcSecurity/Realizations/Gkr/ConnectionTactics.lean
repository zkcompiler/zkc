module

public meta import Zkc.Construction.OriginalComponentReduction
public meta import Zkc.Construction.ArtifactBindingTactic
public meta import Zkc.Construction.ProcessViewTactic
public meta import Mathlib.Tactic.CasesM

@[expose] public meta section

/-! Reusable GKR assembly proof strategies. Every supplied rule is elaborated
against the reached full simulation goal. Source and primitive mathematics stay
in the library; no descriptor, name or tactic result is theorem evidence. -/

set_option hygiene false in
macro "derive_gkr_layer " compiled:ident
    " using " "[" rules:term,* "]"
    " gkr_relations " "[" relationLaws:term,* "]"
    " gkr_effects " "[" effectLaws:term,* "]"
    " gkr_presentation " presentation:term
    " gkr_carried_law " carriedLaw:term " gkr_round_carried " roundCarried:term
    " gkr_initial_law " initialLaw:term " gkr_offset_law " offsetLaw:term " gkr_count_law " countLaw:term
    " gkr_reads " "[" readLaws:term,* "]"
    " gkr_finishing " "(" finish:tacticSeq ")" : tactic => do
  let relationLawsS ← relationLaws.getElems.mapM fun value => `(Lean.Parser.Tactic.simpLemma| $value:term)
  let effectLawsS ← effectLaws.getElems.mapM fun value => `(Lean.Parser.Tactic.simpLemma| $value:term)
  let presentationS ← `(Lean.Parser.Tactic.simpLemma| $presentation:term)
  let carriedLawS ← `(Lean.Parser.Tactic.simpLemma| $carriedLaw:term)
  let roundCarriedS ← `(Lean.Parser.Tactic.simpLemma| $roundCarried:term)
  let initialLawS ← `(Lean.Parser.Tactic.simpLemma| $initialLaw:term)
  let countLawS ← `(Lean.Parser.Tactic.simpLemma| $countLaw:term)
  let offsetLawS ← `(Lean.Parser.Tactic.simpLemma| $offsetLaw:term)
  let readLawsS ← readLaws.getElems.mapM fun value => `(Lean.Parser.Tactic.simpLemma| $value:term)
  `(tactic|
    derive_artifact_binding [$rules,*] normalizing (
        saturate_artifact (
          unfold_component_bodies [$compiled]
          apply Classical.choice
          try cases_type* Values
          simp (config := { failIfUnchanged := false }) only
            [$relationLawsS,*] at *
          try casesm* ∃ _, _
          try casesm* _ ∧ _
          try casesm* ∃ _, _
          try casesm* _ ∧ _
          try subst_vars
          constructor
          simp (config := { failIfUnchanged := false }) only
            [↓Original.simplifyBindHead, ↓Original.simplifyRegionHead, ↓Original.stopAtCall, ↓Original.stopAtViewLoop,
             ↓Original.stopAtViewHelper, Original.fold_bind, Original.fold_done,
             observed_helper, ↓OriginalRegions.coefficient_table, PIR.Process.interpret_identity,
             roundsLeft, roundsRight, $presentationS,
             PIR.Process.bind_assoc, Values.present, Values.get, ↓Values.reify_get, ↓Environment.toValues_get]
          normalize_component_operations
            [↓Values.reify_get, ↓Environment.toValues_get, ↓Original.simplifyBindHead, ↓Original.reducePresent, ↓Original.reducePrepend,
             ↓Original.reducePush, ↓Original.reduceSequence, ↓Original.simplifyRegionHead, ↓Original.stopAtRepeat,
             ↓Original.stopAtViewLoop, ↓Original.stopAtViewHelper, roundsLeft, roundsRight,
             $effectLawsS,*,
             compiledConstant, compiledDraw,
             compiledDelivery, GkrOriginalLine.draw_request]
            unfolding [participantMeaningWithOn, protocolOperationWithOn,
              Participant.owned, RoleFamily.sequence, Participant.restrict, Participant.guard,
              Participant.exchange, Participant.query, Evaluation.componentOperationOn,
              strictComponent, Evaluation.meaningOn, Evaluation.operationOn, Op.calculationRegions,
              profile, suite, Nat.reduceEqDiff, qualify_root, GkrOriginalCoefficient.outer,
              ProtocolContext.roles, ProtocolContext.contains, ProtocolContext.enter,
              GkrSourceBodies.roundsSignature, roleSubstitution, List.range_succ, List.range_zero,
              List.any_cons, List.any_nil, Nat.reduceBEq,
              Values.absent, Values.present, Values.split, Values.append, Values.get,
              TypedABI.get_cons_here, TypedABI.get_cons_there, proverState, verifierState, proverCoefficientState, verifierCoefficientState, proverLayerState,
              verifierLayerState, Environment.prepend, Environment.push,
              List.contains_cons, List.contains_nil,
              Operands.eval, Regions.denote, SiteObservations.silent, ProtocolOp.results, Op.results,
              $carriedLaw, $roundCarried, GkrOriginalCoefficient.carried,
              Original.encodeHelperResult, Domain.encodeValues, Ty.isHandle,
              Original.foldActionCall, Original.foldActionDone, Original.foldActionHalt,
              Original.operations, Original.fieldReply, Request.draw, Domain.Raw,
              PIR.Process.interpret_bind, Original.fold_bind, Original.fold_done, Original.interpretIf, Original.foldIf,
              PIR.Process.bind_ite, List.append_assoc]
          simp (config := { failIfUnchanged := false }) (disch := omega) only
            [↓Original.simplifyBindHead, ↓Original.stopAtCall, List.cons_append, List.nil_append, List.length_cons,
             List.length_nil, List.length_append, List.getElem?_append_left, List.getElem?_append_right,
             $readLawsS,*,
             Nat.add_sub_cancel_left, Nat.sub_self, List.getElem?_cons_zero, List.getElem?_cons_succ]))
        solving (first
          | solve | exact fun index => GkrOriginalRoutes.round _ _ _ _ index
          | solve | exact fun index => GkrOriginalRoutes.coefficient _ _ _ index
          | solve | (intro process frame retained
                     apply ArtifactBinding.captures_trans (inner := retained)
                     simp [ArtifactBinding.Captures, List.append_assoc])
          | solve | (try casesm* ∃ _, _
                     try casesm* _ ∧ _
                     try subst_vars
                     simp [ArtifactBinding.Captures, List.append_assoc])
          | solve | simp [$carriedLawS, $roundCarriedS, GkrOriginalCoefficient.carried, Original.encodeHelperResult, Domain.encodeValues, Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, List.length_append, size]
          | solve | (simp (disch := omega) only [Domain.read, List.mapM_cons, List.mapM_nil, Original.encodeHelperResult, Domain.encodeValues, Domain.Value.encode, Domain.Payload.ofValue,
              Ty.isHandle, $carriedLawS, $roundCarriedS, $initialLawS, $offsetLawS, $countLawS, GkrOriginalCoefficient.carried, List.getElem?_append_left, List.getElem?_append_right,
              $readLawsS,*,
              List.append_assoc, List.cons_append, List.nil_append, List.length_append,
              List.length_cons, List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
              Nat.sub_self, Nat.add_sub_cancel_left, Bind.bind, Option.bind, Option.pure_def] <;> rfl)
          | solve | decide +kernel
          | ($finish)))


set_option hygiene false in
macro "derive_gkr_repeat " application:term
    " gkr_destruct " relationPattern:rcasesPat
    " gkr_callback_destruct " callbackPattern:rcasesPat
    " gkr_returning " witness:term
    " gkr_initial_returning " initialWitness:term
    " gkr_splitting " "(" splitCases:tacticSeq ")"
    " gkr_normalizing " "(" normalizeMask:tacticSeq ")"
    " gkr_callback " callbackProof:term
    " gkr_count_read " countReadProof:term
    " gkr_initial_read " initialReadProof:term : tactic =>
  `(tactic| (
    apply ($application:term)
    · ($splitCases:tacticSeq) <;> rfl
    · intro original frame related
      obtain $relationPattern:rcasesPat := related
      ($splitCases:tacticSeq) <;> exact $witness:term
    · intro value state frame index related
      apply Classical.choice
      obtain $callbackPattern:rcasesPat := related
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
      refine ⟨?_⟩
      ($normalizeMask:tacticSeq)
      exact $callbackProof
    · intro original frame related
      obtain $relationPattern:rcasesPat := related
      rfl
    · exact $countReadProof
    · exact $initialReadProof
    · rfl
    · ($splitCases:tacticSeq) <;> exact $initialWitness:term))

set_option hygiene false in
macro "derive_gkr_body " compiled:ident
    " using " "[" rules:term,* "]"
    " gkr_relations " "[" relationLaws:term,* "]"
    " gkr_input_law " inputLaw:term
    " gkr_inputs " inputDefinition:term " gkr_source_inputs " sourceInputs:term
    " gkr_carried_law " carriedLaw:term
    " gkr_finishing " "(" finish:tacticSeq ")" : tactic => do
  let relationLawsS ← relationLaws.getElems.mapM fun value => `(Lean.Parser.Tactic.simpLemma| $value:term)
  let inputLawS ← `(Lean.Parser.Tactic.simpLemma| $inputLaw:term)
  let inputDefinitionS ← `(Lean.Parser.Tactic.simpLemma| $inputDefinition:term)
  let carriedLawS ← `(Lean.Parser.Tactic.simpLemma| $carriedLaw:term)
  `(tactic|
    derive_artifact_binding [$rules,*]
        normalizing (
          saturate_artifact (
            unfold_component_bodies [$compiled]
            apply Classical.choice
            try cases_type* Values
            simp (config := { failIfUnchanged := false }) only
              [$relationLawsS,*] at *
            try casesm* ∃ _, _
            try casesm* _ ∧ _
            try casesm* ∃ _, _
            try casesm* _ ∧ _
            try subst_vars
            constructor
            simp (config := { failIfUnchanged := false }) only
              [↓Original.simplifyBindHead, ↓Original.simplifyRegionHead, ↓Original.stopAtCall, ↓Original.stopAtViewLoop,
               ↓Original.stopAtViewHelper, Original.fold_bind, Original.fold_done, observed_helper,
               ↓OriginalRegions.output_table, $inputLawS, PIR.Process.interpret_identity, PIR.Process.bind_assoc,
               Values.present, Values.get, ↓Values.reify_get, ↓Environment.toValues_get]
            normalize_component_operations
              [↓Values.reify_get, ↓Environment.toValues_get, ↓Original.simplifyBindHead, ↓Original.reducePresent, ↓Original.reducePrepend,
               ↓Original.reducePush, ↓Original.reduceSequence, ↓Original.simplifyRegionHead, ↓Original.stopAtRepeat,
               ↓Original.stopAtViewLoop, ↓Original.stopAtViewHelper, $inputLawS]
              unfolding [participantMeaningWithOn, protocolOperationWithOn,
                Participant.owned, RoleFamily.sequence, Participant.restrict, Participant.guard,
                Participant.exchange, Participant.query, Evaluation.componentOperationOn,
                strictComponent, Evaluation.meaningOn, Evaluation.operationOn, Op.calculationRegions,
                Nat.reduceEqDiff, qualify_root, ProtocolContext.roles, ProtocolContext.contains, ProtocolContext.enter,
                roleSubstitution, GkrSourceBodies.sourceProtocol80Signature,
                List.contains_cons, List.contains_nil,
                List.range_succ, List.range_zero, List.any_cons, List.any_nil, Nat.reduceBEq,
                Values.absent, Values.present, Values.split, Values.append, Values.get,
                GkrOriginalOutput.values, proverLayerState, verifierLayerState,
                TypedABI.get_cons_here, TypedABI.get_cons_there, Environment.prepend, Environment.push,
                Operands.eval, Regions.denote, SiteObservations.silent, ProtocolOp.results, Op.results,
                $inputDefinition, $sourceInputs, Original.encodeHelperResult,
                Domain.encodeValues, Ty.isHandle, maskValues, ProtocolContext.mapScopes,
                Original.foldActionCall, Original.foldActionDone, Original.foldActionHalt,
                Original.operations, PIR.Process.interpret_bind, Original.fold_bind,
                Original.fold_done, Original.interpretIf, Original.foldIf, PIR.Process.bind_ite, List.append_assoc,
                Primitive.evaluate, primitiveOutcome]
            simp (config := { failIfUnchanged := false }) only
              [↓Original.simplifyBindHead, ↓Original.stopAtCall, List.cons_append, List.nil_append,
               List.getElem?_cons_zero, List.getElem?_cons_succ]))
        solving (first
          | solve | decide +kernel
          | solve | exact fun index => GkrOriginalRoutes.output _ _ index
          | solve | (intro process frame retained
                     apply ArtifactBinding.captures_trans (inner := retained)
                     simp [ArtifactBinding.Captures, $inputDefinitionS, List.append_assoc])
          | solve | (try casesm* ∃ _, _
                     try casesm* _ ∧ _
                     try subst_vars
                     simp [ArtifactBinding.Captures, $inputDefinitionS, List.append_assoc])
          | solve | (simp [$inputDefinitionS, Original.encodeHelperResult, Domain.encodeValues,
              Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, GkrOriginalOutput.carried,
               $carriedLawS, Domain.read, List.mapM_cons, List.mapM_nil,
              Bind.bind, Option.bind, Option.pure_def, List.append_assoc] <;> rfl)
          | ($finish)))
