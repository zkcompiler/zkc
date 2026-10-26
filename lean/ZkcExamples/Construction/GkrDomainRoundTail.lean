module

public import ZkcExamples.Construction.GkrDomainPhaseBinding
public import ZkcExamples.Structured.Generated.Constructed.GkrValidator
public meta import Zkc.Construction.ProcessViewTactic
public meta import Mathlib.Tactic.FailIfNoProgress

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.GkrDomainRoundTail
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform Zkc.Construction.Uniform.LoopedSourceProcess
open ZkcExamples.Structured GkrSourceProtocol
open GkrDomainRounds GkrDomainPhaseBinding
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def leftTailBlocks : List (Domain.View.Block (uniformCarriers F G)) :=
  [
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep15 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep16 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep17 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep18 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep19 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep20 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep21 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep22 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep23 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep24 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep25 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep26 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep27 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep28 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep29 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep30 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep31 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep32 (ringModel F G) program context]

def leftTail : Domain.View.Block (uniformCarriers F G) := sequenceBlocks leftTailBlocks

/-- The actual left round suffix, after all three received coefficients.
The guard is unrestricted and the challenge reply is arbitrary. -/
def left_binding (env : Env (F := F) (G := G)) (length : env.length = 36)
    (layerIndex index handle : Nat) (point : List F) (claim c0 c1 c2 : F)
    (suffix : Hist (F := F) (G := G))
    (layerFound : env[12]? = some (.data (.index layerIndex)))
    (roundFound : env[17]? = some (.data (.index index)))
    (pointFound : env[18]? = some (.data (.vector "bls12-381.fr" point)))
    (claimFound : env[19]? = some (.data (.field "bls12-381.fr" claim)))
    (firstFound : env[21]? = some (.data (.field "bls12-381.fr" c0)))
    (secondFound : env[26]? = some (.data (.field "bls12-381.fr" c1)))
    (thirdFound : env[31]? = some (.data (.field "bls12-381.fr" c2)))
    (historyFound : env[35]? = some (.transcript context.suite suffix)) :
    Original.Simulation RoundReturns (fun _ _ => True)
      (SourceProcess.sourceView context
        (GkrVerifier.roundCheck (GkrVerifier.leftContext {}) handle (point, claim) c0 c1 c2) (history suffix))
      (((leftTail env).bind
          (yieldValues [49, 53, 48] [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"),
            .transcript context.suite])).interpret operations) := by
  unfold leftTail leftTailBlocks sequenceBlocks
  simp only [List.foldr_cons, List.foldr_nil]
  unfold_component_bodies [Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep15,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep16,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep17,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep18,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep19,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep20,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep21,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep22,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep23,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep24,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep25,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep26,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep27,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep28,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep29,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep30,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep31,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep32]
  derive_artifact_binding [query_binding (F := F) (G := G)] normalizing (
    repeat' (first
    | (fail_if_no_progress normalize_artifact_operations [GkrDomainHelpers.append] unfolding
      [roundValues, yieldValues, 
       GkrVerifier.roundCheck, GkrVerifier.roundChallenge,
       guard_decide, PIR.Process.bind_ite, sourceView_ite, interpret_ite, SourceProcess.sourceView, SourceProcess.receive, SourceProcess.send, SourceProcess.query,
       PIR.Process.interpret_bind, PIR.Process.interpret, operations, history, event,
       Domain.queryOrigin, Domain.templateOrigin, Template.origin, Template.qualify, Template.applicationPrefix, Template.repeats,
       Domain.atCoordinates, Origin.withoutCoordinates, context, Context.fiatShamir, Context.suite,
       Context.contract, Context.request, Context.replacement?, Context.query, Context.service,
       Context.role, Context.message, Origin.message, Origin.query,
       GkrVerifier.roundSite, GkrVerifier.challengeSite, GkrVerifier.deliverySite,
       GkrVerifier.leftContext, GkrVerifier.rightContext, ProtocolContext.enter, roleSubstitution,
       qualifyProtocolSite, layerFound, roundFound, pointFound, claimFound, firstFound, secondFound, thirdFound, historyFound,
       ProtocolContext.roles, List.getElem?_append, length, List.isEmpty_cons,
       Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, GkrVerifier.scalar,
       eq_mp_eq_cast, cast_eq, decimalDigit, left_size, right_size,
       Payload.ofValue, DomainAdapter.embedPayload, Ty.isService, Bool.false_eq_true, Bool.not_false,
       entry_metadata, suite_metadata, List.getD_cons_zero, List.getD_cons_succ, decimal,
       List.map_append, Origin.withoutCoordinates])
    | (fail_if_no_progress erw [GkrDomainHelpers.append (F := F) (G := G)])
    | (fail_if_no_progress erw [Domain.Calculations.fieldAdd (F := F) (G := G)])
    | (fail_if_no_progress erw [Domain.Calculations.fieldMultiply (F := F) (G := G)])
    | (fail_if_no_progress erw [Domain.Calculations.fieldEqual (F := F) (G := G)])))
    solving (first
      | rfl
      | (simp only [history, List.map_append, List.map_cons, List.map_nil, event, Origin.withoutCoordinates,
          Origin.withoutCoordinates, String.reduceBEq, String.reduceEq,
          Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true,
          left_size, right_size, Nat.reduceLT, decimalDigit, String.reduceAppend,
          List.getD_cons_zero, List.getD_cons_succ])
      | (
          unfold RoundReturns
          refine ⟨_, _, _, ?_, rfl⟩
          simp only [history, List.map_append, List.map_cons, List.map_nil, event, Origin.withoutCoordinates,
            Origin.withoutCoordinates]
          try rfl))

def rightTailBlocks : List (Domain.View.Block (uniformCarriers F G)) :=
  [
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep15 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep16 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep17 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep18 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep19 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep20 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep21 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep22 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep23 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep24 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep25 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep26 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep27 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep28 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep29 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep30 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep31 (ringModel F G) program context,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep32 (ringModel F G) program context]

def rightTail : Domain.View.Block (uniformCarriers F G) := sequenceBlocks rightTailBlocks

/-- The actual right round suffix, after all three received coefficients.
The guard is unrestricted and the challenge reply is arbitrary. -/
def right_binding (env : Env (F := F) (G := G)) (length : env.length = 40)
    (layerIndex index handle : Nat) (point : List F) (claim c0 c1 c2 : F)
    (suffix : Hist (F := F) (G := G))
    (layerFound : env[12]? = some (.data (.index layerIndex)))
    (roundFound : env[21]? = some (.data (.index index)))
    (pointFound : env[22]? = some (.data (.vector "bls12-381.fr" point)))
    (claimFound : env[23]? = some (.data (.field "bls12-381.fr" claim)))
    (firstFound : env[25]? = some (.data (.field "bls12-381.fr" c0)))
    (secondFound : env[30]? = some (.data (.field "bls12-381.fr" c1)))
    (thirdFound : env[35]? = some (.data (.field "bls12-381.fr" c2)))
    (historyFound : env[39]? = some (.transcript context.suite suffix)) :
    Original.Simulation RoundReturns (fun _ _ => True)
      (SourceProcess.sourceView context
        (GkrVerifier.roundCheck (GkrVerifier.rightContext {}) handle (point, claim) c0 c1 c2) (history suffix))
      (((rightTail env).bind
          (yieldValues [53, 57, 52] [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"),
            .transcript context.suite])).interpret operations) := by
  unfold rightTail rightTailBlocks sequenceBlocks
  simp only [List.foldr_cons, List.foldr_nil]
  unfold_component_bodies [Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep15,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep16,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep17,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep18,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep19,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep20,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep21,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep22,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep23,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep24,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep25,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep26,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep27,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep28,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep29,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep30,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep31,
    Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep32]
  derive_artifact_binding [query_binding (F := F) (G := G)] normalizing (
    repeat' (first
    | (fail_if_no_progress normalize_artifact_operations [GkrDomainHelpers.append] unfolding
      [roundValues, yieldValues, 
       GkrVerifier.roundCheck, GkrVerifier.roundChallenge,
       guard_decide, PIR.Process.bind_ite, sourceView_ite, interpret_ite, SourceProcess.sourceView, SourceProcess.receive, SourceProcess.send, SourceProcess.query,
       PIR.Process.interpret_bind, PIR.Process.interpret, operations, history, event,
       Domain.queryOrigin, Domain.templateOrigin, Template.origin, Template.qualify, Template.applicationPrefix, Template.repeats,
       Domain.atCoordinates, Origin.withoutCoordinates, context, Context.fiatShamir, Context.suite,
       Context.contract, Context.request, Context.replacement?, Context.query, Context.service,
       Context.role, Context.message, Origin.message, Origin.query,
       GkrVerifier.roundSite, GkrVerifier.challengeSite, GkrVerifier.deliverySite,
       GkrVerifier.leftContext, GkrVerifier.rightContext, ProtocolContext.enter, roleSubstitution,
       qualifyProtocolSite, layerFound, roundFound, pointFound, claimFound, firstFound, secondFound, thirdFound, historyFound,
       ProtocolContext.roles, List.getElem?_append, length, List.isEmpty_cons,
       Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, GkrVerifier.scalar,
       eq_mp_eq_cast, cast_eq, decimalDigit, left_size, right_size,
       Payload.ofValue, DomainAdapter.embedPayload, Ty.isService, Bool.false_eq_true, Bool.not_false,
       entry_metadata, suite_metadata, List.getD_cons_zero, List.getD_cons_succ, decimal,
       List.map_append, Origin.withoutCoordinates])
    | (fail_if_no_progress erw [GkrDomainHelpers.append (F := F) (G := G)])
    | (fail_if_no_progress erw [Domain.Calculations.fieldAdd (F := F) (G := G)])
    | (fail_if_no_progress erw [Domain.Calculations.fieldMultiply (F := F) (G := G)])
    | (fail_if_no_progress erw [Domain.Calculations.fieldEqual (F := F) (G := G)])))
    solving (first
      | rfl
      | (simp only [history, List.map_append, List.map_cons, List.map_nil, event, Origin.withoutCoordinates,
          Origin.withoutCoordinates, String.reduceBEq, String.reduceEq,
          Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true,
          left_size, right_size, Nat.reduceLT, decimalDigit, String.reduceAppend,
          List.getD_cons_zero, List.getD_cons_succ])
      | (
          unfold RoundReturns
          refine ⟨_, _, _, ?_, rfl⟩
          simp only [history, List.map_append, List.map_cons, List.map_nil, event, Origin.withoutCoordinates,
            Origin.withoutCoordinates]
          try rfl))

end ZkcExamples.Construction.GkrDomainRoundTail
