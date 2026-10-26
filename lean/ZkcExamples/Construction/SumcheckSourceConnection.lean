module

public import ZkcExamples.Construction.SumcheckDomainVerifier
public import ZkcExamples.Construction.SumcheckDomainControls
public import ZkcExamples.Structured.SumcheckSourceVerifier
public import Zkc.Construction.Uniform.DomainProperties

@[expose] public section
/-! Direct connection of the admitted source to the authoritative Sumcheck
Process. This proof does not use the historical instruction comparison. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Construction.SumcheckDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
open ZkcExamples.Structured
open SumcheckVerifierLaws SumcheckSourceVerifier
attribute [local irreducible] reduce roundState
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

omit [AddCommGroup G] [Module F G] [DecidableEq G] [LawfulMonad m] in
theorem source_round_transform {R : Type} (challenge : History F G → m F)
    (handle : Nat) (point : List F) (scalar : F) (history : History F G) (proof : Proof F G)
    (next : List F × F → PIR.Process (Actions F G) R) :
    transform SumcheckProof.context challenge
        (((roundPresent childContext handle (point, scalar)).interpret CommonAdapter.project).bind next)
        history proof =
      scalarRoundK challenge point scalar history proof (fun point scalar history unread =>
        transform SumcheckProof.context challenge (next (point, scalar)) history unread) := by
  have lowKey : SumcheckProof.context.message (lowSite childContext) (childContext.roles 0)
      SumcheckProof.context.validator = staticOrigin lowTemplate := by kernel_rfl
  have highKey : SumcheckProof.context.message (highSite childContext) (childContext.roles 0)
      SumcheckProof.context.validator = staticOrigin highTemplate := by kernel_rfl
  have drawKey : SumcheckProof.context.query (challengeSite childContext) (.draw "bls12-381.fr") =
      staticOrigin drawTemplate := by kernel_rfl
  have deliveryKey : SumcheckProof.context.message (deliverySite childContext)
      SumcheckProof.context.validator (childContext.roles 0) = staticOrigin deliveryTemplate := by kernel_rfl
  simp only [roundPresent, PIR.Process.interpret, CommonAdapter.project, PIR.Process.bind]
  rw [transform_eq_receive]
  cases proof with
  | nil => rfl
  | cons low unread =>
      cases low with
      | boolean => rfl
      | group => rfl
      | field domain low =>
          by_cases lowDomain : domain = "bls12-381.fr"
          · subst domain
            simp only [Payload.value, ite_true]
            rw [transform_eq_receive]
            cases unread with
            | nil => rfl
            | cons high rest =>
                cases high with
                | boolean => rfl
                | group => rfl
                | field domain high =>
                    by_cases highDomain : domain = "bls12-381.fr"
                    · subst domain
                      simp only [Payload.value, ite_true]
                      by_cases valid : scalar = low + high
                      all_goals simp only [valid, ite_true, ite_false, PIR.Process.interpret,
                        CommonAdapter.project, PIR.Process.bind]
                      · rw [transform_eq_query]
                        simp only [scalarRoundK, ite_true, drawKey, lowKey, highKey, List.append_assoc,
                          List.cons_append, List.nil_append]
                        congr 1
                        funext answer
                        rw [transform_eq_send]
                        simp only [Payload.ofValue, deliveryKey, List.append_assoc,
                          List.cons_append, List.nil_append]
                      · simp [scalarRoundK, valid, transform_eq_halt]
                    · simp [Payload.value, scalarRoundK, highDomain, eq_comm]
          · simp [Payload.value, scalarRoundK, lowDomain, eq_comm]

theorem source_loop_transform {R : Type} (challenge : History F G → m F)
    (initial : History F G) (handle : Nat) (indices : List Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) (suffix : History F G)
    (mapped : readbackHistory Origin.withoutCoordinates history = some suffix) (proof : Proof F G)
    (next : List F × F → PIR.Process (Actions F G) R) :
    transform SumcheckProof.context challenge
        (((PIR.repeatN indices.length (roundPresent childContext handle) (point, scalar)).interpret
          CommonAdapter.project).bind next) (initial ++ suffix) proof =
      runK Origin.withoutCoordinates initial challenge (reduce indices point scalar history) proof
        (readbackRoundK initial (fun point scalar history unread =>
          transform SumcheckProof.context challenge (next (point, scalar)) history unread)) := by
  induction indices generalizing point scalar history suffix proof with
  | nil => simp only [List.length_nil, PIR.repeatN, PIR.Process.interpret, PIR.Process.bind,
      reduce, runK, readbackRoundK, mapped]
  | cons index rest ih =>
      simp only [List.length_cons, PIR.repeatN, PIR.Process.interpret_bind, PIR.Process.bind_assoc]
      rw [source_round_transform]
      simp only [reduce, runK_bind]
      rw [← scalar_round challenge initial index point scalar history suffix mapped proof]
      apply runK_congr_yields _ _ _ _ _ (round_mapped history suffix mapped index point scalar)
      intro state unread hasMapping
      cases found : readbackHistory Origin.withoutCoordinates state.history with
      | none => simp [found] at hasMapping
      | some current =>
          simp only [readbackRoundK, found]
          exact ih state.point state.scalar state.history current found unread

theorem source_terminal_transform (challenge : History F G → m F) (initial : History F G)
    (values : List F) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) (suffix : History F G)
    (mapped : readbackHistory Origin.withoutCoordinates history = some suffix) (proof : Proof F G) :
    transform SumcheckProof.context challenge
        (((SumcheckVerifierTerminal.actualOwnedCheck SumcheckSourceViews.unit 1
          (some values) (some point) (some scalar)).bind fun outputs => .done (outputs.get .here)).interpret
            CommonAdapter.project) (initial ++ suffix) proof =
      (fun result => (mapOutcome SumcheckProof.acceptance result.1, result.2)) <$>
        runK Origin.withoutCoordinates initial challenge (terminal values ⟨point, scalar, history⟩) proof
          (nominalFinish initial) := by
  rw [SumcheckVerifierTerminal.terminal_decision]
  split_ifs <;>
    simp [terminal, *, PIR.Process.bind, PIR.Process.interpret, transform, Values.get,
      runK, nominalFinish, readbackOutcome, readbackValues, readbackValue, readbackData,
      mapOutcome, SumcheckProof.acceptance, SumcheckProof.acceptancePosition_eq]

/-- Direct source-to-Domain transport for arbitrary public values and all
typed replies. The source's sends, helper failure order and unread suffix are
retained. No legacy instruction soundness theorem is used. -/
theorem source_transform (challenge : History F G → m F) (values : List F) (claim : F)
    (rounds handle : Nat) (initial : History F G) (proof : Proof F G) :
    transform SumcheckProof.context challenge (SumcheckProof.verifier values claim rounds handle)
        initial proof =
      (fun result => (mapOutcome SumcheckProof.acceptance result.1, result.2)) <$>
        retained challenge values claim rounds initial proof := by
  have original : SumcheckProof.program.participant F G 1
      (SumcheckProof.verifierInputs values claim rounds handle) =
      (SumcheckVerifierPrelude.admittedRounds SumcheckSourceNormalForms.reduceMaximum childContext
        (some rounds) (some handle) (some claim)).bind
        (fun pc => SumcheckVerifierTerminal.actualOwnedCheck SumcheckSourceViews.unit 1
          (some values) pc.1 pc.2) := verifier_optional (some values) (some claim) (some rounds) (some handle)
  have maximum : SumcheckSourceNormalForms.reduceMaximum = 2 := by kernel_rfl
  rw [SumcheckProof.verifier, SumcheckProof.process, original, retained_root]
  simp only [SumcheckVerifierPrelude.admittedRounds, maximum]
  by_cases bounded : rounds ≤ 2
  · simp only [bounded, ite_true]
    rw [repeat_present (F := F) (G := G) childContext handle rounds ([], claim)]
    simp only [PIR.Process.bind_assoc, PIR.Process.bind,
      PIR.Process.interpret_bind, rootProcess, bounded, ite_true, runK_bind, runK_mapOutcome]
    let next : List F × F → PIR.Process (Actions F G) (Option Bool) := fun pc =>
      ((SumcheckVerifierTerminal.actualOwnedCheck (F := F) (G := G) SumcheckSourceViews.unit 1 (some values)
        (some pc.1) (some pc.2)).interpret CommonAdapter.project).bind fun outputs => .done (outputs.get .here)
    change transform SumcheckProof.context challenge
      (((PIR.repeatN rounds (roundPresent childContext handle) ([], claim)).interpret CommonAdapter.project).bind next)
      initial proof = _
    have loopEq := source_loop_transform challenge initial handle (List.range rounds) [] claim
      [] [] rfl proof next
    simp only [List.length_range, List.append_nil] at loopEq
    rw [loopEq]
    apply runK_congr_yields _ _ _ _ _ (reduce_mapped (List.range rounds) [] claim [] [] rfl)
    intro state unread hasMapping
    cases found : readbackHistory Origin.withoutCoordinates state.history with
    | none => simp [found] at hasMapping
    | some suffix =>
        simp only [readbackRoundK, found]
        simpa only [next, PIR.Process.interpret_bind, PIR.Process.interpret, runK_mapOutcome] using
          source_terminal_transform challenge initial values state.point state.scalar
            state.history suffix found unread
  · simp [bounded, rootProcess, PIR.Process.bind, PIR.Process.interpret, runK, mapOutcome,
      transform]

/-- The maintained original endpoint uses the actual Domain instruction meaning.
The oracle is the existing scalar oracle after the explicit key projection. -/
theorem retained_transform (challenge : History F G → m F) (values : List F) (claim : F)
    (rounds handle : Nat) (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome SumcheckProof.acceptance result.1, result.2)) <$>
        retained challenge values claim rounds initial proof =
      transform SumcheckProof.context challenge (SumcheckProof.verifier values claim rounds handle) initial proof :=
  (source_transform challenge values claim rounds handle initial proof).symm

end ZkcExamples.Construction.SumcheckDomainConnection
