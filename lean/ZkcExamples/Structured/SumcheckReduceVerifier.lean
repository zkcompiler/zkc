module

public import ZkcExamples.Structured.SumcheckReduceAssociations
public import ZkcExamples.Structured.SumcheckVerifierBodies
public import ZkcExamples.Structured.SumcheckVerifierHelpers
public import ZkcExamples.Structured.SumcheckVerifierPrelude

@[expose] public section

/-! Plain verifier equations for the complete original Reduction source unit. -/
namespace ZkcExamples.Structured.SumcheckReduceVerifier
open Zkc.Source Zkc.Source.Structured
open SumcheckReduceViews

/-- Every dependency is a complete body in this source's own definition list. -/
theorem helperBodies : SumcheckVerifierHelpers.Bodies unit.definitions where
  empty := SumcheckReduceAssociations.empty_association
  append := SumcheckReduceAssociations.append_association
  width := SumcheckReduceAssociations.width_association
  «variables» := SumcheckReduceAssociations.variables_association
  values := SumcheckReduceAssociations.values_association

/-- Complete maximum-four body association, including the nested callback and suffix. -/
theorem reduce_raw_shared :
    reduceDefinition.raw = (SumcheckVerifierBodies.reduceBody 4).erase := by
  refine SumcheckReduceViews.reduce_raw.trans ?_
  unfold SumcheckVerifierBodies.reduceBody SumcheckVerifierBodies.roundBody
    SumcheckVerifierBodies.reduceReturn
  rfl

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

open SumcheckVerifierHelpers SumcheckVerifierPrelude

/-- Full signature, member and raw tree select the child in the actual plain table. -/
theorem reduce_invoke_plain (ctx : ProtocolContext) (self : Nat)
    (arguments : Values (Component (assignment F G)) SumcheckVerifierBodies.reduceInputs) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.reduceSignature
      ctx self arguments = reduceDenote 4 unit ctx self arguments := by
  exact protocol_invoke_body_view (.silent _) (participantActions F G) (plainHelpers unit)
    unit.protocols unit.protocolsLinked reduceDefinition reduce_member
    (SumcheckVerifierBodies.reduceBody 4) reduce_raw_shared ctx self arguments

def reduceRootInputs (xs : Option (List F)) (dimension : Option Nat)
    (claim : Option F) (count service : Option Nat) :
    Values (Component (assignment F G)) SumcheckReduceBodies.runSignature.inputs :=
  .cons xs (.cons dimension (.cons claim (.cons count (.cons service .nil))))

def reduceRootResults (pc : Option (List F) × Option F) :
    Values (Component (assignment F G)) SumcheckReduceBodies.runSignature.outputs :=
  .cons none (.cons none (.cons pc.1 (.cons pc.2 .nil)))

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem mask_rootInputs (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (xs : Option (List F)) (dimension : Option Nat) (claim : Option F)
    (count service : Option Nat) :
    maskValues self (ctx.mapScopes SumcheckReduceBodies.runSignature.inputScopes)
      (reduceRootInputs (G := G) xs dimension claim count service) =
        reduceRootInputs none none claim count service := by
  subst self
  unfold reduceRootInputs
  dsimp only [SumcheckReduceBodies.runSignature]
  iterate 6 unfold maskValues
  simp [ProtocolContext.mapScopes, Participant.restrict, Ne.symm separate]

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem mask_rootTuple (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (pointP valuesP pointV : Option (List F)) (claim : Option F) :
    maskValues self (ctx.mapScopes SumcheckReduceBodies.runSignature.outputScopes)
      (Values.cons pointP (.cons valuesP (.cons pointV (.cons claim .nil)))) =
        reduceRootResults (G := G) (pointV, claim) := by
  subst self
  iterate 5 unfold maskValues
  simp [SumcheckReduceBodies.runSignature, ProtocolContext.mapScopes,
    Participant.restrict, Ne.symm separate, reduceRootResults]

/-- The literal root body, evaluated under an arbitrary complete unit's tables. -/
private theorem run_body_context_expansion (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (xs : Option (List F)) (dimension : Option Nat) (claim : Option F)
    (count service : Option Nat) :
    ((SumcheckReduceBodies.runBody.denote
      (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers U)
        self (U.plainProtocolTable F G) ctx)
      (maskValues self (ctx.mapScopes SumcheckReduceBodies.runSignature.inputScopes)
        (reduceRootInputs xs dimension claim count service)).get).bind
      (fun result => .done
        (maskValues self (ctx.mapScopes SumcheckReduceBodies.runSignature.outputScopes) result))) =
      (invokeProtocol (U.plainProtocolTable F G) SumcheckReduceBodies.reduceSignature
        (ctx.enter "s3" [0, 1]) self
        (reduceArguments none none none claim count service)).bind
        (fun result => .done (reduceRootResults
          (result.get (.there (.there (.there (.there .here)))),
            result.get (.there (.there (.there (.there (.there .here)))))))) := by
  rw [mask_rootInputs ctx self verifier separate]
  subst self
  change ((Participant.owned (ctx.roles 1) (ctx.roles 0)
    (invoke (plainHelpers U).closed MapFirstBodies.tableHelper)
    (.cons none (.cons none (.cons (some 1) .nil)))).bind _).bind _ = _
  rw [Participant.owned_other _ _ separate]
  have active : (ctx.enter "s3" [0, 1]).contains SumcheckReduceBodies.reduceSignature
      (ctx.roles 1) = true := by
    apply (ProtocolContext.contains_iff _ _ _).mpr
    exact ⟨1, by decide, rfl⟩
  change ((if (ctx.enter "s3" [0, 1]).contains SumcheckReduceBodies.reduceSignature
      (ctx.roles 1) then
      invokeProtocol (U.plainProtocolTable F G) SumcheckReduceBodies.reduceSignature
        (ctx.enter "s3" [0, 1]) (ctx.roles 1)
        (reduceArguments none none none claim count service)
    else .done (Values.absent (assignment F G) SumcheckReduceBodies.reduceSignature.outputs)).bind _).bind _ = _
  rw [active]
  simp only [↓reduceIte]
  refine (PIR.Proc.bind_assoc _ _ _).trans ?_
  refine congrArg (PIR.Proc.bind _) (funext fun result => ?_)
  cases result with | cons pointP rest =>
    cases rest with | cons valuesP rest =>
      cases rest with | cons dimensionP rest =>
        cases rest with | cons widthP rest =>
          cases rest with | cons pointV rest =>
            cases rest with | cons current rest =>
              cases rest
              change ((invoke (plainHelpers U).components MapFirstBodies.valuesHelper
                (.cons valuesP (.cons dimensionP (.cons widthP .nil)))).bind _).bind _ = _
              rw [values_optional U bodies]
              change PIR.Proc.done (I := participantInterface F G) (maskValues (ctx.roles 1)
                (ctx.mapScopes SumcheckReduceBodies.runSignature.outputScopes)
                (.cons pointP (.cons valuesP (.cons pointV (.cons current .nil))))) = _
              rw [mask_rootTuple ctx (ctx.roles 1) rfl separate]
              rfl


/-- The actual root skips tableP construction, calls Reduce at s3, and selects
its original verifier outputs using the exact optional Math projection. -/
theorem root_context_expansion (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (xs : Option (List F)) (dimension : Option Nat) (claim : Option F)
    (count service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.runSignature
      ctx self (reduceRootInputs xs dimension claim count service) =
      (invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.reduceSignature
        (ctx.enter "s3" [0, 1]) self
        (reduceArguments none none none claim count service)).bind
        (fun result => .done (reduceRootResults
          (result.get (.there (.there (.there (.there .here)))),
            result.get (.there (.there (.there (.there (.there .here)))))))) :=
  (protocol_invoke_body_view (.silent _) (participantActions F G) (plainHelpers unit)
    unit.protocols unit.protocolsLinked runDefinition run_member
    SumcheckReduceBodies.runBody run_raw ctx self
    (reduceRootInputs xs dimension claim count service)).trans
      (run_body_context_expansion unit helperBodies ctx self verifier separate
        xs dimension claim count service)


omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem select_reduceResults
    (process : PIR.Proc (participantInterface F G) (Option (List F) × Option F)) :
    (process.bind (fun pc => .done (reduceResults (G := G) pc))).bind
      (fun result => .done (reduceRootResults
        (result.get (.there (.there (.there (.there .here)))),
          result.get (.there (.there (.there (.there (.there .here)))))))) =
      process.bind (fun pc => .done (reduceRootResults (G := G) pc)) := by
  rw [PIR.Proc.bind_assoc]
  rfl

/-- Contextual equation for the complete imported Reduction root. The child
uses the real s3 application prefix and the caller's mapped participant roles. -/
theorem verifier_context_optional (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (xs : Option (List F)) (dimension : Option Nat) (claim : Option F)
    (count service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.runSignature
      ctx self (reduceRootInputs xs dimension claim count service) =
      (admittedRounds 4 (ctx.enter "s3" [0, 1]) count service claim).bind
        (fun pc => .done (reduceRootResults pc)) := by
  have childVerifier : self = (ctx.enter "s3" [0, 1]).roles 1 := verifier
  have childSeparate : (ctx.enter "s3" [0, 1]).roles 0 ≠ self := separate
  refine (root_context_expansion ctx self verifier separate xs dimension claim count service).trans ?_
  have child := (reduce_invoke_plain (F := F) (G := G) (ctx.enter "s3" [0, 1]) self
      (reduceArguments none none none claim count service)).trans
    (reduce_optional unit helperBodies (ctx.enter "s3" [0, 1]) self childVerifier childSeparate
      4 none none none claim count service)
  exact (congrArg (fun (process : PIR.Proc (participantInterface F G)
      (Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs)) => process.bind
      (fun result => PIR.Proc.done (reduceRootResults
        (result.get (.there (.there (.there (.there .here)))),
          result.get (.there (.there (.there (.there (.there .here))))))))) child).trans
    (select_reduceResults _)

/-- The actual complete source participant, including original root input and
output masks and the original child selected in its full protocol table. -/
theorem verifier_optional (xs : Option (List F)) (dimension : Option Nat)
    (claim : Option F) (count service : Option Nat) :
    program.participant F G 1 (reduceRootInputs xs dimension claim count service) =
      (admittedRounds 4 (ProtocolContext.enter {} "s3" [0, 1]) count service claim).bind
        (fun pc => .done (reduceRootResults pc)) :=
  (unit.protocolTable_forgetSites (F := F) (G := G)
    SumcheckReduceBodies.runSignature {} 1 (reduceRootInputs xs dimension claim count service)).trans
    (verifier_context_optional {} 1 rfl (by decide) xs dimension claim count service)

/-- Missing root count is incomplete even if the other arguments are present. -/
theorem verifier_missing (xs : Option (List F)) (dimension : Option Nat)
    (claim : Option F) (service : Option Nat) :
    program.participant F G 1 (reduceRootInputs xs dimension claim none service) =
      .halt .incomplete :=
  (verifier_optional xs dimension claim none service).trans rfl

/-- Counts above the original maximum four are refused before any callback. -/
theorem verifier_excess (xs : Option (List F)) (dimension : Option Nat)
    (claim : Option F) (count : Nat) (large : 4 < count) (service : Option Nat) :
    program.participant F G 1 (reduceRootInputs xs dimension claim (some count) service) =
      .halt .refused := by
  refine (verifier_optional xs dimension claim (some count) service).trans ?_
  rw [admittedRounds_excess 4 count _ large]
  rfl

/-- With zero rounds, the actual root returns emptyV and the unchanged optional
claim, including absent claim or absent service. -/
theorem verifier_zero (xs : Option (List F)) (dimension : Option Nat)
    (claim : Option F) (service : Option Nat) :
    program.participant F G 1 (reduceRootInputs xs dimension claim (some 0) service) =
      .done (reduceRootResults (some [], claim)) := by
  refine (verifier_optional xs dimension claim (some 0) service).trans ?_
  rw [admittedRounds_zero]
  rfl

/-- A distinct caller mapping and nonempty prefix retain the same real root. -/
theorem verifier_permuted_optional (xs : Option (List F)) (dimension : Option Nat)
    (claim : Option F) (count service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.runSignature
      ⟨some "outer", roleSubstitution [2, 0]⟩ 0
      (reduceRootInputs xs dimension claim count service) =
      (admittedRounds 4
        (ProtocolContext.enter ⟨some "outer", roleSubstitution [2, 0]⟩ "s3" [0, 1])
        count service claim).bind (fun pc => .done (reduceRootResults pc)) :=
  verifier_context_optional _ 0 rfl (by decide) xs dimension claim count service

/-- Successful execution of the actual complete root returns exactly one point
entry per admitted round. Zero preserves the optional claim; a positive return
has a present claim. Every interaction reply and phase remains quantified. -/
theorem verifier_returns (P : PIR.Interaction (participantInterface F G))
    (xs : Option (List F)) (dimension : Option Nat) (claim : Option F)
    (count : Nat) (bounded : count ≤ 4) (service : Option Nat) (phase : P.Phase) :
    PIR.Boundary.Returns P (fun result _ =>
      ∃ point current, result = reduceRootResults (G := G) (some point, current) ∧
        point.length = count ∧ (count = 0 → current = claim) ∧
        (0 < count → current.isSome = true))
      (program.participant F G 1 (reduceRootInputs xs dimension claim (some count) service))
      phase := by
  rw [verifier_optional]
  simp only [admittedRounds, bounded, ↓reduceIte]
  apply PIR.Boundary.returns_bind P _ _
    (fun result _ => ∃ point, result.1 = some point ∧ point.length = count ∧
      (count = 0 → result.2 = claim) ∧ (0 < count → result.2.isSome = true))
  · simpa only [List.length_nil, Nat.zero_add] using
      (SumcheckVerifierLaws.repeat_returns P (ProtocolContext.enter {} "s3" [0, 1])
        service count [] claim phase)
  · intro result nextPhase returned
    obtain ⟨point, present, length, zeroClaim, positiveClaim⟩ := returned
    exact ⟨point, result.2, congrArg (reduceRootResults (G := G)) (Prod.ext present rfl),
      length, zeroClaim, positiveClaim⟩

end ZkcExamples.Structured.SumcheckReduceVerifier
