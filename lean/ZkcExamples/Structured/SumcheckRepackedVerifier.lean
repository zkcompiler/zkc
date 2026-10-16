module

public import ZkcExamples.Structured.SumcheckRepackedViews
public import ZkcExamples.Structured.SumcheckReduceVerifier

@[expose] public section

/-! Plain verifier equations for the complete repacked Reduction unit. The
child Reduce, its helpers and the repeat laws are the retained Reduction's;
only the root's input masks, operand positions and return order are new. -/
namespace ZkcExamples.Structured.SumcheckRepackedVerifier
open Zkc.Source Zkc.Source.Structured
open SumcheckRepackedViews SumcheckRepackedBodies

/-- The repacked unit has exactly the retained Reduction's helper list. -/
theorem helperBodies : SumcheckVerifierHelpers.Bodies unit.definitions :=
  SumcheckReduceVerifier.helperBodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

open SumcheckVerifierHelpers SumcheckVerifierPrelude

/-- Full signature, member and raw tree select the same child in this table. -/
theorem reduce_invoke_plain (ctx : ProtocolContext) (self : Nat)
    (arguments : Values (Component (assignment F G)) SumcheckVerifierBodies.reduceInputs) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.reduceSignature
      ctx self arguments = reduceDenote 4 unit ctx self arguments := by
  exact protocol_invoke_body_view (.silent _) (participantActions F G) (plainHelpers unit)
    unit.protocols unit.protocolsLinked SumcheckReduceViews.reduceDefinition reduce_member
    (SumcheckVerifierBodies.reduceBody 4) SumcheckReduceVerifier.reduce_raw_shared ctx self arguments

/-- Inputs in the repacked order: claim, rounds, variables, values, challenges. -/
def rootInputs (claim : Option F) (count dimension : Option Nat) (xs : Option (List F))
    (service : Option Nat) : Values (Component (assignment F G)) runSignature.inputs :=
  .cons claim (.cons count (.cons dimension (.cons xs (.cons service .nil))))

/-- Outputs in the repacked order: V's point and value first, then P's values. -/
def rootResults (pc : Option (List F) × Option F) :
    Values (Component (assignment F G)) runSignature.outputs :=
  .cons pc.1 (.cons pc.2 (.cons none (.cons none .nil)))

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem mask_rootInputs (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (claim : Option F) (count dimension : Option Nat) (xs : Option (List F))
    (service : Option Nat) :
    maskValues self (ctx.mapScopes runSignature.inputScopes)
      (rootInputs (G := G) claim count dimension xs service) =
        rootInputs claim count none none service := by
  subst self
  unfold rootInputs
  dsimp only [runSignature]
  iterate 6 unfold maskValues
  simp [ProtocolContext.mapScopes, Participant.restrict, Ne.symm separate]

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem mask_rootTuple (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (pointV : Option (List F)) (claim : Option F) (valuesP pointP : Option (List F)) :
    maskValues self (ctx.mapScopes runSignature.outputScopes)
      (Values.cons pointV (.cons claim (.cons valuesP (.cons pointP .nil)))) =
        rootResults (G := G) (pointV, claim) := by
  subst self
  iterate 5 unfold maskValues
  simp [runSignature, ProtocolContext.mapScopes, Participant.restrict, Ne.symm separate, rootResults]

/-- The literal repacked root body, evaluated under an arbitrary complete unit. -/
private theorem run_body_context_expansion (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (claim : Option F) (count dimension : Option Nat) (xs : Option (List F))
    (service : Option Nat) :
    ((runBody.denote
      (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers U)
        self (U.plainProtocolTable F G) ctx)
      (maskValues self (ctx.mapScopes runSignature.inputScopes)
        (rootInputs claim count dimension xs service)).get).bind
      (fun result => .done
        (maskValues self (ctx.mapScopes runSignature.outputScopes) result))) =
      (invokeProtocol (U.plainProtocolTable F G) SumcheckReduceBodies.reduceSignature
        (ctx.enter "s3" [0, 1]) self
        (reduceArguments none none none claim count service)).bind
        (fun result => .done (rootResults
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
                (ctx.mapScopes runSignature.outputScopes)
                (.cons pointV (.cons current (.cons valuesP (.cons pointP .nil))))) = _
              rw [mask_rootTuple ctx (ctx.roles 1) rfl separate]
              rfl

/-- The repacked root skips P's table construction, calls the same Reduce at
s3 and returns V's point and value in its own first two positions. -/
theorem root_context_expansion (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (claim : Option F) (count dimension : Option Nat) (xs : Option (List F))
    (service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) runSignature
      ctx self (rootInputs claim count dimension xs service) =
      (invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.reduceSignature
        (ctx.enter "s3" [0, 1]) self
        (reduceArguments none none none claim count service)).bind
        (fun result => .done (rootResults
          (result.get (.there (.there (.there (.there .here)))),
            result.get (.there (.there (.there (.there (.there .here)))))))) :=
  (protocol_invoke_body_view (.silent _) (participantActions F G) (plainHelpers unit)
    unit.protocols unit.protocolsLinked runDefinition run_member
    runBody run_raw ctx self (rootInputs claim count dimension xs service)).trans
      (run_body_context_expansion unit helperBodies ctx self verifier separate
        claim count dimension xs service)

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem select_reduceResults
    (process : PIR.Proc (participantInterface F G) (Option (List F) × Option F)) :
    (process.bind (fun pc => .done (reduceResults (G := G) pc))).bind
      (fun result => .done (rootResults
        (result.get (.there (.there (.there (.there .here)))),
          result.get (.there (.there (.there (.there (.there .here)))))))) =
      process.bind (fun pc => .done (rootResults (G := G) pc)) := by
  rw [PIR.Proc.bind_assoc]
  rfl

theorem verifier_context_optional (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (claim : Option F) (count dimension : Option Nat) (xs : Option (List F))
    (service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) runSignature
      ctx self (rootInputs claim count dimension xs service) =
      (admittedRounds 4 (ctx.enter "s3" [0, 1]) count service claim).bind
        (fun pc => .done (rootResults pc)) := by
  have childVerifier : self = (ctx.enter "s3" [0, 1]).roles 1 := verifier
  have childSeparate : (ctx.enter "s3" [0, 1]).roles 0 ≠ self := separate
  refine (root_context_expansion ctx self verifier separate claim count dimension xs service).trans ?_
  have child := (reduce_invoke_plain (F := F) (G := G) (ctx.enter "s3" [0, 1]) self
      (reduceArguments none none none claim count service)).trans
    (reduce_optional unit helperBodies (ctx.enter "s3" [0, 1]) self childVerifier childSeparate
      4 none none none claim count service)
  exact (congrArg (fun (process : PIR.Proc (participantInterface F G)
      (Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs)) => process.bind
      (fun result => PIR.Proc.done (rootResults
        (result.get (.there (.there (.there (.there .here)))),
          result.get (.there (.there (.there (.there (.there .here))))))))) child).trans
    (select_reduceResults _)

/-- The actual complete repacked participant V. -/
theorem verifier_optional (claim : Option F) (count dimension : Option Nat)
    (xs : Option (List F)) (service : Option Nat) :
    program.participant F G 1 (rootInputs claim count dimension xs service) =
      (admittedRounds 4 (ProtocolContext.enter {} "s3" [0, 1]) count service claim).bind
        (fun pc => .done (rootResults pc)) :=
  (unit.protocolTable_forgetSites (F := F) (G := G)
    runSignature {} 1 (rootInputs claim count dimension xs service)).trans
    (verifier_context_optional {} 1 rfl (by decide) claim count dimension xs service)

theorem verifier_excess (claim : Option F) (count : Nat) (large : 4 < count)
    (dimension : Option Nat) (xs : Option (List F)) (service : Option Nat) :
    program.participant F G 1 (rootInputs claim (some count) dimension xs service) =
      .halt .refused := by
  refine (verifier_optional claim (some count) dimension xs service).trans ?_
  rw [admittedRounds_excess 4 count _ large]
  rfl

/-- Process-level repacking: the repacked participant is the retained one with
inputs read in the retained order and outputs returned in the repacked order. -/
theorem participant_repacked (claim : Option F) (count dimension : Option Nat)
    (xs : Option (List F)) (service : Option Nat) :
    program.participant F G 1 (rootInputs claim count dimension xs service) =
      (SumcheckReduceViews.program.participant F G 1
        (SumcheckReduceVerifier.reduceRootInputs xs dimension claim count service)).bind
        (fun outputs => .done (rootResults
          (outputs.get (.there (.there .here)), outputs.get (.there (.there (.there .here)))))) := by
  rw [verifier_optional, SumcheckReduceVerifier.verifier_optional]
  refine Eq.trans ?_ (PIR.Proc.bind_assoc _ _ _).symm
  rfl

end ZkcExamples.Structured.SumcheckRepackedVerifier
