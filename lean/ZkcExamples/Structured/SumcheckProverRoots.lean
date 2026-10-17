module

public import ZkcExamples.Structured.SumcheckProverPrelude
public import ZkcExamples.Structured.SumcheckSourceVerifier
public import ZkcExamples.Structured.SumcheckSourceContracts
public import ZkcExamples.Structured.SumcheckReduceVerifier
public import ZkcExamples.Structured.SumcheckReduceContracts

@[expose] public section

/-! Plain prover equations of both complete original roots: the actual table
constructor, the child Reduce at the prover and, for Source, the skipped
verifier terminal. The verifier's inputs are absent at the prover. -/
namespace ZkcExamples.Structured.SumcheckProverRoots
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary
open SumcheckVerifierPrelude SumcheckVerifierHelpers SumcheckProverLaws
open Zkc.Polynomial.Multilinear (restrictPrefixValues)

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

private abbrev oneResult {ty : Ty} (value : Option (assignment F G ty)) :
    Values (Component (assignment F G)) [ty] :=
  .cons value .nil

/-! ### Complete Source root -/

section Source
open SumcheckSourceViews

/-- The literal Source root body at the prover, for present prover inputs. -/
private theorem source_body_prover (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (raw : List F) (rounds : Nat) (shape : HasShape raw rounds 1)
    (bound : raw.length < indexLimit) (admitted : rounds ≤ 2) :
    SumcheckSourceBodies.runBody.denote
      (participantMeaningWith (.silent _) (participantActions F G)
        (plainHelpers unit) (ctx.roles 0) (unit.plainProtocolTable F G) ctx)
      (SumcheckSourceVerifier.sourceRootInputs (G := G) (some raw) none (some rounds) none).get =
      (PIR.repeatN rounds (roundHonest (ctx.enter "label_726564756365" [0, 1]) raw rounds) []).bind
        (fun _ => .done (.cons none .nil)) := by
  have roundsBound : rounds < indexLimit := Nat.lt_trans shape.2.1 (by decide +kernel)
  let m := participantMeaningWith (.silent (participantInterface F G)) (participantActions F G)
    (plainHelpers unit) (ctx.roles 0) (unit.plainProtocolTable F G) ctx
  unfold SumcheckSourceBodies.runBody
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.calculate (.indexConstant 1) rfl) _ .nil _ _
    (oneResult (G := G) (ty := .index) (some 1)) ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.mark "s1") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.localCall SumcheckSourceBodies.tableHelper rfl 0 "s1") _ .nil _ _
    (.cons (some raw) (.cons (some rounds) (.cons (some 1) .nil))) ?_).trans ?_
  · change Participant.owned (ctx.roles 0) (ctx.roles 0)
      (invoke (plainHelpers (F := F) (G := G) unit).closed SumcheckSourceBodies.tableHelper)
      (Values.cons raw (.cons rounds (.cons 1 .nil))).present = _
    rw [Participant.owned_present, closed_invoke_plain]
    change (PIR.Proc.interpret closedLift (invoke (closedMeanings (F := F) (G := G) unit.definitions)
      MapFirstBodies.tableHelper (inputs raw rounds 1))).bind _ = _
    rw [(SumcheckUnitContracts.first_laws unit.linked SumcheckSourceContracts.bodies).tableLaw
      raw rounds 1 bound roundsBound (by decide +kernel)]
    simp only [shape, ↓reduceIte]
    rfl
  refine (Region.denote_letOp_done m (.mark "label_726564756365") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_values m
    (.protocolApply SumcheckSourceBodies.reduceSignature [0, 1] "label_726564756365") _ .nil _ _).trans ?_
  have active : (ctx.enter "label_726564756365" [0, 1]).contains
      SumcheckSourceBodies.reduceSignature (ctx.roles 0) = true := by
    apply (ProtocolContext.contains_iff _ _ _).mpr
    exact ⟨0, by decide, rfl⟩
  change ((if (ctx.enter "label_726564756365" [0, 1]).contains
      SumcheckSourceBodies.reduceSignature (ctx.roles 0) then
      invokeProtocol (unit.plainProtocolTable F G) SumcheckSourceBodies.reduceSignature
        (ctx.enter "label_726564756365" [0, 1]) (ctx.roles 0)
        (reduceArguments (G := G) (some raw) (some rounds) (some 1) none (some rounds) none)
    else .done (Values.absent (assignment F G) SumcheckSourceBodies.reduceSignature.outputs)).bind _) = _
  rw [ite_eq_left_iff.mpr (fun inactive => absurd active inactive),
    SumcheckSourceVerifier.reduce_invoke_plain,
    reduce_prover unit SumcheckSourceContracts.bodies (ctx.enter "label_726564756365" [0, 1])
      (ctx.roles 0) rfl separate 2 raw rounds shape bound rounds admitted (Nat.le_refl _) none none]
  refine (PIR.Proc.bind_assoc _ _ _).trans (congrArg (PIR.Proc.bind _) (funext fun point => ?_))
  simp only [PIR.Proc.bind]
  refine (Region.denote_letOp_done m (.mark "s7") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.localCall SumcheckSourceBodies.checkHelper rfl 1 "s7") _ .nil _ _
    (oneResult (G := G) (ty := .boolean) none) ?_).trans ?_
  · change Participant.owned (ctx.roles 0) (ctx.roles 1)
      (invoke (plainHelpers (F := F) (G := G) unit).closed SumcheckSourceBodies.checkHelper)
      (.cons (some raw) (.cons none (.cons none .nil))) = _
    rw [Participant.owned_other _ _ separate]
    rfl
  rfl

/-- The complete Source root at the prover in an arbitrary caller context: the
checked table, the actual maximum-two Reduce on the prover's own state, and no
terminal. -/
theorem source_context_prover (ctx : ProtocolContext) (self : Nat)
    (prover : self = ctx.roles 0) (separate : ctx.roles 1 ≠ self)
    (raw : List F) (rounds : Nat) (shape : HasShape raw rounds 1)
    (bound : raw.length < indexLimit) (admitted : rounds ≤ 2)
    (claim : Option F) (service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckSourceBodies.runSignature ctx self
      (SumcheckSourceVerifier.sourceRootInputs (some raw) claim (some rounds) service) =
      (PIR.repeatN rounds (roundHonest (ctx.enter "label_726564756365" [0, 1]) raw rounds) []).bind
        (fun _ => .done (.cons none .nil)) := by
  refine (protocol_invoke_body_view (.silent _) (participantActions F G)
    (plainHelpers unit) unit.protocols unit.protocolsLinked
    runDefinition run_member SumcheckSourceBodies.runBody run_raw ctx self
    (SumcheckSourceVerifier.sourceRootInputs (some raw) claim (some rounds) service)).trans ?_
  have inputs : maskValues self (ctx.mapScopes SumcheckSourceBodies.runSignature.inputScopes)
      (SumcheckSourceVerifier.sourceRootInputs (G := G) (some raw) claim (some rounds) service) =
      SumcheckSourceVerifier.sourceRootInputs (some raw) none (some rounds) none := by
    subst self
    unfold SumcheckSourceVerifier.sourceRootInputs
    dsimp only [SumcheckSourceBodies.runSignature]
    iterate 5 unfold maskValues
    simp [ProtocolContext.mapScopes, Participant.restrict, Ne.symm separate]
  change (SumcheckSourceBodies.runBody.denote
    (participantMeaningWith (.silent _) (participantActions F G)
      (plainHelpers unit) self (unit.plainProtocolTable F G) ctx)
    (maskValues self (ctx.mapScopes SumcheckSourceBodies.runSignature.inputScopes)
      (SumcheckSourceVerifier.sourceRootInputs (some raw) claim (some rounds) service)).get).bind
      (fun result => .done
        (maskValues self (ctx.mapScopes SumcheckSourceBodies.runSignature.outputScopes) result)) = _
  rw [inputs]
  subst self
  rw [source_body_prover ctx separate raw rounds shape bound admitted]
  refine (PIR.Proc.bind_assoc _ _ _).trans (congrArg (PIR.Proc.bind _) (funext fun point => ?_))
  change PIR.Proc.done (maskValues (ctx.roles 0)
    (ctx.mapScopes SumcheckSourceBodies.runSignature.outputScopes) (.cons none .nil)) = _
  simp [SumcheckSourceBodies.runSignature, ProtocolContext.mapScopes, maskValues, Participant.restrict]

/-- The complete Source root at the prover. -/
theorem source_prover (raw : List F) (rounds : Nat) (shape : HasShape raw rounds 1)
    (bound : raw.length < indexLimit) (admitted : rounds ≤ 2)
    (claim : Option F) (service : Option Nat) :
    program.participant F G 0
      (SumcheckSourceVerifier.sourceRootInputs (some raw) claim (some rounds) service) =
      (PIR.repeatN rounds (roundHonest SumcheckSourceVerifier.childContext raw rounds) []).bind
        (fun _ => .done (.cons none .nil)) :=
  (unit.protocolTable_forgetSites (F := F) (G := G)
    SumcheckSourceBodies.runSignature {} 0
    (SumcheckSourceVerifier.sourceRootInputs (some raw) claim (some rounds) service)).trans
    (source_context_prover {} 0 rfl (by decide) raw rounds shape bound admitted claim service)

end Source

/-! ### Complete Reduction root -/

section Reduction
open SumcheckReduceViews

/-- The prover's two returned root components, the received point and the
residual entries; the verifier's point and claim are absent. -/
def reductionResults (raw : List F) (point : List F) :
    Values (Component (assignment F G)) SumcheckReduceBodies.runSignature.outputs :=
  .cons (some point) (.cons (some (restrictPrefixValues raw point)) (.cons none (.cons none .nil)))

/-- The literal Reduction root body at the prover, for present prover inputs. -/
private theorem reduction_body_prover (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (raw : List F) (count rounds : Nat) (shape : HasShape raw count 1)
    (bound : raw.length < indexLimit) (admitted : rounds ≤ 4) (enough : rounds ≤ count) :
    SumcheckReduceBodies.runBody.denote
      (participantMeaningWith (.silent _) (participantActions F G)
        (plainHelpers unit) (ctx.roles 0) (unit.plainProtocolTable F G) ctx)
      (SumcheckReduceVerifier.reduceRootInputs (G := G) (some raw) (some count) none (some rounds)
        none).get =
      (PIR.repeatN rounds (roundHonest (ctx.enter "s3" [0, 1]) raw count) []).bind
        (fun point => .done (reductionResults (G := G) raw point)) := by
  have countBound : count < indexLimit := Nat.lt_trans shape.2.1 (by decide +kernel)
  have verifierBodies : SumcheckVerifierHelpers.Bodies unit.definitions :=
    SumcheckReduceVerifier.helperBodies
  let m := participantMeaningWith (.silent (participantInterface F G)) (participantActions F G)
    (plainHelpers unit) (ctx.roles 0) (unit.plainProtocolTable F G) ctx
  unfold SumcheckReduceBodies.runBody
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.calculate (.indexConstant 1) rfl) _ .nil _ _
    (oneResult (G := G) (ty := .index) (some 1)) ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.mark "s1") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.localCall SumcheckReduceBodies.tableHelper rfl 0 "s1") _ .nil _ _
    (.cons (some raw) (.cons (some count) (.cons (some 1) .nil))) ?_).trans ?_
  · change Participant.owned (ctx.roles 0) (ctx.roles 0)
      (invoke (plainHelpers (F := F) (G := G) unit).closed SumcheckReduceBodies.tableHelper)
      (Values.cons raw (.cons count (.cons 1 .nil))).present = _
    rw [Participant.owned_present, closed_invoke_plain]
    change (PIR.Proc.interpret closedLift (invoke (closedMeanings (F := F) (G := G) unit.definitions)
      MapFirstBodies.tableHelper (inputs raw count 1))).bind _ = _
    rw [(SumcheckUnitContracts.first_laws unit.linked SumcheckReduceContracts.bodies).tableLaw
      raw count 1 bound countBound (by decide +kernel)]
    simp only [shape, ↓reduceIte]
    rfl
  refine (Region.denote_letOp_done m (.mark "s3") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_values m
    (.protocolApply SumcheckReduceBodies.reduceSignature [0, 1] "s3") _ .nil _ _).trans ?_
  have active : (ctx.enter "s3" [0, 1]).contains
      SumcheckReduceBodies.reduceSignature (ctx.roles 0) = true := by
    apply (ProtocolContext.contains_iff _ _ _).mpr
    exact ⟨0, by decide, rfl⟩
  change ((if (ctx.enter "s3" [0, 1]).contains
      SumcheckReduceBodies.reduceSignature (ctx.roles 0) then
      invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.reduceSignature
        (ctx.enter "s3" [0, 1]) (ctx.roles 0)
        (reduceArguments (G := G) (some raw) (some count) (some 1) none (some rounds) none)
    else .done (Values.absent (assignment F G) SumcheckReduceBodies.reduceSignature.outputs)).bind _) = _
  rw [ite_eq_left_iff.mpr (fun inactive => absurd active inactive),
    SumcheckReduceVerifier.reduce_invoke_plain,
    reduce_prover unit SumcheckReduceContracts.bodies (ctx.enter "s3" [0, 1])
      (ctx.roles 0) rfl separate 4 raw count shape bound rounds admitted enough none none]
  refine (PIR.Proc.bind_assoc _ _ _).trans (congrArg (PIR.Proc.bind _) (funext fun point => ?_))
  simp only [PIR.Proc.bind]
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.calculate (.invoke MapFirstBodies.valuesHelper) rfl) _ .nil _ _
    (oneResult (G := G) (ty := .vector "bls12-381.fr") (some (restrictPrefixValues raw point))) ?_).trans ?_
  · change invoke (plainHelpers (F := F) (G := G) unit).components MapFirstBodies.valuesHelper
      (.cons (some (restrictPrefixValues raw point)) (.cons (some (count - point.length))
        (.cons (some 1) .nil))) = _
    rw [values_optional unit verifierBodies]
    rfl
  rfl

/-- The complete Reduction root at the prover in an arbitrary caller context: the
checked table, the actual maximum-four Reduce and the residual projection. -/
theorem reduction_context_prover (ctx : ProtocolContext) (self : Nat)
    (prover : self = ctx.roles 0) (separate : ctx.roles 1 ≠ self)
    (raw : List F) (count rounds : Nat) (shape : HasShape raw count 1)
    (bound : raw.length < indexLimit) (admitted : rounds ≤ 4) (enough : rounds ≤ count)
    (claim : Option F) (service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.runSignature ctx self
      (SumcheckReduceVerifier.reduceRootInputs (some raw) (some count) claim (some rounds) service) =
      (PIR.repeatN rounds (roundHonest (ctx.enter "s3" [0, 1]) raw count) []).bind
        (fun point => .done (reductionResults raw point)) := by
  refine (protocol_invoke_body_view (.silent _) (participantActions F G)
    (plainHelpers unit) unit.protocols unit.protocolsLinked
    runDefinition run_member SumcheckReduceBodies.runBody run_raw ctx self
    (SumcheckReduceVerifier.reduceRootInputs (some raw) (some count) claim (some rounds)
      service)).trans ?_
  have inputs : maskValues self (ctx.mapScopes SumcheckReduceBodies.runSignature.inputScopes)
      (SumcheckReduceVerifier.reduceRootInputs (G := G) (some raw) (some count) claim (some rounds)
        service) =
      SumcheckReduceVerifier.reduceRootInputs (some raw) (some count) none (some rounds) none := by
    subst self
    unfold SumcheckReduceVerifier.reduceRootInputs
    dsimp only [SumcheckReduceBodies.runSignature]
    iterate 6 unfold maskValues
    simp [ProtocolContext.mapScopes, Participant.restrict, Ne.symm separate]
  change (SumcheckReduceBodies.runBody.denote
    (participantMeaningWith (.silent _) (participantActions F G)
      (plainHelpers unit) self (unit.plainProtocolTable F G) ctx)
    (maskValues self (ctx.mapScopes SumcheckReduceBodies.runSignature.inputScopes)
      (SumcheckReduceVerifier.reduceRootInputs (some raw) (some count) claim (some rounds)
        service)).get).bind
      (fun result => .done
        (maskValues self (ctx.mapScopes SumcheckReduceBodies.runSignature.outputScopes) result)) = _
  rw [inputs]
  subst self
  rw [reduction_body_prover ctx separate raw count rounds shape bound admitted enough]
  refine (PIR.Proc.bind_assoc _ _ _).trans (congrArg (PIR.Proc.bind _) (funext fun point => ?_))
  change PIR.Proc.done (maskValues (ctx.roles 0)
    (ctx.mapScopes SumcheckReduceBodies.runSignature.outputScopes) (reductionResults raw point)) = _
  simp [SumcheckReduceBodies.runSignature, ProtocolContext.mapScopes, maskValues,
    Participant.restrict, reductionResults, Ne.symm separate]

/-- The complete Reduction root at the prover. -/
theorem reduction_prover (raw : List F) (count rounds : Nat) (shape : HasShape raw count 1)
    (bound : raw.length < indexLimit) (admitted : rounds ≤ 4) (enough : rounds ≤ count)
    (claim : Option F) (service : Option Nat) :
    program.participant F G 0
      (SumcheckReduceVerifier.reduceRootInputs (some raw) (some count) claim (some rounds) service) =
      (PIR.repeatN rounds (roundHonest (ProtocolContext.enter {} "s3" [0, 1]) raw count) []).bind
        (fun point => .done (reductionResults raw point)) :=
  (unit.protocolTable_forgetSites (F := F) (G := G)
    SumcheckReduceBodies.runSignature {} 0
    (SumcheckReduceVerifier.reduceRootInputs (some raw) (some count) claim (some rounds)
      service)).trans
    (reduction_context_prover {} 0 rfl (by decide) raw count rounds shape bound admitted enough
      claim service)

end Reduction

end ZkcExamples.Structured.SumcheckProverRoots
