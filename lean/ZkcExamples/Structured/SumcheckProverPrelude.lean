module

public import ZkcExamples.Structured.SumcheckProverLaws
public import ZkcExamples.Structured.SumcheckVerifierPrelude

@[expose] public section

/-! The complete shared Reduce body at the prover: its width and dimension
guards, the empty point, the admitted repeat on the prover's own state and the
actual six-slot return permutation. Only present prover inputs are covered;
the verifier's claim and service are absent at the prover. -/
namespace ZkcExamples.Structured.SumcheckProverPrelude
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary
open SumcheckVerifierBodies SumcheckVerifierHelpers SumcheckVerifierLaws SumcheckVerifierPrelude
open SumcheckProverLaws
open Zkc.Polynomial.Multilinear (restrictPrefixValues)

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The prover's four returned components: its point, residual entries, remaining
dimension and width. The verifier's point and claim are absent. -/
def proverResults (raw : List F) (count : Nat) (point : List F) :
    Values (Component (assignment F G)) reduceOutputs :=
  .cons (some point) (.cons (some (restrictPrefixValues raw point))
    (.cons (some (count - point.length)) (.cons (some 1) (.cons none (.cons none .nil)))))

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem mask_proverArguments (ctx : ProtocolContext) (self : Nat)
    (prover : self = ctx.roles 0) (separate : ctx.roles 1 ≠ self)
    (raw : List F) (count : Nat) (claim : Option F) (rounds service : Option Nat) :
    maskValues self (ctx.mapScopes reduceInputScopes)
      (reduceArguments (G := G) (some raw) (some count) (some 1) claim rounds service) =
        reduceArguments (some raw) (some count) (some 1) none rounds none := by
  subst self
  unfold reduceArguments
  iterate 7 unfold maskValues
  simp [reduceInputScopes, ProtocolContext.mapScopes, Participant.restrict, Ne.symm separate]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem mask_proverResults (ctx : ProtocolContext) (self : Nat)
    (prover : self = ctx.roles 0) (raw : List F) (count : Nat) (point : List F) :
    maskValues self (ctx.mapScopes reduceOutputScopes) (proverResults (G := G) raw count point) =
      proverResults raw count point := by
  subst self
  unfold proverResults
  iterate 7 unfold maskValues
  simp [reduceOutputScopes, ProtocolContext.mapScopes, Participant.restrict]

private abbrev oneResult {ty : Ty} (value : Option (assignment F G ty)) :
    Values (Component (assignment F G)) [ty] :=
  .cons value .nil

/-- The prelude at the prover: width one, enough variables for the requested
rounds, the empty point, then the actual repeat with the six-slot return. -/
theorem prelude_prover (U : UnitPayload) (bodies : SumcheckUnitContracts.Bodies U.definitions)
    (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0) (maximum : Nat)
    (raw : List F) (count rounds : Nat) (countBound : count < indexLimit)
    (roundsBound : rounds < indexLimit) (enough : rounds ≤ count) :
    (reduceBody maximum).denote
      (participantMeaningWith (.silent _) (participantActions F G)
        (plainHelpers U) (ctx.roles 0) (U.plainProtocolTable F G) ctx)
      (reduceArguments (G := G) (some raw) (some count) (some 1) none (some rounds) none).get =
      (denoteRepeat (repeatSpec maximum) ctx (ctx.roles 0) (some rounds)
        (embedP (G := G) (honestState raw count [])) (cap none)
        (bodyFn U ctx (ctx.roles 0))).bind (fun state => .done (returnValues state)) := by
  have verifierBodies : SumcheckVerifierHelpers.Bodies U.definitions :=
    ⟨bodies.empty, bodies.append, bodies.width, bodies.«variables», bodies.values⟩
  let m := participantMeaningWith (.silent (participantInterface F G)) (participantActions F G)
    (plainHelpers U) (ctx.roles 0) (U.plainProtocolTable F G) ctx
  unfold reduceBody
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.calculate (.invoke MapFirstBodies.widthHelper) rfl) _ .nil _ _
    (oneResult (G := G) (ty := .index) (some 1)) ?_).trans ?_
  · change invoke (plainHelpers (F := F) (G := G) U).components MapFirstBodies.widthHelper
      (.cons (some raw) (.cons (some count) (.cons (some 1) .nil))) = _
    rw [width_optional U verifierBodies]
    rfl
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.calculate (.indexConstant 1) rfl) _ .nil _ _
    (oneResult (G := G) (ty := .index) (some 1)) ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.calculate .indexEqual rfl) _ .nil _ _
    (oneResult (G := G) (ty := .boolean) (some true)) ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.mark "s3") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.guard 0 "s3") _ .nil _ _ .nil ?_).trans ?_
  · change (((Participant.guard (services := services) (Value := assignment F G)
      (ctx.roles 0) (ctx.roles 0) (some true)).interpret (participantActions F G)).bind
      (fun _ => .done (Values.nil : Values (Component (assignment F G)) []))) = _
    simp only [Participant.guard, ↓reduceIte, PIR.Proc.interpret, PIR.Proc.bind]
    rfl
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.calculate (.invoke MapFirstBodies.variablesHelper) rfl) _ .nil _ _
    (oneResult (G := G) (ty := .index) (some count)) ?_).trans ?_
  · change invoke (plainHelpers (F := F) (G := G) U).components MapFirstBodies.variablesHelper
      (.cons (some raw) (.cons (some count) (.cons (some 1) .nil))) = _
    rw [variables_optional U verifierBodies]
    rfl
  refine (Region.denote_letOp_done m (.mark "s5") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.localCall MapFirstBodies.lessHelper rfl 0 "s5") _ .nil _ _
    (oneResult (G := G) (ty := .boolean) (some (decide (count < rounds)))) ?_).trans ?_
  · change Participant.owned (ctx.roles 0) (ctx.roles 0)
      (invoke (plainHelpers (F := F) (G := G) U).closed MapFirstBodies.lessHelper)
      (Values.cons count (.cons rounds .nil)).present = _
    rw [Participant.owned_present, closed_invoke_plain,
      (SumcheckUnitContracts.first_laws U.linked bodies).less count rounds]
    simp only [countBound, roundsBound, and_self, ↓reduceIte]
    rfl
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.calculate (.booleanConstant false) rfl) _ .nil _ _
    (oneResult (G := G) (ty := .boolean) (some false)) ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.calculate .booleanEqual rfl) _ .nil _ _
    (oneResult (G := G) (ty := .boolean) (some true)) ?_).trans ?_
  · have notLess : decide (count < rounds) = false := decide_eq_false (Nat.not_lt.mpr enough)
    show Evaluation.componentOperation (.silent _) (plainHelpers (F := F) (G := G) U) .booleanEqual
      (.cons (some (decide (count < rounds))) (.cons (some false) .nil)) .nil = _
    rw [notLess]
    rfl
  refine (Region.denote_letOp_done m (.mark "s8") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.guard 0 "s8") _ .nil _ _ .nil ?_).trans ?_
  · change (((Participant.guard (services := services) (Value := assignment F G)
      (ctx.roles 0) (ctx.roles 0) (some true)).interpret (participantActions F G)).bind
      (fun _ => .done (Values.nil : Values (Component (assignment F G)) []))) = _
    simp only [Participant.guard, ↓reduceIte, PIR.Proc.interpret, PIR.Proc.bind]
    rfl
  refine (Region.denote_letOp_done m (.mark "s10") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.localCall SumcheckHelperBodies.emptyHelper rfl 0 "s10") _ .nil _ _
    (oneResult (G := G) (ty := .vector "bls12-381.fr") (some [])) ?_).trans ?_
  · change Participant.owned (ctx.roles 0) (ctx.roles 0)
      (invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.emptyHelper)
      (Values.nil : Values (assignment F G) []).present = _
    rw [Participant.owned_present, empty_plain U verifierBodies]
    rfl
  refine (Region.denote_letOp_done m (.mark "s12") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.localCall SumcheckHelperBodies.emptyHelper rfl 1 "s12") _ .nil _ _
    (oneResult (G := G) (ty := .vector "bls12-381.fr") none) ?_).trans ?_
  · change Participant.owned (ctx.roles 0) (ctx.roles 1)
      (invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.emptyHelper) .nil = _
    rw [Participant.owned_other _ _ separate]
    rfl
  refine (Region.denote_letOp_done m (.mark "s15") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_values m _ _ _ _ _).trans ?_
  change (denoteRepeat (repeatSpec maximum) ctx (ctx.roles 0) (some rounds)
    (embedP (G := G) (honestState raw count [])) (cap none)
    (bodyFn U ctx (ctx.roles 0))).bind _ = _
  congr 1
  funext state
  exact return_equation m state _

/-- The complete Reduce body at the prover, for present prover inputs whose
table has at least the requested, admitted number of rounds. The verifier's
claim and service inputs are masked away at the prover. -/
theorem reduce_prover (U : UnitPayload) (bodies : SumcheckUnitContracts.Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (prover : self = ctx.roles 0)
    (separate : ctx.roles 1 ≠ self) (maximum : Nat)
    (raw : List F) (count : Nat) (shape : HasShape raw count 1) (bound : raw.length < indexLimit)
    (rounds : Nat) (admitted : rounds ≤ maximum) (enough : rounds ≤ count)
    (claim : Option F) (service : Option Nat) :
    reduceDenote (G := G) maximum U ctx self
      (reduceArguments (some raw) (some count) (some 1) claim (some rounds) service) =
      (PIR.repeatN rounds (roundHonest ctx raw count) []).bind
        (fun point => .done (proverResults raw count point)) := by
  have countBound : count < indexLimit := Nat.lt_trans shape.2.1 (by decide +kernel)
  have roundsBound : rounds < indexLimit := Nat.lt_of_le_of_lt enough countBound
  unfold reduceDenote
  rw [mask_proverArguments ctx self prover separate]
  subst self
  rw [prelude_prover U bodies ctx separate maximum raw count rounds countBound roundsBound enough]
  have inside : ((repeatSpec maximum).roles.map ctx.roles).contains (ctx.roles 0) = true := by
    simp
  rw [repeat_admitted (repeatSpec maximum) ctx (ctx.roles 0) _ _ _ rounds inside admitted,
    mask_embedP ctx (ctx.roles 0) rfl maximum,
    loop_honest U bodies ctx (ctx.roles 0) rfl separate maximum none raw count shape bound 0 rounds []]
  simp only [PIR.Proc.bind_assoc, PIR.Proc.bind]
  congr 1
  funext point
  change PIR.Proc.done (maskValues (ctx.roles 0) (ctx.mapScopes reduceOutputScopes)
    (proverResults raw count point)) = _
  rw [mask_proverResults ctx (ctx.roles 0) rfl]

end ZkcExamples.Structured.SumcheckProverPrelude
