module

public import ZkcExamples.Structured.SumcheckVerifierBodies
public import ZkcExamples.Structured.SumcheckVerifierHelpers
public import ZkcExamples.Structured.SumcheckVerifierLaws
public import Zkc.Source.Structured.RepeatLaws
public import ZkcExamples.Structured.SumcheckPreludeNormalForms

@[expose] public section

/-! Seven-input Pending admission, exact rounds and consuming return of Reduce. -/
namespace ZkcExamples.Structured.SumcheckVerifierPrelude
open Zkc.Source Zkc.Source.Structured
open SumcheckVerifierBodies SumcheckVerifierHelpers

abbrev reduceInputScopes : List (List Nat) := [[0], [0], [0], [1], [1], [0, 1], [1]]
abbrev reduceOutputScopes : List (List Nat) := [[0], [0], [0], [0], [1], [1]]

/-- The literal source permutation, before any participant mask is applied. -/
def returnValues {Value : Ty → Type} (state : Values Value repeatState) :
    Values Value reduceOutputs :=
  SumcheckVerifierBodies.reduceReturnValues state

/-- The suffix consumes the returned Pending through the actual local helper. -/
theorem return_uses_atPrefix :
    ProtocolOp.localCall SumcheckPendingBodies.atPrefixHelper rfl 1 "s48" ∈
      (reduceReturn []).erase.operations := by structured_mem

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def reduceArguments (valuesP : Option (List F)) (dimensionP widthP : Option Nat)
    (point : Option (List F)) (claim : Option F) (count service : Option Nat) :
    Values (Component (assignment F G)) reduceInputs :=
  .cons valuesP (.cons dimensionP (.cons widthP
    (.cons point (.cons claim (.cons count (.cons service .nil))))))

def reduceResults (pc : Option (List F) × Option F) :
    Values (Component (assignment F G)) reduceOutputs :=
  .cons none (.cons none (.cons none (.cons none (.cons pc.1 (.cons pc.2 .nil)))))

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- At the verifier, the returned tuple keeps exactly the verifier's carried point
and claim, wherever the state layout places them. -/
theorem mask_returnValues (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (state : Values (Component (assignment F G)) repeatState) :
    maskValues self (ctx.mapScopes reduceOutputScopes) (returnValues state) =
      reduceResults (state.get SumcheckRoundNormalForms.verifierPointSlot,
        state.get SumcheckRoundNormalForms.verifierClaimSlot) := by
  subst self
  unfold returnValues SumcheckVerifierBodies.reduceReturnValues reduceResults
  iterate 7 unfold maskValues
  simp [reduceOutputScopes, ProtocolContext.mapScopes, Participant.restrict, Ne.symm separate]

def reduceDenote (maximum : Nat) (U : UnitPayload) (ctx : ProtocolContext) (self : Nat)
    (arguments : Values (Component (assignment F G)) reduceInputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) reduceOutputs) :=
  ((reduceBody maximum).denote
    (participantMeaningWith (.silent _) (participantActions F G)
      (plainHelpers U) self (U.plainProtocolTable F G) ctx)
    (maskValues self (ctx.mapScopes reduceInputScopes) arguments).get).bind
      (fun result => .done (maskValues self (ctx.mapScopes reduceOutputScopes) result))

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem mask_reduceArguments (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (valuesP : Option (List F)) (dimensionP widthP : Option Nat)
    (point : Option (List F)) (claim : Option F) (count service : Option Nat) :
    maskValues self (ctx.mapScopes reduceInputScopes)
      (reduceArguments (G := G) valuesP dimensionP widthP point claim count service) =
        reduceArguments none none none point claim count service := by
  subst self
  unfold reduceArguments
  iterate 8 unfold maskValues
  simp [reduceInputScopes, ProtocolContext.mapScopes, Participant.restrict, Ne.symm separate]

/-- Exact checked normal form, including opening and reconstructing Pending. -/
theorem prelude_expansion (U : UnitPayload) (bodies : Bodies U.definitions)
    (claims : SumcheckPendingLaws.Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (maximum : Nat)
    (point : Option (List F)) (claim : Option F) (count service : Option Nat) :
    (reduceBody maximum).denote
      (participantMeaningWith (.silent _) (participantActions F G)
        (plainHelpers U) self (U.plainProtocolTable F G) ctx)
      (reduceArguments none none none point claim count service).get =
      SumcheckPreludeNormalForms.verifierReduceProcess U maximum ctx point claim count service :=
  SumcheckPreludeNormalForms.verifierReduce_process U maximum bodies claims ctx self verifier separate
    point claim count service

open SumcheckVerifierLaws

/-- Ordinary count admission on a complete Pending value. -/
def pendingRounds (maximum : Nat) (ctx : ProtocolContext)
    (point : Option (List F)) (claim : Option F) (count service : Option Nat) :
    PIR.Process (participantInterface F G) (Option (List F) × Option F) :=
  match point, claim with
  | some point, some claim =>
    match count with
    | none => .halt .incomplete
    | some count =>
      if count ≤ maximum then PIR.repeatN count (roundPlain ctx service) (some point, some claim)
      else .halt .refused
  | _, _ => .halt .incomplete

/-- The caller constructs Pending from its scalar before admitting any rounds. -/
def admittedRounds (maximum : Nat) (ctx : ProtocolContext)
    (count service : Option Nat) (claim : Option F) :=
  pendingRounds (G := G) maximum ctx (some []) claim count service

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem admittedRounds_missing (maximum : Nat) (ctx : ProtocolContext)
    (service : Option Nat) (claim : Option F) :
    admittedRounds (G := G) maximum ctx none service claim = .halt .incomplete := by
  cases claim <;> rfl

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem admittedRounds_excess (maximum count : Nat) (ctx : ProtocolContext)
    (large : maximum < count) (service : Option Nat) (claim : F) :
    admittedRounds (G := G) maximum ctx (some count) service (some claim) = .halt .refused := by
  simp only [admittedRounds, pendingRounds, Nat.not_le_of_lt large, ↓reduceIte]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem admittedRounds_zero (maximum : Nat) (ctx : ProtocolContext)
    (service : Option Nat) (claim : F) :
    admittedRounds (G := G) maximum ctx (some 0) service (some claim) =
      .done (some [], some claim) := by
  simp only [admittedRounds, pendingRounds, Nat.zero_le, ↓reduceIte, PIR.repeatN]

/-- Count admission and the maintained round law for a complete initial Pending. -/
theorem repeat_optional (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1) (maximum : Nat)
    (point : List F) (claim : F) (count service : Option Nat) :
    denoteRepeat (repeatSpec maximum) ctx (ctx.roles 1) count
      (embedV (G := G) (some point, some claim)) (cap service) (bodyFn U ctx (ctx.roles 1)) =
      (pendingRounds maximum ctx (some point) (some claim) count service).bind
        (fun pc => .done (embedV pc)) := by
  have inside : ((repeatSpec maximum).roles.map ctx.roles).contains (ctx.roles 1) = true := by simp
  cases count with
  | none => exact repeat_missing_count (repeatSpec maximum) ctx _ _ _ _ inside
  | some count =>
    by_cases bounded : count ≤ maximum
    · rw [repeat_admitted (repeatSpec maximum) ctx _ _ _ _ count inside bounded,
        mask_embedV ctx _ rfl maximum,
        loop_optional U bodies ctx _ rfl separate 0 count maximum]
      simp only [pendingRounds, bounded, ↓reduceIte]
    · rw [repeat_above_maximum (repeatSpec maximum) ctx _ _ _ _ count inside
        (Nat.lt_of_not_ge bounded)]
      simp only [pendingRounds, bounded, ↓reduceIte, PIR.Process.bind]

-- Returned rounds contain both Pending components, including the zero case.
omit [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem finish_rounds (ctx : ProtocolContext) (point : List F) (claim : F)
    (count : Nat) (service : Option Nat) :
    (PIR.repeatN count (roundPlain (G := G) ctx service) (some point, some claim)).bind
      (fun pc => match pc.1 with
        | none => .halt .incomplete
        | some p => match pc.2 with
          | none => .halt .incomplete
          | some c => .done (returnValues (embedV (G := G) (some p, some c)))) =
    (PIR.repeatN count (roundPlain ctx service) (some point, some claim)).bind
      (fun pc => .done (returnValues (embedV (G := G) pc))) := by
  let interaction : PIR.Interaction (participantInterface F G) :=
    ⟨Unit, Unit, fun _ => (), fun _ _ => True, fun _ _ _ => ()⟩
  apply PIR.Boundary.bind_congr_returns interaction _ _ ()
    (repeat_returns interaction ctx service count point (some claim) ())
  intro result phase returned
  obtain ⟨p, hp, _, zero, positive⟩ := returned
  rcases result with ⟨maybePoint, maybeClaim⟩
  dsimp only at hp zero positive ⊢
  subst maybePoint
  cases maybeClaim with
  | some c => rfl
  | none =>
    cases count with
    | zero => cases zero rfl
    | succ n => simp at positive

/-- The consuming suffix is erased only after proving returned Pending completeness. -/
theorem verifierReduce_rounds (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1) (maximum : Nat)
    (point : Option (List F)) (claim : Option F) (count service : Option Nat) :
    SumcheckPreludeNormalForms.verifierReduceProcess (G := G) U maximum ctx point claim count service =
      (pendingRounds maximum ctx point claim count service).bind
        (fun pc => .done (returnValues (embedV (G := G) pc))) := by
  cases point with
  | none => rfl
  | some point =>
    cases claim with
    | none => rfl
    | some claim =>
      unfold SumcheckPreludeNormalForms.verifierReduceProcess
      change (denoteRepeat (repeatSpec maximum) ctx (ctx.roles 1) count
        (embedV (G := G) (some point, some claim)) (cap service) (bodyFn U ctx (ctx.roles 1))).bind _ = _
      rw [repeat_optional U bodies ctx separate]
      simp only [PIR.Process.bind_assoc, PIR.Process.bind]
      cases count with
      | none => rfl
      | some count =>
        by_cases bounded : count ≤ maximum
        · simp only [pendingRounds, bounded, ↓reduceIte]
          refine Eq.trans ?_ (finish_rounds (G := G) ctx point claim count service)
          apply congrArg (PIR.Process.bind _)
          funext pc
          rcases pc with ⟨p, c⟩
          cases p <;> cases c <;> rfl
        · simp only [pendingRounds, bounded, ↓reduceIte, PIR.Process.bind]

/-- All seven optional inputs and both actual Pending operations, with output masks. -/
theorem reduce_optional (U : UnitPayload) (bodies : Bodies U.definitions)
    (claims : SumcheckPendingLaws.Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (maximum : Nat)
    (valuesP : Option (List F)) (dimensionP widthP : Option Nat)
    (point : Option (List F)) (claim : Option F) (count service : Option Nat) :
    reduceDenote (G := G) maximum U ctx self
      (reduceArguments valuesP dimensionP widthP point claim count service) =
      (pendingRounds maximum ctx point claim count service).bind
        (fun pc => .done (reduceResults pc)) := by
  unfold reduceDenote
  rw [mask_reduceArguments ctx self verifier separate,
    prelude_expansion U bodies claims ctx self verifier separate]
  subst self
  rw [verifierReduce_rounds U bodies ctx separate]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, mask_returnValues ctx _ rfl separate]
  rfl

/-- Missing count always stops, including absent Pending components. -/
theorem reduce_missing (U : UnitPayload) (bodies : Bodies U.definitions)
    (claims : SumcheckPendingLaws.Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (maximum : Nat)
    (valuesP : Option (List F)) (dimensionP widthP : Option Nat)
    (point : Option (List F)) (claim : Option F) (service : Option Nat) :
    reduceDenote (G := G) maximum U ctx self
      (reduceArguments valuesP dimensionP widthP point claim none service) = .halt .incomplete := by
  rw [reduce_optional U bodies claims ctx self verifier separate]
  cases point <;> cases claim <;> rfl

/-- Excess count is refused after both Pending components have been consumed. -/
theorem reduce_excess (U : UnitPayload) (bodies : Bodies U.definitions)
    (claims : SumcheckPendingLaws.Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (maximum count : Nat) (large : maximum < count)
    (valuesP : Option (List F)) (dimensionP widthP : Option Nat)
    (point : List F) (claim : F) (service : Option Nat) :
    reduceDenote (G := G) maximum U ctx self
      (reduceArguments valuesP dimensionP widthP (some point) (some claim) (some count) service) =
      .halt .refused := by
  rw [reduce_optional U bodies claims ctx self verifier separate]
  simp only [pendingRounds, Nat.not_le_of_lt large, ↓reduceIte, PIR.Process.bind]

/-- Zero rounds retain a complete Pending and never demand a service handle. -/
theorem reduce_zero (U : UnitPayload) (bodies : Bodies U.definitions)
    (claims : SumcheckPendingLaws.Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (maximum : Nat)
    (valuesP : Option (List F)) (dimensionP widthP : Option Nat)
    (point : List F) (claim : F) (service : Option Nat) :
    reduceDenote (G := G) maximum U ctx self
      (reduceArguments valuesP dimensionP widthP (some point) (some claim) (some 0) service) =
      .done (reduceResults (some point, some claim)) := by
  rw [reduce_optional U bodies claims ctx self verifier separate]
  simp only [pendingRounds, Nat.zero_le, ↓reduceIte, PIR.repeatN, PIR.Process.bind]

end ZkcExamples.Structured.SumcheckVerifierPrelude
