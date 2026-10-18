module

public import ZkcExamples.Structured.SumcheckVerifierBodies
public import ZkcExamples.Structured.SumcheckVerifierHelpers
public import ZkcExamples.Structured.SumcheckVerifierLaws
public import Zkc.Source.Structured.RepeatLaws
public import ZkcExamples.Structured.SumcheckRoundNormalForms

@[expose] public section

/-! Full verifier prelude and exact six-slot return for the shared Reduce body. -/
namespace ZkcExamples.Structured.SumcheckVerifierPrelude
open Zkc.Source Zkc.Source.Structured
open SumcheckVerifierBodies SumcheckVerifierHelpers

abbrev reduceInputScopes : List (List Nat) := [[0], [0], [0], [1], [0, 1], [1]]
abbrev reduceOutputScopes : List (List Nat) := [[0], [0], [0], [0], [1], [1]]

/-- The literal source permutation, before any participant mask is applied. -/
def returnValues {Value : Ty → Type} (state : Values Value repeatState) :
    Values Value reduceOutputs :=
  .cons (state.get (.there (.there (.there .here))))
    (.cons (state.get .here) (.cons (state.get (.there .here))
      (.cons (state.get (.there (.there .here)))
        (.cons (state.get (.there (.there (.there (.there .here)))))
          (.cons (state.get (.there (.there (.there (.there (.there .here)))))) .nil)))))

theorem return_indices : (reduceReturn []).erase = .ret [3, 0, 1, 2, 4, 5] := rfl

theorem return_equation {I : PIR.Signature} (meaning : RegionMeaning protocolDialect I)
    (state : Values meaning.Value repeatState) {tail : List Ty}
    (outer : Values meaning.Value tail) :
    (reduceReturn tail).denote meaning (state.append outer).get =
      .done (returnValues state) := by
  cases state with | cons a rest =>
    cases rest with | cons b rest =>
      cases rest with | cons c rest =>
        cases rest with | cons d rest =>
          cases rest with | cons e rest =>
            cases rest with | cons f rest =>
              cases rest
              rfl

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def reduceArguments (valuesP : Option (List F)) (dimensionP widthP : Option Nat)
    (claim : Option F) (count service : Option Nat) :
    Values (Component (assignment F G)) reduceInputs :=
  .cons valuesP (.cons dimensionP (.cons widthP
    (.cons claim (.cons count (.cons service .nil)))))

def reduceResults (pc : Option (List F) × Option F) :
    Values (Component (assignment F G)) reduceOutputs :=
  .cons none (.cons none (.cons none (.cons none (.cons pc.1 (.cons pc.2 .nil)))))

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem mask_returnValues (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (state : Values (Component (assignment F G)) repeatState) :
    maskValues self (ctx.mapScopes reduceOutputScopes) (returnValues state) =
      reduceResults (state.get (.there (.there (.there (.there .here)))),
        state.get (.there (.there (.there (.there (.there .here)))))) := by
  subst self
  cases state with | cons a rest =>
    cases rest with | cons b rest =>
      cases rest with | cons c rest =>
        cases rest with | cons d rest =>
          cases rest with | cons e rest =>
            cases rest with | cons f rest =>
              cases rest
              change maskValues (ctx.roles 1) (ctx.mapScopes reduceOutputScopes)
                (.cons d (.cons a (.cons b (.cons c (.cons e (.cons f .nil)))))) =
                  reduceResults (e, f)
              iterate 7 unfold maskValues
              simp [reduceOutputScopes, ProtocolContext.mapScopes, Participant.restrict,
                Ne.symm separate, reduceResults]

def reduceDenote (maximum : Nat) (U : UnitPayload) (ctx : ProtocolContext) (self : Nat)
    (arguments : Values (Component (assignment F G)) reduceInputs) :
    PIR.Proc (participantInterface F G) (Values (Component (assignment F G)) reduceOutputs) :=
  ((reduceBody maximum).denote
    (participantMeaningWith (.silent _) (participantActions F G)
      (plainHelpers U) self (U.plainProtocolTable F G) ctx)
    (maskValues self (ctx.mapScopes reduceInputScopes) arguments).get).bind
      (fun result => .done (maskValues self (ctx.mapScopes reduceOutputScopes) result))

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem mask_reduceArguments (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (valuesP : Option (List F)) (dimensionP widthP : Option Nat)
    (claim : Option F) (count service : Option Nat) :
    maskValues self (ctx.mapScopes reduceInputScopes)
      (reduceArguments (G := G) valuesP dimensionP widthP claim count service) =
        reduceArguments none none none claim count service := by
  subst self
  unfold reduceArguments
  iterate 7 unfold maskValues
  simp [reduceInputScopes, ProtocolContext.mapScopes, Participant.restrict, Ne.symm separate]

/-- The whole prelude skips P work and obtains emptyV from its exact helper body.
The remaining process is the existing repeat with the actual return permutation:
the generated normal form of the body at the verifier. -/
theorem prelude_expansion (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (maximum : Nat)
    (claim : Option F) (count service : Option Nat) :
    (reduceBody maximum).denote
      (participantMeaningWith (.silent _) (participantActions F G)
        (plainHelpers U) self (U.plainProtocolTable F G) ctx)
      (reduceArguments none none none claim count service).get =
      (denoteRepeat (repeatSpec maximum) ctx self count
        (.cons none (.cons none (.cons none (.cons none
          (.cons (some []) (.cons claim .nil)))))) (.cons service .nil)
        (fun args => roundBody.denote
          (participantMeaningWith (.silent _) (participantActions F G)
            (plainHelpers U) self (U.plainProtocolTable F G) ctx) args.get)).bind
        (fun state => .done (returnValues state)) := by
  subst self
  exact SumcheckRoundNormalForms.verifierReduce_process U maximum bodies ctx _ rfl separate
    claim count service


open SumcheckVerifierLaws

/-- The original count is admitted before any round, starting with emptyV. -/
def admittedRounds (maximum : Nat) (ctx : ProtocolContext)
    (count service : Option Nat) (claim : Option F) :
    PIR.Proc (participantInterface F G) (Option (List F) × Option F) :=
  match count with
  | none => .halt .incomplete
  | some count =>
    if count ≤ maximum then PIR.repeatN count (roundPlain ctx service) (some [], claim)
    else .halt .refused

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem admittedRounds_missing (maximum : Nat) (ctx : ProtocolContext)
    (service : Option Nat) (claim : Option F) :
    admittedRounds (G := G) maximum ctx none service claim = .halt .incomplete := rfl

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem admittedRounds_excess (maximum count : Nat) (ctx : ProtocolContext)
    (large : maximum < count) (service : Option Nat) (claim : Option F) :
    admittedRounds (G := G) maximum ctx (some count) service claim = .halt .refused := by
  simp only [admittedRounds, Nat.not_le_of_lt large, ↓reduceIte]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem admittedRounds_zero (maximum : Nat) (ctx : ProtocolContext)
    (service : Option Nat) (claim : Option F) :
    admittedRounds (G := G) maximum ctx (some 0) service claim = .done (some [], claim) := by
  simp only [admittedRounds, Nat.zero_le, ↓reduceIte, PIR.repeatN]


/-- Missing count stops before the callback, independently of P inputs. -/
theorem reduce_missing (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (maximum : Nat)
    (valuesP : Option (List F)) (dimensionP widthP : Option Nat)
    (claim : Option F) (service : Option Nat) :
    reduceDenote (G := G) maximum U ctx self
      (reduceArguments valuesP dimensionP widthP claim none service) = .halt .incomplete := by
  unfold reduceDenote
  rw [mask_reduceArguments ctx self verifier separate,
    prelude_expansion U bodies ctx self verifier separate]
  have inside : ((repeatSpec maximum).roles.map ctx.roles).contains self = true := by
    subst self
    simp
  rw [repeat_missing_count (repeatSpec maximum) ctx self _ _ _ inside]
  rfl

/-- Excess count is refused before the callback. -/
theorem reduce_excess (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (maximum count : Nat) (large : maximum < count)
    (valuesP : Option (List F)) (dimensionP widthP : Option Nat)
    (claim : Option F) (service : Option Nat) :
    reduceDenote (G := G) maximum U ctx self
      (reduceArguments valuesP dimensionP widthP claim (some count) service) = .halt .refused := by
  unfold reduceDenote
  rw [mask_reduceArguments ctx self verifier separate,
    prelude_expansion U bodies ctx self verifier separate]
  have inside : ((repeatSpec maximum).roles.map ctx.roles).contains self = true := by
    subst self
    simp
  rw [repeat_above_maximum (repeatSpec maximum) ctx self _ _ _ count inside large]
  rfl

/-- Zero rounds retain the optional claim and never demand a service handle. -/
theorem reduce_zero (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (maximum : Nat)
    (valuesP : Option (List F)) (dimensionP widthP : Option Nat)
    (claim : Option F) (service : Option Nat) :
    reduceDenote (G := G) maximum U ctx self
      (reduceArguments valuesP dimensionP widthP claim (some 0) service) =
      .done (reduceResults (some [], claim)) := by
  unfold reduceDenote
  rw [mask_reduceArguments ctx self verifier separate,
    prelude_expansion U bodies ctx self verifier separate]
  have inside : ((repeatSpec maximum).roles.map ctx.roles).contains self = true := by
    subst self
    simp
  rw [repeat_zero (repeatSpec maximum) ctx self _ _ _ inside]
  have masked : maskValues self (ctx.mapScopes (repeatSpec maximum).stateScopes)
      (Values.cons none (.cons none (.cons none (.cons none
        (.cons (some ([] : List F)) (.cons claim .nil))))) :
        Values (Component (assignment F G)) repeatState) =
      (Values.cons none (.cons none (.cons none (.cons none
        (.cons (some ([] : List F)) (.cons claim .nil)))))) := by
    subst self
    iterate 7 unfold maskValues
    simp [ProtocolContext.mapScopes, Participant.restrict]
  rw [masked]
  change PIR.Proc.done (I := participantInterface F G)
    (maskValues self (ctx.mapScopes reduceOutputScopes) (returnValues _)) = _
  rw [mask_returnValues ctx self verifier separate]
  rfl

/-- The original repeat admission is retained, including missing and excessive
counts. The successful branch starts at index zero with the exact empty helper. -/
theorem repeat_optional (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (maximum : Nat)
    (claim : Option F) (count service : Option Nat) :
    denoteRepeat (repeatSpec maximum) ctx self count (embedV (G := G) (some [], claim))
      (cap service) (bodyFn U ctx self) =
      (admittedRounds maximum ctx count service claim).bind
        (fun pc => .done (embedV pc)) := by
  have inside : ((repeatSpec maximum).roles.map ctx.roles).contains self = true := by
    subst self
    simp
  cases count with
  | none =>
    exact repeat_missing_count (repeatSpec maximum) ctx self _ _ _ inside
  | some count =>
    by_cases bounded : count ≤ maximum
    · rw [repeat_admitted (repeatSpec maximum) ctx self _ _ _ count inside bounded,
        mask_embedV ctx self verifier maximum,
        loop_optional U bodies ctx self verifier separate 0 count maximum]
      simp only [admittedRounds, bounded, ↓reduceIte]
    · rw [repeat_above_maximum (repeatSpec maximum) ctx self _ _ _ count inside
        (Nat.lt_of_not_ge bounded)]
      simp only [admittedRounds, bounded, ↓reduceIte, PIR.Proc.bind]

/-- The complete body includes the skipped P prelude, optional count admission,
actual callback, exact six-slot return permutation, and output ownership mask. -/
theorem reduce_optional (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (maximum : Nat)
    (valuesP : Option (List F)) (dimensionP widthP : Option Nat)
    (claim : Option F) (count service : Option Nat) :
    reduceDenote (G := G) maximum U ctx self
      (reduceArguments valuesP dimensionP widthP claim count service) =
      (admittedRounds maximum ctx count service claim).bind
        (fun pc => .done (reduceResults pc)) := by
  unfold reduceDenote
  rw [mask_reduceArguments ctx self verifier separate,
    prelude_expansion U bodies ctx self verifier separate]
  simp only [PIR.Proc.bind_assoc, PIR.Proc.bind,
    mask_returnValues ctx self verifier separate]
  change (denoteRepeat (repeatSpec maximum) ctx self count (embedV (G := G) (some [], claim))
    (cap service) (bodyFn U ctx self)).bind _ = _
  rw [repeat_optional U bodies ctx self verifier separate]
  simp only [PIR.Proc.bind_assoc, PIR.Proc.bind]
  rfl


end ZkcExamples.Structured.SumcheckVerifierPrelude
