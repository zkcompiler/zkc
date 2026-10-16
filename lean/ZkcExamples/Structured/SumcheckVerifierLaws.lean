module

public import ZkcExamples.Structured.SumcheckVerifierProcess
public import ZkcExamples.Structured.SumcheckVerifierBodies
public import ZkcExamples.Structured.SumcheckVerifierHelpers
public import Zkc.Source.Structured.RepeatLaws
public import Zkc.Source.DenotationLaws

@[expose] public section

/-! The plain verifier process of the entire retained callback. The normal form
below is derived from that body, including its calculated guard, append and
interpolation. Its action replies are arbitrary; no provider law is assumed. -/
namespace ZkcExamples.Structured.SumcheckVerifierLaws
open Zkc.Source Zkc.Source.Structured
open SumcheckVerifierBodies SumcheckVerifierHelpers

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The two optional verifier components occupy the actual last two slots. -/
def embedV (pc : Option (List F) × Option F) :
    Values (Component (assignment F G)) repeatState :=
  .cons none (.cons none (.cons none (.cons none (.cons pc.1 (.cons pc.2 .nil)))))

def cap (service : Option Nat) :
    Values (Component (assignment F G)) [.service "random.bls12-381.fr/0"] :=
  .cons service .nil

private abbrev scalarResult (value : Option F) :
    Values (Component (assignment F G)) [.field "bls12-381.fr"] :=
  .cons value .nil

/-- The existing Region interpreter, using this unit's own complete tables. -/
def bodyFn (U : UnitPayload) (ctx : ProtocolContext) (self : Nat) :
    RegionFunction (Component (assignment F G)) (participantInterface F G)
      (.index :: (repeatState ++ [.service "random.bls12-381.fr/0"]), repeatState) :=
  fun args => roundBody.denote
    (participantMeaningWith (.silent _) (participantActions F G)
      (plainHelpers U) self (U.plainProtocolTable F G) ctx) args.get

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem mask_embedV (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (maximum : Nat) (pc : Option (List F) × Option F) :
    maskValues self (ctx.mapScopes (repeatSpec maximum).stateScopes) (embedV (G := G) pc) =
      embedV pc := by
  subst self
  unfold embedV
  dsimp only [repeatSpec, ProtocolContext.mapScopes]
  iterate 7 unfold maskValues
  simp [Participant.restrict]


private theorem denote_mark (U : UnitPayload) (ctx : ProtocolContext) (self : Nat)
    {Γ out : List Ty} (site : String) (next : Region protocolDialect Γ out)
    (env : Environment (Component (assignment F G)) Γ) :
    (Region.letOp (dialect := protocolDialect) (.mark site) .nil .nil next).denote
      (participantMeaningWith (.silent _) (participantActions F G)
        (plainHelpers U) self (U.plainProtocolTable F G) ctx) env =
    next.denote (participantMeaningWith (.silent _) (participantActions F G)
        (plainHelpers U) self (U.plainProtocolTable F G) ctx) env := rfl

private theorem denote_calculation (U : UnitPayload) (ctx : ProtocolContext) (self : Nat)
    {Γ out : List Ty} {op : Op} {allowed : op.isCalculation = true}
    {arguments : Operands Γ op.arguments}
    {next : Region protocolDialect (op.results ++ Γ) out}
    {env : Environment (Component (assignment F G)) Γ}
    (result : Values (Component (assignment F G)) op.results)
    (calculation : Evaluation.componentOperation (.silent _) (plainHelpers U) op
      (Operands.eval env arguments) (op.calculationRegions allowed) = .done result) :
    (Region.letOp (dialect := protocolDialect) (.calculate op allowed) arguments .nil next).denote
      (participantMeaningWith (.silent _) (participantActions F G)
        (plainHelpers U) self (U.plainProtocolTable F G) ctx) env =
    next.denote (participantMeaningWith (.silent _) (participantActions F G)
        (plainHelpers U) self (U.plainProtocolTable F G) ctx) (env.prepend result) := by
  change (Evaluation.componentOperation (.silent _) (plainHelpers U) op
    (Operands.eval env arguments) (op.calculationRegions allowed)).bind _ = _
  rw [calculation]
  rfl


/-- The literal suffix computes its scalar using actual selected input values. -/
private theorem round_tail (U : UnitPayload) (ctx : ProtocolContext) (self : Nat)
    (rest : List Ty) (env : Environment (Component (assignment F G)) (roundTailInputs ++ rest))
    (cv hi lo : F)
    (challenge : env (.there (.there (.there (.there (.there (.there (.there (.here)))))))) = some cv)
    (high : env (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))) = some hi)
    (low : env (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))) = some lo) :
    (roundTail rest).denote (participantMeaningWith (.silent _) (participantActions F G)
        (plainHelpers U) self (U.plainProtocolTable F G) ctx) env =
      .done (.cons (env (.there (.there (.here)))) (.cons (env (.there (.there (.there (.here))))) (.cons (env (.there (.there (.there (.there (.here))))))
        (.cons (env (.there (.here))) (.cons (env (.here))
          (.cons (some ((1 - cv) * lo + cv * hi)) .nil)))))) := by
  unfold roundTail
  refine (denote_mark U ctx self "" _ _).trans ?_
  refine (denote_calculation U ctx self (op := .fieldConstant "bls12-381.fr" 1)
    (scalarResult (G := G) (some (((1 : Nat) : F)))) ?_).trans ?_
  · rfl
  simp only [Nat.cast_one]
  refine (denote_mark U ctx self "" _ _).trans ?_
  refine (denote_calculation U ctx self (op := .fieldSubtract "bls12-381.fr")
    (scalarResult (G := G) (some (1 - cv))) ?_).trans ?_
  · change Evaluation.componentOperation (.silent _) (plainHelpers U)
      (.fieldSubtract "bls12-381.fr") (.cons (some (1 : F)) (.cons (env (.there (.there (.there (.there (.there (.there (.there (.here))))))))) .nil)) .nil = _
    rw [challenge]
    rfl
  refine (denote_mark U ctx self "" _ _).trans ?_
  refine (denote_calculation U ctx self (op := .fieldMultiply "bls12-381.fr")
    (scalarResult (G := G) (some ((1 - cv) * lo))) ?_).trans ?_
  · change Evaluation.componentOperation (.silent _) (plainHelpers U)
      (.fieldMultiply "bls12-381.fr") (.cons (some (1 - cv)) (.cons (env (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))) .nil)) .nil = _
    rw [low]
    rfl
  refine (denote_mark U ctx self "" _ _).trans ?_
  refine (denote_calculation U ctx self (op := .fieldMultiply "bls12-381.fr")
    (scalarResult (G := G) (some (cv * hi))) ?_).trans ?_
  · change Evaluation.componentOperation (.silent _) (plainHelpers U)
      (.fieldMultiply "bls12-381.fr") (.cons (env (.there (.there (.there (.there (.there (.there (.there (.here))))))))) (.cons (env (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))) .nil)) .nil = _
    rw [challenge, high]
    rfl
  refine (denote_mark U ctx self "" _ _).trans ?_
  refine (denote_calculation U ctx self (op := .fieldAdd "bls12-381.fr")
    (scalarResult (G := G) (some ((1 - cv) * lo + cv * hi))) ?_).trans ?_
  · rfl
  rfl


theorem round_body_optional (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (index : Nat) (service : Option Nat)
    (pc : Option (List F) × Option F) :
    bodyFn U ctx self (.cons (some index) ((embedV (G := G) pc).append (cap service))) =
      (roundPlain ctx service pc).bind (fun result => .done (embedV result)) := by
  subst self
  rcases pc with ⟨point, claim⟩
  let m := participantMeaningWith (.silent (participantInterface F G)) (participantActions F G)
    (plainHelpers U) (ctx.roles 1) (U.plainProtocolTable F G) ctx
  unfold bodyFn roundBody roundGuard
  simp only [roundPlain, PIR.Proc.bind]
  refine (Region.denote_letOp_done m (.mark "s16") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.localCall SumcheckHelperBodies.sumsHelper rfl 0 "s16") _ .nil _ _ (.cons none (.cons none .nil)) ?_).trans ?_
  · change Participant.owned (ctx.roles 1) (ctx.roles 0)
      (invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.sumsHelper)
      (.cons none (.cons none (.cons none .nil))) = _
    rw [Participant.owned_other _ _ separate]
    rfl
  refine (Region.denote_letOp_done m (.mark "label_726f756e64_0") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine Region.denote_letOp_call m (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_0") _ .nil _ _
    (.receive (.field "bls12-381.fr") (qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_0") (ctx.roles 0)) (fun value => (scalarResult (G := G) (some value))) _ ?_ ?_
  · change (((Participant.exchange (services := services) (Value := assignment F G)
      (ctx.roles 1) (ctx.roles 0) (ctx.roles 1)
      (qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_0") (ty := .field "bls12-381.fr") none).interpret
      (participantActions F G)).bind (fun value => .done (scalarResult (G := G) value))) = _
    simp only [Participant.exchange, separate, ↓reduceIte, PIR.Proc.interpret,
      participantActions, PIR.Proc.bind]
    rfl
  intro lo
  change F at lo
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.restrict (.field "bls12-381.fr") [1]) _ .nil _ _ (scalarResult (G := G) (some lo)) ?_).trans ?_
  · change PIR.Proc.done (I := participantInterface F G)
      (scalarResult (G := G) (Participant.restrict ([ctx.roles 1].contains (ctx.roles 1)) (some lo))) = _
    simp [Participant.restrict]
    rfl
  refine (Region.denote_letOp_done m (.mark "label_726f756e64_1") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine Region.denote_letOp_call m (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_1") _ .nil _ _
    (.receive (.field "bls12-381.fr") (qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_1") (ctx.roles 0)) (fun value => (scalarResult (G := G) (some value))) _ ?_ ?_
  · change (((Participant.exchange (services := services) (Value := assignment F G)
      (ctx.roles 1) (ctx.roles 0) (ctx.roles 1)
      (qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_1") (ty := .field "bls12-381.fr") none).interpret
      (participantActions F G)).bind (fun value => .done (scalarResult (G := G) value))) = _
    simp only [Participant.exchange, separate, ↓reduceIte, PIR.Proc.interpret,
      participantActions, PIR.Proc.bind]
    rfl
  intro hi
  change F at hi
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.restrict (.field "bls12-381.fr") [1]) _ .nil _ _ (scalarResult (G := G) (some hi)) ?_).trans ?_
  · change PIR.Proc.done (I := participantInterface F G)
      (scalarResult (G := G) (Participant.restrict ([ctx.roles 1].contains (ctx.roles 1)) (some hi))) = _
    simp [Participant.restrict]
    rfl
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.calculate (.fieldAdd "bls12-381.fr") rfl) _ .nil _ _ (scalarResult (G := G) (some (lo + hi))) ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  cases claim with
  | none =>
    refine (Region.denote_letOp_done m (.calculate (.fieldEqual "bls12-381.fr") rfl) _ .nil _ _ (.cons none .nil) ?_).trans ?_
    · rfl
    refine (Region.denote_letOp_done m (.mark "s24") .nil .nil _ _ .nil ?_).trans ?_
    · rfl
    apply Region.denote_letOp_halt m (.guard 1 "s24") _ .nil _ _ .incomplete
    change (((Participant.guard (services := services) (Value := assignment F G)
      (ctx.roles 1) (ctx.roles 1) none).interpret (participantActions F G)).bind
      (fun _ => .done (Values.nil : Values (Component (assignment F G)) []))) = _
    simp only [Participant.guard, ↓reduceIte, PIR.Proc.interpret, PIR.Proc.bind]
    rfl
  | some claim =>
    refine (Region.denote_letOp_done m (.calculate (.fieldEqual "bls12-381.fr") rfl) _ .nil _ _ (.cons (some (decide (claim = lo + hi))) .nil) ?_).trans ?_
    · rfl
    refine (Region.denote_letOp_done m (.mark "s24") .nil .nil _ _ .nil ?_).trans ?_
    · rfl
    by_cases boundary : claim = lo + hi
    · simp only [boundary, ↓reduceIte, decide_true]
      refine (Region.denote_letOp_done m (.guard 1 "s24") _ .nil _ _ .nil ?_).trans ?_
      · change (((Participant.guard (services := services) (Value := assignment F G)
          (ctx.roles 1) (ctx.roles 1) (some true)).interpret (participantActions F G)).bind
          (fun _ => .done (Values.nil : Values (Component (assignment F G)) []))) = _
        simp only [Participant.guard, ↓reduceIte, PIR.Proc.interpret, PIR.Proc.bind]
        rfl
      refine (Region.denote_letOp_done m (.mark "label_6368616c6c656e6765") .nil .nil _ _ .nil ?_).trans ?_
      · rfl
      cases service with
      | none =>
        apply Region.denote_letOp_halt m (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") _ .nil _ _ .incomplete
        change (((Participant.query (services := services) (Value := assignment F G)
          (ctx.roles 1) (ctx.roles 1) (qualifyProtocolSite ctx.applicationPrefix "label_6368616c6c656e6765")
          "bls12-381.fr" (.cons none .nil)).interpret (participantActions F G)).bind
          (fun value => .done (scalarResult (G := G) value))) = _
        simp only [Participant.query, ↓reduceIte]
        rfl
      | some handle =>
        refine Region.denote_letOp_call m (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") _ .nil _ _
          (.query (qualifyProtocolSite ctx.applicationPrefix "label_6368616c6c656e6765") "bls12-381.fr" (.cons handle .nil)) (fun value => (scalarResult (G := G) (some value))) _ ?_ ?_
        · change (((Participant.query (services := services) (Value := assignment F G)
            (ctx.roles 1) (ctx.roles 1) (qualifyProtocolSite ctx.applicationPrefix "label_6368616c6c656e6765")
            "bls12-381.fr" (.cons (some handle) .nil)).interpret (participantActions F G)).bind
            (fun value => .done (scalarResult (G := G) value))) = _
          simp only [Participant.query, ↓reduceIte]
          rfl
        intro cv
        change F at cv
        refine (Region.denote_letOp_done m (.mark "label_64656c6976657279_0") .nil .nil _ _ .nil ?_).trans ?_
        · rfl
        refine Region.denote_letOp_call m (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") _ .nil _ _
          (.send (ty := .field "bls12-381.fr") (qualifyProtocolSite ctx.applicationPrefix "label_64656c6976657279_0") (ctx.roles 0) cv) (fun _ => (scalarResult (G := G) (some cv))) _ ?_ ?_
        · change (((Participant.exchange (services := services) (Value := assignment F G)
            (ctx.roles 1) (ctx.roles 1) (ctx.roles 0)
            (qualifyProtocolSite ctx.applicationPrefix "label_64656c6976657279_0") (ty := .field "bls12-381.fr") (some cv)).interpret
            (participantActions F G)).bind (fun value => .done (scalarResult (G := G) value))) = _
          simp only [Participant.exchange, ↓reduceIte, PIR.Proc.interpret,
            participantActions, PIR.Proc.bind]
          rfl
        intro acknowledgment
        refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
        · rfl
        refine (Region.denote_letOp_done m (.restrict (.field "bls12-381.fr") [0]) _ .nil _ _ (scalarResult (G := G) (none)) ?_).trans ?_
        · change PIR.Proc.done (I := participantInterface F G)
            (scalarResult (G := G) (Participant.restrict ([ctx.roles 0].contains (ctx.roles 1)) (some cv))) = _
          simp [Participant.restrict, Ne.symm separate]
          rfl
        refine (Region.denote_letOp_done m (.mark "s29") .nil .nil _ _ .nil ?_).trans ?_
        · rfl
        refine (Region.denote_letOp_done m (.localCall MapFirstBodies.firstHelper rfl 0 "s29") _ .nil _ _ (.cons none (.cons none (.cons none .nil))) ?_).trans ?_
        · change Participant.owned (ctx.roles 1) (ctx.roles 0)
            (invoke (plainHelpers (F := F) (G := G) U).closed MapFirstBodies.firstHelper)
            (.cons none (.cons none (.cons none (.cons none .nil)))) = _
          rw [Participant.owned_other _ _ separate]
          rfl
        refine (Region.denote_letOp_done m (.mark "s31") .nil .nil _ _ .nil ?_).trans ?_
        · rfl
        refine (Region.denote_letOp_done m (.localCall SumcheckHelperBodies.appendHelper rfl 0 "s31") _ .nil _ _ (.cons none .nil) ?_).trans ?_
        · change Participant.owned (ctx.roles 1) (ctx.roles 0)
            (invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.appendHelper)
            (.cons none (.cons none .nil)) = _
          rw [Participant.owned_other _ _ separate]
          rfl
        refine (Region.denote_letOp_done m (.mark "s33") .nil .nil _ _ .nil ?_).trans ?_
        · rfl
        cases point with
        | none =>
          apply Region.denote_letOp_halt m (.localCall SumcheckHelperBodies.appendHelper rfl 1 "s33") _ .nil _ _ .incomplete
          change Participant.owned (ctx.roles 1) (ctx.roles 1)
            (invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.appendHelper)
            (.cons none (.cons (some cv) .nil)) = _
          simp only [Participant.owned, ↓reduceIte]
          rfl
        | some point =>
          refine (Region.denote_letOp_done m (.localCall SumcheckHelperBodies.appendHelper rfl 1 "s33") _ .nil _ _ (.cons (some (point ++ [cv])) .nil) ?_).trans ?_
          · change Participant.owned (ctx.roles 1) (ctx.roles 1)
              (invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.appendHelper)
              (Values.cons point (.cons cv .nil)).present = _
            rw [Participant.owned_present, append_plain U bodies]
            rfl
          refine (round_tail U ctx (ctx.roles 1) _ _ cv hi lo ?_ ?_ ?_).trans ?_
          · rfl
          · rfl
          · rfl
          rfl
    · simp only [boundary, ↓reduceIte, decide_false]
      apply Region.denote_letOp_halt m (.guard 1 "s24") _ .nil _ _ .reject
      change (((Participant.guard (services := services) (Value := assignment F G)
        (ctx.roles 1) (ctx.roles 1) (some false)).interpret (participantActions F G)).bind
        (fun _ => .done (Values.nil : Values (Component (assignment F G)) []))) = _
      simp only [Participant.guard, Bool.false_eq_true, ↓reduceIte, PIR.Proc.interpret, PIR.Proc.bind]
      rfl



/-- Each iteration uses the same immutable context and service capture. -/
theorem round_optional (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (maximum index : Nat) (service : Option Nat)
    (pc : Option (List F) × Option F) :
    Repeat.step (repeatSpec maximum) ctx self (cap service) (bodyFn U ctx self)
      (embedV (G := G) pc) index =
      (roundPlain ctx service pc).bind (fun result => .done (embedV result)) := by
  unfold Repeat.step
  rw [mask_embedV ctx self verifier maximum pc]
  rw [round_body_optional U bodies ctx self verifier separate]
  simp only [PIR.Proc.bind_assoc, PIR.Proc.bind, mask_embedV ctx self verifier maximum]

/-- Arbitrary finite residual count and starting index, without re-admission. -/
theorem loop_optional (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (start count maximum : Nat) (service : Option Nat)
    (pc : Option (List F) × Option F) :
    Repeat.loop (repeatSpec maximum) ctx self (cap service) (bodyFn U ctx self)
      start count (embedV (G := G) pc) =
      (PIR.repeatN count (roundPlain ctx service) pc).bind
        (fun result => .done (embedV result)) := by
  refine (Repeat.loop_embed (F := F) (G := G) (repeatSpec maximum) ctx self
    (cap service) (bodyFn U ctx self) (embedV (F := F) (G := G))
    (fun value _ => roundPlain ctx service value) start count pc
    (fun value index => round_optional U bodies ctx self verifier separate maximum index service value)).trans ?_
  rw [Finite.fold_range_repeatN]



end ZkcExamples.Structured.SumcheckVerifierLaws
