module

public import ZkcExamples.Structured.SumcheckProverProcess
public import ZkcExamples.Structured.SumcheckVerifierLaws
public import ZkcExamples.Structured.SumcheckUnitContracts

@[expose] public section

/-! The plain prover process of the entire retained callback. The normal form
below is derived from the same literal body as the verifier's, at the prover's
participant: the verifier's guard, draw, append and interpolation are skipped,
and the prover's sums, sends, delivery receive, fold and append are performed.
The delivered challenge is an arbitrary reply; no provider law is assumed. -/
namespace ZkcExamples.Structured.SumcheckProverLaws
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary
open SumcheckVerifierBodies SumcheckVerifierHelpers SumcheckVerifierLaws
open Zkc.Polynomial.Multilinear (restrictValues)

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The four prover components occupy the first slots; the verifier's two are absent. -/
def embedP (state : ProverState F) : Values (Component (assignment F G)) repeatState :=
  .cons (some state.1) (.cons (some state.2.1) (.cons (some state.2.2.1)
    (.cons (some state.2.2.2) (.cons none (.cons none .nil)))))

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem mask_embedP (ctx : ProtocolContext) (self : Nat)
    (prover : self = ctx.roles 0) (maximum : Nat) (state : ProverState F) :
    maskValues self (ctx.mapScopes (repeatSpec maximum).stateScopes) (embedP (G := G) state) =
      embedP state := by
  subst self
  unfold embedP
  dsimp only [repeatSpec, ProtocolContext.mapScopes]
  iterate 7 unfold maskValues
  simp [Participant.restrict]

private abbrev scalarResult (value : Option F) :
    Values (Component (assignment F G)) [.field "bls12-381.fr"] :=
  .cons value .nil

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

/-- The verifier-owned suffix computes only absent values at the prover. -/
private theorem round_tail_absent (U : UnitPayload) (ctx : ProtocolContext) (self : Nat)
    (rest : List Ty) (env : Environment (Component (assignment F G)) (roundTailInputs ++ rest))
    (challenge : env (.there (.there (.there (.there (.there (.there (.there (.here)))))))) = none) :
    (roundTail rest).denote (participantMeaningWith (.silent _) (participantActions F G)
        (plainHelpers U) self (U.plainProtocolTable F G) ctx) env =
      .done (.cons (env (.there (.there (.here)))) (.cons (env (.there (.there (.there (.here))))) (.cons (env (.there (.there (.there (.there (.here))))))
        (.cons (env (.there (.here))) (.cons (env (.here))
          (.cons none .nil)))))) := by
  unfold roundTail
  refine (denote_mark U ctx self "" _ _).trans ?_
  refine (denote_calculation U ctx self (op := .fieldConstant "bls12-381.fr" 1)
    (scalarResult (G := G) (some (((1 : Nat) : F)))) ?_).trans ?_
  · rfl
  refine (denote_mark U ctx self "" _ _).trans ?_
  refine (denote_calculation U ctx self (op := .fieldSubtract "bls12-381.fr")
    (scalarResult (G := G) none) ?_).trans ?_
  · change Evaluation.componentOperation (.silent _) (plainHelpers U)
      (.fieldSubtract "bls12-381.fr") (.cons (some ((1 : Nat) : F)) (.cons (env (.there (.there (.there (.there (.there (.there (.there (.here))))))))) .nil)) .nil = _
    rw [challenge]
    rfl
  refine (denote_mark U ctx self "" _ _).trans ?_
  refine (denote_calculation U ctx self (op := .fieldMultiply "bls12-381.fr")
    (scalarResult (G := G) none) ?_).trans ?_
  · rfl
  refine (denote_mark U ctx self "" _ _).trans ?_
  refine (denote_calculation U ctx self (op := .fieldMultiply "bls12-381.fr")
    (scalarResult (G := G) none) ?_).trans ?_
  · change Evaluation.componentOperation (.silent _) (plainHelpers U)
      (.fieldMultiply "bls12-381.fr") (.cons (env (.there (.there (.there (.there (.there (.there (.there (.here))))))))) (.cons (env (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))) .nil)) .nil = _
    rw [challenge]
    rfl
  refine (denote_mark U ctx self "" _ _).trans ?_
  refine (denote_calculation U ctx self (op := .fieldAdd "bls12-381.fr")
    (scalarResult (G := G) none) ?_).trans ?_
  · rfl
  rfl


section Helpers
variable (U : UnitPayload) (bodies : SumcheckUnitContracts.Bodies U.definitions)
include bodies

/-- The actual sums helper on a shaped positive-dimensional table. -/
theorem sums_present (xs : List F) (dimension width : Nat)
    (shape : HasShape xs dimension width) (positive : 0 < dimension) :
    invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.sumsHelper
      (inputs xs dimension width) =
      .done (SumcheckHelperLaws.messageResult (xs.take (xs.length / 2)).sum
        (xs.drop (xs.length / 2)).sum) := by
  rw [closed_invoke_plain, SumcheckUnitContracts.sums_all U.linked bodies]
  have dimensionBound : dimension < indexLimit := Nat.lt_trans shape.2.1 (by decide +kernel)
  simp only [dimensionBound, positive, shape.split_valid positive, and_self, ↓reduceIte]
  rfl

/-- The actual sums helper rejects a zero-dimensional table before any send. -/
theorem sums_zero (xs : List F) (width : Nat) :
    invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.sumsHelper
      (inputs xs 0 width) = .halt .reject := by
  rw [closed_invoke_plain, SumcheckUnitContracts.sums_all U.linked bodies]
  simp only [show 0 < indexLimit by decide +kernel, Nat.lt_irrefl, ↓reduceIte]
  rfl

/-- The actual fold helper on a shaped positive-dimensional table. -/
theorem first_present (xs : List F) (dimension width : Nat) (r : F)
    (shape : HasShape xs dimension width) (bound : xs.length < indexLimit)
    (positive : 0 < dimension) :
    invoke (plainHelpers (F := F) (G := G) U).closed MapFirstBodies.firstHelper
      (MapFirstLaws.firstInputs xs dimension width r) =
      .done (inputs (restrictValues xs r) (dimension - 1) width) := by
  rw [closed_invoke_plain,
    (SumcheckUnitContracts.first_laws U.linked bodies).first xs dimension width r shape bound]
  simp only [positive, ↓reduceIte]
  rfl

end Helpers

/-- The callback, at the prover, on a present positive-dimensional shaped table.
The verifier's slots stay absent; the challenge is the actual delivered reply. -/
theorem round_body_present (U : UnitPayload) (bodies : SumcheckUnitContracts.Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (prover : self = ctx.roles 0)
    (separate : ctx.roles 1 ≠ self) (index : Nat) (service : Option Nat)
    (state : ProverState F) (shape : HasShape state.1 state.2.1 state.2.2.1)
    (bound : state.1.length < indexLimit) (positive : 0 < state.2.1) :
    bodyFn U ctx self (.cons (some index) ((embedP (G := G) state).append (cap service))) =
      (roundPresent ctx state).bind (fun result => .done (embedP result)) := by
  subst self
  rcases state with ⟨xs, dimension, width, point⟩
  dsimp only at shape bound positive
  let m := participantMeaningWith (.silent (participantInterface F G)) (participantActions F G)
    (plainHelpers U) (ctx.roles 0) (U.plainProtocolTable F G) ctx
  unfold bodyFn roundBody roundGuard
  simp only [roundPresent, PIR.Proc.bind]
  refine (Region.denote_letOp_done m (.mark "s16") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.localCall SumcheckHelperBodies.sumsHelper rfl 0 "s16") _ .nil _ _
    (.cons (some (xs.take (xs.length / 2)).sum) (.cons (some (xs.drop (xs.length / 2)).sum) .nil)) ?_).trans ?_
  · change Participant.owned (ctx.roles 0) (ctx.roles 0)
      (invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.sumsHelper)
      (Values.cons xs (.cons dimension (.cons width .nil))).present = _
    rw [Participant.owned_present]
    change (invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.sumsHelper
      (inputs xs dimension width)).bind (fun results => .done results.present) = _
    rw [sums_present U bodies xs dimension width shape positive]
    rfl
  refine (Region.denote_letOp_done m (.mark "label_726f756e64_0") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine Region.denote_letOp_call m (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_0") _ .nil _ _
    (.send (ty := .field "bls12-381.fr") (qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_0")
      (ctx.roles 1) (xs.take (xs.length / 2)).sum)
    (fun _ => scalarResult (G := G) (some (xs.take (xs.length / 2)).sum)) _ ?_ ?_
  · change (((Participant.exchange (services := services) (Value := assignment F G)
      (ctx.roles 0) (ctx.roles 0) (ctx.roles 1)
      (qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_0") (ty := .field "bls12-381.fr")
      (some (xs.take (xs.length / 2)).sum)).interpret
      (participantActions F G)).bind (fun value => .done (scalarResult (G := G) value))) = _
    simp only [Participant.exchange, ↓reduceIte, PIR.Proc.interpret,
      participantActions, PIR.Proc.bind]
    rfl
  intro _
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.restrict (.field "bls12-381.fr") [1]) _ .nil _ _ (scalarResult (G := G) none) ?_).trans ?_
  · change PIR.Proc.done (I := participantInterface F G)
      (scalarResult (G := G) (Participant.restrict ([ctx.roles 1].contains (ctx.roles 0))
        (some (xs.take (xs.length / 2)).sum))) = _
    simp [Participant.restrict, Ne.symm separate]
    rfl
  refine (Region.denote_letOp_done m (.mark "label_726f756e64_1") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine Region.denote_letOp_call m (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_1") _ .nil _ _
    (.send (ty := .field "bls12-381.fr") (qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_1")
      (ctx.roles 1) (xs.drop (xs.length / 2)).sum)
    (fun _ => scalarResult (G := G) (some (xs.drop (xs.length / 2)).sum)) _ ?_ ?_
  · change (((Participant.exchange (services := services) (Value := assignment F G)
      (ctx.roles 0) (ctx.roles 0) (ctx.roles 1)
      (qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_1") (ty := .field "bls12-381.fr")
      (some (xs.drop (xs.length / 2)).sum)).interpret
      (participantActions F G)).bind (fun value => .done (scalarResult (G := G) value))) = _
    simp only [Participant.exchange, ↓reduceIte, PIR.Proc.interpret,
      participantActions, PIR.Proc.bind]
    rfl
  intro _
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.restrict (.field "bls12-381.fr") [1]) _ .nil _ _ (scalarResult (G := G) none) ?_).trans ?_
  · change PIR.Proc.done (I := participantInterface F G)
      (scalarResult (G := G) (Participant.restrict ([ctx.roles 1].contains (ctx.roles 0))
        (some (xs.drop (xs.length / 2)).sum))) = _
    simp [Participant.restrict, Ne.symm separate]
    rfl
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.calculate (.fieldAdd "bls12-381.fr") rfl) _ .nil _ _ (scalarResult (G := G) none) ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.calculate (.fieldEqual "bls12-381.fr") rfl) _ .nil _ _ (.cons none .nil) ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.mark "s24") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.guard 1 "s24") _ .nil _ _ .nil ?_).trans ?_
  · change (((Participant.guard (services := services) (Value := assignment F G)
      (ctx.roles 0) (ctx.roles 1) none).interpret (participantActions F G)).bind
      (fun _ => .done (Values.nil : Values (Component (assignment F G)) []))) = _
    simp only [Participant.guard, separate, ↓reduceIte, PIR.Proc.interpret, PIR.Proc.bind]
    rfl
  refine (Region.denote_letOp_done m (.mark "label_6368616c6c656e6765") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") _ .nil _ _
    (scalarResult (G := G) none) ?_).trans ?_
  · change (((Participant.query (services := services) (Value := assignment F G)
      (ctx.roles 0) (ctx.roles 1) (qualifyProtocolSite ctx.applicationPrefix "label_6368616c6c656e6765")
      "bls12-381.fr" (.cons service .nil)).interpret (participantActions F G)).bind
      (fun value => .done (scalarResult (G := G) value))) = _
    simp only [Participant.query, separate, ↓reduceIte, PIR.Proc.interpret, PIR.Proc.bind]
    rfl
  refine (Region.denote_letOp_done m (.mark "label_64656c6976657279_0") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine Region.denote_letOp_call m (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") _ .nil _ _
    (.receive (.field "bls12-381.fr") (qualifyProtocolSite ctx.applicationPrefix "label_64656c6976657279_0")
      (ctx.roles 1)) (fun value => scalarResult (G := G) (some value)) _ ?_ ?_
  · change (((Participant.exchange (services := services) (Value := assignment F G)
      (ctx.roles 0) (ctx.roles 1) (ctx.roles 0)
      (qualifyProtocolSite ctx.applicationPrefix "label_64656c6976657279_0") (ty := .field "bls12-381.fr")
      none).interpret (participantActions F G)).bind (fun value => .done (scalarResult (G := G) value))) = _
    simp only [Participant.exchange, separate, ↓reduceIte, PIR.Proc.interpret,
      participantActions, PIR.Proc.bind]
    rfl
  intro cp
  change F at cp
  refine (Region.denote_letOp_done m (.mark "") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.restrict (.field "bls12-381.fr") [0]) _ .nil _ _ (scalarResult (G := G) (some cp)) ?_).trans ?_
  · change PIR.Proc.done (I := participantInterface F G)
      (scalarResult (G := G) (Participant.restrict ([ctx.roles 0].contains (ctx.roles 0)) (some cp))) = _
    simp [Participant.restrict]
    rfl
  refine (Region.denote_letOp_done m (.mark "s29") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.localCall MapFirstBodies.firstHelper rfl 0 "s29") _ .nil _ _
    (.cons (some (restrictValues xs cp)) (.cons (some (dimension - 1)) (.cons (some width) .nil))) ?_).trans ?_
  · change Participant.owned (ctx.roles 0) (ctx.roles 0)
      (invoke (plainHelpers (F := F) (G := G) U).closed MapFirstBodies.firstHelper)
      (Values.cons xs (.cons dimension (.cons width (.cons cp .nil)))).present = _
    rw [Participant.owned_present]
    change (invoke (plainHelpers (F := F) (G := G) U).closed MapFirstBodies.firstHelper
      (MapFirstLaws.firstInputs xs dimension width cp)).bind (fun results => .done results.present) = _
    rw [first_present U bodies xs dimension width cp shape bound positive]
    rfl
  refine (Region.denote_letOp_done m (.mark "s31") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.localCall SumcheckHelperBodies.appendHelper rfl 0 "s31") _ .nil _ _
    (.cons (some (point ++ [cp])) .nil) ?_).trans ?_
  · change Participant.owned (ctx.roles 0) (ctx.roles 0)
      (invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.appendHelper)
      (Values.cons point (.cons cp .nil)).present = _
    rw [Participant.owned_present, append_plain U ⟨bodies.empty, bodies.append, bodies.width,
      bodies.«variables», bodies.values⟩]
    rfl
  refine (Region.denote_letOp_done m (.mark "s33") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  refine (Region.denote_letOp_done m (.localCall SumcheckHelperBodies.appendHelper rfl 1 "s33") _ .nil _ _
    (.cons none .nil) ?_).trans ?_
  · change Participant.owned (ctx.roles 0) (ctx.roles 1)
      (invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.appendHelper)
      (.cons none (.cons none .nil)) = _
    rw [Participant.owned_other _ _ separate]
    rfl
  refine (round_tail_absent U ctx (ctx.roles 0) _ _ ?_).trans ?_
  · rfl
  rfl

/-- A zero-dimensional table stops at the actual sums helper, before any send. -/
theorem round_body_zero (U : UnitPayload) (bodies : SumcheckUnitContracts.Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (prover : self = ctx.roles 0)
    (index : Nat) (service : Option Nat) (xs : List F) (width : Nat) (point : List F) :
    bodyFn U ctx self (.cons (some index) ((embedP (G := G) (xs, 0, width, point)).append (cap service))) =
      .halt .reject := by
  subst self
  let m := participantMeaningWith (.silent (participantInterface F G)) (participantActions F G)
    (plainHelpers U) (ctx.roles 0) (U.plainProtocolTable F G) ctx
  unfold bodyFn roundBody
  refine (Region.denote_letOp_done m (.mark "s16") .nil .nil _ _ .nil ?_).trans ?_
  · rfl
  apply Region.denote_letOp_halt m (.localCall SumcheckHelperBodies.sumsHelper rfl 0 "s16") _ .nil _ _ .reject
  change Participant.owned (ctx.roles 0) (ctx.roles 0)
    (invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.sumsHelper)
    (Values.cons xs (.cons 0 (.cons width .nil))).present = _
  rw [Participant.owned_present]
  change (invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.sumsHelper
    (inputs xs 0 width)).bind (fun results => .done results.present) = _
  rw [sums_zero U bodies xs width]
  rfl


open Zkc.Polynomial.Multilinear (restrictPrefixValues restrictPrefixValues_length
  restrictPrefixValues_append)

/-- The prover's carried slots after the ordered challenges `point`, for the
original table `raw` of `count` variables. -/
def honestState (raw : List F) (count : Nat) (point : List F) : ProverState F :=
  (restrictPrefixValues raw point, count - point.length, 1, point)

/-- One round on the prover's own received point. Beyond the table's dimension
the actual sums helper rejects before any send. -/
def roundHonest (ctx : ProtocolContext) (raw : List F) (count : Nat) (point : List F) :
    PIR.Proc (participantInterface F G) (List F) :=
  if point.length < count then
    (roundPresent ctx (honestState raw count point)).bind (fun result => .done result.2.2.2)
  else .halt .reject

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- A shaped one-column table stays shaped and representable after any prefix
that fits its dimension. -/
theorem honestState_shape (raw : List F) (count : Nat) (shape : HasShape raw count 1)
    (bound : raw.length < indexLimit) (point : List F) (fits : point.length ≤ count) :
    HasShape (honestState raw count point).1 (honestState raw count point).2.1 1 ∧
      (honestState raw count point).1.length < indexLimit := by
  have rawLength : raw.length = 2 ^ ((count - point.length) + point.length) := by
    rw [Nat.sub_add_cancel fits]
    simpa only [Nat.mul_one] using shape.length
  have length := restrictPrefixValues_length raw point rawLength
  refine ⟨hasShape_of_length _ _ _ (by decide) (by have := shape.2.1; dsimp [honestState]; omega)
    (by simpa only [honestState, Nat.mul_one] using length), ?_⟩
  dsimp only [honestState]
  rw [length]
  refine Nat.lt_of_le_of_lt ?_ bound
  rw [shape.length, Nat.mul_one]
  exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The fold and append of one round give the honest state of the extended point. -/
theorem honestState_next (raw : List F) (count : Nat) (point : List F) (cp : F) :
    ((restrictValues (honestState raw count point).1 cp,
        (honestState raw count point).2.1 - 1, (honestState raw count point).2.2.1,
        (honestState raw count point).2.2.2 ++ [cp]) : ProverState F) =
      honestState raw count (point ++ [cp]) := by
  simp only [honestState, restrictPrefixValues_append, List.length_append, List.length_singleton,
    Nat.sub_sub]
  rfl

/-- One masked repeat step on an honest state. -/
theorem step_honest (U : UnitPayload) (bodies : SumcheckUnitContracts.Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (prover : self = ctx.roles 0)
    (separate : ctx.roles 1 ≠ self) (maximum : Nat) (service : Option Nat)
    (raw : List F) (count : Nat) (shape : HasShape raw count 1) (bound : raw.length < indexLimit)
    (point : List F) (index : Nat) :
    Repeat.step (repeatSpec maximum) ctx self (cap service) (bodyFn U ctx self)
      (embedP (G := G) (honestState raw count point)) index =
      (roundHonest ctx raw count point).bind
        (fun result => .done (embedP (honestState raw count result))) := by
  unfold Repeat.step
  rw [mask_embedP ctx self prover maximum]
  by_cases fits : point.length < count
  · obtain ⟨stateShape, stateBound⟩ :=
      honestState_shape raw count shape bound point (Nat.le_of_lt fits)
    have positive : 0 < (honestState raw count point).2.1 := by
      dsimp only [honestState]; omega
    rw [round_body_present U bodies ctx self prover separate index service _ stateShape
      stateBound positive]
    simp only [roundHonest, fits, ↓reduceIte, roundPresent, PIR.Proc.bind]
    congr 1; funext; congr 1; funext; congr 1; funext cp
    simp only [mask_embedP ctx self prover maximum]
    rw [honestState_next raw count point cp]
    rfl
  · have zero : (honestState raw count point).2.1 = 0 := by
      dsimp only [honestState]; omega
    have equation : honestState raw count point =
        ((honestState raw count point).1, 0, 1, point) := by
      rw [← zero]; rfl
    rw [equation, round_body_zero U bodies ctx self prover index service]
    simp only [roundHonest, fits, ↓reduceIte, PIR.Proc.bind]

/-- The actual repeat loop at the prover, for every number of rounds and every
delivered challenge, as rounds on the prover's own received point. -/
theorem loop_honest (U : UnitPayload) (bodies : SumcheckUnitContracts.Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (prover : self = ctx.roles 0)
    (separate : ctx.roles 1 ≠ self) (maximum : Nat) (service : Option Nat)
    (raw : List F) (count : Nat) (shape : HasShape raw count 1) (bound : raw.length < indexLimit)
    (start rounds : Nat) (point : List F) :
    Repeat.loop (repeatSpec maximum) ctx self (cap service) (bodyFn U ctx self) start rounds
      (embedP (G := G) (honestState raw count point)) =
      (PIR.repeatN rounds (roundHonest ctx raw count) point).bind
        (fun result => .done (embedP (honestState raw count result))) := by
  refine (Repeat.loop_embed (F := F) (G := G) (repeatSpec maximum) ctx self (cap service)
    (bodyFn U ctx self) (fun value => embedP (honestState raw count value))
    (fun value _ => roundHonest ctx raw count value) start rounds point
    (fun value index => step_honest U bodies ctx self prover separate maximum service raw count
      shape bound value index)).trans ?_
  rw [Finite.fold_range_repeatN]

end ZkcExamples.Structured.SumcheckProverLaws
