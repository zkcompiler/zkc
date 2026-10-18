module

public import ZkcExamples.Structured.SumcheckProverProcess
public import ZkcExamples.Structured.SumcheckVerifierLaws
public import ZkcExamples.Structured.SumcheckUnitContracts
public import ZkcExamples.Structured.SumcheckRoundNormalForms

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
      embedP state :=
  SumcheckRoundNormalForms.proverState_masked ctx self prover state.1 state.2.1 state.2.2.1 state.2.2.2

/-- The callback, at the prover, on a present positive-dimensional shaped table:
the generated normal form of the literal body. The verifier's slots stay absent;
the challenge is the actual delivered reply. -/
theorem round_body_present (U : UnitPayload) (bodies : SumcheckUnitContracts.Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (prover : self = ctx.roles 0)
    (separate : ctx.roles 1 ≠ self) (index : Nat) (service : Option Nat)
    (state : ProverState F) (shape : HasShape state.1 state.2.1 state.2.2.1)
    (bound : state.1.length < indexLimit) (positive : 0 < state.2.1) :
    bodyFn U ctx self (.cons (some index) ((embedP (G := G) state).append (cap service))) =
      (roundPresent ctx state).bind (fun result => .done (embedP result)) :=
  SumcheckRoundNormalForms.prover_process U bodies ctx self prover separate index service
    state.1 state.2.1 state.2.2.1 state.2.2.2 shape bound positive

/-- A zero-dimensional table stops at the actual sums helper, before any send. -/
theorem round_body_zero (U : UnitPayload) (bodies : SumcheckUnitContracts.Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (prover : self = ctx.roles 0)
    (index : Nat) (service : Option Nat) (xs : List F) (width : Nat) (point : List F) :
    bodyFn U ctx self (.cons (some index) ((embedP (G := G) (xs, 0, width, point)).append (cap service))) =
      .halt .reject :=
  SumcheckRoundNormalForms.prover_empty_process U bodies ctx self prover index service xs width point


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
