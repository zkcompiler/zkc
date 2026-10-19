module

public import ZkcExamples.Structured.GkrSourceNormalForms
public import ZkcExamples.Structured.GkrSourceLaws
public import ZkcExamples.Structured.GkrVerifierProcess
public import Zkc.Source.Structured.CommonAdapter
public import Zkc.Semantics.Yields

@[expose] public section

/-! The original GKR verifier is the plain GKR verifier.

The generated normal forms of the admitted original (`GkrSourceNormalForms`,
`GkrRoundsNormalForms`) state what the verifier of the GKR root does: an
output-point loop, a layer loop whose body applies the layer Sumcheck twice and
nests the line-coefficient loop, and the input check, with every owned helper
call kept as the helper's own invocation. Here the helper invocations are read
with the admitted unit's helper laws (`GkrSourceLaws`), each loop with the fold
of its callback's normal form, and the process over the common actions with the
common adapter. On a well-formed statement the original validator, read through
its acceptance output, is `GkrVerifier.verifier` (`verifier_reads`): one step of
the plain verifier per iteration of each loop, the same actions at the same
qualified sites, and the same decision.
-/

namespace ZkcExamples.Structured.GkrSourceVerifier
open Zkc.Source Zkc.Source.Structured SumcheckVerifierHelpers
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Protocols.Gkr

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-! ## Helper invocations of the plain participant tables -/

/-- The closed helper table of the admitted unit's plain participant tables. -/
abbrev closed : HelperTable (assignment F G) (participantInterface F G) :=
  (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed

/-- A helper law of the admitted unit's closed meanings is a law of its plain
participant tables. -/
theorem invoke_law (helper : Helper) (arguments : Values (assignment F G) helper.inputs)
    (results : Values (assignment F G) helper.outputs)
    (law : invoke (GkrSourceLaws.helpers (F := F) (G := G)) helper arguments = .done results) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed helper arguments = .done results := by
  rw [closed_invoke_plain]
  change (invoke (GkrSourceLaws.helpers (F := F) (G := G)) helper arguments).interpret _ = _
  rw [law]
  rfl

theorem append_plain (xs : List F) (x : F) :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.appendHelper (.cons xs (.cons x .nil)) =
      .done (.cons (xs ++ [x]) .nil) :=
  invoke_law _ _ _ (GkrSourceLaws.append_equation xs x)

theorem empty_plain :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.emptyHelper .nil = .done (.cons [] .nil) :=
  invoke_law _ _ _ GkrSourceLaws.empty_equation

/-! ## One step of each loop -/

/-- One round of a layer Sumcheck application of the original, over the common
actions, is one round of the plain verifier. -/
theorem round_reads (ctx : ProtocolContext) (handle : Nat) (state : List F × F) :
    (GkrRoundsNormalForms.verifierProcess (F := F) (G := G) ctx (some handle) (some state.1)
        (some state.2)).interpret CommonAdapter.project =
      (GkrVerifier.round ctx handle state).bind (fun next => .done (some next.1, some next.2)) := by
  simp only [GkrRoundsNormalForms.verifierProcess, GkrVerifier.round, GkrVerifier.roundFirst,
    GkrVerifier.roundSecond, GkrVerifier.roundCheck, PIR.Proc.interpret, CommonAdapter.project,
    PIR.Proc.bind, append_plain]
  refine congrArg (PIR.Proc.call _) (funext fun c0 => congrArg (PIR.Proc.call _) (funext fun c1 =>
    congrArg (PIR.Proc.call _) (funext fun c2 => ?_)))
  split
  · simp only [PIR.Proc.interpret, CommonAdapter.project, PIR.Proc.bind, GkrVerifier.roundChallenge]
    rfl
  · rfl

/-- One output-point iteration of the original is one output-point challenge and
its delivery. -/
theorem output_reads (ctx : ProtocolContext) (handle : Nat) (point : List F) :
    (GkrSourceNormalForms.verifierOutputProcess (F := F) (G := G) ctx (some handle)
        (some point)).interpret CommonAdapter.project =
      (GkrVerifier.outputRound ctx handle point).bind (fun next => .done (some next)) := by
  simp only [GkrSourceNormalForms.verifierOutputProcess, GkrVerifier.outputRound,
    GkrVerifier.outputDelivery, PIR.Proc.interpret, CommonAdapter.project, PIR.Proc.bind, append_plain]
  rfl

/-- One line-coefficient iteration of the original is one further coefficient. -/
theorem coefficient_reads (ctx : ProtocolContext) (coefficients : List F) :
    (GkrSourceNormalForms.verifierCoefficientProcess (F := F) (G := G) ctx
        (some coefficients)).interpret CommonAdapter.project =
      (GkrVerifier.lineCoefficient ctx coefficients).bind (fun next => .done (some next)) := by
  simp only [GkrSourceNormalForms.verifierCoefficientProcess, GkrVerifier.lineCoefficient,
    PIR.Proc.interpret, CommonAdapter.project, PIR.Proc.bind, append_plain]
  rfl

/-! ## Loops -/

/-- Repeated steps whose interpretation is a plain step on embedded states read as
the plain steps repeated. -/
theorem repeatN_reads {I J : PIR.Signature} (operations : PIR.OperationInterpretation I J)
    {S T : Type} (process : S → PIR.Proc I S) (step : T → PIR.Proc J T) (embed : T → S)
    (same : ∀ state, (process (embed state)).interpret operations =
      (step state).bind (fun next => .done (embed next))) :
    ∀ (count : Nat) (state : T), (PIR.repeatN count process (embed state)).interpret operations =
      (PIR.repeatN count step state).bind (fun next => .done (embed next))
  | 0, _ => rfl
  | count + 1, state => by
      simp only [PIR.repeatN, PIR.Proc.interpret_bind, same, PIR.Proc.bind_assoc, PIR.Proc.bind]
      congr 1
      funext next
      exact repeatN_reads operations process step embed same count next

/-! ## The layer Sumcheck -/

/-- The returned tuple of a layer Sumcheck application at the verifier, from its
point and value. -/
def roundsResults (result : List F × F) :
    Values (Component (assignment F G)) GkrRoundsNormalForms.roundsOutputs :=
  .cons none (.cons none (.cons none (.cons none (.cons none (.cons (some result.1)
    (.cons (some result.2) .nil))))))

/-- A layer Sumcheck application of the original at the verifier, over the common
actions, is the plain verifier's rounds, returning their point and value. -/
theorem rounds_reads (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1) (handle count : Nat)
    (bounded : count ≤ 4) (claim : F) :
    (GkrRoundsNormalForms.verifierRoundsProcess (F := F) (G := G) ctx (some claim) (some count)
        (some handle)).interpret CommonAdapter.project =
      (GkrVerifier.rounds ctx handle count claim).bind (fun result => .done (roundsResults result)) := by
  unfold GkrRoundsNormalForms.verifierRoundsProcess
  rw [empty_plain]
  simp only [PIR.Proc.bind, Values.get]
  rw [GkrRoundsNormalForms.verifier_fold ctx separate (some handle) count bounded
    (.cons none (.cons none (.cons none (.cons none (.cons none (.cons (some []) (.cons (some claim) .nil)))))))
    (some [], some claim) (GkrRoundsNormalForms.verifierState_masked ctx _ rfl (some []) (some claim))]
  rw [Finite.fold_range_repeatN (fun result => GkrRoundsNormalForms.verifierProcess ctx (some handle)
    result.1 result.2) 0 count (some [], some claim)]
  simp only [PIR.Proc.bind_assoc, PIR.Proc.bind, PIR.Proc.interpret_bind]
  rw [repeatN_reads CommonAdapter.project _ (GkrVerifier.round ctx handle)
    (fun state : List F × F => (some state.1, some state.2))
    (fun state => round_reads ctx handle state) count ([], claim)]
  simp only [GkrVerifier.rounds, PIR.Proc.bind_assoc, PIR.Proc.bind]
  rfl

theorem sum_plain (xs : List F) :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.sumHelper (.cons xs .nil) = .done (.cons xs.sum .nil) :=
  invoke_law _ _ _ (GkrSourceLaws.sum_equation xs)

theorem evaluate_plain (n : Nat) (xs point : List F) (table : Table F n)
    (decoded : ofList? n xs = some table) (length : point.length = n) (small : n < 64)
    (vectorBound : xs.length < indexLimit) :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.evaluateHelper (.cons xs (.cons point .nil)) =
      .done (.cons (extension n table (coordinates n point)) .nil) :=
  invoke_law _ _ _ (GkrSourceLaws.evaluate_extension n xs point table decoded length small vectorBound)

theorem selectBlock_plain (xs : List F) (position bits size : Nat)
    (shape : xs.length = 2 ^ bits * size) (positive : 0 < size) (inside : position < 2 ^ bits)
    (vectorBound : xs.length < indexLimit) :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.selectBlockHelper
        (.cons xs (.cons position (.cons bits .nil))) =
      .done (.cons (GkrSourceLaws.block xs position size) .nil) :=
  invoke_law _ _ _ (GkrSourceLaws.selectBlock_equation xs position bits size shape positive inside vectorBound)

theorem evaluateWiring_plain (w : Nat) (xs gate left right : List F)
    (table : Table F (w + w + w)) (decoded : ofList? (w + w + w) xs = some table)
    (gateLength : gate.length = w) (leftLength : left.length = w) (rightLength : right.length = w)
    (small : w + w + w < 64) (vectorBound : xs.length < indexLimit) :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.evaluateWiringHelper
        (.cons xs (.cons gate (.cons left (.cons right .nil)))) =
      .done (.cons (extension (w + w + w) table (coordinates (w + w + w) (gate ++ left ++ right))) .nil) :=
  invoke_law _ _ _ (GkrSourceLaws.evaluateWiring_extension w xs gate left right table decoded gateLength
    leftLength rightLength small vectorBound)

theorem evaluateCoefficients_plain (coefficients : List F) (point : F)
    (small : coefficients.length < indexLimit) :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.evaluateCoefficientsHelper
        (.cons coefficients (.cons point .nil)) =
      .done (.cons (powerSum coefficients point) .nil) :=
  invoke_law _ _ _ (GkrSourceLaws.evaluateCoefficients_equation coefficients point small)

theorem linePoint_plain (start finish : List F) (t : F) (sameLength : finish.length = start.length)
    (small : start.length < indexLimit) :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.linePointHelper (.cons start (.cons finish (.cons t .nil))) =
      .done (.cons (linePoints start finish t) .nil) :=
  invoke_law _ _ _ (GkrSourceLaws.linePoint_equation start finish t sameLength small)

/-! ## The plain verifier's returned values -/

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem outputRound_yields (ctx : ProtocolContext) (handle : Nat) (point : List F) :
    PIR.Yields (fun next : List F => next.length = point.length + 1)
      (GkrVerifier.outputRound (G := G) ctx handle point) :=
  fun _ _ => by simp [PIR.Yields]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem round_yields (ctx : ProtocolContext) (handle : Nat) (state : List F × F) :
    PIR.Yields (fun next : List F × F => next.1.length = state.1.length + 1)
      (GkrVerifier.round (G := G) ctx handle state) := by
  intro c0 c1 c2
  change PIR.Yields _ (GkrVerifier.roundCheck ctx handle state c0 c1 c2)
  unfold GkrVerifier.roundCheck
  split
  · exact fun _ _ => by simp [PIR.Yields]
  · trivial

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem rounds_yields (ctx : ProtocolContext) (handle count : Nat) (claim : F) :
    PIR.Yields (fun result : List F × F => result.1.length = count)
      (GkrVerifier.rounds (G := G) ctx handle count claim) := by
  have yields := PIR.Yields.repeatN (invariant := fun index (state : List F × F) => state.1.length = index)
    (step := GkrVerifier.round (G := G) ctx handle)
    (fun index state length => (round_yields ctx handle state).mono fun next same => by omega)
    count 0 ([], claim) rfl
  unfold GkrVerifier.rounds
  simpa using yields

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem lineCoefficient_yields (ctx : ProtocolContext) (coefficients : List F) :
    PIR.Yields (fun next : List F => next.length = coefficients.length + 1)
      (GkrVerifier.lineCoefficient (G := G) ctx coefficients) :=
  fun _ => by simp [PIR.Yields]

/-! ## One layer -/

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem lineCheck_pos (ctx : ProtocolContext) (handle width : Nat)
    (add mul : Wiring F width) (state : GkrVerifier.State F) (left right : List F) (claim first : F)
    (coefficients : List F)
    (check : claim = GkrVerifier.wiringValue
      (extension (width + width + width) add (coordinates (width + width + width) (state.2.1 ++ left ++ right)))
      (extension (width + width + width) mul (coordinates (width + width + width) (state.2.1 ++ left ++ right)))
      first coefficients.sum) :
    GkrVerifier.lineCheck (G := G) ctx handle width add mul state left right claim first coefficients =
      .call (.query (GkrVerifier.lineChallengeSite ctx) "bls12-381.fr" (.cons handle .nil))
        (GkrVerifier.lineDelivery ctx state left right coefficients) :=
  ite_eq_left_iff.mpr fun fails => absurd check fails

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem lineCheck_neg (ctx : ProtocolContext) (handle width : Nat)
    (add mul : Wiring F width) (state : GkrVerifier.State F) (left right : List F) (claim first : F)
    (coefficients : List F)
    (check : ¬ claim = GkrVerifier.wiringValue
      (extension (width + width + width) add (coordinates (width + width + width) (state.2.1 ++ left ++ right)))
      (extension (width + width + width) mul (coordinates (width + width + width) (state.2.1 ++ left ++ right)))
      first coefficients.sum) :
    GkrVerifier.lineCheck (G := G) ctx handle width add mul state left right claim first coefficients =
      .halt .reject :=
  ite_eq_right_iff.mpr fun holds => absurd holds check

theorem contexts_separate :
    ({} : ProtocolContext).roles 0 ≠ ({} : ProtocolContext).roles 1 ∧
      (GkrVerifier.leftContext {}).roles 0 ≠ (GkrVerifier.leftContext {}).roles 1 ∧
      (GkrVerifier.rightContext {}).roles 0 ≠ (GkrVerifier.rightContext {}).roles 1 := by
  decide

/-- One layer of the original at the verifier, over the common actions, is one
layer of the plain verifier: both layer Sumcheck applications, the line
polynomial's coefficients, the wiring check and the line challenge. -/
theorem layer_reads (handle layers width selector : Nat) (add mul : List F)
    (addTables mulTables : Nat → Wiring F width)
    (addShape : add.length = 2 ^ selector * 2 ^ (width + width + width))
    (mulShape : mul.length = 2 ^ selector * 2 ^ (width + width + width))
    (addBound : add.length < indexLimit) (mulBound : mul.length < indexLimit)
    (addDecoded : ∀ layer < layers, ofList? (width + width + width)
      (GkrSourceLaws.block add layer (2 ^ (width + width + width))) = some (addTables layer))
    (mulDecoded : ∀ layer < layers, ofList? (width + width + width)
      (GkrSourceLaws.block mul layer (2 ^ (width + width + width))) = some (mulTables layer))
    (selectorBound : layers ≤ 2 ^ selector) (widthBound : width ≤ 4)
    (state : GkrVerifier.State F) (inside : state.1 < layers) (pointLength : state.2.1.length = width) :
    (GkrSourceNormalForms.verifierLayerProcess (F := F) (G := G) {} state.1 (some add) (some mul)
        (some selector) (some width) (some handle) (some state.2.1) (some state.2.2)).interpret
        CommonAdapter.project =
      (GkrVerifier.layerStep {} handle width addTables mulTables state).bind
        (fun next => .done (some next.2.1, some next.2.2)) := by
  obtain ⟨layer, point, claim⟩ := state
  dsimp only at inside pointLength ⊢
  obtain ⟨separate, leftSeparate, rightSeparate⟩ := contexts_separate
  unfold GkrSourceNormalForms.verifierLayerProcess GkrVerifier.layerStep GkrVerifier.layerAfterLeft
  rw [PIR.Proc.interpret_bind, rounds_reads _ leftSeparate handle width widthBound claim,
    PIR.Proc.bind_assoc, PIR.Proc.bind_assoc]
  refine (rounds_yields _ handle width claim).bind_congr fun left leftLength => ?_
  simp only [PIR.Proc.bind, roundsResults, Values.get]
  rw [PIR.Proc.interpret_bind, rounds_reads _ rightSeparate handle width widthBound left.2,
    PIR.Proc.bind_assoc, PIR.Proc.bind_assoc]
  refine (rounds_yields _ handle width left.2).bind_congr fun right rightLength => ?_
  simp only [PIR.Proc.bind, roundsResults, Values.get, GkrVerifier.layerAfterRight,
    GkrVerifier.layerAfterConstant, PIR.Proc.interpret, PIR.Proc.interpret_bind, CommonAdapter.project,
    empty_plain, append_plain, List.nil_append]
  refine congrArg (PIR.Proc.call _) (funext fun first => ?_)
  have small : width + width + width < 64 := by omega
  have position : layer < 2 ^ selector := by omega
  have positive : 0 < 2 ^ (width + width + width) := by positivity
  have addBlock : (GkrSourceLaws.block add layer (2 ^ (width + width + width))).length < indexLimit :=
    Nat.lt_of_le_of_lt (by simp [GkrSourceLaws.block]) addBound
  have mulBlock : (GkrSourceLaws.block mul layer (2 ^ (width + width + width))).length < indexLimit :=
    Nat.lt_of_le_of_lt (by simp [GkrSourceLaws.block]) mulBound
  have fold := GkrSourceNormalForms.verifierCoefficient_fold (F := F) (G := G) {} separate none width
    widthBound (.cons (some [first]) .nil) (some [first])
    (GkrSourceNormalForms.verifierCoefficientState_masked {} _ rfl (some [first]))
  erw [fold]
  rw [Finite.fold_range_repeatN (fun result => GkrSourceNormalForms.verifierCoefficientProcess (G := G) {}
    result) 0 width (some [first]), PIR.Proc.interpret_bind,
    repeatN_reads CommonAdapter.project _ (GkrVerifier.lineCoefficient {}) some
      (fun coefficients => coefficient_reads {} coefficients) width [first]]
  simp only [PIR.Proc.bind_assoc, PIR.Proc.bind, PIR.Proc.interpret]
  have coefficientsYield := PIR.Yields.repeatN
    (invariant := fun index (coefficients : List F) => coefficients.length = index + 1)
    (step := GkrVerifier.lineCoefficient (G := G) {})
    (fun index coefficients length => (lineCoefficient_yields {} coefficients).mono fun next same => by
      omega) width 0 [first] rfl
  refine coefficientsYield.bind_congr fun coefficients coefficientsLength => ?_
  simp only [Nat.zero_add] at coefficientsLength
  have coefficientsBound : coefficients.length < indexLimit := by
    rw [coefficientsLength]; unfold indexLimit; omega
  have pointsBound : left.1.length < indexLimit := by rw [leftLength]; unfold indexLimit; omega
  simp only [GkrSourceNormalForms.verifierCoefficientState, Values.get, sum_plain,
    selectBlock_plain add layer selector _ addShape positive position addBound,
    selectBlock_plain mul layer selector _ mulShape positive position mulBound,
    evaluateWiring_plain width _ point left.1 right.1 (addTables layer) (addDecoded layer inside)
      pointLength leftLength rightLength small addBlock,
    evaluateWiring_plain width _ point left.1 right.1 (mulTables layer) (mulDecoded layer inside)
      pointLength leftLength rightLength small mulBlock,
    PIR.Proc.bind]
  have powers : ∀ t : F, invoke (closed (F := F) (G := G)) GkrSourceBodies.evaluateCoefficientsHelper
      (.cons coefficients (.cons t .nil)) = .done (.cons (powerSum coefficients t) .nil) :=
    fun t => evaluateCoefficients_plain coefficients t coefficientsBound
  have points : ∀ t : F, invoke (closed (F := F) (G := G)) GkrSourceBodies.linePointHelper
      (.cons left.1 (.cons right.1 (.cons t .nil))) = .done (.cons (linePoints left.1 right.1 t) .nil) :=
    fun t => linePoint_plain left.1 right.1 t (by rw [leftLength, rightLength]) pointsBound
  split
  · rename_i check
    rw [lineCheck_pos {} handle width (addTables layer) (mulTables layer) (layer, point, claim) left.1 right.1
      right.2 first coefficients check]
    refine congrArg (PIR.Proc.call _) (funext fun challenge => congrArg (PIR.Proc.call _)
      (funext fun _ => ?_))
    simp only [PIR.Proc.bind]
    rw [powers challenge, points challenge]
    rfl
  · rename_i check
    rw [lineCheck_neg {} handle width (addTables layer) (mulTables layer) (layer, point, claim) left.1 right.1
      right.2 first coefficients check]
    rfl

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- A layer step advances the layer index and keeps the point's length. -/
theorem layerStep_yields (handle width : Nat) (addTables mulTables : Nat → Wiring F width)
    (state : GkrVerifier.State F) :
    PIR.Yields (fun next : GkrVerifier.State F => next.1 = state.1 + 1 ∧ next.2.1.length = width)
      (GkrVerifier.layerStep (G := G) {} handle width addTables mulTables state) := by
  unfold GkrVerifier.layerStep
  refine (rounds_yields _ handle width state.2.2).bind fun left leftLength => ?_
  unfold GkrVerifier.layerAfterLeft
  refine (rounds_yields _ handle width left.2).bind fun right rightLength => ?_
  intro first
  refine PIR.Yields.bind (property := fun _ => True) ?_ fun coefficients _ => ?_
  · exact PIR.Yields.mono (property := fun _ => True) (by
      have := PIR.Yields.repeatN (invariant := fun _ (_ : List F) => True)
        (step := GkrVerifier.lineCoefficient (G := G) {}) (fun _ _ _ => fun _ => trivial) width 0 [first] trivial
      exact this) fun _ _ => trivial
  unfold GkrVerifier.lineCheck
  split
  · intro challenge _
    refine ⟨rfl, ?_⟩
    simp [linePoints_length, leftLength, rightLength]
  · trivial

/-- The layer loop of the original reads as the plain verifier's repeated layer
steps, from any layer whose point has the width. -/
theorem layers_reads (handle layers width selector : Nat) (add mul : List F)
    (addTables mulTables : Nat → Wiring F width)
    (addShape : add.length = 2 ^ selector * 2 ^ (width + width + width))
    (mulShape : mul.length = 2 ^ selector * 2 ^ (width + width + width))
    (addBound : add.length < indexLimit) (mulBound : mul.length < indexLimit)
    (addDecoded : ∀ layer < layers, ofList? (width + width + width)
      (GkrSourceLaws.block add layer (2 ^ (width + width + width))) = some (addTables layer))
    (mulDecoded : ∀ layer < layers, ofList? (width + width + width)
      (GkrSourceLaws.block mul layer (2 ^ (width + width + width))) = some (mulTables layer))
    (selectorBound : layers ≤ 2 ^ selector) (widthBound : width ≤ 4) :
    ∀ (count : Nat) (state : GkrVerifier.State F), state.1 + count ≤ layers → state.2.1.length = width →
      (Finite.fold (fun (result : Option (List F) × Option F) index =>
          GkrSourceNormalForms.verifierLayerProcess (F := F) (G := G) {} index (some add) (some mul)
            (some selector) (some width) (some handle) result.1 result.2)
          (List.range' state.1 count) (some state.2.1, some state.2.2)).interpret CommonAdapter.project =
        (PIR.repeatN count (GkrVerifier.layerStep {} handle width addTables mulTables) state).bind
          (fun next => .done (some next.2.1, some next.2.2))
  | 0, _, _, _ => rfl
  | count + 1, state, bounded, pointLength => by
      rw [List.range'_succ]
      simp only [Finite.fold, PIR.repeatN, PIR.Proc.interpret_bind]
      rw [layer_reads handle layers width selector add mul addTables mulTables addShape mulShape addBound
        mulBound addDecoded mulDecoded selectorBound widthBound state (by omega) pointLength,
        PIR.Proc.bind_assoc, PIR.Proc.bind_assoc]
      refine (layerStep_yields handle width addTables mulTables state).bind_congr fun next valid => ?_
      simp only [PIR.Proc.bind]
      have rest := layers_reads handle layers width selector add mul addTables mulTables addShape mulShape
        addBound mulBound addDecoded mulDecoded selectorBound widthBound count next (by omega) valid.2
      rw [valid.1] at rest
      exact rest

/-! ## The verifier -/

/-- On a well-formed statement (decoded input and output tables, stacked wiring
tables whose blocks decode, loop counts within the Entry's maxima), the original
GKR validator at the verifier, read through its acceptance output over the
common actions, is the plain GKR verifier. -/
theorem verifier_reads (handle : Nat) (inputs outputs add mul : List F) (layers selector width : Nat)
    (outputsTable inputsTable : Table F width)
    (outputsDecoded : ofList? width outputs = some outputsTable)
    (inputsDecoded : ofList? width inputs = some inputsTable)
    (addTables mulTables : Nat → Wiring F width)
    (addShape : add.length = 2 ^ selector * 2 ^ (width + width + width))
    (mulShape : mul.length = 2 ^ selector * 2 ^ (width + width + width))
    (addBound : add.length < indexLimit) (mulBound : mul.length < indexLimit)
    (addDecoded : ∀ layer < layers, ofList? (width + width + width)
      (GkrSourceLaws.block add layer (2 ^ (width + width + width))) = some (addTables layer))
    (mulDecoded : ∀ layer < layers, ofList? (width + width + width)
      (GkrSourceLaws.block mul layer (2 ^ (width + width + width))) = some (mulTables layer))
    (selectorBound : layers ≤ 2 ^ selector) (widthBound : width ≤ 4) (layersBound : layers ≤ 4) :
    ((GkrSourceViews.program.participant F G 1 (.cons (some inputs) (.cons (some outputs) (.cons (some add)
        (.cons (some mul) (.cons (some layers) (.cons (some selector) (.cons (some width)
          (.cons (some handle) .nil))))))))).bind fun result => .done (result.get .here)).interpret
        CommonAdapter.project =
      GkrVerifier.verifier {} handle layers width outputsTable inputsTable addTables mulTables := by
  obtain ⟨separate, -, -⟩ := contexts_separate
  have small : width < 64 := by omega
  have tableBound : 2 ^ width < indexLimit := by
    unfold indexLimit
    exact Nat.pow_lt_pow_right (by decide) small
  have outputsBound : outputs.length < indexLimit := by
    rw [ofList?_length _ _ outputsDecoded]; exact tableBound
  have inputsBound : inputs.length < indexLimit := by
    rw [ofList?_length _ _ inputsDecoded]; exact tableBound
  rw [GkrSourceNormalForms.verifier_participant, PIR.Proc.bind_assoc]
  simp only [PIR.Proc.bind]
  unfold GkrSourceNormalForms.verifierProcess
  rw [empty_plain]
  simp only [PIR.Proc.bind, Values.get]
  have outputFold := GkrSourceNormalForms.verifierOutput_fold (F := F) (G := G) {} separate (some handle)
    width widthBound (.cons (some []) (.cons none .nil)) (some [])
    (GkrSourceNormalForms.verifierOutputState_masked {} _ rfl (some []))
  erw [outputFold]
  rw [Finite.fold_range_repeatN (fun result => GkrSourceNormalForms.verifierOutputProcess (G := G) {}
      (some handle) result) 0 width (some []),
    PIR.Proc.bind_assoc, PIR.Proc.bind_assoc, PIR.Proc.interpret_bind,
    repeatN_reads CommonAdapter.project _ (GkrVerifier.outputRound {} handle) some
      (fun point => output_reads {} handle point) width []]
  unfold GkrVerifier.verifier
  rw [PIR.Proc.bind_assoc]
  have outputsYield := PIR.Yields.repeatN (invariant := fun index (point : List F) => point.length = index)
    (step := GkrVerifier.outputRound (G := G) {} handle)
    (fun index point length => (outputRound_yields {} handle point).mono fun next same => by omega)
    width 0 [] rfl
  refine outputsYield.bind_congr fun point pointLength => ?_
  simp only [Nat.zero_add] at pointLength
  simp only [PIR.Proc.bind, GkrSourceNormalForms.verifierOutputState, Values.get,
    evaluate_plain width outputs point outputsTable outputsDecoded pointLength small outputsBound]
  have layerFold := GkrSourceNormalForms.verifierLayer_fold (F := F) (G := G) {} separate (some inputs)
    (some add) (some mul) (some layers) (some selector) (some width) (some handle) layers layersBound
    (.cons (some point) (.cons none (.cons (some (extension width outputsTable (coordinates width point))) .nil)))
    (some point, some (extension width outputsTable (coordinates width point)))
    (GkrSourceNormalForms.verifierLayerState_masked {} _ rfl (some point)
      (some (extension width outputsTable (coordinates width point))))
  erw [layerFold]
  rw [PIR.Proc.bind_assoc, PIR.Proc.bind_assoc, PIR.Proc.interpret_bind]
  have layersRead := layers_reads (G := G) handle layers width selector add mul addTables mulTables addShape
    mulShape addBound mulBound addDecoded mulDecoded selectorBound widthBound layers
    (0, point, extension width outputsTable (coordinates width point)) (by simp) pointLength
  erw [layersRead]
  unfold GkrVerifier.afterOutputs
  rw [PIR.Proc.bind_assoc]
  have layersYield := PIR.Yields.repeatN
    (invariant := fun index (state : GkrVerifier.State F) => state.1 = index ∧ state.2.1.length = width)
    (step := GkrVerifier.layerStep (G := G) {} handle width addTables mulTables)
    (fun index state valid => (layerStep_yields handle width addTables mulTables state).mono
      fun next advanced => ⟨by rw [advanced.1, valid.1], advanced.2⟩)
    layers 0 (0, point, extension width outputsTable (coordinates width point)) ⟨rfl, pointLength⟩
  refine layersYield.bind_congr fun final valid => ?_
  simp only [PIR.Proc.bind, GkrSourceNormalForms.verifierLayerState, Values.get,
    evaluate_plain width inputs final.2.1 inputsTable inputsDecoded valid.2 small inputsBound]
  rfl

end ZkcExamples.Structured.GkrSourceVerifier
