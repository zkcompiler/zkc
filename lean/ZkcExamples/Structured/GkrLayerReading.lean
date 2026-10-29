module

public import ZkcExamples.Structured.Generated.Presentations.Gkr
public import ZkcExamples.Structured.SumcheckVerifierHelpers
public import ZkcExamples.Structured.GkrVerifierProcess
public import ZkcExamples.Structured.GkrRoundsReading
public import Zkc.Semantics.Yields
public import Zkc.Source.TypedABI

@[expose] public section

/-! Current-source layer and output correspondence. Pending Rounds retain the
left prefix; the actual source split supplies the independent right point. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Structured.GkrLayerReading
open Zkc.Source Zkc.Source.Structured SumcheckVerifierHelpers
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Protocols.Gkr GkrRoundsReading

structured_associations GkrSourceViews [sourceHelper50 := GkrSourceBodies.sourceHelper50]

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem tuple19_plain (point : List F) (claim : F) :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.sourceHelper19Helper
      (.cons point (.cons claim .nil)) = .done (.cons point (.cons claim .nil)) := by kernel_rfl

theorem tuple20_plain (point : List F) (claim : F) :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.sourceHelper20Helper
      (.cons point (.cons claim .nil)) = .done (.cons point (.cons claim .nil)) := by kernel_rfl

theorem pending_plain (claim : F) :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.sourceHelper37Helper
      (.cons claim .nil) = .done (.cons [] (.cons claim .nil)) := by kernel_rfl

theorem split_pending_plain (left right : List F) (sameLength : right.length = left.length)
    (bounded : (left ++ right).length < indexLimit) :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.sourceHelper50Helper
      (.cons (left ++ right) .nil) = .done (.cons left (.cons right .nil)) := by
  apply invoke_law
  rw [sourceHelper50_association.invoke GkrSourceViews.unit.linked]
  have joinedBound : left.length + right.length < indexLimit := by simpa only [List.length_append] using bounded
  have half : (left ++ right).length / 2 = left.length := by simp only [List.length_append]; omega
  have joinedHalf : (left.length + right.length) / 2 = left.length := by omega
  have joinedEven : (left.length + right.length) % 2 = 0 := by omega
  have even : (left ++ right).length % 2 = 0 := by simp only [List.length_append]; omega
  by_cases empty : left.length = 0
  · have le : left = [] := List.length_eq_zero_iff.mp empty
    have re : right = [] := List.length_eq_zero_iff.mp (sameLength.trans empty)
    subst left; subst right
    simp [GkrSourceBodies.sourceHelper50Body, Region.denote, meaning, Evaluation.meaning,
      Evaluation.operation, Operands.eval, Regions.denote, TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get_cons,
      Environment.prepend, Environment.push, SiteObservations.closed,
      SiteObservations.silent, PIR.Process.bind, Primitive.evaluate, primitiveOutcome,
      checkedIndices, show 0 < indexLimit by decide, Evaluation.invokeCallback]
  · have nonempty : left ≠ [] := by intro h; simp [h] at empty
    have positive : 0 < (left ++ right).length := by simp only [List.length_append]; omega
    simp [GkrSourceBodies.sourceHelper50Body, Region.denote, meaning, Evaluation.meaning,
      Evaluation.operation, Operands.eval, Regions.denote, TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get_cons,
      Environment.prepend, Environment.push, SiteObservations.closed,
      SiteObservations.silent, PIR.Process.bind, Primitive.evaluate, primitiveOutcome,
      checkedIndices, bounded, joinedBound, show 0 < indexLimit by decide, Evaluation.invokeCallback,
      nonempty, empty, positive, even, half, joinedHalf, joinedEven,
      show 0 < left.length by omega, Values.get, List.take_left, List.drop_left]

theorem output_reads (ctx : ProtocolContext) (handle : Nat) (point : List F) :
    (Generated.Presentations.Gkr.Root.verifierOutputProcess (F := F) (G := G) ctx (some handle)
        (some point)).interpret CommonAdapter.project =
      (GkrVerifier.outputRound ctx handle point).bind (fun next => .done (some next)) := by
  simp only [Generated.Presentations.Gkr.Root.verifierOutputProcess, GkrVerifier.outputRound,
    GkrVerifier.outputDelivery, PIR.Process.interpret, CommonAdapter.project, PIR.Process.bind, GkrRoundsReading.append_plain]
  rfl

/-- One line-coefficient iteration of the original is one further coefficient. -/
theorem coefficient_reads (ctx : ProtocolContext) (coefficients : List F) :
    (Generated.Presentations.Gkr.Root.verifierCoefficientProcess (F := F) (G := G) ctx
        (some coefficients)).interpret CommonAdapter.project =
      (GkrVerifier.lineCoefficient ctx coefficients).bind (fun next => .done (some next)) := by
  simp only [Generated.Presentations.Gkr.Root.verifierCoefficientProcess, GkrVerifier.lineCoefficient,
    PIR.Process.interpret, CommonAdapter.project, PIR.Process.bind, GkrRoundsReading.append_plain]
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
    (Generated.Presentations.Gkr.Root.verifierLayerProcess (F := F) (G := G) {} state.1 (some add) (some mul)
        (some selector) (some width) (some handle) (some state.2.1) (some state.2.2)).interpret
        CommonAdapter.project =
      (GkrVerifier.layerStep {} handle width addTables mulTables state).bind
        (fun next => .done (some next.2.1, some next.2.2)) := by
  obtain ⟨layer, point, claim⟩ := state
  dsimp only at inside pointLength ⊢
  obtain ⟨separate, leftSeparate, rightSeparate⟩ := contexts_separate
  unfold Generated.Presentations.Gkr.Root.verifierLayerProcess GkrVerifier.layerStep GkrVerifier.layerAfterLeft
  simp only [Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload, Generated.Presentations.Gkr.program, GkrSourceViews.program, Generated.Presentations.Gkr.Rounds.verifierRoundsView, Bindings.optionalPattern, NormalForm.InputPattern.environment, tuple20_plain, pending_plain, PIR.Process.bind, TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get_cons, Values.get, PIR.Process.bind_assoc]
  erw [PIR.Process.interpret_bind, GkrRoundsReading.reads _ leftSeparate handle width widthBound [] claim]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  refine (rounds_yields _ handle width claim).bind_congr fun left leftLength => ?_
  simp only [PIR.Process.bind, GkrRoundsReading.roundsResults, TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get_cons, List.nil_append]
  erw [PIR.Process.interpret_bind, GkrRoundsReading.reads _ rightSeparate handle width widthBound left.1 left.2]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  refine (rounds_yields _ handle width left.2).bind_congr fun right rightLength => ?_
  simp only [PIR.Process.bind, GkrRoundsReading.roundsResults, Values.get, GkrVerifier.layerAfterRight,
    GkrVerifier.layerAfterConstant, GkrRoundsReading.tuple40_plain, TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get_cons, split_pending_plain left.1 right.1
      (by omega) (by rw [List.length_append, leftLength, rightLength]; unfold indexLimit; omega), PIR.Process.interpret, PIR.Process.interpret_bind, CommonAdapter.project,
    GkrRoundsReading.empty_plain, GkrRoundsReading.append_plain, List.nil_append]
  refine congrArg (PIR.Process.call _) (funext fun first => ?_)
  have small : width + width + width < 64 := by omega
  have position : layer < 2 ^ selector := by omega
  have positive : 0 < 2 ^ (width + width + width) := by positivity
  have addBlock : (GkrSourceLaws.block add layer (2 ^ (width + width + width))).length < indexLimit :=
    Nat.lt_of_le_of_lt (by simp [GkrSourceLaws.block]) addBound
  have mulBlock : (GkrSourceLaws.block mul layer (2 ^ (width + width + width))).length < indexLimit :=
    Nat.lt_of_le_of_lt (by simp [GkrSourceLaws.block]) mulBound
  have fold := Generated.Presentations.Gkr.Root.verifierCoefficient_fold (F := F) (G := G) {} (.ofSeparate separate (by decide)) none width
    widthBound (.cons (some [first]) .nil) (some [first])
    (Generated.Presentations.Gkr.Root.verifierCoefficientState_masked {} _ rfl (some [first]))
  erw [fold]
  rw [Finite.fold_range_repeatN (fun result => Generated.Presentations.Gkr.Root.verifierCoefficientProcess (G := G) {}
    result) 0 width (some [first]), PIR.Process.interpret_bind,
    GkrRoundsReading.repeatN_reads CommonAdapter.project _ (GkrVerifier.lineCoefficient {}) some
      (fun coefficients => coefficient_reads {} coefficients) width [first]]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, PIR.Process.interpret]
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
  simp only [Generated.Presentations.Gkr.Root.verifierCoefficientState, Values.get, sum_plain,
    selectBlock_plain add layer selector _ addShape positive position addBound,
    selectBlock_plain mul layer selector _ mulShape positive position mulBound,
    evaluateWiring_plain width _ point left.1 right.1 (addTables layer) (addDecoded layer inside)
      pointLength leftLength rightLength small addBlock,
    evaluateWiring_plain width _ point left.1 right.1 (mulTables layer) (mulDecoded layer inside)
      pointLength leftLength rightLength small mulBlock,
    PIR.Process.bind]
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
    refine congrArg (PIR.Process.call _) (funext fun challenge => congrArg (PIR.Process.call _)
      (funext fun _ => ?_))
    simp only [PIR.Process.bind]
    simp only [points challenge, powers challenge, tuple19_plain, PIR.Process.bind, TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get_cons]
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
          Generated.Presentations.Gkr.Root.verifierLayerProcess (F := F) (G := G) {} index (some add) (some mul)
            (some selector) (some width) (some handle) result.1 result.2)
          (List.range' state.1 count) (some state.2.1, some state.2.2)).interpret CommonAdapter.project =
        (PIR.repeatN count (GkrVerifier.layerStep {} handle width addTables mulTables) state).bind
          (fun next => .done (some next.2.1, some next.2.2))
  | 0, _, _, _ => rfl
  | count + 1, state, bounded, pointLength => by
      rw [List.range'_succ]
      simp only [Finite.fold, PIR.repeatN, PIR.Process.interpret_bind]
      rw [layer_reads handle layers width selector add mul addTables mulTables addShape mulShape addBound
        mulBound addDecoded mulDecoded selectorBound widthBound state (by omega) pointLength,
        PIR.Process.bind_assoc, PIR.Process.bind_assoc]
      refine (layerStep_yields handle width addTables mulTables state).bind_congr fun next valid => ?_
      simp only [PIR.Process.bind]
      have rest := layers_reads handle layers width selector add mul addTables mulTables addShape mulShape
        addBound mulBound addDecoded mulDecoded selectorBound widthBound count next (by omega) valid.2
      rw [valid.1] at rest
      exact rest

/-! ## The verifier -/


end ZkcExamples.Structured.GkrLayerReading
