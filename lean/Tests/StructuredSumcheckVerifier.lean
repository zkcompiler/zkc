import Tests.StructuredSumcheckVerifierExecution
import Tests.StructuredSumcheckVerifierMutations
import ZkcExamples.Structured.SumcheckReduceVerifier
import ZkcExamples.Structured.SumcheckSourceVerifier
import ZkcExamples.Structured.SumcheckContractRequests

/-! Kernel consumers of the actual source equations. Executable controls above
exercise complete originals and independently re-admitted source mutants. -/
set_option autoImplicit false

namespace Tests.StructuredSumcheckVerifier
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured
open Tests.StructuredSumcheckVerifierSupport
open Tests.StructuredSumcheckVerifierExecution

/-- Zero Reduction rounds preserve a present claim without P operands or service. -/
theorem zero_reduction_without_service :
    SumcheckReduceViews.program.participant (ZMod 5) (ZMod 5) 1
      (SumcheckReduceVerifier.reduceRootInputs none none (some 0) (some 0) none) =
        .done (.cons none (.cons none (.cons (some []) (.cons (some 0) .nil)))) := by
  rw [SumcheckReduceVerifier.verifier_optional]
  rfl

theorem missing_count_before_other_missing_inputs :
    SumcheckReduceViews.program.participant (ZMod 5) (ZMod 5) 1
      (SumcheckReduceVerifier.reduceRootInputs none none none none none) =
        .halt .incomplete := by
  rw [SumcheckReduceVerifier.verifier_optional]
  rfl

theorem source_count_three_refused :
    SumcheckSourceViews.program.participant (ZMod 5) (ZMod 5) 1
      (SumcheckSourceVerifier.sourceRootInputs none (some 0) (some 3) none) =
        .halt .refused := by
  rw [SumcheckSourceVerifier.verifier_optional]
  rfl

theorem zero_source_checks_singleton_without_service :
    SumcheckSourceViews.program.participant (ZMod 5) (ZMod 5) 1
      (SumcheckSourceVerifier.sourceRootInputs (some [3]) (some 3) (some 0) none) =
        .done (.cons (some true) .nil) := by
  rw [SumcheckSourceVerifier.verifier_optional]
  change SumcheckVerifierTerminal.actualOwnedCheck (F := ZMod 5) (G := ZMod 5)
    SumcheckSourceViews.unit 1 (some [3]) (some []) (some 3) = _
  rw [SumcheckVerifierTerminal.terminal_equation 1 _ _ _ (by decide) (by decide)]
  rfl

/-- A false mathematical terminal answer is returned, rather than a guard stop. -/
theorem zero_source_false_claim_returns_false :
    SumcheckSourceViews.program.participant (ZMod 5) (ZMod 5) 1
      (SumcheckSourceVerifier.sourceRootInputs (some [3]) (some 4) (some 0) none) =
        .done (.cons (some false) .nil) := by
  rw [SumcheckSourceVerifier.verifier_optional]
  change SumcheckVerifierTerminal.actualOwnedCheck (F := ZMod 5) (G := ZMod 5)
    SumcheckSourceViews.unit 1 (some [3]) (some []) (some 4) = _
  rw [SumcheckVerifierTerminal.terminal_equation 1 _ _ _ (by decide) (by decide)]
  rfl

/-- Characteristic two: the received endpoints sum to zero, but interpolation
at the actual challenge one returns one. No division by two is available. -/
theorem characteristic_two_source_arithmetic :
    reduceRun (some (0 : ZMod 2)) (some 1) (some 7)
      ⟨[.value 1, .value 1, .value 1, .ack], 0⟩ =
        ⟨.returned (some [1], some 1), ⟨[], 4⟩, roundEvents reduceContext 7 1 1 1⟩ := by
  change ((SumcheckReduceViews.program.participant (ZMod 2) (ZMod 2) 1
    (SumcheckReduceVerifier.reduceRootInputs none none (some 0) (some 1) (some 7))).bind
      (fun values => .done (reduceResult values))).run handler
        ⟨[.value 1, .value 1, .value 1, .ack], 0⟩ = _
  rw [SumcheckReduceVerifier.verifier_optional]
  rfl

/-- The source equation works in a nonfield, including a nonunit challenge. -/
theorem nonfield_source_arithmetic :
    reduceRun (some (3 : ZMod 4)) (some 1) (some 7)
      ⟨[.value 1, .value 2, .value 2, .ack], 0⟩ =
        ⟨.returned (some [2], some 3), ⟨[], 4⟩, roundEvents reduceContext 7 1 2 2⟩ := by
  change ((SumcheckReduceViews.program.participant (ZMod 4) (ZMod 4) 1
    (SumcheckReduceVerifier.reduceRootInputs none none (some 3) (some 1) (some 7))).bind
      (fun values => .done (reduceResult values))).run handler
        ⟨[.value 1, .value 2, .value 2, .ack], 0⟩ = _
  rw [SumcheckReduceVerifier.verifier_optional]
  rfl

/-- The complete Source root appends the query reply and checks its unchanged
raw V table against the resulting point and claim. -/
theorem source_uses_actual_challenge :
    sourceRun (some [0, 1]) (some (1 : ZMod 5)) (some 1) (some 7)
      ⟨[.value 0, .value 1, .value 1, .ack], 0⟩ =
        ⟨.returned (some true), ⟨[], 4⟩, roundEvents sourceContext 7 0 1 1⟩ := by
  change ((SumcheckSourceViews.program.participant (ZMod 5) (ZMod 5) 1
    (SumcheckSourceVerifier.sourceRootInputs (some [0, 1]) (some 1) (some 1) (some 7))).bind
      (fun values => .done (values.get .here))).run handler
        ⟨[.value 0, .value 1, .value 1, .ack], 0⟩ = _
  rw [SumcheckSourceVerifier.verifier_optional]
  change (((SumcheckVerifierPrelude.admittedRounds (F := ZMod 5) (G := ZMod 5)
    2 SumcheckSourceVerifier.childContext (some 1) (some 7) (some 1)).bind
      (fun pc => SumcheckVerifierTerminal.actualOwnedCheck SumcheckSourceViews.unit 1
        (some [0, 1]) pc.1 pc.2)).bind
      (fun (values : Values (Component (assignment (ZMod 5) (ZMod 5))) [.boolean]) =>
        .done (values.get .here))).run handler
        ⟨[.value 0, .value 1, .value 1, .ack], 0⟩ = _
  rw [PIR.Process.bind_assoc, PIR.run_bind]
  have rounds :
      (SumcheckVerifierPrelude.admittedRounds (F := ZMod 5) (G := ZMod 5)
        2 SumcheckSourceVerifier.childContext (some 1) (some 7) (some 1)).run handler
          ⟨[.value 0, .value 1, .value 1, .ack], 0⟩ =
        ⟨.returned (some [1], some 1), ⟨[], 4⟩, roundEvents sourceContext 7 0 1 1⟩ := rfl
  rw [rounds]
  dsimp only [PIR.Execution.follow]
  rw [SumcheckVerifierTerminal.terminal_equation 1 _ _ _ (by decide) (by decide)]
  rfl

/-- The callback equation retains delayed point demand after the send acknowledgement. -/
theorem absent_callback_point_after_delivery :
    (Repeat.step (SumcheckVerifierBodies.repeatSpec 4) reduceContext 1
      (SumcheckVerifierLaws.cap (F := ZMod 5) (G := ZMod 5) (some 7))
      (SumcheckVerifierLaws.bodyFn SumcheckReduceViews.unit reduceContext 1)
      (SumcheckVerifierLaws.embedV (none, some 1)) 0).run handler
        ⟨[.value 0, .value 1, .value 1, .ack, .value 4], 0⟩ =
      ⟨.stopped .incomplete, ⟨[.value 4], 4⟩, roundEvents reduceContext 7 0 1 1⟩ := by
  rw [SumcheckVerifierLaws.round_optional (F := ZMod 5) (G := ZMod 5)
    _ SumcheckReduceVerifier.helperBodies reduceContext 1 rfl (by decide)
    4 0 (some 7) (none, some 1)]
  rfl

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- A symbolic length premise avoids constructing an oversized test allocation. -/
theorem terminal_point_overflow_first (raw point : List F) (claim : F)
    (overflow : Zkc.Source.Structured.indexLimit ≤ point.length) :
    SumcheckVerifierTerminal.actualOwnedCheck (G := G) SumcheckSourceViews.unit 1
      (some raw) (some point) (some claim) = .halt .exhausted := by
  rw [SumcheckVerifierTerminal.terminal_decision]
  simp only [Nat.not_lt.mpr overflow, ↓reduceIte]

/-- Large representable point dimension returns false before inspecting raw length. -/
theorem terminal_large_dimension_before_raw_length (raw point : List F) (claim : F)
    (representable : point.length < Zkc.Source.Structured.indexLimit) (large : 64 ≤ point.length) :
    SumcheckVerifierTerminal.actualOwnedCheck (G := G) SumcheckSourceViews.unit 1
      (some raw) (some point) (some claim) = .done (.cons (some false) .nil) := by
  rw [SumcheckVerifierTerminal.terminal_decision]
  simp only [representable, Nat.not_lt.mpr large, ↓reduceIte]

theorem terminal_raw_overflow_after_small_point (raw point : List F) (claim : F)
    (representable : point.length < Zkc.Source.Structured.indexLimit) (small : point.length < 64)
    (overflow : Zkc.Source.Structured.indexLimit ≤ raw.length) :
    SumcheckVerifierTerminal.actualOwnedCheck (G := G) SumcheckSourceViews.unit 1
      (some raw) (some point) (some claim) = .halt .exhausted := by
  rw [SumcheckVerifierTerminal.terminal_decision]
  simp only [representable, small, Nat.not_lt.mpr overflow, ↓reduceIte]

open SumcheckContractBindings SumcheckContractInterpretations SumcheckContractRequests

variable (environment : RelationEnvironment SumcheckSourceViews.imported (ZMod 5) (ZMod 5))

/-- The extra input clause must not become the public request's selected target. -/
theorem public_request_selects_named_target :
    (publicSelection (sourceEnvironment := environment)).selection =
      .subject (publicOwner.namedClause "public_sum") ∧
      publicOwner.namedClause "public_sum" = ⟨1, by decide⟩ := ⟨rfl, rfl⟩

theorem child_request_uses_actual_formula :
    childFormula.original.name = SumcheckRelationContract.pendingHelper.name ∧
      childFormula.original.kind = .math := ⟨rfl, rfl⟩

/-- An input formula has no acceptance selector, even on a returned boundary. -/
theorem shape_clause_cannot_accept
    (boundary : BoundaryValuation (assignment (ZMod 5) (ZMod 5))
      publicOwner.protocol.inputs publicOwner.protocol.outputs) :
    ¬ (publicContract (sourceEnvironment := environment)).Accepts {}
      (publicOwner.namedClause "shape") boundary := by
  rintro ⟨selector, selected, _⟩
  change none = some selector at selected
  cases selected

/-- A true sum does not imply the independent input-shape clause. The target
translation remains available without assuming honest input shape. -/
theorem true_sum_with_false_shape :
    PublicTruth (G := ZMod 5) ([0] : List (ZMod 5)) 0 ∧
      inputShapeFormula.invokeRelation (F := ZMod 5) (G := ZMod 5)
        (.cons [0] (.cons 1 .nil)) = .done (.cons false .nil) := by
  constructor
  · exact (public_truth_iff _ _ (by decide)).mpr (by decide)
  · rw [input_shape_formula_equation]
    rfl

/-- False-claim refutation is still available on the same malformed shape. -/
theorem public_refutation_without_honest_shape :
    (publicRefutation (sourceEnvironment := environment)
      ([0] : List (ZMod 5)) 1 1 0).Meaning := by
  intro holds
  have translation := public_translation (sourceEnvironment := environment)
    ([0] : List (ZMod 5)) 1 1 0 (.stopped .incomplete) (by decide)
  have equality := ((publicUse (sourceEnvironment := environment)
    ([0] : List (ZMod 5)) 1 1 0 (.stopped .incomplete)).equivalence translation).mp holds
  exact (by decide : (1 : ZMod 5) ≠ ([0] : List (ZMod 5)).sum) equality

theorem zero_round_shape_accepts_singleton :
    inputShapeFormula.invokeRelation (F := ZMod 5) (G := ZMod 5)
      (.cons [3] (.cons 0 .nil)) = .done (.cons true .nil) := by
  rw [input_shape_formula_equation]
  rfl

/-- Reading both parameter coordinates from the actual boundary preserves an
absent count instead of shifting another input into that coordinate. -/
theorem missing_shape_count_is_unavailable :
    let input : ComponentInput publicOwner (ZMod 5) (ZMod 5) :=
      ⟨{}, 1, SumcheckSourceVerifier.sourceRootInputs (some [0]) (some 0) none none⟩
    let boundary := input.boundary (.stopped .incomplete)
    inputShapeApplication.read {} boundary
      (⟨fun _ selector => selector.read {} boundary, fun _ _ => none⟩ :
        LogicalAssignments (assignment (ZMod 5) (ZMod 5)) publicOwner rootInvocation) = none := rfl

/-- The formula's power test is mathematical even beyond machine dimensions. -/
theorem power_test_has_no_machine_cutoff (rounds : Nat) :
    naturalPowerOfTwo (2 ^ rounds) rounds = true :=
  (naturalPowerOfTwo_eq_true _ _).mpr rfl

/-- Reject an excessive mathematical dimension without an index-admission premise. -/
theorem shape_excess_is_false (raw : List F) (rounds : Nat) (excess : 2 < rounds) :
    inputShapeFormula.invokeRelation (F := F) (G := G)
      (.cons raw (.cons rounds .nil)) = .done (.cons false .nil) := by
  rw [input_shape_formula_equation]
  simp only [Nat.not_le_of_lt excess, and_false, decide_false]

end Tests.StructuredSumcheckVerifier
