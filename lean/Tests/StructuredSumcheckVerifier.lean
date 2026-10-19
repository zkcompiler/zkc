import Tests.StructuredSumcheckVerifierExecution
import Tests.StructuredSumcheckVerifierMutations
import ZkcExamples.Structured.SumcheckReduceVerifier
import ZkcExamples.Structured.SumcheckSourceVerifier

/-! Kernel consumers of the actual source equations. Executable controls above
exercise complete originals and independently re-admitted source mutants. -/
set_option autoImplicit false

namespace Tests.StructuredSumcheckVerifier
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured
open Tests.StructuredSumcheckVerifierSupport
open Tests.StructuredSumcheckVerifierExecution

/-- No P operand, active service, or claim is needed for zero Reduction rounds. -/
theorem zero_reduction_without_service :
    SumcheckReduceViews.program.participant (ZMod 5) (ZMod 5) 1
      (SumcheckReduceVerifier.reduceRootInputs none none none (some 0) none) =
        .done (.cons none (.cons none (.cons (some []) (.cons none .nil)))) := by
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
      (SumcheckSourceVerifier.sourceRootInputs none none (some 3) none) =
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
  rw [PIR.Proc.bind_assoc, PIR.run_bind]
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

end Tests.StructuredSumcheckVerifier
