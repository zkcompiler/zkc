module

public import Zkc.Tests.Protocol.Construction.AdaptiveSource

/-! Selected admission around the complete multiround source. The refusing arm executes
no sampler. Honest completeness requires admission explicitly; the upper request retains
refusing executions and includes zero and nested runtime iteration counts.
-/

@[expose] public section
noncomputable section
set_option experimental.vcgen true
open PIR Zkc.Source ProtocolProof Std.WP
open ProtocolProofExamples.AdaptiveChecks ProtocolProofExamples.AdaptiveSource

namespace ProtocolProofExamples.GuardedAdaptive

def source (count width : Nat) :
    Region (scalarDialect language) [.bit, .accumulator] [.result] :=
  .letOp (.branch [.accumulator] .result) (.cons .here (.cons (.there .here) .nil))
    (.cons (AdaptiveSource.source count width) (.cons (.stop .refused) .nil))
    (.ret (.cons .here .nil))

def game (allowed : Bool) (count width : Nat) (e : AdaptiveChecks.Environment) :
    Process Challenge (Bool × Bool) :=
  ((source count width).denote (meaning e).regionMeaning
    (Values.cons allowed (.cons ([], true) .nil)).get).bind fun out => .done (out.get .here)

attribute [local instance] upperLogic

theorem game_upper (allowed : Bool) (count width : Nat) (e : AdaptiveChecks.Environment)
    (value : Bool → ENNReal) :
    ⦃OrderDual.toDual (fun _ => if allowed then
      (factor e.residual ^ width) ^ count * value e.residual else 0)⦄
      game allowed count width e
    ⦃fun out => OrderDual.toDual (fun _ => reward out.2 (value out.1));
      OrderDual.toDual (fun _ _ => 0)⦄ := by
  unfold game source
  construct_region
  all_goals simp_all
  all_goals exact le_rfl

section Lower
attribute [local instance] lowerLogic

theorem game_lower (allowed : Bool) (count width : Nat) (e : AdaptiveChecks.Environment)
    (value : Bool → ENNReal)
    (honest : e.residual = false → ∀ history, e.strategy history = false) :
    ⦃fun _ => if allowed then (factor e.residual ^ width) ^ count * value e.residual else 0⦄
      game allowed count width e
    ⦃fun out => fun _ => reward out.2 (value out.1); fun _ _ => 0⦄ := by
  unfold game source
  construct_region
  all_goals try exact honest ‹_› _
  all_goals simp_all
  all_goals exact le_rfl

end Lower

def soundnessRequest (allowed : Bool) (count width : Nat) :
    SoundnessRequest AdaptiveChecks.Environment (Execution Unit Unit (Bool × Bool)) Bool where
  experiment := system.experiment (game allowed count width)
  admissible _ := True
  accepts out := accepted out.outcome = true
  statement out := residualOf out.outcome
  problem := PromiseProblem.ofPredicate (fun residual => residual = false)
  measurable_bad := MeasurableSet.of_discrete
  error _ := (half ^ width) ^ count

def completenessRequest (allowed : Bool) (count width : Nat) :
    CompletenessRequest AdaptiveChecks.Environment (Execution Unit Unit (Bool × Bool)) where
  experiment := system.experiment (game allowed count width)
  admissible e := allowed = true ∧ e.residual = false ∧ ∀ history, e.strategy history = false
  accepts := accepting
  measurable_accepts := MeasurableSet.of_discrete
  error _ := 0

theorem complete_upper (allowed : Bool) (count width : Nat) (e : AdaptiveChecks.Environment) :
    UpperBound coinSpec (game allowed count width e)
      (fun out state => falseAccepting.indicator 1 ⟨out, state.1, state.2⟩)
      (fun _ => (half ^ width) ^ count) := by
  have bound := (coinSpec.upperBound_iff_triple coinSpec_mono _ _ _ _).mpr
    (game_upper allowed count width e (fun residual => if residual then 1 else 0))
  simp only [AdaptiveSource.falseReward]
  apply bound.consequence coinSpec_mono le_rfl
  intro state
  cases allowed <;> cases e.residual <;> simp [factor]

theorem complete_lower (allowed : Bool) (count width : Nat) (e : AdaptiveChecks.Environment)
    (honest : allowed = true ∧ e.residual = false ∧ ∀ history, e.strategy history = false) :
    LowerBound coinSpec (game allowed count width e)
      (fun out state => accepting.indicator 1 ⟨out, state.1, state.2⟩) (fun _ => 1) := by
  have bound := (coinSpec.lowerBound_iff_triple coinSpec_mono _ _ _ _).mpr
    (game_lower allowed count width e (fun _ => 1) (fun _ => honest.2.2))
  simp only [AdaptiveSource.acceptanceReward]
  simpa only [honest.1, honest.2.1, factor, Bool.false_eq_true, ite_false,
    Bool.true_eq, ite_true, one_pow, one_mul] using bound

def soundnessEvidence (allowed : Bool) (count width : Nat) :
    UpperEvidence (soundnessRequest allowed count width).toUpper system system
      (game allowed count width) (fun _ s t => s = t) where
  subject := rfl
  installation := Installation.reflexive system _
  spec _ := coinSpec
  local_bound _ _ operation post state := (operation_expectation _ operation post state).le
  model_event _ := falseAccepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential _ _ := (half ^ width) ^ count
  mathematics e _ := complete_upper allowed count width e
  budget _ _ := by
    simp [System.initialWithEvents, system, soundnessRequest, SoundnessRequest.toUpper]

def completenessEvidence (allowed : Bool) (count width : Nat) :
    LowerEvidence (completenessRequest allowed count width).toLower system system
      (game allowed count width) (fun _ s t => s = t) where
  subject := rfl
  installation := Installation.reflexive system _
  spec _ := coinSpec
  local_bound _ _ operation post state := (operation_expectation _ operation post state).ge
  model_event _ := accepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential _ _ := 1
  mathematics e honest := complete_lower allowed count width e honest
  budget _ _ := by
    simp [System.initialWithEvents, system, completenessRequest, CompletenessRequest.toLower]

theorem soundness (allowed : Bool) (count width : Nat) :
    (soundnessRequest allowed count width).Holds := (soundnessEvidence allowed count width).establish

theorem completeness (allowed : Bool) (count width : Nat) :
    (completenessRequest allowed count width).Holds :=
  (completenessEvidence allowed count width).establish

/-- A rejected guard stops before any finite-loop callback, including a zero-width body. -/
theorem rejected (count width : Nat) (e : AdaptiveChecks.Environment) :
    game false count width e = .halt .refused := rfl

end ProtocolProofExamples.GuardedAdaptive
