module

public import Zkc.Tools.Protocol.Construction
public import Zkc.Tests.Protocol.Models.AdaptiveChecks

/-! A complete typed-region client of the adaptive challenge mathematics.
The source fixes a guess before drawing a challenge. The constructor supplies sequencing,
callback substitution and finite iteration; the companion supplies the prediction bound.
-/

@[expose] public section
noncomputable section
set_option experimental.vcgen true
open PIR Zkc.Source ProtocolProof Std.WP
open ProtocolProofExamples.AdaptiveChecks

namespace ProtocolProofExamples.AdaptiveSource

inductive Ty | accumulator | bit | result deriving DecidableEq
inductive Op | guess | draw | check | finish

abbrev language : Language where
  Ty := Ty
  Op := Op
  arguments
    | .guess => [.accumulator]
    | .draw => []
    | .check => [.accumulator, .bit, .bit]
    | .finish => [.accumulator]
  result
    | .guess | .draw => .bit
    | .check => .accumulator
    | .finish => .result
  condition := .bit

abbrev meaning (e : Environment) : Interpretation language Challenge where
  Value
    | .accumulator => Accumulator
    | .bit => Bool
    | .result => Bool × Bool
  condition := id
  operation
    | .guess, .cons acc .nil => .done (e.strategy acc.1)
    | .draw, .nil => .call () .done
    | .check, .cons acc (.cons guess (.cons challenge .nil)) =>
        .done (challenge :: acc.1, acc.2 && (guess == (e.residual && challenge)))
    | .finish, .cons acc .nil => .done (e.residual, acc.2)

def round : Region (scalarDialect language) [.accumulator] [.accumulator] :=
  .letOp (.ordinary .guess) (.cons .here .nil) .nil
    (.letOp (.ordinary .draw) .nil .nil
      (.letOp (.ordinary .check)
        (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil
        (.ret (.cons .here .nil))))

def rounds (count : Nat) : Region (scalarDialect language) [.accumulator] [.accumulator] :=
  .letOp (.repeat count [] .accumulator) (.cons .here .nil)
    (.cons round .nil) (.ret (.cons .here .nil))

def batches (count width : Nat) :
    Region (scalarDialect language) [.accumulator] [.accumulator] :=
  .letOp (.repeat count [] .accumulator) (.cons .here .nil)
    (.cons (rounds width) .nil) (.ret (.cons .here .nil))

def source (count width : Nat) :
    Region (scalarDialect language) [.accumulator] [.result] :=
  .bind (batches count width)
    (.letOp (.ordinary .finish) (.cons .here .nil) .nil (.ret (.cons .here .nil)))

abbrev upperLogic : WPMonad (Process Challenge)
    (Potential Unit Unit)ᵒᵈ (Stop → Potential Unit Unit)ᵒᵈ :=
  coinSpec.toUpperWPMonad coinSpec_mono
attribute [local instance] upperLogic

@[spec] theorem guess_rule (e : Environment) (acc : Accumulator) :
    (meaning e).operation .guess (.cons acc .nil) = .done (e.strategy acc.1) := rfl

@[spec] theorem draw_rule (e : Environment) :
    (meaning e).operation .draw .nil = .call () .done := rfl

@[spec] theorem check_rule (e : Environment) (acc : Accumulator) (guess challenge : Bool) :
    (meaning e).operation .check (.cons acc (.cons guess (.cons challenge .nil))) =
      .done (challenge :: acc.1, acc.2 && (guess == (e.residual && challenge))) := rfl

@[spec] theorem finish_rule (e : Environment) (acc : Accumulator) :
    (meaning e).operation .finish (.cons acc .nil) = .done (e.residual, acc.2) := rfl

abbrev potential (value : ENNReal) (acc : Accumulator) : Potential Unit Unit :=
  fun _ => reward acc.2 value

@[spec high] theorem round_upper (e : Environment)
    (env : Zkc.Source.Environment (meaning e).Value [.accumulator]) (value : ENNReal) :
    ⦃OrderDual.toDual (potential (factor e.residual * value) (env .here))⦄
      round.denote (meaning e).regionMeaning env
    ⦃fun out => OrderDual.toDual (potential value (out.get .here));
      OrderDual.toDual (fun _ _ => 0)⦄ := by
  unfold round
  construct_region
  change ∀ state, half * reward ((env .here).2 &&
      (e.strategy (env .here).1 == (e.residual && false))) value +
    half * reward ((env .here).2 &&
      (e.strategy (env .here).1 == (e.residual && true))) value ≤
        reward (env .here).2 (factor e.residual * value)
  intro state
  exact primitive_upper e.residual (e.strategy (env .here).1) (env .here).2 value

@[spec high] theorem rounds_upper (count : Nat) (e : Environment)
    (env : Zkc.Source.Environment (meaning e).Value [.accumulator]) (value : ENNReal) :
    ⦃OrderDual.toDual (potential (factor e.residual ^ count * value) (env .here))⦄
      (rounds count).denote (meaning e).regionMeaning env
    ⦃fun out => OrderDual.toDual (potential value (out.get .here));
      OrderDual.toDual (fun _ _ => 0)⦄ := by
  unfold rounds
  construct_region with_invariants [fun remaining acc =>
    OrderDual.toDual (potential (factor e.residual ^ remaining * value) acc)]
  all_goals try simp only [pow_zero, one_mul, pow_succ', mul_assoc]
  all_goals exact le_rfl


@[spec high] theorem batches_upper (count width : Nat) (e : Environment)
    (env : Zkc.Source.Environment (meaning e).Value [.accumulator]) (value : ENNReal) :
    ⦃OrderDual.toDual (potential ((factor e.residual ^ width) ^ count * value) (env .here))⦄
      (batches count width).denote (meaning e).regionMeaning env
    ⦃fun out => OrderDual.toDual (potential value (out.get .here));
      OrderDual.toDual (fun _ _ => 0)⦄ := by
  unfold batches
  construct_region with_invariants [fun remaining acc =>
    OrderDual.toDual (potential ((factor e.residual ^ width) ^ remaining * value) acc)]
  all_goals try simp only [pow_zero, one_mul, pow_succ', mul_assoc]
  all_goals exact le_rfl

@[spec high] theorem source_upper (count width : Nat) (e : Environment)
    (env : Zkc.Source.Environment (meaning e).Value [.accumulator]) (value : Bool → ENNReal) :
    ⦃OrderDual.toDual (potential ((factor e.residual ^ width) ^ count * value e.residual) (env .here))⦄
      (source count width).denote (meaning e).regionMeaning env
    ⦃fun out => OrderDual.toDual (fun _ => reward (out.get .here).2 (value (out.get .here).1));
      OrderDual.toDual (fun _ _ => 0)⦄ := by
  unfold source
  construct_region

abbrev lowerLogic : WPMonad (Process Challenge)
    (Potential Unit Unit) (Stop → Potential Unit Unit) :=
  coinSpec.toWPMonad coinSpec_mono

section Lower
attribute [local instance] lowerLogic

@[spec high] theorem round_lower (e : Environment)
    (env : Zkc.Source.Environment (meaning e).Value [.accumulator]) (value : ENNReal)
    (honest : e.residual = false → ∀ history, e.strategy history = false) :
    ⦃potential (factor e.residual * value) (env .here)⦄
      round.denote (meaning e).regionMeaning env
    ⦃fun out => potential value (out.get .here); fun _ _ => 0⦄ := by
  unfold round
  construct_region
  change reward (env .here).2 (factor e.residual * value) ≤
    half * reward ((env .here).2 &&
      (e.strategy (env .here).1 == (e.residual && false))) value +
    half * reward ((env .here).2 &&
      (e.strategy (env .here).1 == (e.residual && true))) value
  exact primitive_lower e.residual (e.strategy (env .here).1) (env .here).2 value
    (fun h => honest h (env .here).1)

@[spec high] theorem rounds_lower (count : Nat) (e : Environment)
    (env : Zkc.Source.Environment (meaning e).Value [.accumulator]) (value : ENNReal)
    (honest : e.residual = false → ∀ history, e.strategy history = false) :
    ⦃potential (factor e.residual ^ count * value) (env .here)⦄
      (rounds count).denote (meaning e).regionMeaning env
    ⦃fun out => potential value (out.get .here); fun _ _ => 0⦄ := by
  unfold rounds
  construct_region with_invariants [fun remaining acc =>
    potential (factor e.residual ^ remaining * value) acc]
  all_goals try simp only [pow_zero, one_mul, pow_succ', mul_assoc]
  all_goals exact le_rfl

@[spec high] theorem batches_lower (count width : Nat) (e : Environment)
    (env : Zkc.Source.Environment (meaning e).Value [.accumulator]) (value : ENNReal)
    (honest : e.residual = false → ∀ history, e.strategy history = false) :
    ⦃potential ((factor e.residual ^ width) ^ count * value) (env .here)⦄
      (batches count width).denote (meaning e).regionMeaning env
    ⦃fun out => potential value (out.get .here); fun _ _ => 0⦄ := by
  unfold batches
  construct_region with_invariants [fun remaining acc =>
    potential ((factor e.residual ^ width) ^ remaining * value) acc]
  all_goals try simp only [pow_zero, one_mul, pow_succ', mul_assoc]
  all_goals exact le_rfl

@[spec high] theorem source_lower (count width : Nat) (e : Environment)
    (env : Zkc.Source.Environment (meaning e).Value [.accumulator]) (value : Bool → ENNReal)
    (honest : e.residual = false → ∀ history, e.strategy history = false) :
    ⦃potential ((factor e.residual ^ width) ^ count * value e.residual) (env .here)⦄
      (source count width).denote (meaning e).regionMeaning env
    ⦃fun out => fun _ => reward (out.get .here).2 (value (out.get .here).1); fun _ _ => 0⦄ := by
  unfold source
  construct_region

end Lower


/-- Observe the result of the actual typed source, without replacing its computation. -/
def game (count width : Nat) (e : Environment) : Process Challenge (Bool × Bool) :=
  ((source count width).denote (meaning e).regionMeaning
    (Values.singleton ([], true)).get).bind fun out => .done (out.get .here)

@[spec] theorem game_upper (count width : Nat) (e : Environment) (value : Bool → ENNReal) :
    ⦃OrderDual.toDual (fun _ => (factor e.residual ^ width) ^ count * value e.residual)⦄
      game count width e
    ⦃fun out => OrderDual.toDual (fun _ => reward out.2 (value out.1));
      OrderDual.toDual (fun _ _ => 0)⦄ := by
  unfold game
  construct_region

section LowerGame
attribute [local instance] lowerLogic
@[spec] theorem game_lower (count width : Nat) (e : Environment) (value : Bool → ENNReal)
    (honest : e.residual = false → ∀ history, e.strategy history = false) :
    ⦃fun _ => (factor e.residual ^ width) ^ count * value e.residual⦄
      game count width e
    ⦃fun out => fun _ => reward out.2 (value out.1); fun _ _ => 0⦄ := by
  unfold game
  construct_region
end LowerGame

/-- The event and error are fixed independently of constructor success. -/
noncomputable def soundnessRequest (count width : Nat) :
    SoundnessRequest Environment (Execution Unit Unit (Bool × Bool)) Bool where
  experiment := system.experiment (game count width)
  admissible _ := True
  accepts out := accepted out.outcome = true
  statement out := residualOf out.outcome
  problem := PromiseProblem.ofPredicate (fun residual => residual = false)
  measurable_bad := MeasurableSet.of_discrete
  error _ := (half ^ width) ^ count

noncomputable def completenessRequest (count width : Nat) :
    CompletenessRequest Environment (Execution Unit Unit (Bool × Bool)) where
  experiment := system.experiment (game count width)
  admissible e := e.residual = false ∧ ∀ history, e.strategy history = false
  accepts := accepting
  measurable_accepts := MeasurableSet.of_discrete
  error _ := 0

theorem falseReward (outcome : Outcome (Bool × Bool)) (state : Unit × List Unit) :
    falseAccepting.indicator 1 ⟨outcome, state.1, state.2⟩ =
      OperationSpec.outcomePost (fun out _ => reward out.2 (if out.1 then 1 else 0))
        (fun _ _ => 0) outcome state := by
  cases outcome with
  | stopped reason => simp [falseAccepting, accepted, residualOf, OperationSpec.outcomePost]
  | returned value =>
    rcases value with ⟨residual, accepts⟩
    cases residual <;> cases accepts <;>
      simp [falseAccepting, accepted, residualOf, reward, OperationSpec.outcomePost]

theorem acceptanceReward (outcome : Outcome (Bool × Bool)) (state : Unit × List Unit) :
    accepting.indicator 1 ⟨outcome, state.1, state.2⟩ =
      OperationSpec.outcomePost (fun out _ => reward out.2 1)
        (fun _ _ => 0) outcome state := by
  cases outcome with
  | stopped reason => simp [accepting, accepted, OperationSpec.outcomePost]
  | returned value =>
    cases h : value.2 <;> simp [h, accepting, accepted, reward, OperationSpec.outcomePost]

theorem complete_upper (count width : Nat) (e : Environment) :
    UpperBound coinSpec (game count width e)
      (fun out state => falseAccepting.indicator 1 ⟨out, state.1, state.2⟩)
      (fun _ => (half ^ width) ^ count) := by
  have bound := (coinSpec.upperBound_iff_triple coinSpec_mono _ _ _ _).mpr
    (game_upper count width e (fun residual => if residual then 1 else 0))
  simp only [falseReward]
  apply bound.consequence coinSpec_mono le_rfl
  intro state
  cases e.residual <;> simp [factor]

theorem complete_lower (count width : Nat) (e : Environment)
    (honest : e.residual = false ∧ ∀ history, e.strategy history = false) :
    LowerBound coinSpec (game count width e)
      (fun out state => accepting.indicator 1 ⟨out, state.1, state.2⟩) (fun _ => 1) := by
  have bound := (coinSpec.lowerBound_iff_triple coinSpec_mono _ _ _ _).mpr
    (game_lower count width e (fun _ => 1) (fun _ => honest.2))
  simp only [acceptanceReward]
  simpa only [honest.1, factor, Bool.false_eq_true, ite_false,
    one_pow, one_mul] using bound

noncomputable def soundnessEvidence (count width : Nat) :
    UpperEvidence (soundnessRequest count width).toUpper system system (game count width)
      (fun _ s t => s = t) where
  subject := rfl
  installation := Installation.reflexive system _
  spec _ := coinSpec
  local_bound _ _ operation post state := (operation_expectation _ operation post state).le
  model_event _ := falseAccepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential _ _ := (half ^ width) ^ count
  mathematics e _ := complete_upper count width e
  budget _ _ := by
    simp [System.initialWithEvents, system, soundnessRequest, SoundnessRequest.toUpper]

noncomputable def completenessEvidence (count width : Nat) :
    LowerEvidence (completenessRequest count width).toLower system system (game count width)
      (fun _ s t => s = t) where
  subject := rfl
  installation := Installation.reflexive system _
  spec _ := coinSpec
  local_bound _ _ operation post state := (operation_expectation _ operation post state).ge
  model_event _ := accepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential _ _ := 1
  mathematics e honest := complete_lower count width e honest
  budget _ _ := by
    simp [System.initialWithEvents, system, completenessRequest, CompletenessRequest.toLower]

/-- Whole-source soundness, for every history-dependent adversary and finite loop sizes. -/
theorem adaptive_soundness (count width : Nat) : (soundnessRequest count width).Holds :=
  (soundnessEvidence count width).establish

/-- Whole-source honest completeness, including zero iterations and all stop outcomes. -/
theorem honest_completeness (count width : Nat) : (completenessRequest count width).Holds :=
  (completenessEvidence count width).establish

end ProtocolProofExamples.AdaptiveSource
