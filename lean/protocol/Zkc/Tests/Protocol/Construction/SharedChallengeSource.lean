module

public import Zkc.Tools.Protocol.Construction
public import Zkc.Tests.Protocol.Models.SharedState
public import Zkc.Protocol.Claims.Assembly

/-! Held-out after the construction interface freeze. One equality reply recovers a private
Boolean challenge; the second check uses the same provider state. A general multi-result
Region keeps both answers and the final counter. There is no independent-query assumption.
-/

@[expose] public section
noncomputable section
set_option experimental.vcgen true
open PIR Zkc.Source ProtocolProof Std.WP MeasureTheory ProbabilityTheory
open ProtocolProofExamples.SharedState

namespace ProtocolProofExamples.SharedChallengeSource

def recover (guess answer : Bool) : Bool := if answer then guess else !guess

theorem recover_reply (guess secret : Bool) : recover guess (guess == secret) = secret := by
  cases guess <;> cases secret <;> rfl

def spec : OperationSpec Component ModelState Unit := fun operation post current =>
  match operation with
  | .challenge => post (.returned current.1) current
  | .verify guess => post (.returned (guess == current.1.1, current.1.2 + 1))
      ((current.1.1, current.1.2 + 1), current.2)

theorem spec_mono : spec.Monotone := by
  intro op post next h current
  cases op <;> exact h _ _

theorem operation_expectation (e : SharedState.Environment) (op : Component.Op)
    (post : Outcome Reply → Potential ModelState Unit) (current : ModelState × List Unit) :
    opExpectation (I := Component) (modelSystem.accumulatedOperations e) op post current =
      spec op post current := by
  change (∫⁻ out, post out.1 out.2 ∂modelSystem.accumulatedOperations e op current) = _
  rw [modelSystem.accumulatedOperations_apply,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  change (∫⁻ out, post out.outcome (out.state, current.2 ++ out.events)
    ∂modelHandler op current.1) = _
  cases op with
  | challenge => rw [model_challenge_meaning]; simp [spec]
  | verify guess => rw [model_verify_meaning]; simp [spec]

inductive Ty | bit | count deriving DecidableEq
inductive Op | query | recover

abbrev dialect : Dialect where
  Ty := Ty
  Op := Op
  arguments | .query => [.bit] | .recover => [.bit, .bit]
  results | .query => [.bit, .count] | .recover => [.bit]
  regions _ := []

abbrev meaning : RegionMeaning dialect Component where
  Value | .bit => Bool | .count => Nat
  operation
    | .query, .cons guess .nil, .nil =>
      .call (.verify guess) fun reply => .done (.cons reply.1 (.cons reply.2 .nil))
    | .recover, .cons guess (.cons answer .nil), .nil =>
      .done (.singleton (recover guess answer))

def query : Region dialect [.bit] [.bit, .count] :=
  .letOp .query (.singleton .here) .nil
    (.ret (.cons .here (.cons (.there .here) .nil)))

def source : Region dialect [.bit] [.bit, .bit, .count] :=
  .bind query
    (.letOp .recover (.cons (.there (.there .here)) (.cons .here .nil)) .nil
      (.bind (query.rename
        (Values.singleton (.here : Var [Ty.bit, .bit, .count, .bit] .bit)).get)
        (.ret (.cons (.there (.there (.there .here)))
          (.cons .here (.cons (.there .here) .nil))))))

@[spec] theorem query_meaning (guess : Bool) :
    meaning.operation .query (.singleton guess) .nil =
      .call (.verify guess) (fun reply => .done (.cons reply.1 (.cons reply.2 .nil))) := rfl

@[spec] theorem recover_meaning (guess answer : Bool) :
    meaning.operation .recover (.cons guess (.cons answer .nil)) .nil =
      .done (.singleton (recover guess answer)) := rfl

abbrev upperLogic : WPMonad (Process Component)
    (Potential ModelState Unit)ᵒᵈ (Stop → Potential ModelState Unit)ᵒᵈ :=
  spec.toUpperWPMonad spec_mono
attribute [local instance] upperLogic

@[spec high] theorem query_upper (env : Environment meaning.Value [.bit])
    (post : Values meaning.Value [.bit, .count] → (Potential ModelState Unit)ᵒᵈ)
    (stopped : (Stop → Potential ModelState Unit)ᵒᵈ) :
    ⦃OrderDual.toDual (fun current =>
      OrderDual.ofDual (post (.cons (env .here == current.1.1) (.cons (current.1.2 + 1) .nil)))
        ((current.1.1, current.1.2 + 1), current.2))⦄
      query.denote meaning env ⦃post; stopped⦄ := by
  unfold query
  construct_region

@[spec high] theorem source_upper (env : Environment meaning.Value [.bit])
    (post : Values meaning.Value [.bit, .bit, .count] → (Potential ModelState Unit)ᵒᵈ)
    (stopped : (Stop → Potential ModelState Unit)ᵒᵈ) :
    ⦃OrderDual.toDual (fun current =>
      OrderDual.ofDual (post (.cons (env .here == current.1.1)
        (.cons true (.cons (current.1.2 + 2) .nil))))
        ((current.1.1, current.1.2 + 2), current.2))⦄
      source.denote meaning env ⦃post; stopped⦄ := by
  unfold source
  construct_region
  change ∀ current, _ ≤ _
  intro current
  simp only [recover_reply, beq_self_eq_true, Nat.add_assoc]
  exact le_rfl

abbrev lowerLogic : WPMonad (Process Component)
    (Potential ModelState Unit) (Stop → Potential ModelState Unit) := spec.toWPMonad spec_mono

section Lower
attribute [local instance] lowerLogic

@[spec high] theorem query_lower (env : Environment meaning.Value [.bit])
    (post : Values meaning.Value [.bit, .count] → Potential ModelState Unit)
    (stopped : Stop → Potential ModelState Unit) :
    ⦃fun current => post (.cons (env .here == current.1.1) (.cons (current.1.2 + 1) .nil))
      ((current.1.1, current.1.2 + 1), current.2)⦄
      query.denote meaning env ⦃post; stopped⦄ := by
  unfold query
  construct_region

@[spec high] theorem source_lower (env : Environment meaning.Value [.bit])
    (post : Values meaning.Value [.bit, .bit, .count] → Potential ModelState Unit)
    (stopped : Stop → Potential ModelState Unit) :
    ⦃fun current => post (.cons (env .here == current.1.1)
        (.cons true (.cons (current.1.2 + 2) .nil)))
      ((current.1.1, current.1.2 + 2), current.2)⦄
      source.denote meaning env ⦃post; stopped⦄ := by
  unfold source
  construct_region
  simp only [recover_reply, beq_self_eq_true, Nat.add_assoc]
  exact le_rfl

end Lower

def game (e : SharedState.Environment) : Process Component (Bool × Bool × Nat) :=
  (source.denote meaning (Values.singleton e.1).get).bind fun out =>
    .done (out.get .here, out.get (.there .here), out.get (.there (.there .here)))

def accepting : Set (Execution ModelState Unit (Bool × Bool × Nat)) :=
  {out | match out.outcome with
    | .returned result => result.2.1 = true ∧ result.2.2 = 2
    | .stopped _ => False}

def reward (result : Bool × Bool × Nat) : Potential ModelState Unit :=
  fun _ => if result.2.1 && (result.2.2 == 2) then 1 else 0

def potential : Potential ModelState Unit := fun current => if current.1.2 = 0 then 1 else 0

theorem acceptance_reward (outcome : Outcome (Bool × Bool × Nat)) (current : ModelState × List Unit) :
    accepting.indicator 1 ⟨outcome, current.1, current.2⟩ =
      OperationSpec.outcomePost reward (fun _ _ => 0) outcome current := by
  cases outcome <;> simp [accepting, Set.indicator_apply, OperationSpec.outcomePost, reward]

noncomputable def upperRequest : UpperRequest SharedState.Environment
    (Execution ModelState Unit (Bool × Bool × Nat)) where
  experiment := modelSystem.experiment game
  admissible _ := True
  event := accepting
  measurable_event := MeasurableSet.of_discrete
  bound _ := 1

noncomputable def lowerRequest : LowerRequest SharedState.Environment
    (Execution ModelState Unit (Bool × Bool × Nat)) where
  experiment := modelSystem.experiment game
  admissible _ := True
  event := accepting
  measurable_event := MeasurableSet.of_discrete
  bound _ := 1

theorem game_upper (e : SharedState.Environment) :
    ⦃OrderDual.toDual potential⦄ game e
    ⦃fun result => OrderDual.toDual (reward result); OrderDual.toDual (fun _ _ => 0)⦄ := by
  unfold game
  construct_region
  change ∀ current, _ ≤ _
  intro current
  simp [potential, reward]

section LowerGame
attribute [local instance] lowerLogic

theorem game_lower (e : SharedState.Environment) :
    ⦃potential⦄ game e ⦃reward; fun _ _ => 0⦄ := by
  unfold game
  construct_region
  simp [potential, reward]

end LowerGame

theorem initial_potential (e : SharedState.Environment) :
    (∫⁻ current, potential current ∂modelSystem.initialWithEvents e) = 1 := by
  change (∫⁻ current, potential current
    ∂modelInitial.map (fun state : ModelState => (state, ([] : List Unit)))) = 1
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp [modelInitial, potential, lintegral_add_measure, lintegral_smul_measure,
    SharedState.half, ENNReal.inv_two_add_inv_two]

def upperEvidence : UpperEvidence upperRequest modelSystem modelSystem game (fun _ s t => s = t) where
  subject := rfl
  installation := Installation.reflexive modelSystem _
  spec _ := spec
  local_bound e _ op post state := (operation_expectation e op post state).le
  model_event _ := accepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential _ := potential
  mathematics e _ := by
    simp only [acceptance_reward]
    exact (spec.upperBound_iff_triple spec_mono _ _ _ _).mpr (game_upper e)
  budget e _ := (initial_potential e).le

def lowerEvidence : LowerEvidence lowerRequest modelSystem modelSystem game (fun _ s t => s = t) where
  subject := rfl
  installation := Installation.reflexive modelSystem _
  spec _ := spec
  local_bound e _ op post state := (operation_expectation e op post state).ge
  model_event _ := accepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential _ := potential
  mathematics e _ := by
    simp only [acceptance_reward]
    exact (spec.lowerBound_iff_triple spec_mono _ _ _ _).mpr (game_lower e)
  budget e _ := (initial_potential e).ge

theorem adaptive_search_acceptance (e : SharedState.Environment) :
    (modelSystem.experiment game).run e accepting = 1 :=
  le_antisymm (upperEvidence.establish e trivial) (lowerEvidence.establish e trivial)

/-- Changing the requested observation is not justified by reusing the source proof. -/
def bothAccepting : Set (Execution ModelState Unit (Bool × Bool × Nat)) :=
  {out | match out.outcome with
    | .returned result => result.1 = true ∧ result.2.1 = true ∧ result.2.2 = 2
    | .stopped _ => False}

def bothReward (result : Bool × Bool × Nat) : Potential ModelState Unit :=
  fun _ => if result.1 && result.2.1 && (result.2.2 == 2) then 1 else 0

def bothPotential (guess : Bool) : Potential ModelState Unit :=
  fun current => if (guess == current.1.1) && (current.1.2 == 0) then 1 else 0

def bothRequest : UpperRequest SharedState.Environment
    (Execution ModelState Unit (Bool × Bool × Nat)) where
  experiment := modelSystem.experiment game
  admissible _ := True
  event := bothAccepting
  measurable_event := MeasurableSet.of_discrete
  bound _ := SharedState.half

theorem game_both_upper (e : SharedState.Environment) :
    ⦃OrderDual.toDual (bothPotential e.1)⦄ game e
    ⦃fun result => OrderDual.toDual (bothReward result); OrderDual.toDual (fun _ _ => 0)⦄ := by
  unfold game
  construct_region
  change ∀ current, _ ≤ _
  intro current
  simp [bothPotential, bothReward]

def bothEvidence : UpperEvidence bothRequest modelSystem modelSystem game (fun _ s t => s = t) where
  subject := rfl
  installation := Installation.reflexive modelSystem _
  spec _ := spec
  local_bound e _ op post state := (operation_expectation e op post state).le
  model_event _ := bothAccepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential e := bothPotential e.1
  mathematics e _ := by
    have observation (outcome : Outcome (Bool × Bool × Nat)) (current : ModelState × List Unit) :
        bothAccepting.indicator 1 ⟨outcome, current.1, current.2⟩ =
          OperationSpec.outcomePost bothReward (fun _ _ => 0) outcome current := by
      cases outcome <;>
        simp [bothAccepting, Set.indicator_apply, OperationSpec.outcomePost, bothReward, and_assoc]
    simp only [observation]
    exact (spec.upperBound_iff_triple spec_mono _ _ _ _).mpr (game_both_upper e)
  budget e _ := by
    change (∫⁻ current, bothPotential e.1 current
      ∂modelInitial.map (fun state : ModelState => (state, ([] : List Unit)))) ≤ SharedState.half
    rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
    cases e.1 <;> simp [modelInitial, bothPotential, lintegral_add_measure, lintegral_smul_measure]

theorem swapped_observation_refused (e : SharedState.Environment) :
    (modelSystem.experiment game).run e bothAccepting ≠ 1 := by
  intro equality
  have bound := bothEvidence.establish e trivial
  change (modelSystem.experiment game).run e bothAccepting ≤ SharedState.half at bound
  rw [equality] at bound
  norm_num [SharedState.half] at bound

end ProtocolProofExamples.SharedChallengeSource
