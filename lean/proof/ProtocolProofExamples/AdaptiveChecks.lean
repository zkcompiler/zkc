module

public import ProtocolProof.Claims.Assembly

/-!
# Adaptive finite challenge checks

A residual is true exactly when the claimed equation is false. Before each fresh fair Bool
challenge, the prover commits to a bit using only previous challenges. The verifier checks
`guess = residual && challenge`; a zero residual has the honest response zero, whereas a
nonzero residual requires predicting the challenge. Every check must pass. This finite model
tests iterative composition; it is not an implementation or soundness theorem for Sumcheck.

The outer loop reuses whole inner loops without resetting the challenge history. Both fixed
requests close through the common evidence roots and a generic identity representation.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory PFunctor
open scoped ENNReal

namespace ProtocolProofExamples.AdaptiveChecks

open ProtocolProof PIR

abbrev Challenge : Signature := ⟨Unit, fun _ ↦ Bool⟩

@[expose] def half : ℝ≥0∞ := 1 / 2

private theorem half_add_half : half + half = 1 := ENNReal.add_halves 1

/-- The complete primitive law includes both answers and the unchanged private state. -/
@[expose] noncomputable def operations :
    (op : Challenge.Op) → Kernel Unit (Execution Unit Unit (Challenge.Reply op)) :=
  fun _ ↦ Kernel.const Unit
    (half • Measure.dirac ⟨.returned false, (), []⟩ +
      half • Measure.dirac ⟨.returned true, (), []⟩)

theorem operation_probability (operation : Challenge.Op) (state : Unit) :
    operations operation state Set.univ = 1 := by
  simpa [operations] using half_add_half

/-- Strategies see only the past, with the newest challenge first. -/
@[expose] def Strategy := List Bool → Bool

structure Environment where
  residual : Bool
  strategy : Strategy

/-- Accumulators retain all previous challenges and the conjunction of all checks so far. -/
@[expose] def Accumulator := List Bool × Bool

/-- The guess is fixed outside the challenge's continuation. -/
@[expose] def checkRound (residual : Bool) (strategy : Strategy) (_round : Nat)
    (acc : Accumulator) : Process Challenge Accumulator :=
  let guess := strategy acc.1
  (Process.call (I := Challenge) () .done).bind fun challenge ↦
    pure (challenge :: acc.1, acc.2 && (guess == (residual && challenge)))

@[expose] def rounds (count : Nat) (residual : Bool) (strategy : Strategy)
    (acc : Accumulator) : Process Challenge Accumulator :=
  (List.range count).foldlM (fun acc round ↦ checkRound residual strategy round acc) acc

/-- Each batch is itself an arbitrary finite adaptive loop using the same strategy and history. -/
@[expose] def batches (count width : Nat) (residual : Bool) (strategy : Strategy)
    (acc : Accumulator) : Process Challenge Accumulator :=
  (List.range count).foldlM (fun acc _ ↦ rounds width residual strategy acc) acc

/-- The complete output is the claimed residual and the final accept/reject bit. -/
@[expose] def game (count width : Nat) (environment : Environment) :
    Process Challenge (Bool × Bool) :=
  (batches count width environment.residual environment.strategy ([], true)).bind fun acc ↦
    pure (environment.residual, acc.2)

@[expose] noncomputable def system : System Environment Challenge Unit Unit where
  operations _ := operations
  initial _ := Measure.dirac ()
  operation_mass _ := operation_probability
  initial_probability _ := inferInstance

/-- No independence assumption: this exact law holds at every call and private state. -/
theorem operation_expectation (environment : Environment) (operation : Challenge.Op)
    (post : Outcome Bool → Unit × List Unit → ℝ≥0∞) (state : Unit × List Unit) :
    opExpectation (I := Challenge) (system.accumulatedOperations environment) operation post state =
      half * post (.returned false) ((), state.2) + half * post (.returned true) ((), state.2) := by
  change (∫⁻ out, post out.1 out.2 ∂system.accumulatedOperations environment operation state) = _
  rw [system.accumulatedOperations_apply environment operation state]
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp [system, operations, lintegral_add_measure, lintegral_smul_measure]

/-- Either committed bit matches a fresh challenge with probability exactly one half. -/
theorem challenge_probability (guess : Bool) :
    operations () () {out | out.outcome = .returned guess} = half := by
  cases guess <;> simp [operations]

private def coinSpec : OperationSpec Challenge Unit Unit :=
  fun _ post state ↦ half * post (.returned false) ((), state.2) +
    half * post (.returned true) ((), state.2)

private theorem coinSpec_mono : coinSpec.Monotone := by
  intro _ post post' hpost state
  exact add_le_add (mul_le_mul_right (hpost (.returned false) ((), state.2)) half)
    (mul_le_mul_right (hpost (.returned true) ((), state.2)) half)

/-- Stops retain their execution state and receive zero acceptance reward. -/
private def resultReward {A : Type} (post : A → ℝ≥0∞) : Outcome A → ℝ≥0∞
  | .returned value => post value
  | .stopped _ => 0

private def reward (accepted : Bool) (value : ℝ≥0∞) : ℝ≥0∞ :=
  if accepted then value else 0

private def factor (residual : Bool) : ℝ≥0∞ := if residual then half else 1

private theorem primitive_upper (residual guess accepted : Bool) (value : ℝ≥0∞) :
    half * reward (accepted && (guess == (residual && false))) value +
      half * reward (accepted && (guess == (residual && true))) value ≤
        reward accepted (factor residual * value) := by
  cases residual <;> cases guess <;> cases accepted <;>
    simp [reward, factor, ← add_mul, half_add_half]

private theorem primitive_lower (residual guess accepted : Bool) (value : ℝ≥0∞)
    (honest : residual = false → guess = false) :
    reward accepted (factor residual * value) ≤
      half * reward (accepted && (guess == (residual && false))) value +
        half * reward (accepted && (guess == (residual && true))) value := by
  cases residual <;> cases guess <;> cases accepted <;>
    simp_all [reward, factor, ← add_mul, half_add_half]

private theorem round_upper (residual : Bool) (strategy : Strategy) (round : Nat)
    (acc : Accumulator) (value : ℝ≥0∞) :
    UpperBound coinSpec (checkRound residual strategy round acc)
      (fun out _ ↦ resultReward (fun next ↦ reward next.2 value) out)
      (fun _ ↦ reward acc.2 (factor residual * value)) := by
  apply (UpperBound.operation (spec := coinSpec) ()
    (fun out _ ↦ resultReward (fun challenge ↦
      reward (acc.2 && (strategy acc.1 == (residual && challenge))) value) out)
    (fun _ ↦ primitive_upper residual (strategy acc.1) acc.2 value)).bind coinSpec_mono
      (hstop := fun _ _ ↦ le_rfl)
  intro challenge
  exact UpperBound.pure _ le_rfl

private theorem round_lower (residual : Bool) (strategy : Strategy) (round : Nat)
    (acc : Accumulator) (value : ℝ≥0∞)
    (honest : residual = false → ∀ history, strategy history = false) :
    LowerBound coinSpec (checkRound residual strategy round acc)
      (fun out _ ↦ resultReward (fun next ↦ reward next.2 value) out)
      (fun _ ↦ reward acc.2 (factor residual * value)) := by
  apply (LowerBound.operation (spec := coinSpec) ()
    (fun out _ ↦ resultReward (fun challenge ↦
      reward (acc.2 && (strategy acc.1 == (residual && challenge))) value) out)
    (fun _ ↦ primitive_lower residual (strategy acc.1) acc.2 value
      (fun h ↦ honest h acc.1))).bind coinSpec_mono (hstop := fun _ _ ↦ le_rfl)
  intro challenge
  exact LowerBound.pure _ le_rfl

private theorem remaining_power (base value : ℝ≥0∞) (count round : Nat)
    (hround : round < count) :
    base * (base ^ (count - (round + 1)) * value) = base ^ (count - round) * value := by
  have hcount : count - round = count - (round + 1) + 1 := by omega
  rw [hcount, pow_succ']
  exact (mul_assoc _ _ _).symm

private theorem rounds_upper (count : Nat) (residual : Bool) (strategy : Strategy)
    (acc : Accumulator) (value : ℝ≥0∞) :
    UpperBound coinSpec (rounds count residual strategy acc)
      (fun out _ ↦ resultReward (fun next ↦ reward next.2 value) out)
      (fun _ ↦ reward acc.2 (factor residual ^ count * value)) := by
  simpa [rounds, resultReward] using UpperBound.iterate coinSpec_mono (checkRound residual strategy)
    (fun round out _ ↦ resultReward
      (fun next ↦ reward next.2 (factor residual ^ (count - round) * value)) out) count
    (hstop := fun _ _ _ _ ↦ le_rfl)
    (fun round hround next ↦ by
      simpa only [remaining_power _ _ _ _ hround, resultReward] using
        round_upper residual strategy round next
          (factor residual ^ (count - (round + 1)) * value)) acc

private theorem rounds_lower (count : Nat) (residual : Bool) (strategy : Strategy)
    (acc : Accumulator) (value : ℝ≥0∞)
    (honest : residual = false → ∀ history, strategy history = false) :
    LowerBound coinSpec (rounds count residual strategy acc)
      (fun out _ ↦ resultReward (fun next ↦ reward next.2 value) out)
      (fun _ ↦ reward acc.2 (factor residual ^ count * value)) := by
  simpa [rounds, resultReward] using LowerBound.iterate coinSpec_mono (checkRound residual strategy)
    (fun round out _ ↦ resultReward
      (fun next ↦ reward next.2 (factor residual ^ (count - round) * value)) out) count
    (hstop := fun _ _ _ _ ↦ le_rfl)
    (fun round hround next ↦ by
      simpa only [remaining_power _ _ _ _ hround, resultReward] using
        round_lower residual strategy round next
          (factor residual ^ (count - (round + 1)) * value) honest) acc

private theorem batches_upper (count width : Nat) (residual : Bool) (strategy : Strategy)
    (acc : Accumulator) (value : ℝ≥0∞) :
    UpperBound coinSpec (batches count width residual strategy acc)
      (fun out _ ↦ resultReward (fun next ↦ reward next.2 value) out)
      (fun _ ↦ reward acc.2 ((factor residual ^ width) ^ count * value)) := by
  simpa [batches, resultReward] using UpperBound.iterate coinSpec_mono
    (fun _ next ↦ rounds width residual strategy next)
    (fun round out _ ↦ resultReward
      (fun next ↦ reward next.2 ((factor residual ^ width) ^ (count - round) * value)) out)
    count (hstop := fun _ _ _ _ ↦ le_rfl) (fun round hround next ↦ by
      simpa only [remaining_power _ _ _ _ hround, resultReward] using
        rounds_upper width residual strategy next
          ((factor residual ^ width) ^ (count - (round + 1)) * value)) acc

private theorem batches_lower (count width : Nat) (residual : Bool) (strategy : Strategy)
    (acc : Accumulator) (value : ℝ≥0∞)
    (honest : residual = false → ∀ history, strategy history = false) :
    LowerBound coinSpec (batches count width residual strategy acc)
      (fun out _ ↦ resultReward (fun next ↦ reward next.2 value) out)
      (fun _ ↦ reward acc.2 ((factor residual ^ width) ^ count * value)) := by
  simpa [batches, resultReward] using LowerBound.iterate coinSpec_mono
    (fun _ next ↦ rounds width residual strategy next)
    (fun round out _ ↦ resultReward
      (fun next ↦ reward next.2 ((factor residual ^ width) ^ (count - round) * value)) out)
    count (hstop := fun _ _ _ _ ↦ le_rfl) (fun round hround next ↦ by
      simpa only [remaining_power _ _ _ _ hround, resultReward] using
        rounds_lower width residual strategy next
          ((factor residual ^ width) ^ (count - (round + 1)) * value) honest) acc

@[expose] def accepted : Outcome (Bool × Bool) → Bool
  | .returned value => value.2
  | .stopped _ => false

@[expose] def residualOf : Outcome (Bool × Bool) → Bool
  | .returned value => value.1
  | .stopped _ => false

@[expose] def accepting : Set (Execution Unit Unit (Bool × Bool)) :=
  {out | accepted out.outcome = true}

@[expose] def falseAccepting : Set (Execution Unit Unit (Bool × Bool)) :=
  {out | accepted out.outcome = true ∧ residualOf out.outcome ≠ false}

/-- Admissibility includes every history-dependent guessing strategy and either statement. -/
@[expose] noncomputable def soundnessRequest (count width : Nat) :
    SoundnessRequest Environment (Execution Unit Unit (Bool × Bool)) Bool where
  experiment := system.experiment (game count width)
  admissible _ := True
  accepts out := accepted out.outcome = true
  statement out := residualOf out.outcome
  problem := PromiseProblem.ofPredicate (fun residual ↦ residual = false)
  measurable_bad := MeasurableSet.of_discrete
  error _ := (half ^ width) ^ count

/-- A true equation and the honest zero response must accept, including every failure outcome. -/
@[expose] noncomputable def completenessRequest (count width : Nat) :
    CompletenessRequest Environment (Execution Unit Unit (Bool × Bool)) where
  experiment := system.experiment (game count width)
  admissible e := e.residual = false ∧ ∀ history, e.strategy history = false
  accepts := accepting
  measurable_accepts := MeasurableSet.of_discrete
  error _ := 0

private theorem game_upper (count width : Nat) (e : Environment) :
    UpperBound coinSpec (game count width e)
      (fun value state ↦ falseAccepting.indicator 1 ⟨value, state.1, state.2⟩)
      (fun _ ↦ (half ^ width) ^ count) := by
  have h := (batches_upper count width e.residual e.strategy ([], true)
    (if e.residual then 1 else 0)).bind coinSpec_mono
    (next := fun acc ↦ pure (e.residual, acc.2))
    (reward := fun value state ↦ falseAccepting.indicator 1 ⟨value, state.1, state.2⟩)
    (hstop := by intro why state; simp [falseAccepting, accepted, residualOf, resultReward])
    (fun acc ↦ UpperBound.pure _ (by
      intro state
      cases e.residual <;> cases ha : acc.2 <;>
        simp [ha, falseAccepting, accepted, residualOf, resultReward, reward, Set.indicator]))
  apply h.consequence coinSpec_mono le_rfl
  intro state
  cases e.residual <;> simp [reward, factor]

private theorem game_lower (count width : Nat) (e : Environment)
    (honest : e.residual = false ∧ ∀ history, e.strategy history = false) :
    LowerBound coinSpec (game count width e)
      (fun value state ↦ accepting.indicator 1 ⟨value, state.1, state.2⟩) (fun _ ↦ 1) := by
  have h := (batches_lower count width e.residual e.strategy ([], true) 1
    (fun _ ↦ honest.2)).bind coinSpec_mono
    (next := fun acc ↦ pure (e.residual, acc.2))
    (reward := fun value state ↦ accepting.indicator 1 ⟨value, state.1, state.2⟩)
    (hstop := by intro why state; simp [resultReward])
    (fun acc ↦ LowerBound.pure _ (by
      intro state
      cases ha : acc.2 <;> simp [ha, accepting, accepted, resultReward, reward, Set.indicator]))
  simpa [game, factor, reward, honest.1] using h

private noncomputable def soundnessEvidence (count width : Nat) :
    UpperEvidence (soundnessRequest count width).toUpper system system (game count width)
      (fun _ s t ↦ s = t) where
  subject := rfl
  installation := Installation.reflexive system _
  spec _ := coinSpec
  local_bound _ _ operation post state := (operation_expectation _ operation post state).le
  model_event _ := falseAccepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential _ _ := (half ^ width) ^ count
  mathematics e _ := game_upper count width e
  budget _ _ := by
    simp [System.initialWithEvents, system, soundnessRequest, SoundnessRequest.toUpper]

private noncomputable def completenessEvidence (count width : Nat) :
    LowerEvidence (completenessRequest count width).toLower system system (game count width)
      (fun _ s t ↦ s = t) where
  subject := rfl
  installation := Installation.reflexive system _
  spec _ := coinSpec
  local_bound _ _ operation post state := (operation_expectation _ operation post state).ge
  model_event _ := accepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential _ _ := 1
  mathematics e honest := game_lower count width e honest
  budget _ _ := by
    simp [System.initialWithEvents, system, completenessRequest, CompletenessRequest.toLower]

/-- The common upper root closes the complete nested game for every adaptive adversary. -/
theorem adaptive_soundness (count width : Nat) : (soundnessRequest count width).Holds :=
  (soundnessEvidence count width).establish

/-- The common lower root closes honest completeness with error zero for all finite sizes. -/
theorem honest_completeness (count width : Nat) : (completenessRequest count width).Holds :=
  (completenessEvidence count width).establish

/-- One batch gives the requested arbitrary-round exponential bound. -/
theorem false_acceptance_le (roundCount : Nat) (e : Environment) :
    (system.experiment (game 1 roundCount)).run e falseAccepting ≤ half ^ roundCount := by
  simpa [SoundnessRequest.Holds, SoundnessRequest.toUpper, soundnessRequest, falseAccepting]
    using adaptive_soundness 1 roundCount e trivial

/-- Nesting reuses the same component, with persistent history across batch boundaries. -/
theorem nested_false_acceptance_le (count width : Nat) (e : Environment) :
    (system.experiment (game count width)).run e falseAccepting ≤ half ^ (width * count) := by
  simpa [SoundnessRequest.Holds, SoundnessRequest.toUpper, soundnessRequest, falseAccepting,
    pow_mul] using adaptive_soundness count width e trivial

private theorem false_game_lower (count width : Nat) (e : Environment)
    (nonzero : e.residual = true) :
    LowerBound coinSpec (game count width e)
      (fun value state ↦ falseAccepting.indicator 1 ⟨value, state.1, state.2⟩)
      (fun _ ↦ (half ^ width) ^ count) := by
  have h := (batches_lower count width e.residual e.strategy ([], true) 1
    (by simp [nonzero])).bind coinSpec_mono
    (next := fun acc ↦ pure (e.residual, acc.2))
    (reward := fun value state ↦ falseAccepting.indicator 1 ⟨value, state.1, state.2⟩)
    (hstop := by intro why state; simp [resultReward])
    (fun acc ↦ LowerBound.pure _ (by
      intro state
      cases ha : acc.2 <;>
        simp [ha, nonzero, falseAccepting, accepted, residualOf, resultReward,
          reward, Set.indicator]))
  simpa [game, factor, reward, nonzero] using h

private noncomputable def falseLowerRequest (count width : Nat) :
    LowerRequest Environment (Execution Unit Unit (Bool × Bool)) where
  experiment := system.experiment (game count width)
  admissible e := e.residual = true
  event := falseAccepting
  measurable_event := MeasurableSet.of_discrete
  bound _ := (half ^ width) ^ count

private noncomputable def falseLowerEvidence (count width : Nat) :
    LowerEvidence (falseLowerRequest count width) system system (game count width)
      (fun _ s t ↦ s = t) where
  subject := rfl
  installation := Installation.reflexive system _
  spec _ := coinSpec
  local_bound _ _ operation post state := (operation_expectation _ operation post state).ge
  model_event _ := falseAccepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential _ _ := (half ^ width) ^ count
  mathematics e nonzero := false_game_lower count width e nonzero
  budget _ _ := by simp [System.initialWithEvents, system, falseLowerRequest]

/-- The exponential bound is tight even for arbitrary history-dependent strategies. -/
theorem false_acceptance_eq (roundCount : Nat) (e : Environment)
    (nonzero : e.residual = true) :
    (system.experiment (game 1 roundCount)).run e falseAccepting = half ^ roundCount := by
  apply le_antisymm (false_acceptance_le roundCount e)
  simpa [falseLowerRequest] using (falseLowerEvidence 1 roundCount).establish e nonzero

/-- The same tight law holds for nested batches without resetting the adversary's history. -/
theorem nested_false_acceptance_eq (count width : Nat) (e : Environment)
    (nonzero : e.residual = true) :
    (system.experiment (game count width)).run e falseAccepting = half ^ (width * count) := by
  apply le_antisymm (nested_false_acceptance_le count width e)
  simpa [falseLowerRequest, pow_mul] using
    (falseLowerEvidence count width).establish e nonzero

/-- An explicit nonconstant strategy: predict the most recently seen challenge. -/
@[expose] def echoStrategy : Strategy := fun history ↦ history.headD false

theorem three_adaptive_checks :
    (system.experiment (game 1 3)).run ⟨true, echoStrategy⟩ falseAccepting = half ^ 3 :=
  false_acceptance_eq 3 _ rfl

theorem two_batches_of_three_checks :
    (system.experiment (game 2 3)).run ⟨true, echoStrategy⟩ falseAccepting = half ^ 6 :=
  nested_false_acceptance_eq 2 3 _ rfl

theorem zero_checks_accept_false (strategy : Strategy) :
    (system.experiment (game 1 0)).run ⟨true, strategy⟩ falseAccepting = 1 := by
  simpa using false_acceptance_eq 0 ⟨true, strategy⟩ rfl

/-- The honest experiment has accepting mass one, not merely conditional acceptance. -/
theorem honest_acceptance_eq (count width : Nat) (e : Environment)
    (honest : e.residual = false ∧ ∀ history, e.strategy history = false) :
    (system.experiment (game count width)).run e accepting = 1 := by
  have := (system.experiment (game count width)).normalized e
  apply le_antisymm (measure_le_one _ _)
  simpa [CompletenessRequest.Holds, CompletenessRequest.toLower, completenessRequest]
    using honest_completeness count width e honest

@[expose] def honestEnvironment : Environment := ⟨false, fun _ ↦ false⟩

theorem honest_zero_response_accepts (count width : Nat) :
    (system.experiment (game count width)).run honestEnvironment accepting = 1 :=
  honest_acceptance_eq count width honestEnvironment ⟨rfl, fun _ ↦ rfl⟩

/-- Deliberate timing violation: the guess is chosen after receiving the current challenge. -/
@[expose] def revealedGame (_ : Environment) : Process Challenge (Bool × Bool) :=
  (Process.call (I := Challenge) () .done).bind fun challenge ↦
    let guess := challenge
    pure (true, guess == challenge)

/-- The original canonical false-acceptance meaning and half bound, applied to the attack. -/
@[expose] noncomputable def revealedSoundnessRequest :
    SoundnessRequest Environment (Execution Unit Unit (Bool × Bool)) Bool where
  experiment := system.experiment revealedGame
  admissible _ := True
  accepts out := accepted out.outcome = true
  statement out := residualOf out.outcome
  problem := PromiseProblem.ofPredicate (fun residual ↦ residual = false)
  measurable_bad := MeasurableSet.of_discrete
  error _ := half

private noncomputable def revealedLowerRequest :
    LowerRequest Environment (Execution Unit Unit (Bool × Bool)) where
  experiment := system.experiment revealedGame
  admissible _ := True
  event := falseAccepting
  measurable_event := MeasurableSet.of_discrete
  bound _ := 1

private theorem revealed_lower (e : Environment) :
    LowerBound coinSpec (revealedGame e)
      (fun value state ↦ falseAccepting.indicator 1 ⟨value, state.1, state.2⟩) (fun _ ↦ 1) := by
  apply (LowerBound.operation (spec := coinSpec) () (fun out _ ↦ resultReward (fun _ ↦ 1) out) (by
    intro state
    simp [coinSpec, resultReward, half_add_half])).bind coinSpec_mono
      (hstop := by intro why state; simp [resultReward])
  intro challenge
  apply LowerBound.pure
  intro state
  simp [falseAccepting, accepted, residualOf, resultReward, Set.indicator]

private noncomputable def revealedLowerEvidence :
    LowerEvidence revealedLowerRequest system system revealedGame (fun _ s t ↦ s = t) where
  subject := rfl
  installation := Installation.reflexive system _
  spec _ := coinSpec
  local_bound _ _ operation post state := (operation_expectation _ operation post state).ge
  model_event _ := falseAccepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential _ _ := 1
  mathematics e _ := revealed_lower e
  budget _ _ := by simp [revealedLowerRequest, System.initialWithEvents, system]

theorem revealed_false_acceptance_eq_one (e : Environment) :
    (system.experiment revealedGame).run e falseAccepting = 1 := by
  have := (system.experiment revealedGame).normalized e
  apply le_antisymm (measure_le_one _ _)
  exact revealedLowerEvidence.establish e trivial

/-- Revealing the challenge first falsifies the same nontrivial canonical soundness claim. -/
theorem revealed_bound_refused : ¬revealedSoundnessRequest.Holds := by
  intro alleged
  have h := alleged ⟨true, echoStrategy⟩ trivial
  change (system.experiment revealedGame).run _ falseAccepting ≤ half at h
  rw [revealed_false_acceptance_eq_one] at h
  exact (not_le_of_gt (by simpa only [half, one_div] using ENNReal.one_half_lt_one)) h

end ProtocolProofExamples.AdaptiveChecks
