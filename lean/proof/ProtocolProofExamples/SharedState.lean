module

public import ProtocolProof.Claims.Closure
public import ProtocolProof.Components.Representation

/-!
# A shared challenge behind an installed stateful component

Setup samples one private bit. Every check uses that same bit; no query resamples it.
The service retains an observable check counter. The concrete service additionally records an
unobservable audit counter, which the representation map erases. The component implements both
challenge revelation and checking by two primitive operations, and a separate adaptive caller
uses the component twice. All public execution and composition use Process and complete
execution kernels.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor ProtocolProof PIR
open scoped ENNReal

namespace ProtocolProofExamples.SharedState

local instance : MeasurableSpace Bool := ⊤

abbrev ModelState := Bool × Nat
abbrev ConcreteState := ModelState × Nat
abbrev Reply := Bool × Nat

/-- The primitive counter query cannot observe the separate concrete audit counter. -/
inductive PrimitiveOperation where
  | reveal
  | check (guess : Bool)
  | count

abbrev Primitive : Signature := ⟨PrimitiveOperation, fun _ ↦ Reply⟩

/-- Both component operations are implemented by multiple primitive operations. -/
inductive ComponentOperation where
  | challenge
  | verify (guess : Bool)

abbrev Component : Signature := ⟨ComponentOperation, fun _ ↦ Reply⟩

/-- Private service transition, including the observable number of checks. -/
@[expose] def primitiveStep : Handler Primitive ModelState Unit
  | .reveal, state => ⟨.returned (state.1, state.2), state, []⟩
  | .check guess, state =>
      ⟨.returned (guess == state.1, state.2 + 1), (state.1, state.2 + 1), []⟩
  | .count, state => ⟨.returned (false, state.2), state, []⟩

/-- Concrete queries perform the same transition and increment the hidden audit counter. -/
@[expose] def concreteStep (operation : PrimitiveOperation) (state : ConcreteState) :
    Execution ConcreteState Unit Reply :=
  let out := primitiveStep operation state.1
  ⟨out.outcome, (out.state, state.2 + 1), out.events⟩

@[expose] noncomputable def primitiveModel :
    (op : Primitive.Op) → Kernel ModelState (Execution ModelState Unit (Primitive.Reply op)) :=
  fun operation ↦ Kernel.deterministic (primitiveStep operation) (measurable_of_countable _)

@[expose] noncomputable def primitiveConcrete :
    (op : Primitive.Op) →
      Kernel ConcreteState (Execution ConcreteState Unit (Primitive.Reply op)) :=
  fun operation ↦ Kernel.deterministic (concreteStep operation) (measurable_of_countable _)

/-- Erase only the audit counter, retaining both the challenge and the observable counter. -/
@[expose] def represent : ConcreteState → ModelState := Prod.fst

/-- Accumulated event prefixes are retained by the non-injective state representation. -/
@[expose] def representAccumulated (state : ConcreteState × List Unit) :
    ModelState × List Unit := (represent state.1, state.2)

theorem representation_not_injective : ¬ Function.Injective represent := by
  intro h
  have hbad := h (a₁ := ((false, 0), 0)) (a₂ := ((false, 0), 1)) rfl
  exact Nat.zero_ne_one (congrArg Prod.snd hbad)

/-- The full answer/successor law commutes with the representation at every concrete state. -/
theorem primitive_representation (operation : PrimitiveOperation) (state : ConcreteState) :
    (primitiveConcrete operation state).map
      (fun out ↦ (⟨out.outcome, represent out.state, out.events⟩ :
        Execution ModelState Unit Reply)) =
      primitiveModel operation (represent state) := by
  simp [primitiveConcrete, primitiveModel, Kernel.deterministic_apply,
    Measure.map_dirac, concreteStep, represent]

@[expose] noncomputable def primitiveModelSystem : System Unit Primitive ModelState Unit where
  operations _ := primitiveModel
  initial _ := Measure.dirac (false, 0)
  operation_mass _ _ _ := by simp [primitiveModel, Kernel.deterministic_apply]
  initial_probability _ := inferInstance

@[expose] noncomputable def primitiveConcreteSystem : System Unit Primitive ConcreteState Unit where
  operations _ := primitiveConcrete
  initial _ := Measure.dirac ((false, 0), 0)
  operation_mass _ _ _ := by simp [primitiveConcrete, Kernel.deterministic_apply]
  initial_probability _ := inferInstance

private noncomputable def primitiveInstallation :
    KernelHandler.CouplingContract (primitiveConcreteSystem.accumulatedOperations ())
      (primitiveModelSystem.accumulatedOperations ())
      (fun concrete model ↦ representAccumulated concrete = model) :=
  Representation.contractOfMap (I := Primitive)
    (primitiveConcreteSystem.accumulatedOperations ())
    (primitiveModelSystem.accumulatedOperations ())
    representAccumulated (measurable_of_countable _) (by
    intro operation state
    rw [primitiveConcreteSystem.accumulatedOperations_apply () operation state,
      primitiveModelSystem.accumulatedOperations_apply () operation (representAccumulated state)]
    simp [primitiveConcreteSystem, primitiveModelSystem, primitiveConcrete, primitiveModel,
      Kernel.deterministic_apply, Measure.map_dirac, concreteStep, representAccumulated, represent])

/-- Reading the retained counter is a second operation, rather than a primitive leaf alias. -/
@[expose] def componentImplementation : OperationInterpretation Component Primitive
  | .challenge => do
      let challenge ← Process.call (I := Primitive) .reveal .done
      let counter ← Process.call (I := Primitive) .count .done
      pure (challenge.1, counter.2)
  | .verify guess => do
      let checked ← Process.call (I := Primitive) (.check guess) .done
      let counter ← Process.call (I := Primitive) .count .done
      pure (checked.1, counter.2)

@[expose] noncomputable def modelHandler :
    (op : Component.Op) → Kernel ModelState (Execution ModelState Unit (Component.Reply op)) :=
  fun operation ↦ Kernel.deterministic
    ((componentImplementation operation).run primitiveStep) (measurable_of_countable _)

@[expose] noncomputable def concreteHandler :
    (op : Component.Op) → Kernel ConcreteState
      (Execution ConcreteState Unit (Component.Reply op)) :=
  fun operation ↦ Kernel.deterministic
    ((componentImplementation operation).run concreteStep) (measurable_of_countable _)

/-- The component handler is the public probabilistic execution of its primitive implementation. -/
theorem model_implementation (operation : ComponentOperation) (state : ModelState) :
    primitiveModelSystem.run () (componentImplementation operation) state =
      modelHandler operation state :=
  primitiveModelSystem.run_eq_dirac () primitiveStep (fun _ _ ↦ rfl) _ _

theorem concrete_implementation (operation : ComponentOperation) (state : ConcreteState) :
    primitiveConcreteSystem.run () (componentImplementation operation) state =
      concreteHandler operation state :=
  primitiveConcreteSystem.run_eq_dirac () concreteStep (fun _ _ ↦ rfl) _ _

/-- Local component meaning: both primitive calls preserve the one shared challenge. -/
theorem model_verify_meaning (guess : Bool) (state : ModelState) :
    modelHandler (.verify guess) state =
      Measure.dirac ⟨.returned (guess == state.1, state.2 + 1),
        (state.1, state.2 + 1), []⟩ := by
  rfl

theorem model_challenge_meaning (state : ModelState) :
    modelHandler .challenge state = Measure.dirac ⟨.returned (state.1, state.2), state, []⟩ := by
  rfl

private theorem component_representation (operation : ComponentOperation)
    (state : ConcreteState) :
    let actual := (componentImplementation operation).run concreteStep state
    let model := (componentImplementation operation).run primitiveStep (represent state)
    actual.outcome = model.outcome ∧ represent actual.state = model.state ∧
      actual.events = model.events := by
  have related := PIR.run_related (fun concrete model ↦ represent concrete = model)
    (fun event : Unit ↦ [event]) (fun event : Unit ↦ [event])
    concreteStep primitiveStep (by
      intro op concrete model h
      subst model
      exact ⟨rfl, rfl, rfl⟩)
    (componentImplementation operation) state (represent state) rfl
  exact ⟨related.outcome, related.state, by simpa [observeEvents] using related.events⟩

@[expose] noncomputable def half : ENNReal := (2 : ENNReal)⁻¹

@[expose] noncomputable def modelInitial : Measure ModelState :=
  half • Measure.dirac (false, 0) + half • Measure.dirac (true, 0)

@[expose] noncomputable def concreteInitial : Measure ConcreteState :=
  half • Measure.dirac ((false, 0), 0) + half • Measure.dirac ((true, 0), 0)

/-- The adversary fixes its first guess, then chooses a second guess using the first reply. -/
abbrev Environment := Bool × (Reply → Bool)

@[expose] noncomputable def actualSystem : System Environment Component ConcreteState Unit where
  operations _ := concreteHandler
  initial _ := concreteInitial
  operation_mass _ _ _ := by simp [concreteHandler, Kernel.deterministic_apply]
  initial_probability _ := ⟨by simp [concreteInitial, half, ENNReal.inv_two_add_inv_two]⟩

@[expose] noncomputable def modelSystem : System Environment Component ModelState Unit where
  operations _ := modelHandler
  initial _ := modelInitial
  operation_mass _ operation state := by
    cases operation with
    | challenge => rw [model_challenge_meaning]; simp
    | verify guess => rw [model_verify_meaning]; simp
  initial_probability _ := ⟨by simp [modelInitial, half, ENNReal.inv_two_add_inv_two]⟩

private theorem initial_coverage : concreteInitial.map represent = modelInitial := by
  unfold concreteInitial modelInitial represent
  rw [Measure.map_add _ _ measurable_fst]
  simp [Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_dirac]

/-- Installing the whole component uses the full accumulated-state representation. -/
private noncomputable def componentInstallation :
    KernelHandler.CouplingContract (actualSystem.accumulatedOperations (false, fun _ ↦ false))
      (modelSystem.accumulatedOperations (false, fun _ ↦ false))
      (fun concrete model ↦ representAccumulated concrete = model) :=
  Representation.contractOfMap (I := Component)
    (actualSystem.accumulatedOperations (false, fun _ ↦ false))
    (modelSystem.accumulatedOperations (false, fun _ ↦ false))
    representAccumulated (measurable_of_countable _) (by
    intro operation state
    obtain ⟨ho, hs, hl⟩ := component_representation operation state.1
    rw [actualSystem.accumulatedOperations_apply _ operation state,
      modelSystem.accumulatedOperations_apply _ operation (representAccumulated state)]
    simp only [actualSystem, modelSystem, concreteHandler, modelHandler,
      Kernel.deterministic_apply, Measure.map_dirac]
    simp only [representAccumulated, ho, hs, hl])

private noncomputable def installation (admissible : Environment → Prop) :
    Installation actualSystem modelSystem admissible
      (fun _ concrete model ↦ representAccumulated concrete = model) where
  operations _ _ := componentInstallation
  initial _ _ := Representation.initial_of_map_eq _ _ representAccumulated
    (measurable_of_countable _) (by
      simp only [System.initialWithEvents, actualSystem, modelSystem]
      rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
      change concreteInitial.map (fun state ↦ (represent state, ([] : List Unit))) = _
      rw [← initial_coverage]
      exact (Measure.map_map (measurable_id.prodMk measurable_const)
        (show Measurable represent from measurable_fst)).symm)

/-- Hierarchical execution also agrees exactly with Process inlining, with shared state. -/
theorem component_inlining (program : Process Component Bool) (state : ConcreteState) :
    primitiveConcreteSystem.run () (program.interpret componentImplementation) state =
      actualSystem.run (false, fun _ ↦ false) program state := by
  have lower := primitiveConcreteSystem.run_eq_dirac () concreteStep (fun _ _ ↦ rfl)
    (program.interpret componentImplementation) state
  have upper := actualSystem.run_eq_dirac (false, fun _ ↦ false)
    (fun operation ↦ (componentImplementation operation).run concreteStep)
    (by
      intro operation current
      change concreteHandler operation current = _
      exact Kernel.deterministic_apply _ _) program state
  exact lower.trans ((congrArg Measure.dirac
    (Process.run_interpret componentImplementation concreteStep program state)).trans upper.symm)

/-- The first answer controls the branch and therefore the second operation's argument. -/
@[expose] def conjunction (environment : Environment) : Process Component Bool := do
  let first ← Process.call (I := Component) (.verify environment.1) .done
  let second ← if first.1 then
      Process.call (I := Component) (.verify (environment.2 (true, first.2))) .done
    else Process.call (I := Component) (.verify (environment.2 (false, first.2))) .done
  pure (first.1 && second.1 && (second.2 == first.2 + 1))

/-- The honest caller learns the shared challenge, then makes the two matching checks. -/
@[expose] def honest (_ : Environment) : Process Component Bool := do
  let challenge ← Process.call (I := Component) .challenge .done
  let first ← Process.call (I := Component) (.verify challenge.1) .done
  let second ← Process.call (I := Component) (.verify challenge.1) .done
  pure (first.1 && second.1 && (second.2 == first.2 + 1))

private theorem expectation_verify (guess : Bool)
    (post : Outcome Reply → ModelState × List Unit → ENNReal) :
    opExpectation (I := Component) (modelSystem.accumulatedOperations (false, fun _ ↦ false))
      (.verify guess) post =
      fun state ↦ post (.returned (guess == state.1.1, state.1.2 + 1))
        ((state.1.1, state.1.2 + 1), state.2) := by
  funext state
  change (∫⁻ out, post out.1 out.2 ∂(modelSystem.accumulatedOperations
    (false, fun _ ↦ false)) _ state) = _
  rw [modelSystem.accumulatedOperations_apply (false, fun _ ↦ false) _ state]
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  change (∫⁻ out : Execution ModelState Unit Reply,
    post out.outcome (out.state, state.2 ++ out.events)
    ∂modelHandler (.verify guess) state.1) = _
  rw [model_verify_meaning guess state.1]
  simp

private theorem expectation_challenge (post : Outcome Reply → ModelState × List Unit → ENNReal) :
    opExpectation (I := Component) (modelSystem.accumulatedOperations (false, fun _ ↦ false))
      .challenge post =
      fun state ↦ post (.returned (state.1.1, state.1.2)) state := by
  funext state
  change (∫⁻ out, post out.1 out.2 ∂(modelSystem.accumulatedOperations
    (false, fun _ ↦ false)) _ state) = _
  rw [modelSystem.accumulatedOperations_apply (false, fun _ ↦ false) _ state]
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  change (∫⁻ out : Execution ModelState Unit Reply,
    post out.outcome (out.state, state.2 ++ out.events)
    ∂modelHandler .challenge state.1) = _
  rw [model_challenge_meaning state.1]
  simp

private def accepting (State : Type) : Set (Execution State Unit Bool) :=
  {out | out.outcome = .returned true}

private def firstPotential (guess : Bool) (state : ModelState × List Unit) : ENNReal :=
  if guess == state.1.1 then 1 else 0

/-- A fixed false statement is accepted only when both checks and the retained counter agree.
The adversary can adapt to the complete first component reply, including its counter. -/
@[expose] noncomputable def soundness :
    SoundnessRequest Environment (Execution ConcreteState Unit Bool) Unit where
  experiment := actualSystem.experiment conjunction
  admissible _ := True
  accepts out := out.outcome = .returned true
  statement _ := ()
  problem := PromiseProblem.ofPredicate (fun _ ↦ False)
  measurable_bad := MeasurableSet.of_discrete
  error _ := half

/-- Honest revelation followed by two checks must accept with unconditional probability one. -/
@[expose] noncomputable def completeness :
    CompletenessRequest Environment (Execution ConcreteState Unit Bool) where
  experiment := actualSystem.experiment honest
  admissible _ := True
  accepts := {out | out.outcome = .returned true}
  measurable_accepts := MeasurableSet.of_discrete
  error _ := 0

private theorem conjunction_upper (environment : Environment) :
    UpperBound
      (opExpectation (I := Component) (modelSystem.accumulatedOperations (false, fun _ ↦ false)))
      (conjunction environment)
      (fun value state ↦ (accepting ModelState).indicator 1 ⟨value, state.1, state.2⟩)
      (firstPotential environment.1) := by
  intro state
  change wpFold _ (conjunction environment) _ state ≤ _
  simp only [conjunction, bind, pure, Process.bind, wpFold_call, expectation_verify]
  cases hfirst : (environment.1 == state.1.1) <;>
    simp [hfirst, wpFold_call, wpFold_done, expectation_verify,
      firstPotential, accepting, Set.indicator]
  split <;> simp

private theorem first_budget (guess : Bool) :
    (∫⁻ state, firstPotential guess state
      ∂(modelSystem.initialWithEvents (false, fun _ ↦ false))) = half := by
  change (∫⁻ state, firstPotential guess state
    ∂(modelInitial.map (fun state : ModelState ↦ (state, ([] : List Unit))))) = half
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  cases guess <;> simp [modelInitial, firstPotential, lintegral_add_measure,
    lintegral_smul_measure]

private noncomputable def soundnessEvidence :
    UpperEvidence soundness.toUpper actualSystem modelSystem conjunction
      (fun _ concrete model ↦ representAccumulated concrete = model) where
  subject := rfl
  installation := installation _
  spec _ :=
    opExpectation (I := Component) (modelSystem.accumulatedOperations (false, fun _ ↦ false))
  local_bound _ _ _ _ := le_rfl
  model_event _ := accepting ModelState
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h.1
  potential environment := firstPotential environment.1
  mathematics environment _ := conjunction_upper environment
  budget environment _ := (first_budget environment.1).le

/-- Root closure proves the actual fixed soundness request for every adaptive environment. -/
theorem shared_soundness : soundness.Holds := soundnessEvidence.establish

private theorem honest_lower (environment : Environment) :
    LowerBound
      (opExpectation (I := Component) (modelSystem.accumulatedOperations (false, fun _ ↦ false)))
      (honest environment)
      (fun value state ↦ (accepting ModelState).indicator 1 ⟨value, state.1, state.2⟩)
      (fun _ ↦ 1) := by
  intro state
  change _ ≤ wpFold _ (honest environment) _ state
  simp only [honest, bind, pure, Process.bind, wpFold_call, wpFold_done,
    expectation_verify, expectation_challenge]
  simp [accepting]

private noncomputable def completenessEvidence :
    LowerEvidence completeness.toLower actualSystem modelSystem honest
      (fun _ concrete model ↦ representAccumulated concrete = model) where
  subject := rfl
  installation := installation _
  spec _ :=
    opExpectation (I := Component) (modelSystem.accumulatedOperations (false, fun _ ↦ false))
  local_bound _ _ _ _ := le_rfl
  model_event _ := accepting ModelState
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential _ _ := 1
  mathematics environment _ := honest_lower environment
  budget environment _ := by
    change (1 - 0 : ENNReal) ≤ ∫⁻ _ : ModelState × List Unit, (1 : ENNReal)
      ∂(modelSystem.initialWithEvents environment)
    rw [tsub_zero, lintegral_one]
    change 1 ≤ (modelInitial.map (fun state : ModelState ↦ (state, ([] : List Unit)))) Set.univ
    have hm : Measurable (fun state : ModelState ↦ (state, ([] : List Unit))) :=
      measurable_of_countable _
    rw [Measure.map_apply hm MeasurableSet.univ]
    simp [modelInitial, half, ENNReal.inv_two_add_inv_two]

/-- Root closure proves the fixed honest completeness request, including all rejecting mass. -/
theorem shared_completeness : completeness.Holds := completenessEvidence.establish

/-- A nonadaptive admitted strategy that submits the same guess on both branches. -/
@[expose] def matchingEnvironment (guess : Bool) : Environment := (guess, fun _ ↦ guess)

/-- A separately fixed lower request makes the shared-challenge upper bound sharp. -/
@[expose] noncomputable def matchingAcceptance :
    CompletenessRequest Environment (Execution ConcreteState Unit Bool) where
  experiment := actualSystem.experiment conjunction
  admissible environment := ∃ guess, environment = matchingEnvironment guess
  accepts := {out | out.outcome = .returned true}
  measurable_accepts := MeasurableSet.of_discrete
  error _ := half

private theorem matching_lower (guess : Bool) :
    LowerBound
      (opExpectation (I := Component) (modelSystem.accumulatedOperations (false, fun _ ↦ false)))
      (conjunction (matchingEnvironment guess))
      (fun value state ↦ (accepting ModelState).indicator 1 ⟨value, state.1, state.2⟩)
      (firstPotential guess) := by
  intro state
  change _ ≤ wpFold _ (conjunction (matchingEnvironment guess)) _ state
  simp only [conjunction, matchingEnvironment, bind, pure, Process.bind, wpFold_call,
    expectation_verify]
  cases hfirst : (guess == state.1.1) <;>
    simp [hfirst, wpFold_call, wpFold_done, expectation_verify,
      firstPotential, accepting]

private noncomputable def matchingEvidence :
    LowerEvidence matchingAcceptance.toLower actualSystem modelSystem conjunction
      (fun _ concrete model ↦ representAccumulated concrete = model) where
  subject := rfl
  installation := installation _
  spec _ :=
    opExpectation (I := Component) (modelSystem.accumulatedOperations (false, fun _ ↦ false))
  local_bound _ _ _ _ := le_rfl
  model_event _ := accepting ModelState
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential environment := firstPotential environment.1
  mathematics _ hadmitted := by
    obtain ⟨guess, rfl⟩ := hadmitted
    exact matching_lower guess
  budget environment _ := by
    change 1 - half ≤ ∫⁻ state, firstPotential environment.1 state
      ∂(modelSystem.initialWithEvents (false, fun _ ↦ false))
    rw [first_budget]
    exact (ENNReal.one_sub_inv_two).le

/-- The same root lower closure proves the matching strategy's actual accepting mass. -/
theorem matching_acceptance : matchingAcceptance.Holds := matchingEvidence.establish

/-- Two equal guesses against the shared bit succeed with probability one half. -/
theorem matching_probability (guess : Bool) :
    (actualSystem.experiment conjunction).run (matchingEnvironment guess)
      {out | out.outcome = .returned true} = half := by
  apply le_antisymm
  · simpa [SoundnessRequest.Holds, SoundnessRequest.toUpper, soundness] using
      shared_soundness (matchingEnvironment guess) trivial
  · have h := matching_acceptance (matchingEnvironment guess) ⟨guess, rfl⟩
    simpa [matchingAcceptance, CompletenessRequest.toLower, half,
      ENNReal.one_sub_inv_two] using h

/-- Even though a single check against a fair bit has probability one half, its repetition
uses the same bit. The arbitrary counter emphasizes that advancing it does not refresh setup. -/
theorem single_check_probability (guess : Bool) (counter : Nat) :
    (∫⁻ state, opExpectation (I := Component)
      (modelSystem.accumulatedOperations (false, fun _ ↦ false))
      (.verify guess) (fun outcome _ ↦ match outcome with
        | .returned reply => if reply.1 then 1 else 0
        | .stopped _ => 0) (state, [])
      ∂(half • Measure.dirac (false, counter) + half • Measure.dirac (true, counter))) = half := by
  cases guess <;> simp [expectation_verify, lintegral_add_measure, lintegral_smul_measure]

/-- Multiplying the two per-check probabilities gives a strictly false upper bound. -/
theorem multiplying_check_probabilities_invalid (guess : Bool) :
    ¬ (actualSystem.experiment conjunction).run (matchingEnvironment guess)
      {out | out.outcome = .returned true} ≤ half * half := by
  rw [matching_probability]
  have hpos : (0 : ENNReal) < half := by simp [half]
  have hlt : half < 1 := by simp [half]
  exact not_le.mpr (by
    calc
      half * half < 1 * half := ENNReal.mul_lt_mul_left (a := half) (ne_of_gt hpos)
        (by simp [half]) hlt
      _ = half := one_mul _)

/-- Resetting the retained service counter changes an observable answer, even if the bit
is preserved. Therefore that reset cannot satisfy the installed local representation law. -/
theorem resetting_counter_invalid :
    modelHandler (.verify false) (false, 1) ≠ modelHandler (.verify false) (false, 0) := by
  rw [model_verify_meaning, model_verify_meaning]
  intro h
  have hcounter := congrArg (fun law : Measure (Execution ModelState Unit Reply) ↦
    law {out | ∃ accepted, out.outcome = .returned (accepted, 2)}) h
  simp at hcounter

end ProtocolProofExamples.SharedState
