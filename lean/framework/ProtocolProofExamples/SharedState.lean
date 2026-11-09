module

public import ProtocolProof.Claims.Closure
public import ProtocolProof.Components.Representation

/-!
# A shared challenge behind an installed stateful component

Setup samples one private bit. Every check uses that same bit; no query resamples it.
The service retains an observable check counter. The concrete service additionally records an
unobservable audit counter, which the representation map erases. The component implements both
challenge revelation and checking by two primitive operations, and a separate adaptive caller
uses the component twice. All execution and composition use the upstream free monad and kernels.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor ProtocolProof
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

abbrev Primitive : PFunctor := ⟨PrimitiveOperation, fun _ ↦ Reply⟩

/-- Both component operations are implemented by multiple primitive operations. -/
inductive ComponentOperation where
  | challenge
  | verify (guess : Bool)

abbrev Component : PFunctor := ⟨ComponentOperation, fun _ ↦ Reply⟩

/-- Private service transition, including the observable number of checks. -/
@[expose] def primitiveStep : PrimitiveOperation → ModelState → Reply × ModelState
  | .reveal, state => ((state.1, state.2), state)
  | .check guess, state =>
      ((guess == state.1, state.2 + 1), (state.1, state.2 + 1))
  | .count, state => ((false, state.2), state)

/-- Concrete queries perform the same transition and increment the hidden audit counter. -/
@[expose] def concreteStep (operation : PrimitiveOperation) (state : ConcreteState) :
    Reply × ConcreteState :=
  let out := primitiveStep operation state.1
  (out.1, (out.2, state.2 + 1))

@[expose] noncomputable def primitiveModel : KernelHandler Primitive ModelState := fun operation ↦
  Kernel.deterministic (primitiveStep operation) (measurable_of_countable _)

@[expose] noncomputable def primitiveConcrete : KernelHandler Primitive ConcreteState :=
  fun operation ↦ Kernel.deterministic (concreteStep operation) (measurable_of_countable _)

/-- Erase only the audit counter, retaining both the challenge and the observable counter. -/
@[expose] def represent : ConcreteState → ModelState := Prod.fst

theorem representation_not_injective : ¬ Function.Injective represent := by
  intro h
  have hbad := h (a₁ := ((false, 0), 0)) (a₂ := ((false, 0), 1)) rfl
  exact Nat.zero_ne_one (congrArg Prod.snd hbad)

/-- The full answer/successor law commutes with the representation at every concrete state. -/
theorem primitive_representation (operation : PrimitiveOperation) (state : ConcreteState) :
    (primitiveConcrete operation state).map (fun out ↦ (out.1, represent out.2)) =
      primitiveModel operation (represent state) := by
  simp [primitiveConcrete, primitiveModel, Kernel.deterministic_apply,
    Measure.map_dirac, concreteStep, represent]

private noncomputable def primitiveInstallation :
    KernelHandler.CouplingContract primitiveConcrete primitiveModel
      (fun concrete model ↦ represent concrete = model) :=
  Representation.contractOfMap primitiveConcrete primitiveModel represent measurable_fst
    primitive_representation

/-- Reading the retained counter is a second operation, rather than a primitive leaf alias. -/
@[expose] def componentImplementation :
    (operation : Component.A) → FreeM Primitive (Component.B operation)
  | .challenge => do
      let challenge ← FreeM.lift (P := Primitive) .reveal
      let counter ← FreeM.lift (P := Primitive) .count
      pure (challenge.1, counter.2)
  | .verify guess => do
      let checked ← FreeM.lift (P := Primitive) (.check guess)
      let counter ← FreeM.lift (P := Primitive) .count
      pure (checked.1, counter.2)

@[expose] noncomputable def modelHandler : KernelHandler Component ModelState :=
  fun operation ↦ FreeM.runKernel primitiveModel (componentImplementation operation)

@[expose] noncomputable def concreteHandler : KernelHandler Component ConcreteState :=
  fun operation ↦ FreeM.runKernel primitiveConcrete (componentImplementation operation)

/-- Local component meaning: both primitive calls preserve the one shared challenge. -/
theorem model_verify_meaning (guess : Bool) (state : ModelState) :
    modelHandler (.verify guess) state =
      Measure.dirac ((guess == state.1, state.2 + 1), (state.1, state.2 + 1)) := by
  change FreeM.runKernel primitiveModel
    ((FreeM.lift (P := Primitive) (.check guess)).bind fun checked ↦
      (FreeM.lift (P := Primitive) .count).bind fun counter ↦
        pure (checked.1, counter.2)) state = _
  simp only [FreeM.runKernel_bind primitiveModel, FreeM.runKernel_lift primitiveModel,
    FreeM.runKernel_pure primitiveModel]
  simp only [primitiveModel, Kernel.deterministic_apply, primitiveStep]
  rw [Measure.dirac_bind (measurable_of_countable _)]
  simp only [Measure.dirac_bind (measurable_of_countable _)]

theorem model_challenge_meaning (state : ModelState) :
    modelHandler .challenge state = Measure.dirac ((state.1, state.2), state) := by
  change FreeM.runKernel primitiveModel
    ((FreeM.lift (P := Primitive) .reveal).bind fun challenge ↦
      (FreeM.lift (P := Primitive) .count).bind fun counter ↦
        pure (challenge.1, counter.2)) state = _
  simp only [FreeM.runKernel_bind primitiveModel, FreeM.runKernel_lift primitiveModel,
    FreeM.runKernel_pure primitiveModel]
  simp only [primitiveModel, Kernel.deterministic_apply, primitiveStep]
  rw [Measure.dirac_bind (measurable_of_countable _)]
  simp only [Measure.dirac_bind (measurable_of_countable _)]

/-- Installing the whole component uses the generic upstream free-handler installer. -/
private noncomputable def componentInstallation :
    KernelHandler.CouplingContract concreteHandler modelHandler
      (fun concrete model ↦ represent concrete = model) :=
  primitiveInstallation.freeHandler componentImplementation

/-- Hierarchical execution also agrees exactly with upstream inlining, with shared state. -/
theorem component_inlining (program : FreeM Component Bool) (state : ConcreteState) :
    FreeM.runKernel primitiveConcrete (program.liftM componentImplementation) state =
      FreeM.runKernel concreteHandler program state :=
  FreeM.runKernel_liftM primitiveConcrete componentImplementation program state

@[expose] noncomputable def half : ENNReal := (2 : ENNReal)⁻¹

@[expose] noncomputable def modelInitial : Measure ModelState :=
  half • Measure.dirac (false, 0) + half • Measure.dirac (true, 0)

@[expose] noncomputable def concreteInitial : Measure ConcreteState :=
  half • Measure.dirac ((false, 0), 0) + half • Measure.dirac ((true, 0), 0)

/-- The adversary fixes its first guess, then chooses a second guess using the first reply. -/
abbrev Environment := Bool × (Reply → Bool)

@[expose] noncomputable def actualSystem : System Environment Component ConcreteState where
  operations _ := concreteHandler
  initial _ := concreteInitial
  operation_mass _ operation state :=
    runKernel_mass_one primitiveConcrete (by
      intro a s
      simp [primitiveConcrete, Kernel.deterministic_apply])
      (componentImplementation operation) state
  initial_probability _ := ⟨by simp [concreteInitial, half, ENNReal.inv_two_add_inv_two]⟩

@[expose] noncomputable def modelSystem : System Environment Component ModelState where
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

private noncomputable def connection (admissible : Environment → Prop) :
    Connection actualSystem modelSystem admissible
    (fun _ concrete model ↦ represent concrete = model) where
  operations _ _ := componentInstallation
  initial _ _ := Representation.initial_of_map_eq concreteInitial modelInitial represent
    measurable_fst initial_coverage

/-- The first answer controls the branch and therefore the second operation's argument. -/
@[expose] def conjunction (environment : Environment) : FreeM Component Bool := do
  let first ← FreeM.lift (P := Component) (.verify environment.1)
  let second ← if first.1 then FreeM.lift (P := Component) (.verify (environment.2 (true, first.2)))
    else FreeM.lift (P := Component) (.verify (environment.2 (false, first.2)))
  pure (first.1 && second.1 && (second.2 == first.2 + 1))

/-- The honest caller learns the shared challenge, then makes the two matching checks. -/
@[expose] def honest (_ : Environment) : FreeM Component Bool := do
  let challenge ← FreeM.lift (P := Component) .challenge
  let first ← FreeM.lift (P := Component) (.verify challenge.1)
  let second ← FreeM.lift (P := Component) (.verify challenge.1)
  pure (first.1 && second.1 && (second.2 == first.2 + 1))

private theorem expectation_verify (guess : Bool) (post : Reply → ModelState → ENNReal) :
    opExpectation modelHandler (.verify guess) post =
      fun state ↦ post (guess == state.1, state.2 + 1) (state.1, state.2 + 1) := by
  funext state
  unfold opExpectation
  rw [model_verify_meaning]
  simp

private theorem expectation_challenge (post : Reply → ModelState → ENNReal) :
    opExpectation modelHandler .challenge post = fun state ↦ post (state.1, state.2) state := by
  funext state
  unfold opExpectation
  rw [model_challenge_meaning]
  simp

private def accepting (State : Type) : Set (Bool × State) := {out | out.1 = true}

private def firstPotential (guess : Bool) (state : ModelState) : ENNReal :=
  if guess == state.1 then 1 else 0

/-- A fixed false statement is accepted only when both checks and the retained counter agree.
The adversary can adapt to the complete first component reply, including its counter. -/
@[expose] noncomputable def soundness :
    SoundnessRequest Environment (Bool × ConcreteState) Unit where
  experiment := actualSystem.experiment conjunction
  admissible _ := True
  accepts out := out.1 = true
  statement _ := ()
  problem := PromiseProblem.ofPredicate (fun _ ↦ False)
  measurable_bad := MeasurableSet.of_discrete
  error _ := half

/-- Honest revelation followed by two checks must accept with unconditional probability one. -/
@[expose] noncomputable def completeness :
    CompletenessRequest Environment (Bool × ConcreteState) where
  experiment := actualSystem.experiment honest
  admissible _ := True
  accepts := {out | out.1 = true}
  measurable_accepts := MeasurableSet.of_discrete
  error _ := 0

private theorem conjunction_upper (environment : Environment) :
    UpperBound (opExpectation modelHandler) (conjunction environment)
      (fun value state ↦ (accepting ModelState).indicator 1 (value, state))
      (firstPotential environment.1) := by
  intro state
  simp only [conjunction, FreeM.wpFold_bind, FreeM.wpFold_lift, FreeM.wpFold_ite,
    FreeM.wpFold_pure, expectation_verify]
  cases hfirst : (environment.1 == state.1) <;>
    simp [hfirst, firstPotential, accepting, Set.indicator]
  split <;> simp

private theorem first_budget (guess : Bool) :
    (∫⁻ state, firstPotential guess state ∂modelInitial) = half := by
  cases guess <;> simp [modelInitial, firstPotential, lintegral_add_measure,
    lintegral_smul_measure]

private noncomputable def soundnessEvidence :
    UpperEvidence soundness.toUpper actualSystem modelSystem conjunction
      (fun _ concrete model ↦ represent concrete = model) where
  subject := rfl
  connection := connection _
  spec _ := opExpectation modelHandler
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
    LowerBound (opExpectation modelHandler) (honest environment)
      (fun value state ↦ (accepting ModelState).indicator 1 (value, state)) (fun _ ↦ 1) := by
  intro state
  simp only [honest, FreeM.wpFold_bind, FreeM.wpFold_lift, FreeM.wpFold_pure,
    expectation_verify, expectation_challenge]
  simp [accepting]

private noncomputable def completenessEvidence :
    LowerEvidence completeness.toLower actualSystem modelSystem honest
      (fun _ concrete model ↦ represent concrete = model) where
  subject := rfl
  connection := connection _
  spec _ := opExpectation modelHandler
  local_bound _ _ _ _ := le_rfl
  model_event _ := accepting ModelState
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential _ _ := 1
  mathematics environment _ := honest_lower environment
  budget _ _ := by simp [completeness, CompletenessRequest.toLower, modelSystem,
    modelInitial, half, ENNReal.inv_two_add_inv_two]

/-- Root closure proves the fixed honest completeness request, including all rejecting mass. -/
theorem shared_completeness : completeness.Holds := completenessEvidence.establish

/-- A nonadaptive admitted strategy that submits the same guess on both branches. -/
@[expose] def matchingEnvironment (guess : Bool) : Environment := (guess, fun _ ↦ guess)

/-- A separately fixed lower request makes the shared-challenge upper bound sharp. -/
@[expose] noncomputable def matchingAcceptance :
    CompletenessRequest Environment (Bool × ConcreteState) where
  experiment := actualSystem.experiment conjunction
  admissible environment := ∃ guess, environment = matchingEnvironment guess
  accepts := {out | out.1 = true}
  measurable_accepts := MeasurableSet.of_discrete
  error _ := half

private theorem matching_lower (guess : Bool) :
    LowerBound (opExpectation modelHandler) (conjunction (matchingEnvironment guess))
      (fun value state ↦ (accepting ModelState).indicator 1 (value, state))
      (firstPotential guess) := by
  intro state
  simp only [conjunction, matchingEnvironment, FreeM.wpFold_bind, FreeM.wpFold_lift,
    FreeM.wpFold_ite, FreeM.wpFold_pure, expectation_verify]
  cases hfirst : (guess == state.1) <;>
    simp [hfirst, firstPotential, accepting]

private noncomputable def matchingEvidence :
    LowerEvidence matchingAcceptance.toLower actualSystem modelSystem conjunction
      (fun _ concrete model ↦ represent concrete = model) where
  subject := rfl
  connection := connection _
  spec _ := opExpectation modelHandler
  local_bound _ _ _ _ := le_rfl
  model_event _ := accepting ModelState
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential environment := firstPotential environment.1
  mathematics _ hadmitted := by
    obtain ⟨guess, rfl⟩ := hadmitted
    exact matching_lower guess
  budget environment _ := by
    change 1 - half ≤ ∫⁻ state, firstPotential environment.1 state ∂modelInitial
    rw [first_budget]
    exact (ENNReal.one_sub_inv_two).le

/-- The same root lower closure proves the matching strategy's actual accepting mass. -/
theorem matching_acceptance : matchingAcceptance.Holds := matchingEvidence.establish

/-- Two equal guesses against the shared bit succeed with probability one half. -/
theorem matching_probability (guess : Bool) :
    (actualSystem.experiment conjunction).run (matchingEnvironment guess)
      {out | out.1 = true} = half := by
  apply le_antisymm
  · simpa [SoundnessRequest.Holds, SoundnessRequest.toUpper, soundness] using
      shared_soundness (matchingEnvironment guess) trivial
  · have h := matching_acceptance (matchingEnvironment guess) ⟨guess, rfl⟩
    simpa [matchingAcceptance, CompletenessRequest.toLower, half,
      ENNReal.one_sub_inv_two] using h

/-- Even though a single check against a fair bit has probability one half, its repetition
uses the same bit. The arbitrary counter emphasizes that advancing it does not refresh setup. -/
theorem single_check_probability (guess : Bool) (counter : Nat) :
    (∫⁻ state, opExpectation modelHandler (.verify guess)
      (fun reply _ ↦ if reply.1 then 1 else 0) state
      ∂(half • Measure.dirac (false, counter) + half • Measure.dirac (true, counter))) = half := by
  cases guess <;> simp [expectation_verify, lintegral_add_measure, lintegral_smul_measure]

/-- Multiplying the two per-check probabilities gives a strictly false upper bound. -/
theorem multiplying_check_probabilities_invalid (guess : Bool) :
    ¬ (actualSystem.experiment conjunction).run (matchingEnvironment guess)
      {out | out.1 = true} ≤ half * half := by
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
  have hcounter := congrArg (fun law : Measure (Reply × ModelState) ↦
    law {out | out.1.2 = 2}) h
  simp at hcounter

end ProtocolProofExamples.SharedState
