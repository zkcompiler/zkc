module

public import VCVio.EvalDist.PFunctorKernel
public import PolyFun.PFunctor.Free.WP

/-!
# Expectations of stateful interactions

The operation transformer integrates the joint answer and successor state supplied by a kernel
handler. Its extension is the upstream specification fold, and its probability interpretation is
the upstream `FreeM.runKernel`. No additional program evaluator is introduced.

The measurable-postcondition bridge allows arbitrary measurable state and result spaces. The
unrestricted-postcondition specialization uses countable spaces with measurable singletons.
Neither bridge assumes mass one. Constant rewards retain the execution's total mass. Normalized
operations give a separate losslessness theorem, including every explicitly returned exit value.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe uA uB uS uX uY

namespace ProtocolProof

variable {P : PFunctor.{uA, uB}} {S : Type uS} {α : Type uX} {β : Type uY}
variable [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S]

/-- One operation's expected continuation potential, including its successor private state. -/
@[expose]
noncomputable def opExpectation (handler : PFunctor.KernelHandler P S) :
    PFunctor.OpSpec P (S → ENNReal) :=
  fun a post state ↦ ∫⁻ out, post out.1 out.2 ∂handler a state

/-- Joint kernel expectations are monotone in arbitrary nonnegative continuation potentials. -/
theorem opExpectation_monotone (handler : PFunctor.KernelHandler P S) :
    (opExpectation handler).Monotone := by
  intro a post post' hpost state
  exact lintegral_mono fun out ↦ hpost out.1 out.2

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
variable [MeasurableSpace α] [MeasurableSpace β]

/-- Expected terminal reward under the existing joint result-and-state execution kernel. -/
@[expose]
noncomputable def runExpectation (handler : PFunctor.KernelHandler P S)
    (program : PFunctor.FreeM P α) (post : α → S → ENNReal) : S → ENNReal :=
  fun state ↦ ∫⁻ out, post out.1 out.2 ∂PFunctor.FreeM.runKernel handler program state

/-- Folding exact local expectations agrees with kernel execution for measurable rewards. -/
theorem wpFold_eq_runExpectation_of_measurable (handler : PFunctor.KernelHandler P S)
    (program : PFunctor.FreeM P α) (post : α → S → ENNReal)
    (hpost : Measurable fun out : α × S ↦ post out.1 out.2) :
    PFunctor.FreeM.wpFold (opExpectation handler) program post =
      runExpectation handler program post := by
  induction program with
  | pure value =>
      funext state
      change post value state = _
      unfold runExpectation
      rw [PFunctor.FreeM.runKernel_pure]
      exact (lintegral_dirac' (value, state) hpost).symm
  | lift_bind a next ih =>
      funext state
      change (∫⁻ out, PFunctor.FreeM.wpFold (opExpectation handler) (next out.1) post out.2
        ∂handler a state) = _
      simp_rw [ih]
      unfold runExpectation
      rw [← PFunctor.FreeM.liftBind_eq, PFunctor.FreeM.runKernel_liftBind]
      exact (Measure.lintegral_bind
        (PFunctor.FreeM.measurable_runKernel_continuation handler next).aemeasurable
        hpost.aemeasurable).symm

/-- On countable discrete spaces every terminal reward has the kernel interpretation. -/
theorem wpFold_eq_runExpectation [Countable S] [MeasurableSingletonClass S]
    [Countable α] [MeasurableSingletonClass α] (handler : PFunctor.KernelHandler P S)
    (program : PFunctor.FreeM P α) (post : α → S → ENNReal) :
    PFunctor.FreeM.wpFold (opExpectation handler) program post =
      runExpectation handler program post :=
  wpFold_eq_runExpectation_of_measurable handler program post (measurable_of_countable _)

/-- The tower law threads the prefix's actual returned value and private state into the suffix. -/
theorem runExpectation_bind [Countable α] [MeasurableSingletonClass α]
    (handler : PFunctor.KernelHandler P S) (program : PFunctor.FreeM P α)
    (next : α → PFunctor.FreeM P β) (post : β → S → ENNReal)
    (hpost : Measurable fun out : β × S ↦ post out.1 out.2) (state : S) :
    runExpectation handler (program.bind next) post state =
      runExpectation handler program (fun value ↦ runExpectation handler (next value) post)
        state := by
  unfold runExpectation
  rw [PFunctor.FreeM.runKernel_bind]
  exact Measure.lintegral_bind
    (PFunctor.FreeM.measurable_runKernel_continuation handler next).aemeasurable
    hpost.aemeasurable

/-- Integrating over the initial law gives the expectation of the closed execution. -/
theorem lintegral_runExpectation (handler : PFunctor.KernelHandler P S)
    (program : PFunctor.FreeM P α) (post : α → S → ENNReal)
    (hpost : Measurable fun out : α × S ↦ post out.1 out.2) (initial : Measure S) :
    (∫⁻ state, runExpectation handler program post state ∂initial) =
      ∫⁻ out, post out.1 out.2 ∂initial.bind (PFunctor.FreeM.runKernel handler program) :=
  (Measure.lintegral_bind (PFunctor.FreeM.runKernel handler program).aemeasurable
    hpost.aemeasurable).symm

/-- An indicator reward is exactly the event's unconditional output mass. -/
theorem runExpectation_indicator (handler : PFunctor.KernelHandler P S)
    (program : PFunctor.FreeM P α) (event : Set (α × S)) (hevent : MeasurableSet event)
    (state : S) :
    runExpectation handler program (fun value state ↦ event.indicator 1 (value, state)) state =
      PFunctor.FreeM.runKernel handler program state event :=
  lintegral_indicator_one hevent

/-- The same indicator interpretation holds after sampling the fixed initial state law. -/
theorem lintegral_runExpectation_indicator (handler : PFunctor.KernelHandler P S)
    (program : PFunctor.FreeM P α) (event : Set (α × S)) (hevent : MeasurableSet event)
    (initial : Measure S) :
    (∫⁻ state, runExpectation handler program
      (fun value state ↦ event.indicator 1 (value, state)) state ∂initial) =
      initial.bind (PFunctor.FreeM.runKernel handler program) event := by
  rw [lintegral_runExpectation handler program _ (measurable_const.indicator hevent)]
  exact lintegral_indicator_one hevent

/-- A constant reward is multiplied by the execution mass, including for lossy handlers. -/
theorem runExpectation_const (handler : PFunctor.KernelHandler P S)
    (program : PFunctor.FreeM P α) (reward : ENNReal) (state : S) :
    runExpectation handler program (fun _ _ ↦ reward) state =
      reward * PFunctor.FreeM.runKernel handler program state Set.univ :=
  lintegral_const reward

/-- Mass-one primitive operations preserve total mass through every well-founded free program. -/
theorem runKernel_mass_one (handler : PFunctor.KernelHandler P S)
    (hmass : ∀ a state, handler a state Set.univ = 1) (program : PFunctor.FreeM P α)
    (state : S) : PFunctor.FreeM.runKernel handler program state Set.univ = 1 := by
  induction program generalizing state with
  | pure value => simp
  | lift_bind a next ih =>
      rw [← PFunctor.FreeM.liftBind_eq, PFunctor.FreeM.runKernel_liftBind,
        Measure.bind_apply MeasurableSet.univ
          (PFunctor.FreeM.measurable_runKernel_continuation handler next).aemeasurable]
      simp_rw [ih]
      simpa only [lintegral_one] using hmass a state

/-- Normalized primitive operations yield a Markov kernel for the entire program. -/
theorem runKernel_isMarkov (handler : PFunctor.KernelHandler P S)
    (hmass : ∀ a state, handler a state Set.univ = 1) (program : PFunctor.FreeM P α) :
    IsMarkovKernel (PFunctor.FreeM.runKernel handler program) :=
  ⟨fun state ↦ ⟨runKernel_mass_one handler hmass program state⟩⟩

/-- A normalized initial law and normalized operations give a normalized closed experiment. -/
theorem closed_mass_one (handler : PFunctor.KernelHandler P S)
    (hmass : ∀ a state, handler a state Set.univ = 1) (program : PFunctor.FreeM P α)
    (initial : Measure S) [IsProbabilityMeasure initial] :
    initial.bind (PFunctor.FreeM.runKernel handler program) Set.univ = 1 := by
  rw [Measure.bind_apply MeasurableSet.univ
    (PFunctor.FreeM.runKernel handler program).aemeasurable]
  simp_rw [runKernel_mass_one handler hmass program]
  simp

end ProtocolProof
