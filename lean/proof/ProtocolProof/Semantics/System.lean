module

public import ProtocolProof.Semantics.Experiment
public import ProtocolProof.Internal.Process
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# One complete normalized interpretation of Process

Primitive kernels return a complete Execution. The internal interpreter adds the reached
state and ordered event prefix to its state, and short-circuits every stopped reply.
The only probability evaluator is the upstream FreeM kernel interpreter.
-/

public section
open PIR MeasureTheory ProbabilityTheory PFunctor

namespace ProtocolProof

variable (E : Type) (I : Signature) (S L : Type)
  [∀ op, MeasurableSpace (I.Reply op)] [MeasurableSpace S] [MeasurableSpace L]

/-- Fixed normalized primitive meanings and a whole initial state law. -/
structure System where
  operations : E → (op : I.Op) → Kernel S (Execution S L (I.Reply op))
  initial : E → Measure S
  operation_mass : ∀ environment operation state,
    operations environment operation state Set.univ = 1
  initial_probability : ∀ environment, IsProbabilityMeasure (initial environment)

variable {E I S L}

namespace System
variable (system : System E I S L)

/-- Primitive calls retain the current ordered prefix and append all newly reached events. -/
@[expose] noncomputable def accumulatedOperations (environment : E) :
    KernelHandler (Internal.effects I) (S × List L) := fun operation ↦
  let service := (system.operations environment operation).comap Prod.fst measurable_fst
  (Kernel.id ×ₖ service).map fun out ↦
    (out.2.outcome, (out.2.state, out.1.2 ++ out.2.events))

private theorem measurable_accumulate (operation : I.Op) :
    Measurable (fun out : (S × List L) × Execution S L (I.Reply operation) ↦
      (out.2.outcome, (out.2.state, out.1.2 ++ out.2.events))) :=
  (Execution.measurable_outcome.comp measurable_snd).prodMk
    ((Execution.measurable_state.comp measurable_snd).prodMk
      (List.measurable_append.comp
        (measurable_fst.snd.prodMk (Execution.measurable_events.comp measurable_snd))))

/-- This equation includes the stopped operation's successor state and emitted events. -/
theorem accumulatedOperations_apply (environment : E) (operation : I.Op)
    (current : S × List L) :
    system.accumulatedOperations environment operation current =
      (system.operations environment operation current.1).map
        (fun result ↦ (result.outcome, (result.state, current.2 ++ result.events))) := by
  let : IsMarkovKernel (system.operations environment operation) :=
    ⟨fun state ↦ ⟨system.operation_mass environment operation state⟩⟩
  unfold accumulatedOperations
  rw [Kernel.map_apply _ (measurable_accumulate operation), Kernel.prod_apply,
    Kernel.id_apply, Kernel.comap_apply, Measure.dirac_prod,
    Measure.map_map (measurable_accumulate operation) measurable_prodMk_left]
  rfl

/-- The full initial distribution is retained and every execution starts with an empty log. -/
@[expose] noncomputable def initialWithEvents (environment : E) : Measure (S × List L) :=
  (system.initial environment).map (fun state ↦ (state, []))

end System

namespace Internal

/-- The checked backend receives the unique failure-aware interpretation. -/
@[expose] noncomputable def backendSystem (system : ProtocolProof.System E I S L) :
    ProtocolProof.Internal.System E (effects I) (S × List L) where
  operations := system.accumulatedOperations
  initial := system.initialWithEvents
  operation_mass environment operation current := by
    have hmap : Measurable (fun result : Execution S L (I.Reply operation) ↦
        (result.outcome, (result.state, current.2 ++ result.events))) :=
      Execution.measurable_outcome.prodMk (Execution.measurable_state.prodMk
        (List.measurable_append.comp (measurable_const.prodMk Execution.measurable_events)))
    rw [System.accumulatedOperations_apply, Measure.map_apply hmap MeasurableSet.univ]
    exact system.operation_mass environment operation current.1
  initial_probability environment := by
    have := system.initial_probability environment
    have hmap : Measurable (fun state : S ↦ (state, ([] : List L))) :=
      measurable_id.prodMk measurable_const
    exact ⟨by rw [System.initialWithEvents, Measure.map_apply hmap MeasurableSet.univ]; simp⟩

end Internal

namespace System
variable (system : System E I S L)

variable [∀ op, Countable (I.Reply op)] [∀ op, MeasurableSingletonClass (I.Reply op)]
  {A : Type} [MeasurableSpace A]

/-- Complete execution from an already reached state and event prefix. -/
@[expose] noncomputable def runFrom (environment : E) (program : Process I A) :
    Kernel (S × List L) (Execution S L A) :=
  (FreeM.runKernel (system.accumulatedOperations environment) (Internal.encode program)).map
    Execution.measurableEquiv.symm

/-- Public execution starts with an empty event prefix. -/
@[expose] noncomputable def run (environment : E) (program : Process I A) :
    Kernel S (Execution S L A) :=
  (system.runFrom environment program).comap (fun state ↦ (state, []))
    (measurable_id.prodMk measurable_const)

/-- The fixed whole experiment; observing records is a measurable bijection, not conditioning. -/
@[expose] noncomputable def experiment (client : E → Process I A) :
    Experiment E (Execution S L A) :=
  ((Internal.backendSystem system).experiment (fun environment ↦ Internal.encode (client environment))).observe
    ⟨Execution.measurableEquiv.symm, Execution.measurableEquiv.symm.measurable⟩

theorem runFrom_apply (environment : E) (program : Process I A) (current : S × List L) :
    system.runFrom environment program current =
      (FreeM.runKernel (system.accumulatedOperations environment) (Internal.encode program)
        current).map Execution.measurableEquiv.symm :=
  Kernel.map_apply _ Execution.measurableEquiv.symm.measurable _

theorem experiment_run (client : E → Process I A) (environment : E) :
    (system.experiment client).run environment =
      (system.initial environment).bind (system.run environment (client environment)) := by
  change ((system.initialWithEvents environment).bind
    (FreeM.runKernel (system.accumulatedOperations environment)
      (Internal.encode (client environment)))).map Execution.measurableEquiv.symm = _
  have hmap : Measurable (fun state : S ↦ (state, ([] : List L))) :=
    measurable_id.prodMk measurable_const
  rw [Measure.map_bind (FreeM.runKernel _ _).aemeasurable
    Execution.measurableEquiv.symm.measurable.aemeasurable, initialWithEvents]
  have hcont : Measurable (fun current : S × List L ↦
      (FreeM.runKernel (system.accumulatedOperations environment)
        (Internal.encode (client environment)) current).map Execution.measurableEquiv.symm) :=
    (Measure.measurable_map _ Execution.measurableEquiv.symm.measurable).comp
      (FreeM.runKernel _ _).measurable
  rw [Measure.bind_map hmap.aemeasurable hcont.aemeasurable]
  congr 1
  funext state
  exact (runFrom_apply system environment _ (state, [])).symm

end System
end ProtocolProof

namespace ProtocolProof.System
open PIR MeasureTheory ProbabilityTheory PFunctor
variable {E : Type} {I : Signature} {S L A : Type}
  [∀ op, MeasurableSpace (I.Reply op)]
  [∀ op, Countable (I.Reply op)] [∀ op, MeasurableSingletonClass (I.Reply op)]
  [MeasurableSpace S] [MeasurableSpace L] [MeasurableSpace A]
  (system : System E I S L)

@[simp] theorem runFrom_done (environment : E) (value : A) (current : S × List L) :
    system.runFrom environment (.done value) current =
      Measure.dirac ⟨.returned value, current.1, current.2⟩ := by
  rw [runFrom_apply]
  exact (congrArg (Measure.map Execution.measurableEquiv.symm)
    (FreeM.runKernel_pure (P := Internal.effects I)
      (system.accumulatedOperations environment) (Outcome.returned value) current)).trans
    (Measure.map_dirac' Execution.measurableEquiv.symm.measurable _)

@[simp] theorem runFrom_halt (environment : E) (reason : Stop) (current : S × List L) :
    system.runFrom environment (.halt reason : Process I A) current =
      Measure.dirac ⟨.stopped reason, current.1, current.2⟩ := by
  rw [runFrom_apply]
  exact (congrArg (Measure.map Execution.measurableEquiv.symm)
    (FreeM.runKernel_pure (P := Internal.effects I)
      (system.accumulatedOperations environment) (Outcome.stopped (A := A) reason) current)).trans
    (Measure.map_dirac' Execution.measurableEquiv.symm.measurable _)

/-- The continuation kernel short-circuits failed replies without losing the reached record. -/
theorem runFrom_call (environment : E) (operation : I.Op)
    (next : I.Reply operation → Process I A) (current : S × List L) :
    system.runFrom environment (.call operation next) current =
      (system.accumulatedOperations environment operation current).bind (fun out ↦
        match out.1 with
        | .returned value => system.runFrom environment (next value) out.2
        | .stopped reason => Measure.dirac ⟨.stopped reason, out.2.1, out.2.2⟩) := by
  rw [runFrom_apply, Internal.encode, FreeM.runKernel_liftBind]
  have hcont : Measurable (fun out : Outcome (I.Reply operation) × (S × List L) ↦
      FreeM.runKernel (system.accumulatedOperations environment)
        (match out.1 with
          | .returned value => Internal.encode (next value)
          | .stopped reason => FreeM.pure (.stopped reason)) out.2) :=
    FreeM.measurable_runKernel_continuation (P := Internal.effects I)
      (system.accumulatedOperations environment)
      (fun answer : Outcome (I.Reply operation) ↦ match answer with
        | .returned value => Internal.encode (next value)
        | .stopped reason => FreeM.pure (Outcome.stopped (A := A) reason))
  refine (Measure.map_bind (m := system.accumulatedOperations environment operation current)
    hcont.aemeasurable Execution.measurableEquiv.symm.measurable.aemeasurable).trans ?_
  congr 1
  funext out
  cases out with
  | mk outcome reached =>
      cases outcome with
      | returned value => exact (runFrom_apply system environment _ reached).symm
      | stopped reason =>
          exact (congrArg (Measure.map Execution.measurableEquiv.symm)
            (FreeM.runKernel_pure (P := Internal.effects I)
              (system.accumulatedOperations environment) (Outcome.stopped (A := A) reason)
              reached)).trans (Measure.map_dirac' Execution.measurableEquiv.symm.measurable _)

/-- Normalization follows from the backend, and includes process stops and handler stops. -/
theorem runFrom_mass_one (environment : E) (program : Process I A) (current : S × List L) :
    system.runFrom environment program current Set.univ = 1 := by
  rw [runFrom_apply, Measure.map_apply Execution.measurableEquiv.symm.measurable
    MeasurableSet.univ]
  exact Internal.runKernel_mass_one _ ((Internal.backendSystem system).operation_mass environment) _ current

theorem run_mass_one (environment : E) (program : Process I A) (state : S) :
    system.run environment program state Set.univ = 1 :=
  system.runFrom_mass_one environment program (state, [])

/-- Every deterministic handler agrees with the full probability interpretation under Dirac. -/
theorem runFrom_eq_dirac (environment : E) (handler : Handler I S L)
    (hlocal : ∀ operation state, system.operations environment operation state =
      Measure.dirac (handler operation state))
    (program : Process I A) (state : S) (prior : List L) :
    system.runFrom environment program (state, prior) =
      Measure.dirac ⟨(program.run handler state).outcome, (program.run handler state).state,
        prior ++ (program.run handler state).events⟩ := by
  induction program generalizing state prior with
  | done value => simpa only [Process.run, List.append_nil] using
      runFrom_done system environment value (state, prior)
  | halt reason =>
      simpa only [Process.run, List.append_nil] using
        runFrom_halt system environment (A := A) reason (state, prior)
  | call operation next ih =>
      have hmap : Measurable (fun result : Execution S L (I.Reply operation) ↦
          (result.outcome, (result.state, prior ++ result.events))) :=
        Execution.measurable_outcome.prodMk (Execution.measurable_state.prodMk
          (List.measurable_append.comp (measurable_const.prodMk Execution.measurable_events)))
      rw [runFrom_call, accumulatedOperations_apply, hlocal, Measure.map_dirac' hmap]
      rw [Measure.dirac_bind (by
        apply measurable_from_prod_countable_right
        intro outcome
        cases outcome with
        | returned value => exact (system.runFrom environment (next value)).measurable
        | stopped reason =>
            exact Measure.measurable_dirac.comp
              (Execution.measurableEquiv.symm.measurable.comp
                (measurable_const.prodMk measurable_id))) ]
      cases hr : handler operation state with
      | mk outcome reached emitted =>
          cases outcome with
          | stopped reason => simp only [Process.run, hr, Execution.follow]
          | returned value =>
              dsimp only
              rw [ih]
              simp only [Process.run, hr, Execution.follow, List.append_assoc]

/-- The public state-to-record kernel agrees with the canonical deterministic interpreter. -/
theorem run_eq_dirac (environment : E) (handler : Handler I S L)
    (hlocal : ∀ operation state, system.operations environment operation state =
      Measure.dirac (handler operation state)) (program : Process I A) (state : S) :
    system.run environment program state = Measure.dirac (program.run handler state) := by
  change system.runFrom environment program (state, []) = _
  rw [runFrom_eq_dirac system environment handler hlocal]
  rfl

end ProtocolProof.System
