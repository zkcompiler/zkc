module

public import VCVio.ProgramLogic.Relational.KernelHandler

/-!
# Installation of fixed observations

`PFunctor.KernelHandler.CouplingContract` supplies per-operation joint kernels, exact
marginals, and a measurable state invariant. Its `bind_state_laws` theorem constructs the
coupling of complete adaptive executions from an explicit coupling of their initial laws.
The transports here observe those complete laws directly through measurable events or
nonnegative observations. Private states and final results can be uncountable.

The left handler is the actual execution and the right handler is the mathematical model.
Upper bounds require an actual-to-model terminal implication. Lower bounds require the
reverse implication. Both use exact marginals of the entire initial and terminal measures,
including any explicitly returned rejection or abort. These inequalities apply to arbitrary
measures. A probability interpretation additionally needs the relevant mass certificates.
In particular, a lower bound is on unconditional accepting mass.

The caller and its dependent operation answers are common to both executions. A
meaning-changing response adapter must establish its own complete answer-and-state law
before this common-interface installation applies. Such an adapter's malformed-input or
failure cases belong in that law and in the fixed terminal observation.
-/

public section

open MeasureTheory PFunctor

universe uA uB uS uT uR

namespace ProtocolProof.Internal.Installation

section Measures

variable {X : Type uS} {Y : Type uT} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}

/-- A coupled pointwise comparison transports expectations with their full marginal mass. -/
theorem coupling_lintegral_le (f : X → ENNReal) (g : Y → ENNReal)
    (hf : Measurable f) (hg : Measurable g)
    (h : ExpectationWP.CouplingPost μ ν (fun x y ↦ f x ≤ g y)) :
    (∫⁻ x, f x ∂μ) ≤ ∫⁻ y, g y ∂ν := by
  obtain ⟨⟨joint, hjoint⟩, hc⟩ := h
  rw [← hjoint.fst_eq, ← hjoint.snd_eq, Measure.fst, Measure.snd,
    lintegral_map hf measurable_fst, lintegral_map hg measurable_snd]
  exact lintegral_mono_ae hc

/-- The reversed comparison transports lower expectations without restricting either law. -/
theorem coupling_lintegral_ge (f : X → ENNReal) (g : Y → ENNReal)
    (hf : Measurable f) (hg : Measurable g)
    (h : ExpectationWP.CouplingPost μ ν (fun x y ↦ g y ≤ f x)) :
    (∫⁻ y, g y ∂ν) ≤ ∫⁻ x, f x ∂μ := by
  obtain ⟨⟨joint, hjoint⟩, hc⟩ := h
  rw [← hjoint.fst_eq, ← hjoint.snd_eq, Measure.fst, Measure.snd,
    lintegral_map hf measurable_fst, lintegral_map hg measurable_snd]
  exact lintegral_mono_ae hc

/-- An implication under an exact coupling bounds the measure of the fixed left event. -/
theorem coupling_event_le (actualEvent : Set X) (modelEvent : Set Y)
    (ha : MeasurableSet actualEvent) (hm : MeasurableSet modelEvent)
    (h : ExpectationWP.CouplingPost μ ν (fun x y ↦ x ∈ actualEvent → y ∈ modelEvent)) :
    μ actualEvent ≤ ν modelEvent := by
  obtain ⟨⟨joint, hjoint⟩, hc⟩ := h
  rw [← hjoint.fst_eq, ← hjoint.snd_eq, Measure.fst, Measure.snd,
    Measure.map_apply measurable_fst ha, Measure.map_apply measurable_snd hm]
  exact measure_mono_ae hc

/-- The reverse event implication gives a lower bound on the entire actual event mass. -/
theorem coupling_event_ge (actualEvent : Set X) (modelEvent : Set Y)
    (ha : MeasurableSet actualEvent) (hm : MeasurableSet modelEvent)
    (h : ExpectationWP.CouplingPost μ ν (fun x y ↦ y ∈ modelEvent → x ∈ actualEvent)) :
    ν modelEvent ≤ μ actualEvent := by
  obtain ⟨⟨joint, hjoint⟩, hc⟩ := h
  rw [← hjoint.fst_eq, ← hjoint.snd_eq, Measure.fst, Measure.snd,
    Measure.map_apply measurable_fst ha, Measure.map_apply measurable_snd hm]
  exact measure_mono_ae hc

end Measures

variable {P : PFunctor.{uA, uB}} {S : Type uS} {T : Type uT}
  [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] [MeasurableSpace T]
  {actual : KernelHandler P S} {model : KernelHandler P T} {R : S → T → Prop}
  (contract : KernelHandler.CouplingContract actual model R)

include contract

/-- Related deterministic initial states give an explicit initial coupling. -/
theorem initial_dirac {s : S} {t : T} (hstate : R s t) :
    ExpectationWP.CouplingPost (Measure.dirac s) (Measure.dirac t) R := by
  refine ⟨Measure.Coupling.dirac s t, ?_⟩
  exact (ae_dirac_iff contract.measurable_relation).2 hstate

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  {α : Type uR} [MeasurableSpace α] {μ : Measure S} {ν : Measure T}

/-- Exact local installation equates the two execution masses from covered initial laws. -/
theorem mass_eq (hinit : ExpectationWP.CouplingPost μ ν R) (program : FreeM P α) :
    (μ.bind (FreeM.runKernel actual program)) Set.univ =
      (ν.bind (FreeM.runKernel model program)) Set.univ := by
  obtain ⟨coupling, _⟩ := contract.bind_state_laws hinit program
    (post := fun _ _ ↦ True) MeasurableSet.univ (fun _ _ _ _ ↦ trivial)
  exact coupling.isCoupling.apply_univ_eq

/-- Local installation and initial coverage transport an upper terminal expectation. -/
theorem lintegral_le
    (hinit : ExpectationWP.CouplingPost μ ν R) (program : FreeM P α)
    (actualObservation : α × S → ENNReal) (modelObservation : α × T → ENNReal)
    (ha : Measurable actualObservation) (hm : Measurable modelObservation)
    (hterminal : ∀ x s t, R s t → actualObservation (x, s) ≤ modelObservation (x, t)) :
    (∫⁻ out, actualObservation out ∂μ.bind (FreeM.runKernel actual program)) ≤
      ∫⁻ out, modelObservation out ∂ν.bind (FreeM.runKernel model program) := by
  exact coupling_lintegral_le actualObservation modelObservation ha hm
    (contract.bind_state_laws hinit program
      (measurableSet_le (ha.comp measurable_fst) (hm.comp measurable_snd)) hterminal)

/-- The lower transport keeps exact initial and terminal marginals, even for lossy kernels. -/
theorem lintegral_ge
    (hinit : ExpectationWP.CouplingPost μ ν R) (program : FreeM P α)
    (actualObservation : α × S → ENNReal) (modelObservation : α × T → ENNReal)
    (ha : Measurable actualObservation) (hm : Measurable modelObservation)
    (hterminal : ∀ x s t, R s t → modelObservation (x, t) ≤ actualObservation (x, s)) :
    (∫⁻ out, modelObservation out ∂ν.bind (FreeM.runKernel model program)) ≤
      ∫⁻ out, actualObservation out ∂μ.bind (FreeM.runKernel actual program) := by
  exact coupling_lintegral_ge actualObservation modelObservation ha hm
    (contract.bind_state_laws hinit program
      (measurableSet_le (hm.comp measurable_snd) (ha.comp measurable_fst)) hterminal)

/-- An actual-to-model terminal implication transports a fixed measurable bad event. -/
theorem event_le
    (hinit : ExpectationWP.CouplingPost μ ν R) (program : FreeM P α)
    (actualEvent : Set (α × S)) (modelEvent : Set (α × T))
    (ha : MeasurableSet actualEvent) (hm : MeasurableSet modelEvent)
    (hterminal : ∀ x s t, R s t → (x, s) ∈ actualEvent → (x, t) ∈ modelEvent) :
    (μ.bind (FreeM.runKernel actual program)) actualEvent ≤
      (ν.bind (FreeM.runKernel model program)) modelEvent := by
  exact coupling_event_le actualEvent modelEvent ha hm
    (contract.bind_state_laws hinit program
      ((ha.preimage measurable_fst).imp (hm.preimage measurable_snd)) hterminal)

/-- A model-to-actual terminal implication transports unconditional accepting mass. -/
theorem event_ge
    (hinit : ExpectationWP.CouplingPost μ ν R) (program : FreeM P α)
    (actualEvent : Set (α × S)) (modelEvent : Set (α × T))
    (ha : MeasurableSet actualEvent) (hm : MeasurableSet modelEvent)
    (hterminal : ∀ x s t, R s t → (x, t) ∈ modelEvent → (x, s) ∈ actualEvent) :
    (ν.bind (FreeM.runKernel model program)) modelEvent ≤
      (μ.bind (FreeM.runKernel actual program)) actualEvent := by
  exact coupling_event_ge actualEvent modelEvent ha hm
    (contract.bind_state_laws hinit program
      ((hm.preimage measurable_snd).imp (ha.preimage measurable_fst)) hterminal)

/-- Close an upper model bound using only local installation and terminal comparison. -/
theorem upper_bound
    (hinit : ExpectationWP.CouplingPost μ ν R) (program : FreeM P α)
    (actualObservation : α × S → ENNReal) (modelObservation : α × T → ENNReal)
    (ha : Measurable actualObservation) (hm : Measurable modelObservation)
    (hterminal : ∀ x s t, R s t → actualObservation (x, s) ≤ modelObservation (x, t))
    {bound : ENNReal}
    (hmodel : (∫⁻ out, modelObservation out ∂ν.bind (FreeM.runKernel model program)) ≤
      bound) :
    (∫⁻ out, actualObservation out ∂μ.bind (FreeM.runKernel actual program)) ≤ bound :=
  (lintegral_le contract hinit program actualObservation modelObservation ha hm hterminal).trans
    hmodel

/-- Close a lower model bound on the unconditioned actual execution. -/
theorem lower_bound
    (hinit : ExpectationWP.CouplingPost μ ν R) (program : FreeM P α)
    (actualObservation : α × S → ENNReal) (modelObservation : α × T → ENNReal)
    (ha : Measurable actualObservation) (hm : Measurable modelObservation)
    (hterminal : ∀ x s t, R s t → modelObservation (x, t) ≤ actualObservation (x, s))
    {bound : ENNReal}
    (hmodel : bound ≤ ∫⁻ out, modelObservation out ∂ν.bind (FreeM.runKernel model program)) :
    bound ≤ ∫⁻ out, actualObservation out ∂μ.bind (FreeM.runKernel actual program) :=
  hmodel.trans (lintegral_ge contract hinit program actualObservation modelObservation ha hm
    hterminal)

/-- Close a fixed bad-event upper bound from its mathematical-model bound. -/
theorem event_upper_bound
    (hinit : ExpectationWP.CouplingPost μ ν R) (program : FreeM P α)
    (actualEvent : Set (α × S)) (modelEvent : Set (α × T))
    (ha : MeasurableSet actualEvent) (hm : MeasurableSet modelEvent)
    (hterminal : ∀ x s t, R s t → (x, s) ∈ actualEvent → (x, t) ∈ modelEvent)
    {bound : ENNReal} (hmodel : (ν.bind (FreeM.runKernel model program)) modelEvent ≤ bound) :
    (μ.bind (FreeM.runKernel actual program)) actualEvent ≤ bound :=
  (event_le contract hinit program actualEvent modelEvent ha hm hterminal).trans hmodel

/-- Close a fixed accepting-event lower bound with complete initial-law coverage. -/
theorem event_lower_bound
    (hinit : ExpectationWP.CouplingPost μ ν R) (program : FreeM P α)
    (actualEvent : Set (α × S)) (modelEvent : Set (α × T))
    (ha : MeasurableSet actualEvent) (hm : MeasurableSet modelEvent)
    (hterminal : ∀ x s t, R s t → (x, t) ∈ modelEvent → (x, s) ∈ actualEvent)
    {bound : ENNReal} (hmodel : bound ≤ (ν.bind (FreeM.runKernel model program)) modelEvent) :
    bound ≤ (μ.bind (FreeM.runKernel actual program)) actualEvent :=
  hmodel.trans (event_ge contract hinit program actualEvent modelEvent ha hm hterminal)

/-- Components implemented by arbitrary free programs inherit the upstream local contract.
The initial coupling is still explicit when a caller uses the installed components. -/
theorem freeHandler_coupling
    {Q : PFunctor.{uA, uB}} [∀ a, MeasurableSpace (Q.B a)]
    [∀ a, Countable (Q.B a)] [∀ a, MeasurableSingletonClass (Q.B a)]
    (implementation : (a : Q.A) → FreeM P (Q.B a))
    (hinit : ExpectationWP.CouplingPost μ ν R) (program : FreeM Q α)
    {post : (α × S) → (α × T) → Prop}
    (hpost : MeasurableSet {out : (α × S) × (α × T) | post out.1 out.2})
    (hterminal : ∀ x s t, R s t → post (x, s) (x, t)) :
    ExpectationWP.CouplingPost
      (μ.bind (FreeM.runKernel (fun a ↦ FreeM.runKernel actual (implementation a)) program))
      (ν.bind (FreeM.runKernel (fun a ↦ FreeM.runKernel model (implementation a)) program))
      post :=
  (contract.freeHandler implementation).bind_state_laws hinit program hpost hterminal

end ProtocolProof.Internal.Installation
