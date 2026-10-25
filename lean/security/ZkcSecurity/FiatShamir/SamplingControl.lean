module

public import ZkcSecurity.FiatShamir.SampledCompiled

@[expose] public section

/-! Probability and runtime rules for private sampling controls. These rules
use the existing Domain runtime and HonestSampling experiment; no source root,
formula, input policy, or generated assembly is selected here. -/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.SamplingControl
open OracleComp OracleSpec ZkcSecurity.FiatShamir
open Zkc.Source Zkc.Construction

/-- A continuation can use arbitrary public queries after the private draw;
its conditional unsuccessful mass, not just its pointwise return, is fixed. -/
theorem failure_after_private {E A F : Type} {Raw : E → Type}
    [DecidableEq E] [∀ event, SampleableType (Raw event)]
    [SampleableType F] [Fintype F] [DecidableEq F]
    (bad : F) (next : F → OracleComp (HonestSampling.Spec Raw) A)
    (success : A → Prop)
    (conditional : ∀ value cache,
      Pr{let observed ← (simulateQ (TranscriptOracle.Spec Raw).romImpl (next value)).run cache}[¬ success observed.1] = if value = bad then 1 else 0) :
    HonestSampling.failure (do
      let value ← (liftM ($ᵗ F) : OracleComp (HonestSampling.Spec Raw) F)
      next value) success = 1 / (Fintype.card F : ENNReal) := by
  classical
  rw [HonestSampling.failure_eq_unsuccessful]
  unfold HonestSampling.run
  simp only [simulateQ_bind, StateT.run_bind, HonestSampling.private_preserves_cache,
    map_bind, bind_map_left]
  have law := prEvent_bind_congr_of_support ($ᵗ F)
    (fun value => do
      let observed ← (simulateQ (TranscriptOracle.Spec Raw).romImpl (next value)).run ∅
      pure (¬ success observed.1))
    (fun value => pure (value = bad)) (fun value _ => by
      simpa [bind_pure_comp] using conditional value ∅)
  simp only [bind_pure_comp] at law
  rw [law, SampleableType.prEvent_uniformSample_eq_singleton]
  simp only [one_div]

/-- The existing Domain runtime sequences an authorized private operation
without changing its state or adding a public observation. This equation is
usable with any actual generated continuation and any explicit service state. -/
theorem run_local_uniform {carriers : Structured.Carriers} {S A : Type}
    [∀ event : Domain.Event carriers, SampleableType (Domain.Raw event)]
    (context : Context) (producer validator : List ServicePort)
    (mode : Domain.Mode) (port : ServicePort) (origin : Origin)
    (oracle : Domain.Oracle (OracleComp (SampledCompiled.Spec carriers)) carriers S)
    (next : Domain.Raw (.challenge origin : Domain.Event carriers) →
      PIR.Process (Domain.effects carriers) A)
    (initial : Domain.RuntimeState carriers S)
    (admitted : SampledCompiled.allowed context producer validator mode port origin = true) :
    Domain.run mode oracle (.call (.localService port origin) next) initial
      (SampledCompiled.services context producer validator) = (do
        let value ← (liftM ($ᵗ (Domain.Raw (.challenge origin : Domain.Event carriers))) :
          OracleComp (SampledCompiled.Spec carriers) _)
        Domain.run mode oracle (next value) initial (SampledCompiled.services context producer validator)) := by
  simp [Domain.run, PIR.Process.runM, Domain.handler, SampledCompiled.services,
    SampledCompiled.privateServices, admitted, PIR.Execution.followM]

#print axioms failure_after_private
#print axioms run_local_uniform
end ZkcSecurity.FiatShamir.SamplingControl
