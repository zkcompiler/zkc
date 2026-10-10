import Zkc.Compiler.Checking
import Zkc.Compiler.RegionArtifact
import Zkc.Source.PhaseAdmission

/-! Join source admission with independently checked logical-plan preservation.

The candidate cannot choose its own interaction meaning. The consumer supplies
the resolved interpretation and its summary laws. Instrumentation retains actual
stopped outcomes, residual state and events; a stop never becomes a typed reply.
-/

set_option autoImplicit false

namespace Zkc.Compiler.CheckedPlan

open Source PhaseAdmission

variable {language : Language} [DecidableEq language.Ty]
variable {Γ : List language.Ty} {ty : language.Ty}
variable {source : Program language Γ ty} {candidate : RawProgram language.Ty language.Op}
variable (checked : CheckedPlan source candidate)
variable {Phase : Type} [DecidableEq Phase] {policy : Policy language Phase}
variable {starts allowed : List Phase} (admitted : Admitted policy source starts allowed)
variable {interface : PIR.Signature} (meaning : Interpretation language interface)
variable (interaction : PIR.Interaction interface) (laws : Realizes policy meaning interaction)
variable {S E : Type} (handler : PIR.Handler interface S E)
variable (env : Environment meaning.Value Γ) (phase : interaction.Phase) (state : S)
variable (initial : Covered laws starts phase)

include admitted initial in
theorem calls_permitted :
    ∀ before op, Sum.inl (before, op) ∈
      (checked.plan.run meaning (PIR.ExecutionPath.handler interaction handler)
        env (phase, state)).events → interaction.enabled before op := by
  rw [checked.correct]
  exact PIR.ExecutionPath.calls_permitted interaction handler _ phase state
    (admitted.sound meaning interaction laws env phase initial).1

include admitted initial in
theorem return_permitted (value : meaning.Value ty)
    (returned : (checked.plan.run meaning (PIR.ExecutionPath.handler interaction handler)
      env (phase, state)).outcome = .returned value) :
    Covered laws allowed (checked.plan.run meaning (PIR.ExecutionPath.handler interaction handler)
      env (phase, state)).state.1 := by
  rw [checked.correct] at returned ⊢
  exact PIR.Boundary.actual_return interaction _ handler _ phase state
    (admitted.sound meaning interaction laws env phase initial).2 value returned

/-- Auditing phases preserves the complete underlying execution, even on failure. -/
theorem instrumented_erasure :
    let out := checked.plan.run meaning (PIR.ExecutionPath.handler interaction handler)
      env (phase, state)
    (⟨out.outcome, out.state.2, out.events.filterMap (fun
      | .inl _ => none | .inr event => some event)⟩ : PIR.Execution S E (meaning.Value ty)) =
      checked.plan.run meaning handler env state := by
  simp only [checked.correct]
  refine Eq.trans ?_ (PIR.ExecutionPath.erasure interaction handler (source.denote meaning env) phase state)
  congr 2
  funext event
  cases event <;> rfl

end Zkc.Compiler.CheckedPlan

namespace Zkc.Compiler.RegionArtifact.Checked

open Source PhaseAdmission

variable {language : Language} [DecidableEq language.Ty]
  {request : RegionArtifact.Request language.Ty language.Op}
  {candidate : RegionArtifact.Candidate language.Ty language.Op}
  (checked : RegionArtifact.Checked request candidate)
  {Phase : Type} [DecidableEq Phase] (policy : Policy language Phase)
  (certificate : Certificate Phase) (starts exits allowed : List Phase)
  (accepted : checkRegion policy checked.region certificate starts = some exits)
  (permitted : ∀ phase ∈ exits, phase ∈ allowed)
  {interface : PIR.Signature} (meaning : Interpretation language interface)
  (interaction : PIR.Interaction interface) (laws : Realizes policy meaning interaction)
  (env : Environment meaning.Value (request.context.inputs.map (·.type)))
  (phase : interaction.Phase) (initial : Covered laws starts phase)

include accepted permitted initial in
/-- Phase evidence is checked against the region decoded from the retained
request and candidate. Certificate data does not choose the policy or domain. -/
theorem phase_sound :
    PIR.Conforms interaction (checked.region.denote meaning env) phase ∧
    PIR.Boundary.Returns interaction (fun _ finish => Covered laws allowed finish)
      (checked.region.denote meaning env) phase := by
  have result := checkRegion_sound policy meaning interaction laws checked.region
    certificate starts exits accepted env phase initial
  exact ⟨result.1, PIR.Boundary.returns_mono interaction _ _ _ phase result.2
    (fun _ _ h => covered_mono laws permitted h)⟩

variable {S E : Type} (handler : PIR.Handler interface S E) (state : S)
  (plan : Region language (request.context.inputs.map (·.type)) request.context.resultType)
  (decoded : candidate.body.elaborate _ _ = .ok plan)

include accepted initial decoded in
theorem calls_permitted :
    ∀ before op, Sum.inl (before, op) ∈
      ((plan.denote meaning env).run (PIR.ExecutionPath.handler interaction handler)
        (phase, state)).events → interaction.enabled before op := by
  rw [checked.correct plan decoded]
  exact PIR.ExecutionPath.calls_permitted interaction handler _ phase state
    (checkRegion_sound policy meaning interaction laws checked.region certificate
      starts exits accepted env phase initial).1

include accepted permitted initial decoded in
theorem return_permitted (value : meaning.Value request.context.resultType)
    (returned : ((plan.denote meaning env).run
      (PIR.ExecutionPath.handler interaction handler) (phase, state)).outcome = .returned value) :
    Covered laws allowed ((plan.denote meaning env).run
      (PIR.ExecutionPath.handler interaction handler) (phase, state)).state.1 := by
  rw [checked.correct plan decoded] at returned ⊢
  exact PIR.Boundary.actual_return interaction _ handler _ phase state
    (checked.phase_sound policy certificate starts exits allowed accepted permitted
      meaning interaction laws env phase initial).2 value returned

end Zkc.Compiler.RegionArtifact.Checked
