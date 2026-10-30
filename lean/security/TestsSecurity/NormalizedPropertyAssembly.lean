import ZkcSecurityTools.ComponentDerivation
import Zkc.Obligations.NormalizedComponent
import Zkc.Obligations.Assembly
import Tests.StructuredOccurrenceNormalForm

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option smartUnfolding false
set_option trace.zkc.componentAssembly true
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
noncomputable section
namespace TestsSecurity.NormalizedPropertyAssembly
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Transcript Zkc.Obligations
open ZkcSecurity.Obligations
open Tests.StructuredOccurrenceNormalForm

variable (model : DomainModel)

def interaction : PIR.Interaction (occurrenceInterface model) where
  Role := Unit
  Phase := Unit
  owner _ := ()
  enabled _ _ := True
  advance _ _ _ := ()

def stepInputs (index handle : Nat) : Binders model stepPattern.scope :=
  .cons (some true) (.cons (some true) (.cons (some index) (.cons (some handle) .nil)))

def indexFrame (index : Nat) (values : Values (Component model.Value) stateTypes) : Prop :=
  values.get .here = some index

/-- A private residual projection of the actual complete nominal return.
The challenge is arbitrary. The source helper is its admitted body, not an
assumed family equation or an honest-message replacement. -/
theorem step_returns (index handle : Nat) :
    PIR.Boundary.Returns (interaction model) (fun values _ => indexFrame model index values)
      (stepProcess model {} (stepInputs model index handle)) () := by
  have projected :
      PIR.Boundary.Returns (interaction model) (fun values _ => indexFrame model index values)
        (stepProcess model {} (stepInputs model index handle)) () =
        (∀ _ : model.Field "bls12-381.fr", some index = some index) := by kernel_rfl
  rw [projected]
  intro _
  rfl

def step_frame {E P : Type} {Raw : E → Type} [∀ event, SampleableType (Raw event)]
    (absorb : Zkc.Transcript.Interface (occurrenceInterface model) E P Raw)
    (charge : List E → E → ENNReal)
    (index handle : Nat) (history : List E) :
    Derivation absorb (boundedEscape charge) (fun _ => indexFrame model index) history
      (stepProcess model {} (stepInputs model index handle)) :=
  Assembly.preserve (interaction model) () (indexFrame model index)
    (step_returns model index handle) (unrestricted _ _)

/-- Builder selection and normalization transport both consume the same form
and body used by the occurrence/connection fixture. Every output stays in the
result type; only the requested property projects the retained index. -/
def source_frame {E P : Type} {Raw : E → Type} [∀ event, SampleableType (Raw event)]
    (absorb : Zkc.Transcript.Interface (occurrenceInterface model) E P Raw)
    (charge : List E → E → ENNReal)
    (index handle : Nat) (history : List E) :
    Derivation absorb (boundedEscape charge) (fun _ => indexFrame model index) history
      (stepBody.denote
        (meaningAtOn model Occurrence.actions Occurrence.iterations (helpers model) [] {} 0)
        (stepPattern.environment model (stepInputs model index handle)).get) := by
  apply NormalizedComponent.ofOccurrence stepNormalizer stepBody 0 1 stepPattern stepForm
    (by kernel_rfl) (by kernel_rfl)
    (fun other bound different => False.elim (different (by omega)))
    (LawResults.empty model) (noCallees model _) (stepInputs model index handle)
    (LawsHold.empty _ _) (noCallees_hold _ _)
  change Derivation absorb (boundedEscape charge) (fun _ => indexFrame model index) history
    (stepProcess model {} (stepInputs model index handle))
  assemble_component_property [step_frame model absorb charge] unfolding [] repeating []
    reporting "actual nominal source private residual" from (stepForm, ({} : ProtocolContext))

/-- A false source guard is a soundness stop. This is deliberately not a
return/completeness proof, and it consumes no helper or sampling premise. -/
def stopped_source {E P : Type} {Raw : E → Type}
    (absorb : Zkc.Transcript.Interface (occurrenceInterface model) E P Raw)
    (escape : EscapeJudgment E Raw) (context : ProtocolContext)
    (index handle : Nat) (history : List E) :
    Derivation absorb escape (fun _ (_ : Values (Component model.Value) stateTypes) => False) history
      (stepProcess model context
        (.cons (some false) (.cons (some true) (.cons (some index) (.cons (some handle) .nil))))) := by
  change Derivation absorb escape (fun _ (_ : Values (Component model.Value) stateTypes) => False)
    history (.halt .reject)
  assemble_component_property [] unfolding [] repeating []
    reporting "actual source guard rejection" from (stepForm, context)

/-- Arbitrary symbolic source loops require installed body/invariant laws.
The report is generated from the actual form, rather than a separate checklist.
This refusal is not a proof of the deliberately impossible property. -/
example {E P : Type} {Raw : E → Type} [∀ event, SampleableType (Raw event)]
    (_absorb : Zkc.Transcript.Interface (occurrenceInterface model) E P Raw)
    (_charge : List E → E → ENNReal) (_binders : Binders model rootPattern.scope)
    (_history : List E) : True := by
  fail_if_success
    have unsupported : Derivation _absorb (boundedEscape _charge)
        (fun _ (_ : Values (Component model.Value) stateTypes) => False) _history
        (rootForm.denoteOn model Occurrence.actions (helpers model) (LawResults.empty model) {}
          (runsAtOn model Occurrence.actions Occurrence.iterations (helpers model)
            (protocols model) {} 0) (noCallees model _) _binders) := by
      solve | assemble_component_property [] unfolding [] repeating [] finishing assumption
        reporting "actual nested source requires loop laws" from (rootForm, ({} : ProtocolContext), _binders)
  trivial

#print axioms source_frame
#print axioms stopped_source
#print axioms NormalizedComponent.ofOccurrence
#print axioms NormalizedComponent.ofOccurrenceState
end TestsSecurity.NormalizedPropertyAssembly
