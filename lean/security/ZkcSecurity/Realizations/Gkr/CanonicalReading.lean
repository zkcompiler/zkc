module

public import ZkcSecurity.Realizations.Gkr.OccurrenceRootRouting
public import ZkcSecurity.Realizations.Gkr.CanonicalSource
public import ZkcSecurity.Realizations.Gkr.Budget
public import ZkcSecurity.FiatShamir.OccurrenceReading

@[expose] public section

/-! The full nominal current-source presentation and its universal rejection
and query budget. The same complete source process is used by installation
and honest execution; scalar projection is only a proof transport. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalReading
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Obligations Zkc.Transcript
open ZkcExamples.Structured ZkcExamples.Construction.GkrSourceRouting
open ZkcSecurity.FiatShamir ZkcSecurity.Obligations
open OracleComp OracleSpec
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev ValuesResult (F G : Type) := Values (Component (assignment F G)) [.boolean]
abbrev Result (F G : Type) := ValuesResult F G × Original.State (uniformCarriers F G)

def inputs (runtime : Source.Invocation F) :=
  GkrSourceAdmission.inputs (G := G) runtime.inputs runtime.outputs runtime.add runtime.mul
    runtime.layers runtime.selector runtime.width runtime.handle

def occurrence (runtime : Source.Invocation F) :=
  Occurrence.participant (ringModel F G) GkrSourceViews.program 1 (inputs (G := G) runtime)

def routed (runtime : Source.Invocation F) :
    Uniform.OccurrenceSourceProcess.Routed (routing runtime.handle) [] [] (occurrence (G := G) runtime) :=
  OccurrenceRouting.participant_routed runtime.inputs runtime.outputs runtime.add runtime.mul
    runtime.layers runtime.selector runtime.width runtime.handle

def source (runtime : Source.Invocation F) (history : Domain.History (uniformCarriers F G)) :=
  Original.participant (ringModel F G) GkrSourceViews.program (routing runtime.handle) 1
    (inputs (G := G) runtime) ⟨[], history⟩

def presented (runtime : Source.Invocation F) (history : Domain.History (uniformCarriers F G)) :=
  OccurrenceReading.presentation (routed (G := G) runtime) history

def acceptance (result : Result F G) : Option Bool := result.1.get .here

/-- Exact histories and empty final frames, with all stops and typed replies. -/
theorem reading (runtime : Source.Invocation F) (history : Domain.History (uniformCarriers F G)) :
    DomainReduction.Bridge (OccurrenceReading.interface (F := F) (G := G))
      (OccurrenceReading.Post []) history (source runtime history) (presented runtime history) := by
  have snapshot : { routing runtime.handle with snapshot := GkrSourceViews.program.snapshot } =
      routing runtime.handle := by kernel_rfl
  unfold source Original.participant
  rw [snapshot]
  exact OccurrenceReading.reading rfl _ rfl (routed runtime) history

/-- The established all-input source theorem is a pure projection of this
complete process. No occurrence is erased in the actual nominal execution. -/
theorem projection (runtime : Source.Invocation F) :
    (((occurrence (G := G) runtime).interpret Occurrence.erase).interpret CommonAdapter.project).bind
      (fun values => .done (values.get .here)) = Source.body runtime := by
  unfold occurrence
  rw [Occurrence.participant_erase]
  conv_rhs =>
    unfold Source.body Source.actualVerifier GkrSourceAdmission.participant
    rw [Program.participant_eq_participantOn, PIR.Process.interpret_bind]
  rfl

variable [Fintype F] [SampleableType F]
attribute [local instance] OccurrenceReading.rawSampleable
attribute [local irreducible] Source.body Source.actualVerifier occurrence routed source presented

def price : ENNReal := 4 / (Fintype.card F : ENNReal)

/-- Universal fixed-target rejection of the actual nominal presentation. -/
def rejected
    (statement : (Canonical.subject (ringModel F G)).validatorArtifacts.Statement (ringModel F G))
    (handle : Nat) (wrong : (Canonical.validatorSubject (ringModel F G)).FalseStatement statement)
    (history : Domain.History (uniformCarriers F G)) :
    Derivation (OccurrenceReading.interface (F := F) (G := G))
      (boundedEscape (fun _ _ => price (F := F)))
      (fun _ result => acceptance result ≠ some true) history
      (presented (Canonical.invocation (ringModel F G) statement handle) history) := by
  let runtime := Canonical.invocation (ringModel F G) statement handle
  have base : Derivation (routing handle).context.interface
      (boundedEscape (fun _ _ => price (F := F)))
      (fun _ result => result ≠ some true) [] (Source.body (G := G) runtime) :=
    CanonicalSource.uniformly_rejected (F := F) (G := G)
      statement handle (routing handle).context wrong []
  have scalar := base.charged (boundedEscape_antitone (fun _ _ => price (F := F)))
  rw [← projection (G := G) runtime, Interface.charged_bind] at scalar
  have nominal := OccurrenceReading.charged (F := F) (G := G) (price (F := F))
    (fun values : ValuesResult F G => values.get .here ≠ some true)
    (routed (G := G) runtime) [] history scalar
  exact Classical.choice (Derivation.of_charged _ _ (by
    simpa only [presented, acceptance] using nominal))

omit [SampleableType F] in
/-- Forty is the pathwise maximum of the actual source, including all raw
admission failures. The full nominal history is retained during this transfer. -/
theorem costs (runtime : Source.Invocation F) (history : Domain.History (uniformCarriers F G)) :
    Typed.ChargedCostBound (OccurrenceReading.interface (F := F) (G := G))
      (fun _ _ => price (F := F)) (presented runtime history) history (40 * price (F := F)) := by
  have scalar := Budget.source_cost (G := G) runtime (routing runtime.handle).context
    (price (F := F)) []
  rw [← projection (G := G) runtime] at scalar
  have full := CostComposition.map_iff _ _ _ |>.mp scalar
  simpa only [presented] using
    OccurrenceReading.cost (price (F := F)) _ (routed runtime) [] history full

end ZkcSecurity.Realizations.Gkr.CanonicalReading
