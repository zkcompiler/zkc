module

public import ZkcSecurity.Bindings.Source.PublicProperties
public import ZkcSecurity.Bindings.Transcript.RootConnectionReading

@[expose] public section

/-! Rejection and cost installation on the same root-owned public presentation.
The full nominal source output and state are retained. These adapters evaluate
only the actual source input ABI; they accept no whole-source equation.
-/
set_option autoImplicit false
namespace ZkcSecurity.Source.RootPublic
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot
open ZkcSecurity.FiatShamir Zkc.Transcript Zkc.Obligations

variable {program : Program} {routing : Original.Routing} {role : Nat} {artifact : Participant}
  (root : RootCertificate program routing role artifact) (mode : routing.mode = .validator)
  (model : DomainModel) (physical : Domain.Environment model.toCarriers)
  (values : Values (Component model.Value) program.payload.entry.inputs)
  (read : root.inputs.abi.read physical program.payload.entry.inputs = some values)
  (price : ENNReal)
include mode read

variable [samples : ∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]

noncomputable def rejects
    (post : Values (Component model.Value) program.payload.entry.outputs → Prop)
    (history : List (PublicProperties.Event model.toCarriers))
    (source : Derivation PublicProperties.interface (PublicProperties.escape price) (fun _ => post) history
      (Occurrence.participant model program role values)) :
    Derivation NominalDomain.interface (ZkcSecurity.Obligations.boundedEscape (fun _ _ => price))
      (fun _ result => post result.1) (root.inputs.initial physical).history
      (RootConnection.publicPresentation root model physical) := by
  simp only [RootConnection.publicPresentation, read]
  exact PublicProperties.install { routing with snapshot := program.snapshot } mode price post _ history source _

omit samples in
theorem cost (history : List (PublicProperties.Event model.toCarriers)) (budget : ENNReal)
    (source : Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (Occurrence.participant model program role values) history budget) :
    Typed.ChargedCostBound NominalDomain.interface (fun _ _ => price)
      (RootConnection.publicPresentation root model physical) (root.inputs.initial physical).history budget := by
  simp only [RootConnection.publicPresentation, read]
  exact PublicProperties.install_cost { routing with snapshot := program.snapshot } mode price _ history budget source _

omit mode read samples in
/-- Successful ABI decoding recovers the caller's entire incoming transcript.
This depends on the public ABI, independently of the root's body certificate. -/
theorem input_history (data : Domain.Environment model.toCarriers)
    (initial : Domain.History model.toCarriers) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (found : root.inputs.abi.read (Domain.inputFrame routing.context data initial)
      program.payload.entry.inputs = some values) :
    (root.inputs.initial (Domain.inputFrame routing.context data initial)).history = initial := by
  exact ConnectionInputs.inputHistory_inputFrame routing.context replacement profile artifact.inputs data initial
    ((Original.InputABI.read_iff _ _ _ _).mp found).1

omit read in
noncomputable def rejects_inputFrame (data : Domain.Environment model.toCarriers)
    (initial : Domain.History model.toCarriers) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (found : root.inputs.abi.read (Domain.inputFrame routing.context data initial)
      program.payload.entry.inputs = some values)
    (post : Values (Component model.Value) program.payload.entry.outputs → Prop)
    (history : List (PublicProperties.Event model.toCarriers))
    (source : Derivation PublicProperties.interface (PublicProperties.escape price) (fun _ => post) history
      (Occurrence.participant model program role values)) :
    Derivation NominalDomain.interface (ZkcSecurity.Obligations.boundedEscape (fun _ _ => price))
      (fun _ result => post result.1) initial
      (RootConnection.publicPresentation root model (Domain.inputFrame routing.context data initial)) := by
  have installed := rejects root mode model _ values found price post history source
  rw [input_history root model values data initial replacement profile found] at installed
  exact installed

omit read samples in
theorem cost_inputFrame (data : Domain.Environment model.toCarriers)
    (initial : Domain.History model.toCarriers) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (found : root.inputs.abi.read (Domain.inputFrame routing.context data initial)
      program.payload.entry.inputs = some values)
    (history : List (PublicProperties.Event model.toCarriers)) (budget : ENNReal)
    (source : Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (Occurrence.participant model program role values) history budget) :
    Typed.ChargedCostBound NominalDomain.interface (fun _ _ => price)
      (RootConnection.publicPresentation root model (Domain.inputFrame routing.context data initial)) initial budget := by
  have installed := cost root mode model _ values found price history budget source
  rw [input_history root model values data initial replacement profile found] at installed
  exact installed

end ZkcSecurity.Source.RootPublic
