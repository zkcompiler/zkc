module

public import ZkcSecurity.FiatShamir.RootConnectionEndpoint
public import ZkcSecurity.FiatShamir.OriginalClaims
public import Zkc.Construction.DomainPublicBinding

@[expose] public section

/-! Package a complete finite root into the existing source security consumer.
The selected source output, encoded statement and initial history are assembled
from their existing owners. Property derivations, costs and probability laws
remain separate obligations of the existing claims modules.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.RootConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ConnectionInputs ConnectionRoot

attribute [local implicit_reducible] CheckedProtocol.signature


variable {program : Program} {routing : Original.Routing} {role : Nat} {artifact : Participant}

/-- At a caller's initial history, sorted rows use their exact supplied
transcript. Malformed rows have no effects and hence read at that same history
without fabricating a decoded source tuple or a successful return. -/
noncomputable def publicBridge_inputFrame (root : RootCertificate program routing role artifact)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = []) (model : DomainModel)
    (data : Domain.Environment model.toCarriers) (initial : Domain.History model.toCarriers) :
    FiatShamir.Original.Bridge NominalDomain.interface SourceReading.Post initial
      (root.source model (Domain.inputFrame routing.context data initial))
      (Domain.participant model program routing.context artifact (Domain.inputFrame routing.context data initial))
      (publicPresentation root model (Domain.inputFrame routing.context data initial))
      (Original.CompleteReturns program.payload.entry.signature routing.context role artifact)
      (InputFrames root.inputs.abi program.payload.entry.inputs (Domain.inputFrame routing.context data initial)) := by
  let physical := Domain.inputFrame routing.context data initial
  refine ⟨?_, root.simulation model physical⟩
  by_cases sorted : Domain.sortsMatch artifact.inputs physical = true
  · have same : (root.inputs.initial physical).history = initial :=
      inputHistory_inputFrame routing.context replacement profile artifact.inputs data initial sorted
    have reading := (publicBridge root replacement profile noLocal model physical).sourceReading
    rw [same] at reading
    exact reading
  · have malformed : Domain.sortsMatch artifact.inputs physical = false := Bool.eq_false_iff.mpr sorted
    have refused : root.inputs.abi.read physical program.payload.entry.inputs = none := by
      simp only [Original.InputABI.read, InputLayout.abi, malformed, Bool.false_eq_true, ↓reduceIte]
    dsimp only [physical] at refused
    simp only [RootCertificate.source, Original.participantFromABI, publicPresentation, refused]
    exact .halt initial .refused

/-- Fully automatic source installation in the existing request-owned claims
consumer. A family supplies its finite root; no source equation, source reading,
observation coherence, chosen return relation or acceptance agreement is asked
of the family. The checked endpoint selection is the Boolean authority. -/
noncomputable def claimsInstallation {model : DomainModel} {art : ZkcSecurity.Endpoint.Domain.Artifacts}
    (subject : ZkcSecurity.Claims.Domain.Subject model art) (routing : Original.Routing)
    (context : routing.context = subject.compiled.selection.context)
    (root : RootCertificate subject.compiled.imported.program routing
      subject.compiled.selection.context.validator art.participant)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = []) : FiatShamir.Original.Claims.Installation subject where
  result := Values (Component model.Value) subject.compiled.imported.program.payload.entry.outputs ×
    Original.State model.toCarriers
  signature := NominalDomain.signature model.toCarriers
  absorb := NominalDomain.interface
  inputs statement := (Domain.encodeValues statement).getD []
  encoded statement := by
    apply Domain.encodeValues_getD
    rw [← subject.compiled.publics]
    exact Domain.PublicBinding.selectionData _ _ _ subject.compiled.checked
  source statement initial := root.source model
    (Domain.inputFrame subject.compiled.selection.context ((Domain.encodeValues statement).getD []) initial)
  presented statement initial := publicPresentation root model
    (Domain.inputFrame subject.compiled.selection.context ((Domain.encodeValues statement).getD []) initial)
  Post := SourceReading.Post
  returns := Original.CompleteReturns subject.compiled.imported.program.payload.entry.signature
    subject.compiled.selection.context subject.compiled.selection.context.validator art.participant
  live statement initial := InputFrames root.inputs.abi subject.compiled.imported.program.payload.entry.inputs
    (Domain.inputFrame subject.compiled.selection.context ((Domain.encodeValues statement).getD []) initial)
  acceptance source := source.1.get subject.compiled.selection.output
  bridge statement initial := by
    simpa only [context] using publicBridge_inputFrame root replacement profile noLocal model
      ((Domain.encodeValues statement).getD []) initial
  agrees _ _ related := compiledAcceptance_agree subject.compiled related

end ZkcSecurity.FiatShamir.RootConnection
