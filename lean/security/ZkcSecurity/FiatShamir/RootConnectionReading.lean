module

public import Zkc.Construction.ConnectionRootCertificate
public import ZkcSecurity.FiatShamir.DomainSourceReading
public import ZkcSecurity.FiatShamir.OriginalTransport

@[expose] public section

/-! Install an operation interpretation on the actual ABI source of a root
certificate. Decoding, the source snapshot and the initial construction history
are inherited from that root. The full simulation retains its source-owned
return relation and every physical checkpoint; no source equation or reading
is an instance premise. Admission and route coverage remain separate gates.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.RootConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ConnectionRoot

attribute [local implicit_reducible] CheckedProtocol.signature

variable {I : PIR.Signature}

/-- Interpret precisely the occurrence participant selected by the original
ABI. A malformed row refuses before executing any source operation. -/
def presentationFromABI (model : DomainModel) (program : Program)
    (routing : Original.Routing) (role : Nat) (abi : Original.InputABI)
    (physical : Domain.Environment model.toCarriers) (initial : Original.State model.toCarriers)
    {absorb : Interface I (Domain.Event model.toCarriers) (Domain.Payload model.toCarriers) Domain.Raw}
    (adapter : SourceReading.Interpretation { routing with snapshot := program.snapshot } absorb) :
    PIR.Process I
      (Values (Component model.Value) program.payload.entry.outputs × Original.State model.toCarriers) :=
  match abi.read physical program.payload.entry.inputs with
  | none => .halt .refused
  | some inputs => adapter.presentation (Occurrence.participant model program role inputs) initial

/-- The existing operation laws lift through the actual ABI for every model,
physical row, source return and typed reply. No input well-formedness premise
is needed, and the source's actual snapshot is used even for stale routing. -/
theorem readingFromABI (model : DomainModel) (program : Program)
    (routing : Original.Routing) (role : Nat) (abi : Original.InputABI)
    (physical : Domain.Environment model.toCarriers) (initial : Original.State model.toCarriers)
    {absorb : Interface I (Domain.Event model.toCarriers) (Domain.Payload model.toCarriers) Domain.Raw}
    (adapter : SourceReading.Interpretation { routing with snapshot := program.snapshot } absorb) :
    DomainReduction.Bridge absorb SourceReading.Post initial.history
      (Original.participantFromABI model program routing role abi physical initial)
      (presentationFromABI model program routing role abi physical initial adapter) := by
  cases found : abi.read physical program.payload.entry.inputs with
  | none =>
    simp only [Original.participantFromABI, presentationFromABI, found]
    exact .halt _ _
  | some inputs =>
    simp only [Original.participantFromABI, presentationFromABI, found, Original.participant]
    exact adapter.reading _ initial

variable {program : Program} {routing : Original.Routing} {role : Nat} {artifact : Participant}

/-- A complete bridge on the actual root source and actual artifact. The
adapter only supplies primitive laws; the root fixes CompleteReturns and all
input readbacks independently of any later acceptance projection. -/
noncomputable def bridge (root : RootCertificate program routing role artifact)
    (model : DomainModel) (physical : Domain.Environment model.toCarriers)
    {absorb : Interface I (Domain.Event model.toCarriers) (Domain.Payload model.toCarriers) Domain.Raw}
    (adapter : SourceReading.Interpretation { routing with snapshot := program.snapshot } absorb) :
    FiatShamir.Original.Bridge absorb SourceReading.Post (root.inputs.initial physical).history
      (root.source model physical) (Domain.participant model program routing.context artifact physical)
      (presentationFromABI model program routing role root.inputs.abi physical
        (root.inputs.initial physical) adapter)
      (Original.CompleteReturns program.payload.entry.signature routing.context role artifact)
      (InputFrames root.inputs.abi program.payload.entry.inputs physical) where
  sourceReading := readingFromABI model program routing role root.inputs.abi physical
    (root.inputs.initial physical) adapter
  simulation := root.simulation model physical

/-- Public transcript presentation of either folded role. This is an endpoint
projection; producer execution and honest completeness use other consumers. -/
def publicPresentation (root : RootCertificate program routing role artifact)
    (model : DomainModel) (physical : Domain.Environment model.toCarriers) :
    PIR.Process (NominalDomain.signature model.toCarriers)
      (Values (Component model.Value) program.payload.entry.outputs × Original.State model.toCarriers) :=
  match root.inputs.abi.read physical program.payload.entry.inputs with
  | none => .halt .refused
  | some inputs => DomainSourceReading.presentation { routing with snapshot := program.snapshot }
      (Occurrence.participant model program role inputs) (root.inputs.initial physical)

/-- The public adapter requires a Fiat-Shamir profile and no local routes.
These are adapter conditions, not source admission or route-coverage proofs.
All source reading and observation coherence are derived automatically. -/
noncomputable def publicBridge (root : RootCertificate program routing role artifact)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = []) (model : DomainModel)
    (physical : Domain.Environment model.toCarriers) :
    FiatShamir.Original.Bridge NominalDomain.interface SourceReading.Post
      (root.inputs.initial physical).history
      (root.source model physical) (Domain.participant model program routing.context artifact physical)
      (publicPresentation root model physical)
      (Original.CompleteReturns program.payload.entry.signature routing.context role artifact)
      (InputFrames root.inputs.abi program.payload.entry.inputs physical) := by
  let adapter := DomainSourceReading.interpretation { routing with snapshot := program.snapshot }
    replacement profile noLocal (carriers := model.toCarriers)
  have same : presentationFromABI model program routing role root.inputs.abi physical
      (root.inputs.initial physical) adapter = publicPresentation root model physical := by
    unfold presentationFromABI publicPresentation
    cases root.inputs.abi.read physical program.payload.entry.inputs <;> rfl
  simpa only [same] using bridge root model physical adapter

/-- Every explicit query of the actual artifact agrees with its actual
observation prefix, carrying the full source return and complete return row. -/
theorem publicCoherent (root : RootCertificate program routing role artifact)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = []) (model : DomainModel)
    (physical : Domain.Environment model.toCarriers) :
    DomainReduction.CoherentTo
      (fun reached target => ∃ source, SourceReading.Post reached source ∧
        Original.CompleteReturns program.payload.entry.signature routing.context role artifact source target)
      (root.inputs.initial physical).history
      (Domain.participant model program routing.context artifact physical) :=
  (publicBridge root replacement profile noLocal model physical).actualCoherent

end ZkcSecurity.FiatShamir.RootConnection
