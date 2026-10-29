module

public import ZkcSecurity.FiatShamir.PublicSourceSupport
public import ZkcSecurity.FiatShamir.RootConnectionClaims
public import ZkcSecurity.FiatShamir.LosslessPresentationClaims

@[expose] public section

/-! Full-result lossless consumers derived from a finite public source root.
The finite stored-body check excludes service receives. It is a separate,
computable support certificate, not a replacement for source admission, root
correspondence, route coverage, rejection, costs or cryptographic assumptions.
The nominal signature and its actual refusing decoder are unchanged.
-/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.FiatShamir.RootConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript ConnectionRoot

variable {program : Program} {routing : Original.Routing} {role : Nat} {artifact : Participant}

/-- Finite body data, rather than global interface losslessness, supplies every
local operation law for this root. Malformed ABI rows still stop immediately. -/
theorem publicLossless (root : RootCertificate program routing role artifact)
    (data : PublicSourceSupport.check program = true) (model : DomainModel)
    (physical : Domain.Environment model.toCarriers) :
    FiatShamir.Original.LosslessOn NominalDomain.interface (publicPresentation root model physical) := by
  unfold publicPresentation
  cases root.inputs.abi.read physical program.payload.entry.inputs with
  | none => trivial
  | some inputs =>
    exact DomainSourceReading.presentation_lossless model _ _
      (PublicSourceSupport.participant program data model role inputs) _

/-- Logical reconstruction may depend on the whole reply path and complete
artifact frame. It is not a return encoder or a request-fixed knowledge extractor. -/
def losslessPresentation (root : RootCertificate program routing role artifact)
    (data : PublicSourceSupport.check program = true)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = []) (model : DomainModel)
    (physical : Domain.Environment model.toCarriers) :
    PIR.Process (NominalDomain.signature model.toCarriers) (Domain.Result model.toCarriers) :=
  Classical.choose ((publicBridge root replacement profile noLocal model physical).exists_lossless_presentation_on
    (publicLossless root data model physical))

theorem losslessAlignment (root : RootCertificate program routing role artifact)
    (data : PublicSourceSupport.check program = true)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = []) (model : DomainModel)
    (physical : Domain.Environment model.toCarriers) :
    FiatShamir.Original.Alignment
      (Original.CompleteReturns program.payload.entry.signature routing.context role artifact)
      (publicPresentation root model physical)
      (losslessPresentation root data replacement profile noLocal model physical) :=
  (Classical.choose_spec ((publicBridge root replacement profile noLocal model physical).exists_lossless_presentation_on
    (publicLossless root data model physical))).1

/-- Full source output components, reached history and complete artifact values
remain in the postcondition; acceptance is a later selected consequence. -/
theorem losslessBridge (root : RootCertificate program routing role artifact)
    (data : PublicSourceSupport.check program = true)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = []) (model : DomainModel)
    (physical : Domain.Environment model.toCarriers) :
    DomainReduction.Bridge NominalDomain.interface
      (fun reached target => ∃ source, SourceReading.Post reached source ∧
        Original.CompleteReturns program.payload.entry.signature routing.context role artifact source target)
      (root.inputs.initial physical).history
      (Domain.participant model program routing.context artifact physical)
      (losslessPresentation root data replacement profile noLocal model physical) :=
  (Classical.choose_spec ((publicBridge root replacement profile noLocal model physical).exists_lossless_presentation_on
    (publicLossless root data model physical))).2

/-- Actual reading preserves the entire Domain.Result and unread proof suffix
in any monad, for arbitrary histories and oracle replies. -/
theorem losslessRead (root : RootCertificate program routing role artifact)
    (data : PublicSourceSupport.check program = true)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = []) (model : DomainModel)
    (physical : Domain.Environment model.toCarriers)
    {m : Type → Type} [Monad m]
    (query : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) → m (Domain.Raw event))
    (proof : Domain.Proof model.toCarriers) :
    ZkcSecurity.Endpoint.Domain.readExecution query (Domain.participant model program routing.context artifact physical) proof =
      transform NominalDomain.interface query (losslessPresentation root data replacement profile noLocal model physical)
        (root.inputs.initial physical).history proof :=
  (losslessBridge root data replacement profile noLocal model physical).reading.run query proof

/-- The existing root-derived installation obtains local lossless authority
from one finite body check. No source equation or per-statement proof is needed. -/
theorem claimsLossless {model : DomainModel} {art : ZkcSecurity.Endpoint.Domain.Artifacts}
    (subject : ZkcSecurity.Claims.Domain.Subject model art) (routing : Original.Routing)
    (context : routing.context = subject.compiled.selection.context)
    (root : RootCertificate subject.compiled.imported.program routing
      subject.compiled.selection.context.validator art.participant)
    (data : PublicSourceSupport.check subject.compiled.imported.program = true)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = []) (statement : art.Statement model) (initial : Domain.History model.toCarriers) :
    let installation := claimsInstallation subject routing context root replacement profile noLocal
    FiatShamir.Original.LosslessOn installation.absorb (installation.presented statement initial) :=
  publicLossless root data model _

variable {model : DomainModel} {art : ZkcSecurity.Endpoint.Domain.Artifacts}
variable [∀ event, SampleableType (@Domain.Raw model.toCarriers event)]

/-- The ordinary charged export consumes the existing installation directly.
Rejection, escape prices and pathwise costs remain explicit source obligations;
the fixed selected claim and full artifact return relation are retained. -/
def losslessChargedExport (subject : ZkcSecurity.Claims.Domain.Subject model art)
    (routing : Original.Routing) (context : routing.context = subject.compiled.selection.context)
    (root : RootCertificate subject.compiled.imported.program routing
      subject.compiled.selection.context.validator art.participant)
    (data : PublicSourceSupport.check subject.compiled.imported.program = true)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = [])
    (schedule : ZkcSecurity.Claims.Domain.ChargeSchedule subject) (queries : Nat) (budget : ENNReal)
    (rejects : let installation := claimsInstallation subject routing context root replacement profile noLocal
      ∀ statement, subject.FalseStatement statement → ∀ initial,
        Zkc.Obligations.Derivation installation.absorb
          (ZkcSecurity.Obligations.boundedEscape (schedule.charge queries))
          (fun _ result => installation.acceptance result ≠ some true) initial (installation.presented statement initial))
    (costs : let installation := claimsInstallation subject routing context root replacement profile noLocal
      ∀ statement initial, Typed.ChargedCostBound installation.absorb (schedule.charge queries)
        (installation.presented statement initial) initial budget) :
    ZkcSecurity.Claims.Domain.ChargedExport subject schedule queries budget :=
  (claimsInstallation subject routing context root replacement profile noLocal).losslessChargedExportOn
    (claimsLossless subject routing context root data replacement profile noLocal) schedule queries budget rejects costs

end ZkcSecurity.FiatShamir.RootConnection
