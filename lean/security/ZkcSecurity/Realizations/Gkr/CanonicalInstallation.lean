module

public import ZkcExamples.Structured.Generated.Connections.Gkr
public import ZkcSecurity.Realizations.Gkr.Generated.ABI
public import ZkcSecurity.FiatShamir.RootConnectionLossless

@[expose] public section

/-! The canonical endpoint consumes the shared root interface. The root fixes
source inputs, full returns, history and frames before acceptance is selected.
Source reading, coherence and acceptance agreement are generic consequences. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalInstallation
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir Generated.Subject

abbrev root := ZkcExamples.Structured.Generated.Connections.Gkr.validator
abbrev routing := ZkcExamples.Structured.Generated.Connections.Gkr.validatorRouting

def replacement : Replacement := validatorCompiled.selection.context.replacement?.getD
  ⟨0, "", none, "", []⟩

theorem context : routing.context = validatorCompiled.selection.context := rfl
theorem profile : routing.context.profile = .fiatShamir replacement := rfl
theorem noLocal : routing.locals = [] := by decide +kernel

def installation : Original.Claims.Installation validatorSubject :=
  RootConnection.claimsInstallation validatorSubject routing context root replacement profile noLocal

theorem publicSource : PublicSourceSupport.check validatorCompiled.imported.program = true := by
  decide +kernel

theorem lossless (statement : validatorArtifacts.Statement subject.domainModel)
    (history : Domain.History subject.domainModel.toCarriers) :
    Original.LosslessOn installation.absorb (installation.presented statement history) :=
  RootConnection.claimsLossless validatorSubject routing context root publicSource replacement profile noLocal
    statement history

end ZkcSecurity.Realizations.Gkr.CanonicalInstallation
