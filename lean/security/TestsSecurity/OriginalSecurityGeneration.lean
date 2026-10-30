module

import TestsSecurity.SourcePropertyAssociations
import TestsSecurity.SourcePairProperties
import TestsSecurity.SourcePropertyAssembly
import TestsSecurity.GeneratedRootConnections
import TestsSecurity.RootConnectionControls
import ZkcTools.ConstructionBindings.Analysis
meta import ZkcTools.ConstructionBindings.Analysis
import ZkcSecurityExamples.Generation.Roots.Catalogue
meta import ZkcSecurityExamples.Generation.Roots.Catalogue
meta import Zkc.Construction.ConnectionInstallation

/-! Replacement for the retired method-specific generator test. Exact typed
signature/body and static-bound mismatch are kernel controls in Associations;
complete non-Boolean returns, no successful halt and reached histories are
checked in PairProperties/Assembly. GeneratedRootConnections consumes the
production certificates and independent route coverage. A proposer refusal
alone makes no assertion that the requested theorem has no proof. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.OriginalSecurityGeneration
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured SumcheckSourceSelections

/-- An identical helper name and Boolean ABI do not admit projection as conjunction. -/
theorem projection_not_associated :
    ¬ BodyIn (source .twoSums).payload.definitions Generated.Bindings.TwoSumsInputs.helper25Helper
      (.ret (.cons .here .nil)) := by
  have incompatible : ∀ candidate ∈ (source .twoSums).payload.definitions,
      candidate.helper = Generated.Bindings.TwoSumsInputs.helper25Helper →
        candidate.raw.operations.length ≠ 0 := by decide +kernel
  rintro ⟨candidate, member, helper, body⟩
  exact incompatible candidate member helper (congrArg (fun raw => raw.operations.length) body)

-- Proposal refusals test the current source/artifact boundary only. They do
-- not assert that an arbitrary modified program has no possible connection.
private meta def refuses {α : Type} (label : String) (result : Except String α) :
    Lean.Elab.Command.CommandElabM Unit := do
  match result with
  | .ok _ => throwError "accepted invalid proposal: {label}"
  | .error reason => Lean.logInfo m!"PASS source/artifact proposal {label}: {reason}"

run_cmd do
  let roots ← ZkcSecurity.Generation.Roots.evaluateSelections
  for root in roots do
    let .ok program := check root.snapshot | throwError "source admission"
    let .ok layout := ZkcTools.ConstructionBindings.analyze program root.artifacts.validator
      | throwError "current source/artifact association refused"
    unless layout.calls.length == layout.loops.length do throwError "dropped source occurrence"
    refuses "missing root calls" <| ZkcTools.ConstructionBindings.analyze program
      { root.artifacts.validator with instructions := [] }
    refuses "wrong root instruction order" <| ZkcTools.ConstructionBindings.analyze program
      { root.artifacts.validator with instructions := root.artifacts.validator.instructions.reverse }
    refuses "unavailable return reference" <| ZkcTools.ConstructionBindings.analyze program
      { root.artifacts.validator with returned := [layout.arity] }
    refuses "missing full return tuple" <| ConnectionInstallation.ReturnLayout.build
      program.payload.entry.signature layout.context layout.context.validator
      { root.artifacts.validator with returned := [] }
    refuses "wrong nominal return types" <| ConnectionInstallation.ReturnLayout.build
      program.payload.entry.signature layout.context layout.context.validator
      { root.artifacts.validator with outputs := [] }
    for other in roots do
      if root.name != other.name then
        refuses "wrong source/artifact association" <|
          ZkcTools.ConstructionBindings.analyze program other.artifacts.validator

-- The actual source certificate refuses a missing physical ABI before running
-- the source; full-return/history disagreements are proved in RootConnectionControls.
example (model : DomainModel) :
    Generated.Connections.SmallSumcheck.validator.source model [] = .halt .refused := rfl
example (model : DomainModel) :
    Generated.Connections.TwoSums.validator.source model [] = .halt .refused := rfl

-- Identical host carriers cannot hide a wrong nominal vector sort in a full
-- physical ABI. The actual root refuses before any source interaction.
example (model : DomainModel) (raw : List (model.Field "other"))
    (scalar : model.Field field) (count : Nat) (history : Domain.History model.toCarriers) :
    Generated.Connections.SmallSumcheck.validator.source model
      [.data (.vector "other" raw), .data (.field field scalar), .data (.index count),
        .transcript Generated.Connections.SmallSumcheck.context.suite history] = .halt .refused := rfl

#check TestsSecurity.SourcePropertyAssociations.changed_body
#check TestsSecurity.SourcePropertyAssociations.changed_signature
#check TestsSecurity.SourcePairProperties.no_stopped_completeness
#check TestsSecurity.SourcePairProperties.captured_installed
#check TestsSecurity.GeneratedRootConnections.smallCoherence
#check TestsSecurity.GeneratedRootConnections.twoCoherence
#check TestsSecurity.RootConnectionControls.wrong_residual
#check TestsSecurity.RootConnectionControls.wrong_history
#print axioms projection_not_associated

end TestsSecurity.OriginalSecurityGeneration
