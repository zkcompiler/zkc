module

public import ZkcExamples.Structured.Generated.Connections.Gkr
public import ZkcSecurity.Realizations.Gkr.CanonicalPolicy
public import ZkcSecurity.Realizations.Gkr.CanonicalReadback
public import ZkcSecurity.Source.Installation

@[expose] public section

/-! Root-owned installation facts. Independent generated coverage supplies every
reached source route; no GKR-specific route equation or handler is required. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Source Generated.Subject Generated.ABI

abbrev scope := PairScope.ofContext ZkcExamples.Structured.Generated.Connections.Gkr.context

theorem foldLaws : Pair.FoldLaws (carriers := model.toCarriers) scope
    ZkcExamples.Structured.Generated.Connections.Gkr.producerRouting ZkcExamples.Structured.Generated.Connections.Gkr.validatorRouting :=
  publicFoldLaws ZkcExamples.Structured.Generated.Connections.Gkr.context _ rfl _ _ rfl rfl rfl rfl (by decide +kernel)

end ZkcSecurity.Realizations.Gkr.CanonicalConnection
