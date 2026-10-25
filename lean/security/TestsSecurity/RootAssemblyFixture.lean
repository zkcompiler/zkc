module

public import TestsSecurity.ABIInstallations.NoData
public import ZkcSecurity.Claims.Completeness

@[expose] public section
noncomputable section

/-! A model fixture for fresh printer checks. The ordinary indexed Subject
associates an admitted source and an actual pair; this is not a native export. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.RootAssemblyFixture
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair TestsSecurity.ABIInstallations.Fixtures

abbrev original := TestsSecurity.ABIInstallations.NoData.original
abbrev imported := TestsSecurity.ABIInstallations.NoData.imported
abbrev artifacts := TestsSecurity.ABIInstallations.NoData.artifacts
abbrev selected := TestsSecurity.ABIInstallations.NoData.selected

def subject : Subject ZkcSecurity.Domains.PrimeField.blsScalarModel original imported selected := by
  bind_authored_subject "claim" exports digest, digest, digest

abbrev validatorArtifacts := subject.validatorArtifacts
def validatorSubject := subject.validatorSubject []

local instance : ∀ event : Domain.Event subject.domainModel.toCarriers,
    SampleableType (Domain.Raw event) := ZkcSecurity.Domains.PrimeField.rawSampleable blsModulus

/-- A deliberately weaker quantitative law tests that direct consumers check
the selected error, rather than silently applying a perfect adapter. -/
theorem one_of_perfect
    (perfect : CanonicalCompleteness subject 0) : CanonicalCompleteness subject 1 := by
  refine ⟨perfect.1, ?_⟩
  intro values related honest
  exact (perfect.2 values related honest).trans zero_le_one

end TestsSecurity.RootAssemblyFixture
