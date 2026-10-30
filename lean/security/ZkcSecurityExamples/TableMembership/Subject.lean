module

public import ZkcExamples.Construction.TableMembership
public import ZkcSecurity.Bindings.Models.PrimeField
public import CompPoly.Fields.KoalaBear.Basic
public import ZkcSecurityTools.PairConstruction
public import ZkcSecurity.Bindings.Subjects.ABI

@[expose] public section

/-! The actual native-exported CheckMembership pair and retained selected_rows
clause, interpreted over the catalogue's prime field. Physical identities name
the original export and canonical JSON participant exports in the manifest. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section
namespace ZkcSecurity.Examples.TableMembership.Subject
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims

abbrev original := ZkcExamples.Construction.TableMembership.snapshot
abbrev imported := ZkcExamples.Construction.TableMembership.imported
abbrev artifacts := ZkcExamples.Construction.TableMembership.artifacts
abbrev selected := ZkcExamples.Construction.TableMembership.selected
abbrev Scalar := ZMod 2130706433
abbrev model := ZkcSecurity.Domains.PrimeField.model 2130706433

instance prime : Fact (2130706433 : Nat).Prime := ⟨_root_.KoalaBear.is_prime⟩

def capabilities : Claims.Domain.Capabilities model original :=
  ZkcSecurity.Domains.PrimeField.capabilities original 2130706433 (by decide +kernel)

noncomputable instance samples : ∀ event : Domain.Event model.toCarriers,
    SampleableType (Domain.Raw event) := capabilities.samples

def subject : HonestPair.Subject model original imported selected := by
  bind_authored_subject "selected_rows" exports
    "sha256:f9ad0166f81e29dacbc6be4e2e674912a349fcff66f6cf01826b81b8511326fc",
    "sha256:031121c1a6117b34ca2edacf20d589dd65958524d9054cb3edf674278330a977",
    "sha256:fdb65e400d7005ce06cbeddeda37f05f2ab0f24dab1625f9198b9dc65a45d59d"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled
abbrev validatorSubject := subject.validatorSubject

end ZkcSecurity.Examples.TableMembership.Subject
