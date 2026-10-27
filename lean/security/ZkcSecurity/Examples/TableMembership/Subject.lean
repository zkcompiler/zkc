module

public import ZkcExamples.Construction.TableMembership
public import ZkcSecurity.Domains.PrimeField
public import CompPoly.Fields.KoalaBear.Basic
public import ZkcSecurity.Tools.PairConstruction
public import ZkcSecurity.Claims.SubjectABI

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
    "sha256:4f999b8a75cff894105d7a535f7b16453d7635ddc3af3b73f49415833b295617",
    "sha256:e7d8db9a3a3140e28a5167809f95e3df45507cd76fa3080a3478366abea814cb",
    "sha256:c93e2b6585b74d9eaee11131fb3a5676e56d9aab511dc1810bae4ce31d4616d6"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled
abbrev validatorSubject := subject.validatorSubject

end ZkcSecurity.Examples.TableMembership.Subject
