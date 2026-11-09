module

public import Zkc.Applications.IR.Construction.TableMembership
public import Zkc.Verification.Bindings.Models.PrimeField
public import CompPoly.Fields.KoalaBear.Basic
public import Zkc.Tools.Verification.PairConstruction
public import Zkc.Verification.Bindings.Subjects.ABI

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

/-- Closed source and artifact admission, before the required connection installation. -/
def admittedSubject : HonestPair.Subject model original imported selected := by
  bind_authored_subject "selected_rows" exports
    "sha256:6af83ed2005d9869fa10e2565db4a9e8b1dbdb36e65e5cf22caeef760822126f",
    "sha256:e8eeb5f53b2c09587f867564d77ae2f16a9d219a413f926c47e2387d07ae97c6",
    "sha256:2f9247eabe6adc88896857f1c4bf7f91366c6b0965157cd5046019f323186ca5"

/-- Fix the admitted metadata before deriving both complete source connections.
This subject requires the links explicitly; failed proof production cannot
leave an optional connection unresolved in a certified fixture. -/
def subject : HonestPair.Subject model original imported selected := {
  admittedSubject with
  -- Read role metadata from a checked context literal, without recomputing the
  -- complete source selection during bounded request extraction.
  selection := { admittedSubject.selection with context := ZkcExamples.Construction.TableMembership.context }
  selectionExact := by kernel_rfl
  selectionChecked := by decide +kernel
  producerOccurrences := by kernel_rfl
  validatorOccurrences := by kernel_rfl
  producerConnection := some ⟨by derive_source_connection⟩
  validatorConnection := some ⟨by derive_source_connection⟩ }

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled
abbrev validatorSubject := subject.validatorSubject

end ZkcSecurity.Examples.TableMembership.Subject
