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

/-- Closed source and artifact admission, before the required connection installation. -/
def admittedSubject : HonestPair.Subject model original imported selected := by
  bind_authored_subject "selected_rows" exports
    "sha256:74d4bc43c8cb1cf3ec783e4cfbffcceb2671d08d0c6132c2d884dfbf06895964",
    "sha256:df57c1cb2687526661407fe7edf64ae135a7e39949b99ee7b36cef61e5870744",
    "sha256:604950bc7ce10f42e51966e1edbbaf6fd28f5394a5341b4b3626f39d58edaa16"

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
