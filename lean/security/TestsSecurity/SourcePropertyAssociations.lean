module

public import ZkcSecurityExamples.Sumcheck.SourceRootReference
public meta import ZkcTools.StructuredSource.Association

@[expose] public section
set_option autoImplicit false
namespace TestsSecurity.SourcePropertyAssociations
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Source
open ZkcExamples.Structured SumcheckSourceSelections
open ZkcSecurity.Realizations.Sumcheck.SourceRootReference

private def limits (body : RawRegion Ty ProtocolOp) : List Nat :=
  body.operations.filterMap fun op => match op with
    | .repeat spec _ => some spec.maximum
    | _ => none

theorem changed_body : ¬ Nonempty (Template.Association (source .small).payload
    (reductionSignature .small) (SumcheckVerifierBodies.reduceBody 3)) := by
  have incompatible : ∀ candidate ∈ (source .small).payload.protocols,
      candidate.signature = reductionSignature .small →
        limits candidate.raw ≠ limits (SumcheckVerifierBodies.reduceBody 3).erase := by
    decide +kernel
  rintro ⟨association⟩
  exact incompatible association.definition association.member association.signature_eq
    (congrArg limits association.body_eq)

noncomputable def changedSignature : ProtocolSignature :=
  { reductionSignature .small with name := "SourcePropertyControl/absent-signature" }

theorem changed_signature : ¬ Nonempty (Template.Association (source .small).payload
    changedSignature (SumcheckVerifierBodies.reduceBody 2)) := by
  have incompatible : ∀ candidate ∈ (source .small).payload.protocols,
      candidate.signature ≠ changedSignature := by decide +kernel
  rintro ⟨association⟩
  exact incompatible association.definition association.member association.signature_eq

/-- The same search discovers the actual root at a different table position. -/
noncomputable def rootAssociation : Template.Association (source .small).payload
    (source .small).payload.entry.signature (source .small).payload.entry.body := by
  derive_source_association

example : True := by
  fail_if_success
    have : Template.Association (source .small).payload
        (reductionSignature .small) (SumcheckVerifierBodies.reduceBody 3) := by
      derive_source_association
  fail_if_success
    have : Template.Association (source .small).payload
        changedSignature (SumcheckVerifierBodies.reduceBody 2) := by
      derive_source_association
  trivial

#print axioms Template.Association.invoke
#print axioms changed_body
#print axioms changed_signature
end TestsSecurity.SourcePropertyAssociations
