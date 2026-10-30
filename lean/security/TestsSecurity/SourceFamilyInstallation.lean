module

public import ZkcSecurityExamples.Sumcheck.SourceFamilySelections
public meta import ZkcTools.StructuredSource.Association

@[expose] public section

/-! Template inference is data discovery, followed by complete membership,
signature and body checks. In particular a first matching ABI is insufficient. -/
set_option autoImplicit false
noncomputable section
namespace TestsSecurity.SourceFamilyInstallation
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Source
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck ZkcExamples.Structured SumcheckSourceSelections

def small : (bound : Nat) × (name : String) × Template.Association
    (source .small).payload (SourceFamily.reductionSignature name)
      (SumcheckVerifierBodies.reduceBody bound) := by
  infer_source_template

def two : (bound : Nat) × (name : String) × Template.Association
    (source .twoSums).payload (SourceFamily.reductionSignature name)
      (SumcheckVerifierBodies.reduceBody bound) := by
  infer_source_template

example : small.fst = 2 := rfl
example : two.fst = 4 := rfl

example : True ∧ True := by
  constructor
  · have selected : (bound : Nat) × (name : String) × Template.Association
        (source .small).payload (SourceFamily.reductionSignature name)
          (SumcheckVerifierBodies.reduceBody bound) := by
      infer_source_template
    rcases selected with ⟨_, _, _⟩
    trivial
  · trivial

example : True := by
  fail_if_success
    have : (name : String) × Template.Association (source .small).payload
        (SourceFamily.reductionSignature name) (SumcheckVerifierBodies.reduceBody 3) := by
      infer_source_template
  fail_if_success
    have : Template.Association (source .small).payload
        (SourceFamily.reductionSignature "unadmitted") (SumcheckVerifierBodies.reduceBody 2) := by
      derive_source_association
  trivial

#print axioms small
#print axioms two
end TestsSecurity.SourceFamilyInstallation
