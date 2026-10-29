import Tests.HelperReferenceLaws
import Zkc.Source.Structured.ReferenceLibrary
import Zkc.Source.Structured.NormalForm.Reference

/-! Exact references enter the existing normal-form law table. A dependency
change, an omitted result or an unproved premise cannot use the returning law.
Stopping retains its reason in every surrounding effect interface. -/
set_option autoImplicit false
namespace Tests.NormalFormReferences
open Zkc.Source Zkc.Source.Structured NormalForm
open Tests.ConnectionHelperCertificate Tests.HelperReferenceLaws
attribute [local implicit_reducible] field scalarInputs CheckedDefinition.helper

variable (model : DomainModel)

def pairLaw : ReferenceLaw model scalarInputs [field, field] :=
  ReferenceLibrary.call model (scalarLeaf false).helper
    (.cons .here (.cons (.there .here) .nil))
    (.cons .here (.cons (.there .here) .nil)) (difference model).reference

def pairResult (args : Values model.Value scalarInputs) : Values model.Value [field, field] :=
  .cons ((show model.Field "bls12-381.fr" from args.get .here) - (show model.Field "bls12-381.fr" from args.get (.there .here)))
    (.cons (args.get .here) .nil)

theorem dependent_pair (left right : model.Field "bls12-381.fr") :
    invoke ((scalarProgram false).payload.definitions.foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      scalarPair.helper (.cons left (.cons right .nil)) =
      .done (.cons (left - right) (.cons left .nil)) := by
  derive_helper_reference [pairLaw model, difference model] using scalarProgram false

/-- The wrapper is unchanged, but its dependency is now addition. -/
example (_left _right : model.Field "bls12-381.fr") : True := by
  fail_if_success
    have : invoke ((scalarProgram true).payload.definitions.foldl
        (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
        scalarPair.helper (.cons _left (.cons _right .nil)) =
        .done (.cons (_left - _right) (.cons _left .nil)) := by
      derive_helper_reference [pairLaw model, difference model] using scalarProgram true
  trivial

/-- The source law retains the non-Boolean caller frame in the normal form. -/
theorem pair_installed {I : PIR.Signature} :
    LawHolds (((scalarProgram false).payload.definitions).foldl
      (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩)
      (Values.nil : Values (Component model.Value) [])
      ⟨scalarPair.helper, .returns [], []⟩ (pairResult model) := by
  apply reference_returns (scalarProgram false).payload.definitions
    (scalarProgram false).payload.linked (pairLaw model)
  · bind_structured_bodies
  · intro args _
    derive_helper_reference [difference model] using scalarProgram false
  · intro args _
    cases args with
    | cons left rest => cases rest with
      | cons right rest => cases rest; rfl

/-- The same exact reference cannot manufacture a missing equality premise. -/
example : True := by
  fail_if_success
    have : LawHolds (((scalarProgram false).payload.definitions).foldl
        (Evaluation.ComponentTablesOn.extend model (.silent closedInterface)) ⟨[], []⟩)
        (Values.nil : Values (Component model.Value) [])
        ⟨(scalarLeaf false).helper, .returns [], []⟩
        (fun _ => .cons (0 : model.Field "bls12-381.fr") .nil) := by
      apply reference_returns (scalarProgram false).payload.definitions
        (scalarProgram false).payload.linked (equalDifference model)
      · bind_structured_bodies
  trivial

def exhaustedBody : Region dialect [] [field, .index] := .stop .exhausted
def exhausted : CheckedDefinition :=
  ⟨"exhausted", .local, [], [field, .index], exhaustedBody.erase,
    exhaustedBody, exhaustedBody.elaborate_erase⟩
def exhaustedLaw : ReferenceLaw model [] [field, .index] where
  body := exhaustedBody
  Requires _ _ := True
  reference _ := .stopped .exhausted
  valid _ _ _ := rfl

theorem exhaustion_installed {I : PIR.Signature} :
    LawHolds ([exhausted].foldl
      (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩)
      (Values.nil : Values (Component model.Value) [])
      ⟨exhausted.helper, .stops .exhausted, []⟩
      (fun _ => .cons (0 : model.Field "bls12-381.fr") (.cons 0 .nil)) := by
  apply reference_stops [exhausted] (by decide +kernel) (exhaustedLaw model)
  · bind_structured_bodies
  · intro _ _; trivial
  · intro _ _; rfl

#print axioms dependent_pair
#print axioms pair_installed
#print axioms exhaustion_installed
#print axioms reference_returns
#print axioms reference_stops
end Tests.NormalFormReferences
