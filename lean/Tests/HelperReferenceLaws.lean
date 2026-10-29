import ZkcTools.StructuredSource.ReferenceLaws
import Tests.ConnectionHelperCertificate

/-! One typed body law is reused at actual named declarations. Mathematical
reference equations concern complete nominal tuples, including stopping. -/
set_option autoImplicit false
namespace Tests.HelperReferenceLaws
open Zkc.Source Zkc.Source.Structured
open Tests.ConnectionHelperCertificate

attribute [local implicit_reducible] field scalarInputs readInputs readLeaf CheckedDefinition.helper

variable (model : DomainModel)

def difference : ReferenceLaw model scalarInputs [field] where
  body := scalarLeafBody false
  Requires _ _ := True
  reference args := .returned (.cons ((show model.Field "bls12-381.fr" from args.get .here) -
    (show model.Field "bls12-381.fr" from args.get (.there .here))) .nil)
  valid table args _ := by
    cases args with
    | cons left rest => cases rest with
      | cons right rest => cases rest; rfl

/-- No invocation or body equation is supplied by this instance. -/
theorem actual_difference (left right : model.Field "bls12-381.fr") :
    invoke ((scalarProgram false).payload.definitions.foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      (scalarLeaf false).helper (.cons left (.cons right .nil)) =
      .done (.cons (left - right) .nil) := by
  apply_helper_reference difference model using scalarProgram false

/-- A declaration's spelling is not part of its mathematical template. -/
def renamedDifference : CheckedDefinition := { scalarLeaf false with name := "newDifference" }

theorem renamed_difference (left right : model.Field "bls12-381.fr") :
    invoke ([renamedDifference].foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      renamedDifference.helper (.cons left (.cons right .nil)) =
      .done (.cons (left - right) .nil) := by
  apply ReferenceLaw.invoke (helper := renamedDifference.helper)
    (difference model) [renamedDifference] (by decide +kernel)
  · bind_structured_bodies
  · trivial

/-- Conditional mathematics leaves its real premise to the author. -/
def equalDifference : ReferenceLaw model scalarInputs [field] where
  body := scalarLeafBody false
  Requires _ args := args.get .here = args.get (.there .here)
  reference _ := .returned (.cons (0 : model.Field "bls12-381.fr") .nil)
  valid table args same := by
    calc
      _ = primitiveOutcome ((difference model).reference args) :=
        (difference model).valid table args trivial
      _ = _ := by
        cases args with
        | cons left rest => cases rest with
          | cons right rest =>
            cases rest
            change left = right at same
            subst right
            simp [difference, primitiveOutcome, Values.get, field]

theorem conditional_difference (left right : model.Field "bls12-381.fr") (same : left = right) :
    invoke ((scalarProgram false).payload.definitions.foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      (scalarLeaf false).helper (.cons left (.cons right .nil)) =
      .done (.cons (0 : model.Field "bls12-381.fr") .nil) := by
  apply_helper_reference equalDifference model using scalarProgram false
  exact same

example (_left _right : model.Field "bls12-381.fr") : True := by
  fail_if_success
    have : invoke ((scalarProgram false).payload.definitions.foldl
        (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
        (scalarLeaf false).helper (.cons _left (.cons _right .nil)) =
        .done (.cons (0 : model.Field "bls12-381.fr") .nil) := by
      apply_helper_reference equalDifference model using scalarProgram false
  trivial

/-- The spelling is unchanged but the body has changed from subtraction to
addition. Exact-body matching must refuse the old law. -/
example (_left _right : model.Field "bls12-381.fr") : True := by
  fail_if_success
    have : invoke ((scalarProgram true).payload.definitions.foldl
        (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
        (scalarLeaf true).helper (.cons _left (.cons _right .nil)) =
        .done (.cons (_left - _right) .nil) := by
      apply_helper_reference difference model using scalarProgram true
  trivial

/-- A bounded read is an outcome reference, with no artificial precondition
excluding its rejecting executions. -/
def boundedRead : ReferenceLaw model readInputs [field] where
  body := readLeafBody
  Requires _ _ := True
  reference args := match (args.get .here)[args.get (.there .here)]? with
    | some value => .returned (.cons value .nil)
    | none => .stopped .refused
  valid table args _ := by
    cases args with
    | cons values rest => cases rest with
      | cons index rest =>
        cases rest
        simp only [readLeafBody, Region.denote, Evaluation.meaningOn, Regions.denote,
          Operands.eval, Evaluation.operationOn_boundedAt]
        cases selected : values[index]? <;>
          simp [field, Values.get, Environment.prepend, Environment.push, selected, PIR.Process.bind, primitiveOutcome]


theorem actual_bounded_read (values : List (model.Field "bls12-381.fr")) (index : Nat) :
    invoke (readProgram.payload.definitions.foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      readLeaf.helper (.cons values (.cons index .nil)) =
      primitiveOutcome ((boundedRead model).reference (.cons values (.cons index .nil))) := by
  apply_helper_reference boundedRead model using readProgram

theorem out_of_bounds (values : List (model.Field "bls12-381.fr")) :
    invoke (readProgram.payload.definitions.foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      readLeaf.helper (.cons values (.cons values.length .nil)) = .halt .refused := by
  rw [actual_bounded_read]
  change primitiveOutcome (match values[values.length]? with
    | some value => PIR.Outcome.returned (show Values model.Value [field] from .cons value .nil)
    | none => .stopped .refused) = _
  simp [primitiveOutcome]

#print axioms renamed_difference
#print axioms conditional_difference
#print axioms actual_bounded_read
#print axioms out_of_bounds
#print axioms actual_difference
#print axioms ReferenceLaw.invoke
#print axioms boundedRead
end Tests.HelperReferenceLaws
