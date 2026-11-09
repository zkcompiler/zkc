import Zkc.Tests.Applications.IR.MultilinearReferences
import Zkc.Verification.Installations.Sumcheck.Source.PendingBodies
import Zkc.IR.Source.Structured.MultilinearAdmissionInstallation

set_option autoImplicit false
namespace Tests.MultilinearAdmissions
open Zkc.Source Zkc.Source.Structured
open ReferenceLibrary.Multilinear
open Tests.MultilinearReferences

abbrev slot := ZkcExamples.Structured.SumcheckPendingBodies.custodySlot

abbrev checker := "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc"

theorem bodies (selected : RetainedSource) :
    Admission.Bodies (source selected).payload.definitions "bls12-381.fr" (bindings selected) slot checker := by
  refine ⟨Tests.MultilinearReferences.bodies selected, ?_, ?_, ?_, ?_, ?_⟩
  all_goals cases selected <;> bind_structured_bodies

variable (model : DomainModel) (selected : RetainedSource)

theorem actual_constructor (xs : List (model.Field "bls12-381.fr")) (n w : Nat)
    (lengthBound : xs.length < indexLimit) (nBound : n < indexLimit) (wBound : w < indexLimit) :
    invoke (closed model (definitions := (source selected).payload.definitions))
      (Admission.tableHelper "bls12-381.fr" (bindings selected)) (tableValues model "bls12-381.fr" xs n w) =
      primitiveOutcome (Admission.tableOutcome model "bls12-381.fr" xs n w) :=
  Admission.table_eq model (source selected).payload.linked (bodies selected)
    xs n w lengthBound nBound wBound

/-- No truth premise: a false claim computes the ordinary false boolean. -/
theorem actual_terminal (xs point : List (model.Field "bls12-381.fr")) (token : CustodyToken)
    (claim : model.Field "bls12-381.fr")
    (lengthBound : xs.length < indexLimit) (pointBound : point.length < indexLimit) :
    invoke (closed model (definitions := (source selected).payload.definitions))
      ⟨checker, .local, [.vector "bls12-381.fr", .resourceUnit slot, .vector "bls12-381.fr", .field "bls12-381.fr"], [.boolean]⟩
      (Admission.terminalInputs model "bls12-381.fr" slot xs token point claim) =
      .done (Admission.boolResult model (decide (Admission.HasShape xs point.length 1 ∧
        (Zkc.Polynomial.Multilinear.restrictPrefixValues xs point).sum = claim))) :=
  Admission.check_eq model (source selected).payload.linked (bodies selected)
    xs token point claim lengthBound pointBound

theorem honest_terminal (xs point : List (model.Field "bls12-381.fr")) (token : CustodyToken)
    (lengthBound : xs.length < indexLimit) (pointBound : point.length < indexLimit)
    (shape : Admission.HasShape xs point.length 1) :
    invoke (closed model (definitions := (source selected).payload.definitions))
      ⟨checker, .local, [.vector "bls12-381.fr", .resourceUnit slot, .vector "bls12-381.fr", .field "bls12-381.fr"], [.boolean]⟩
      (Admission.terminalInputs model "bls12-381.fr" slot xs token point
        (Zkc.Polynomial.Multilinear.restrictPrefixValues xs point).sum) =
      .done (Admission.boolResult model true) := by
  rw [actual_terminal model selected xs point token _ lengthBound pointBound]
  simp [shape]

example (_xs _point : List (model.Field "bls12-381.fr"))
    (_claim : model.Field "bls12-381.fr") : True := by
  fail_if_success
    have : invoke (closed model (definitions := (source selected).payload.definitions))
        (Admission.checkTableHelper "bls12-381.fr" (bindings selected))
        (Admission.checkInputs model "bls12-381.fr" _xs _point _claim) =
        primitiveOutcome (Admission.checkTableOutcome model "bls12-381.fr" _xs _point _claim) := by
      apply Admission.checkTable_eq model (source selected).payload.linked (bodies selected)
      all_goals assumption
  trivial

#print axioms bodies
#print axioms actual_constructor
#print axioms actual_terminal
#print axioms honest_terminal
#print axioms Admission.rows
#print axioms Admission.shape
#print axioms Admission.checkTable
#print axioms Admission.check
end Tests.MultilinearAdmissions
