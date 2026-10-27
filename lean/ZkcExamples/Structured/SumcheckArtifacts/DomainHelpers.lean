module

public import Zkc.Construction.DomainBinding
public import ZkcExamples.Structured.SumcheckUnitContracts
public import ZkcExamples.Structured.MapPrefixContracts
public import ZkcExamples.Structured.OriginalSumcheckChecks
public import ZkcExamples.Structured.SumcheckPendingLaws

@[expose] public section

/-! Nominal constructed helper equations from complete checked source bodies.
These laws use the exact admitted program's closed dependency fold. They do
not replace a helper by a name-based mathematical implementation. Successful
equations retain the actual argument and output ABI encodings; the underlying
Domain binding also exposes failed lookup, decoding and stopped outcomes.
-/

set_option autoImplicit false
namespace ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured PrimitiveLibrary SumcheckHelperBodies SumcheckHelperLaws

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Complete source-owned arithmetic dependencies of a table component.
Membership and exact bodies are checked in the actual program's definition list. -/
structure Bodies (program : Structured.Program) : Prop where
  sumcheck : SumcheckUnitContracts.Bodies program.payload.definitions
  terminal : OriginalSumcheckLibrary.TerminalBodies program.payload.definitions

theorem Bodies.check {program : Structured.Program} (bodies : Bodies program) :
    BodyIn program.payload.definitions checkHelper checkBody :=
  bodies.terminal.elim fun _ implementation => implementation.check

/-- A uniform arithmetic theorem is transported through the exact same helper
table, not through an equality of source and constructed operation signatures. -/
theorem call_return (program : Structured.Program) (helper : Helper)
    (arguments : Values (assignment F G) helper.inputs)
    (results : Values (assignment F G) helper.outputs)
    (law : invoke (closedMeanings program.payload.definitions) helper arguments = .done results)
    (encodedArguments encodedResults : Domain.Environment (ringModel F G).toCarriers)
    (argumentsEncoding : Domain.encodeValues arguments = some encodedArguments)
    (resultsEncoding : Domain.encodeValues results = some encodedResults) :
    Domain.callHelper (ringModel F G) program helper.name
      (helper.outputs.map ValueSort.data) encodedArguments = .returned encodedResults := by
  apply Domain.Binding.callHelper_of_invoke_return _ _ helper arguments results _
    encodedArguments encodedResults argumentsEncoding resultsEncoding
  rw [Domain.Binding.helperTable_ringModel]
  exact law

theorem pending (program : Structured.Program)
    (claims : SumcheckPendingLaws.Bodies program.payload.definitions) (scalar : F) :
    Domain.callHelper (ringModel F G) program SumcheckPendingBodies.pendingHelper.name
      [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")]
      [.data (.field "bls12-381.fr" scalar)] =
      .returned [.data (.vector "bls12-381.fr" []), .data (.field "bls12-381.fr" scalar)] := by
  apply call_return program SumcheckPendingBodies.pendingHelper (.cons scalar .nil)
    (.cons [] (.cons scalar .nil)) _ _ _ rfl rfl
  rw [claims.pending.invoke program.payload.linked]
  rfl

theorem claim_identity (program : Structured.Program) (name : String)
    (body : BodyIn program.payload.definitions (SumcheckPendingLaws.identityHelper name)
      SumcheckPendingLaws.identityBody) (point : List F) (scalar : F) :
    Domain.callHelper (ringModel F G) program name
      [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")]
      [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" scalar)] =
      .returned [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" scalar)] := by
  apply call_return program (SumcheckPendingLaws.identityHelper name)
    (.cons point (.cons scalar .nil)) (.cons point (.cons scalar .nil)) _ _ _ rfl rfl
  rw [body.invoke program.payload.linked]
  rfl

variable (program : Structured.Program)
  (bodies : SumcheckUnitContracts.Bodies program.payload.definitions)

include bodies

theorem empty :
    Domain.callHelper (ringModel F G) program emptyHelper.name
      [.data (.vector "bls12-381.fr")] [] =
      .returned [.data (.vector "bls12-381.fr" [])] :=
  call_return program emptyHelper .nil (.cons [] .nil)
    (SumcheckUnitContracts.empty_equation program.payload.linked bodies) _ _ rfl rfl

theorem append (point : List F) (challenge : F) :
    Domain.callHelper (ringModel F G) program appendHelper.name
      [.data (.vector "bls12-381.fr")]
      [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" challenge)] =
      .returned [.data (.vector "bls12-381.fr" (point ++ [challenge]))] :=
  call_return program appendHelper (.cons point (.cons challenge .nil))
    (.cons (point ++ [challenge]) .nil)
    (SumcheckUnitContracts.append_equation program.payload.linked bodies point challenge) _ _ rfl rfl

theorem table (raw : List F) (dimension columns : Nat)
    (shape : HasShape raw dimension columns) (bounded : raw.length < indexLimit)
    (dimensionBound : dimension < indexLimit) (columnsBound : columns < indexLimit) :
    Domain.callHelper (ringModel F G) program MapFirstBodies.tableHelper.name
      [.data (.vector "bls12-381.fr"), .data .index, .data .index]
      [.data (.vector "bls12-381.fr" raw), .data (.index dimension), .data (.index columns)] =
      .returned [.data (.vector "bls12-381.fr" raw),
        .data (.index dimension), .data (.index columns)] := by
  apply call_return program MapFirstBodies.tableHelper
    (inputs raw dimension columns) (inputs raw dimension columns) _ _ _ rfl rfl
  simpa only [shape, ite_true] using
    (SumcheckUnitContracts.first_laws program.payload.linked bodies).tableLaw raw dimension columns
      bounded dimensionBound columnsBound

theorem first (raw : List F) (dimension columns : Nat) (challenge : F)
    (shape : HasShape raw dimension columns) (bounded : raw.length < indexLimit)
    (positive : 0 < dimension) :
    Domain.callHelper (ringModel F G) program MapFirstBodies.firstHelper.name
      [.data (.vector "bls12-381.fr"), .data .index, .data .index]
      [.data (.vector "bls12-381.fr" raw), .data (.index dimension),
        .data (.index columns), .data (.field "bls12-381.fr" challenge)] =
      .returned [.data (.vector "bls12-381.fr"
          (Zkc.Polynomial.Multilinear.restrictValues raw challenge)),
        .data (.index (dimension - 1)), .data (.index columns)] := by
  apply call_return program MapFirstBodies.firstHelper
    (MapFirstLaws.firstInputs raw dimension columns challenge)
    (inputs (Zkc.Polynomial.Multilinear.restrictValues raw challenge) (dimension - 1) columns)
    _ _ _ rfl rfl
  simpa only [positive, ite_true] using
    (SumcheckUnitContracts.first_laws program.payload.linked bodies).first raw dimension columns
      challenge shape bounded

theorem sums (raw : List F) (dimension columns : Nat)
    (dimensionBound : dimension < indexLimit) (positive : 0 < dimension)
    (splitShape : 0 < raw.length ∧ raw.length % 2 = 0) :
    Domain.callHelper (ringModel F G) program sumsHelper.name
      [.data (.field "bls12-381.fr"), .data (.field "bls12-381.fr")]
      [.data (.vector "bls12-381.fr" raw), .data (.index dimension), .data (.index columns)] =
      .returned [.data (.field "bls12-381.fr" (raw.take (raw.length / 2)).sum),
        .data (.field "bls12-381.fr" (raw.drop (raw.length / 2)).sum)] := by
  apply call_return program sumsHelper (inputs raw dimension columns)
    (messageResult (raw.take (raw.length / 2)).sum (raw.drop (raw.length / 2)).sum)
    _ _ _ rfl rfl
  rw [SumcheckUnitContracts.sums_all program.payload.linked bodies raw dimension columns,
    ite_eq_left dimensionBound, ite_eq_left positive, ite_eq_left splitShape]

theorem less (left right : Nat) (leftBound : left < indexLimit) (rightBound : right < indexLimit) :
    Domain.callHelper (ringModel F G) program MapFirstBodies.lessHelper.name
      [.data .boolean] [.data (.index left), .data (.index right)] =
      .returned [.data (.boolean (decide (left < right)))] :=
  call_return program MapFirstBodies.lessHelper (.cons left (.cons right .nil))
    (.cons (decide (left < right)) .nil)
    (lessAll_bounded _ (SumcheckUnitContracts.first_laws program.payload.linked bodies).less
      left right leftBound rightBound)
    _ _ rfl rfl

omit bodies in
theorem check
    (terminal : OriginalSumcheckLibrary.TerminalBodies program.payload.definitions)
    (raw point : List F) (claim : F)
    (rawBound : raw.length < indexLimit) (pointBound : point.length < indexLimit) :
    Domain.callHelper (ringModel F G) program checkHelper.name [.data .boolean]
      [.data (.vector "bls12-381.fr" raw), .data (.vector "bls12-381.fr" point),
        .data (.field "bls12-381.fr" claim)] =
      .returned [.data (.boolean (decide (HasShape raw point.length 1 ∧
        (Zkc.Polynomial.Multilinear.restrictPrefixValues raw point).sum = claim)))] := by
  obtain ⟨bindings, implementation⟩ := terminal
  obtain ⟨collectBindings, first⟩ := implementation.first
  apply call_return program checkHelper (checkInputs raw point claim)
    (boolResult (decide (HasShape raw point.length 1 ∧
      (Zkc.Polynomial.Multilinear.restrictPrefixValues raw point).sum = claim)))
    _ _ _ rfl rfl
  exact (implementation.check.invoke program.payload.linked (checkInputs raw point claim)).trans
    (SumcheckHelperLaws.check_generic_body _
      (MapPrefixContracts.laws_of_bodies program.payload.linked implementation.restriction first)
      (fun raw point claim => implementation.checkTable.invoke program.payload.linked (checkInputs raw point claim))
      raw point claim rawBound pointBound)

end ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers
