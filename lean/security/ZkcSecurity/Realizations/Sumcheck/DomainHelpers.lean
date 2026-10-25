module

public import Zkc.Construction.DomainBinding
public import ZkcSecurity.Families.Sumcheck.TableComponentReadbackRound
public import ZkcSecurity.Families.Sumcheck.TableComponentPrefix
public import ZkcExamples.Structured.SumcheckUnitContracts
public import ZkcExamples.Structured.MapPrefixContracts

@[expose] public section

/-! Nominal constructed helper equations from complete checked source bodies.
These laws use the exact admitted program's closed dependency fold. They do
not replace a helper by a name-based mathematical implementation. Successful
equations retain the actual argument and output ABI encodings; the underlying
Domain binding also exposes failed lookup, decoding and stopped outcomes.
-/

set_option autoImplicit false
namespace ZkcSecurity.Realizations.Sumcheck.DomainHelpers
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured PrimitiveLibrary SumcheckHelperBodies SumcheckHelperLaws

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Complete source-owned arithmetic dependencies of a table component.
Membership and exact bodies are checked in the actual program's definition list. -/
structure Bodies (program : Structured.Program) : Prop where
  sumcheck : SumcheckUnitContracts.Bodies program.payload.definitions
  prefixBodies : MapPrefixContracts.Bodies program.payload.definitions
  check : BodyIn program.payload.definitions checkHelper checkBody
  checkTable : BodyIn program.payload.definitions checkTableHelper checkTableBody

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
    MapFirstContracts.table_equation program.payload.linked bodies.first raw dimension columns
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
    MapFirstContracts.first_equation program.payload.linked bodies.first raw dimension columns
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
    (MapFirstContracts.less_law program.payload.linked bodies.first left right leftBound rightBound)
    _ _ rfl rfl

omit bodies in
theorem check
    (prefixBodies : MapPrefixContracts.Bodies program.payload.definitions)
    (firstBodies : MapFirstContracts.Bodies program.payload.definitions)
    (checkBody : BodyIn program.payload.definitions checkHelper checkBody)
    (tableBody : BodyIn program.payload.definitions checkTableHelper checkTableBody)
    (raw point : List F) (claim : F)
    (rawBound : raw.length < indexLimit) (pointBound : point.length < indexLimit) :
    Domain.callHelper (ringModel F G) program checkHelper.name [.data .boolean]
      [.data (.vector "bls12-381.fr" raw), .data (.vector "bls12-381.fr" point),
        .data (.field "bls12-381.fr" claim)] =
      .returned [.data (.boolean (decide (HasShape raw point.length 1 ∧
        (Zkc.Polynomial.Multilinear.restrictPrefixValues raw point).sum = claim)))] := by
  apply call_return program checkHelper (checkInputs raw point claim)
    (boolResult (decide (HasShape raw point.length 1 ∧
      (Zkc.Polynomial.Multilinear.restrictPrefixValues raw point).sum = claim)))
    _ _ _ rfl rfl
  exact (checkBody.invoke program.payload.linked (checkInputs raw point claim)).trans
    (SumcheckHelperLaws.check_generic_body _
      (MapPrefixContracts.laws_of_bodies program.payload.linked prefixBodies firstBodies)
      (fun raw point claim => tableBody.invoke program.payload.linked (checkInputs raw point claim))
      raw point claim rawBound pointBound)

omit bodies in
/-- Only the example layer connects complete admitted bodies to the generic
family's semantic law record. All names and the nominal domain are checked. -/
theorem round_helpers {K H : Type} [Field K] [AddCommGroup H] [Module K H]
    [DecidableEq K] [DecidableEq H] (program : Structured.Program) (bodies : Bodies program)
    (plan : ZkcSecurity.Families.Sumcheck.TableComponent.ReadbackRound.Plan)
    (fieldName : plan.field = "bls12-381.fr")
    (sumsName : plan.sumsHelper = sumsHelper.name)
    (firstName : plan.firstHelper = MapFirstBodies.firstHelper.name)
    (appendName : plan.appendHelper = appendHelper.name) :
    ZkcSecurity.Families.Sumcheck.TableComponent.ReadbackRound.HelperLaws
      (F := K) (G := H) program plan := by
  constructor
  · intro raw dimension length bounded small positive
    rw [fieldName, sumsName]
    have shape : HasShape raw dimension 1 :=
      hasShape_of_length _ _ _ (by decide) small (by simpa using length)
    exact sums program bodies.sumcheck raw dimension 1
      (lt_trans small (by decide +kernel)) positive (shape.split_valid positive)
  · intro raw dimension challenge length bounded small positive
    rw [fieldName, firstName]
    exact first program bodies.sumcheck raw dimension 1 challenge
      (hasShape_of_length _ _ _ (by decide) small (by simpa using length)) bounded positive
  · intro point challenge
    rw [fieldName, appendName]
    exact append program bodies.sumcheck point challenge

omit bodies in
/-- The same terminal source condition follows from every completed honest
prefix invariant, independently of the caller's retained frame. -/
theorem terminal_condition {K Frame : Type} [Field K]
    (raw : List K) (state : ZkcSecurity.Families.Sumcheck.TableComponent.PrefixState K Frame 0)
    (original : state.original = raw) (bounded : raw.length < indexLimit)
    (honest : state.scalar = state.entries.sum) :
    HasShape raw state.point.length 1 ∧
      (Zkc.Polynomial.Multilinear.restrictPrefixValues raw state.point).sum = state.scalar := by
  have length : raw.length = 2 ^ state.point.length := by
    simpa only [original, List.length_nil, Nat.zero_add] using state.shape
  have shape : HasShape raw state.point.length 1 := by
    apply hasShape_of_length _ _ _ (by decide)
    · apply (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : Nat))).mp
      simpa only [length, indexLimit] using bounded
    · simpa only [Nat.mul_one] using length
  refine ⟨shape, ?_⟩
  simpa only [ZkcSecurity.Families.Sumcheck.TableComponent.PrefixState.entries, original]
    using honest.symm

end ZkcSecurity.Realizations.Sumcheck.DomainHelpers
