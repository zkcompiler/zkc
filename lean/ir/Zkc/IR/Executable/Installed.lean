module

public import Zkc.IR.Executable.Execution

@[expose] public section

/-! The installed vocabulary of the native BLS12-381 proof deployments.

Each row assigns a meaning to an exact contract, static arguments, installed
implementation and physical specialization; each representation row admits a value sort at an installed
representation. These rows are assumptions about native code, not theorems:
the arkworks kernels compute BLS12-381 scalar-field, G1 and scalar-vector
operations, the native index kernels compute unsigned 64-bit index operations
and build occurrence coordinates, and the Merlin transcript kernels absorb
canonical encodings of their occurrence and value and derive a scalar
challenge, which the ideal transcript model idealizes. Vector and index
operations have the meanings of the structured primitives
(`Zkc.Source.Structured.Primitive.evaluate`), element access is
`Zkc.Construction.Calculation.boundedAt`, and the pointwise vector operations
and the requirement have the meanings of `Zkc.Executable.Computation.apply`.
The total word operations on indices (wrapping addition and subtraction,
bitwise conjunction and logical right shift) have the meanings of their
structured calculations (`Zkc.Source.Structured.IndexWords`). Checked index
addition has the meaning of the structured primitive, which refuses on
overflow; Boolean conjunction and disjunction are the structured calculations
and negation is `Zkc.Executable.Computation.apply`.

The three logical custody rows (`logical/resource_unit.*`) take the slot as
their one static argument and admit the custody sort of a valid slot at
`logical.resource_unit/0`. They select logical bookkeeping, not an external
backend. Their native meaning is the custody ledger (`PIR.Custody`). Checked
local helper recipes use its closed, payload-erased projection, with exact slot
and arity checks. The constructed instruction profile has no standalone custody
transfer; reading one as a participant instruction still refuses explicitly.
The runtime acceptance-inclusion assumption covers successful ledger execution
relative to this projection.

The arkworks numerical kernels (`numerical.map`, `numerical.sum` and
`numerical.product` over the scalar field) are one row each, whatever their
operand mask: the row takes the mask as the binding's last static argument. Their
assumed meaning is that, within the runtime's row bound
(`Zkc.Executable.Numerical.rowLimit`), the kernel evaluates the expression of the
`zkc.numerical-plan/0` plan its parameter carries, as
`Zkc.Executable.Numerical.decode` reads it,
at every row with the operands the mask selects, and returns the vector of the
values, their sum or their product (`Zkc.Executable.Computation.apply`); a payload
the decoder refuses has no meaning, as the runtime's program admission refuses
it. Above the row bound the kernel refuses, a capacity limit like the element
limit of every vector kernel, which only stops a run.

A row absent from this table makes the lowering rule refuse.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source

/-- The native Fiat–Shamir suite over the BLS12-381 scalar field. -/
abbrev nativeSuite : String := "merlin3.bls12-381.fr64be/0"

/-- The BLS12-381 scalar field. -/
abbrev scalarField : String := "bls12-381.fr"

/-- The characteristic of the BLS12-381 scalar field: numerical expression
literals are below it. -/
def scalarCharacteristic : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

def installed : Vocabulary where
  operations := [
    ⟨"indices.empty", [], "native/indices.empty", .indicesEmpty, []⟩,
    ⟨"indices.append", [], "native/indices.append", .indicesAppend, []⟩,
    ⟨"transcript.native.indexed.observe.data", [nativeSuite, "group:bls12-381.g1"],
      "arkworks/transcript.native.indexed.observe.data", .observe nativeSuite (.group "bls12-381.g1"), [⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩]⟩,
    ⟨"transcript.native.indexed.observe.data", [nativeSuite, "field:bls12-381.fr"],
      "arkworks/transcript.native.indexed.observe.data", .observe nativeSuite (.field scalarField), [⟨.data (.field scalarField), "arkworks.fr/0"⟩]⟩,
    ⟨"transcript.native.indexed.challenge", [nativeSuite],
      "arkworks/transcript.native.indexed.challenge", .challenge nativeSuite scalarField, []⟩,
    ⟨"curve.scale", ["bls12-381.g1"], "arkworks/curve.scale",
      .calculate (.groupScale "bls12-381.g1" scalarField), []⟩,
    ⟨"curve.add", ["bls12-381.g1"], "arkworks/curve.add", .calculate (.groupAdd "bls12-381.g1"), []⟩,
    ⟨"curve.equal", ["bls12-381.g1"], "arkworks/curve.equal", .calculate (.groupEqual "bls12-381.g1"), []⟩,
    ⟨"field.add", [scalarField], "arkworks/field.add", .calculate (.fieldAdd scalarField), []⟩,
    ⟨"field.mul", [scalarField], "arkworks/field.mul", .calculate (.fieldMultiply scalarField), []⟩,
    ⟨"field.sub", [scalarField], "arkworks/field.sub", .calculate (.fieldSubtract scalarField), []⟩,
    ⟨"field.equal", [scalarField], "arkworks/field.equal", .calculate (.fieldEqual scalarField), []⟩,
    ⟨"field.constant", [scalarField], "arkworks/field.constant", .fieldConstant scalarField, []⟩,
    ⟨"index.constant", [], "native/index.constant", .indexConstant, []⟩,
    ⟨"index.equal", [], "native/index.equal", .calculate .indexEqual, []⟩,
    ⟨"index.less", [], "native/index.less", .compute (.primitive .indexLess), []⟩,
    ⟨"index.sub", [], "native/index.sub", .compute (.primitive .indexSub), []⟩,
    ⟨"index.mul", [], "native/index.mul", .compute (.primitive .indexMul), []⟩,
    ⟨"index.div", [], "native/index.div", .compute (.primitive .indexDiv), []⟩,
    ⟨"index.mod", [], "native/index.mod", .compute (.primitive .indexMod), []⟩,
    ⟨"index.wrapping_add", [], "native/index.wrapping_add", .calculate .indexWrappingAdd, []⟩,
    ⟨"index.wrapping_sub", [], "native/index.wrapping_sub", .calculate .indexWrappingSubtract, []⟩,
    ⟨"index.bit_and", [], "native/index.bit_and", .calculate .indexBitAnd, []⟩,
    ⟨"index.logical_shift_right", [], "native/index.logical_shift_right",
      .calculate .indexLogicalShiftRight, []⟩,
    ⟨"index.add", [], "native/index.add", .compute (.primitive .indexAdd), []⟩,
    ⟨"bool.and", [], "arkworks/bool.and", .calculate .booleanAnd, []⟩,
    ⟨"bool.or", [], "arkworks/bool.or", .calculate .booleanOr, []⟩,
    ⟨"bool.not", [], "arkworks/bool.not", .compute .booleanNot, []⟩,
    ⟨"resource_unit.create", [], "logical/resource_unit.create", .custody .create, []⟩,
    ⟨"resource_unit.pass", [], "logical/resource_unit.pass", .custody .pass, []⟩,
    ⟨"resource_unit.consume", [], "logical/resource_unit.consume", .custody .consume, []⟩,
    ⟨"vector.empty", [scalarField], "arkworks/vector.empty", .compute (.primitive (.vectorEmpty scalarField)), []⟩,
    ⟨"vector.append", [scalarField], "arkworks/vector.append",
      .compute (.primitive (.vectorAppend scalarField)), []⟩,
    ⟨"vector.length", [scalarField], "arkworks/vector.length",
      .compute (.primitive (.vectorLength scalarField)), []⟩,
    ⟨"vector.split", [scalarField], "arkworks/vector.split", .compute (.primitive (.vectorSplit scalarField)), []⟩,
    ⟨"vector.sum", [scalarField], "arkworks/vector.sum", .compute (.primitive (.vectorSum scalarField)), []⟩,
    ⟨"vector.get", [scalarField], "arkworks/vector.get", .calculate (.boundedAt scalarField), []⟩,
    ⟨"vector.add", [scalarField], "arkworks/vector.add", .compute (.vectorAdd scalarField), []⟩,
    ⟨"vector.sub", [scalarField], "arkworks/vector.sub", .compute (.vectorSubtract scalarField), []⟩,
    ⟨"vector.scale", [scalarField], "arkworks/vector.scale", .compute (.vectorScale scalarField), []⟩,
    ⟨"control.require", [], "arkworks/control.require", .compute .require, []⟩,
    ⟨"numerical.map", [scalarField], "arkworks/numerical.map",
      .numerical .map scalarField scalarCharacteristic, []⟩,
    ⟨"numerical.sum", [scalarField], "arkworks/numerical.sum",
      .numerical .sum scalarField scalarCharacteristic, []⟩,
    ⟨"numerical.product", [scalarField], "arkworks/numerical.product",
      .numerical .product scalarField scalarCharacteristic, []⟩]
  representations := [
    (.data (.group "bls12-381.g1"), "arkworks.g1/0"),
    (.data (.field scalarField), "arkworks.fr/0"),
    (.data (.vector scalarField), "arkworks.fr-vector/0"),
    (.data .index, "native.index/0"),
    (.data .boolean, "native.bool/0"),
    (.transcript nativeSuite, "host.resource/0")]
  custodyRepresentations := ["logical.resource_unit/0"]

end Zkc.Executable
