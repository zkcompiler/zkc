module

public import Zkc.IR.Executable.HelperSoundness
public import Mathlib.Data.Rat.Defs

@[expose] public section

/-! The scalar codec is a genuine admission boundary for helper recipes.
These controls use actual helper walks and primitive outcomes. They do not
extend the executable ABI or assume a numerical backend implementation. -/
set_option autoImplicit false
namespace Tests.ConsumerContractCodec
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Executable

-- The historical universal argument-profile assertion has concrete counterexamples.
example : (Primitive.numerical .indicesAppend "F" "F").arguments.all dataType = false := rfl
example : (Primitive.numerical .polyCoefficients "F" "F").arguments.all dataType = false := rfl

-- Scalar inputs alone are insufficient: these outputs cannot use the selected codec.
example : (Primitive.numerical .indicesEmpty "F" "F").arguments.all dataType = true := rfl
example : primitiveDataProfile (.numerical .indicesEmpty "F" "F") = false := rfl
example : primitiveDataProfile (.numerical .polyFromCoefficients "F" "F") = false := rfl

private def scalarBody : Region dialect [.boolean] [.boolean] :=
  .letOp (.exec .booleanNot) (.cons .here .nil) .nil (.ret (.cons .here .nil))
private def vectorBody : Region dialect [.vector "F", .field "F"] [.vector "F"] :=
  .letOp (.exec (.vectorAppend "F")) (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))
private def scalarDefinition : CheckedDefinition :=
  ⟨"negate", .local, [.boolean], [.boolean], scalarBody.erase, scalarBody,
    scalarBody.elaborate_erase⟩
private def vectorDefinition : CheckedDefinition :=
  ⟨"append", .local, [.vector "F", .field "F"], [.vector "F"], vectorBody.erase, vectorBody,
    vectorBody.elaborate_erase⟩
private def booleanType : PhysicalType := ⟨.data .boolean, "bool"⟩
private def fieldType : PhysicalType := ⟨.data (.field "F"), "field"⟩
private def vectorType : PhysicalType := ⟨.data (.vector "F"), "vector"⟩
private def validator : Validator :=
  ⟨"Root", "V", "validator", [], [], [],
    [⟨"negate", [("x", booleanType)], [booleanType],
      [.operation "negation" "not" [] ["x"] ["y"], .ret ["y"]]⟩,
     ⟨"append", [("xs", vectorType), ("x", fieldType)], [vectorType],
      [.operation "extension" "append" [] ["xs", "x"] ["ys"], .ret ["ys"]]⟩],
    [⟨"not", "boolean.not", [], "logical/not", []⟩,
     ⟨"append", "vector.append", ["F"], "logical/append", []⟩]⟩
private def vocabulary : Vocabulary :=
  ⟨[⟨"boolean.not", [], "logical/not", .compute (.primitive .booleanNot), []⟩,
    ⟨"vector.append", ["F"], "logical/append", .compute (.primitive (.vectorAppend "F")), []⟩],
    [], []⟩

example : checkHelper vocabulary validator [scalarDefinition, vectorDefinition] "negate" =
    .ok () := by decide +kernel
example : checkHelper vocabulary validator [scalarDefinition, vectorDefinition] "append" =
    .ok () := by decide +kernel

-- Output-only incompatibility is refused even when the helper signature has no inputs.
private def indicesBody : Region dialect [] [.indices] :=
  .letOp (.exec (.numerical .indicesEmpty "F" "F")) .nil .nil (.ret (.cons .here .nil))
private def indicesDefinition : CheckedDefinition :=
  ⟨"emptyIndices", .local, [], [.indices], indicesBody.erase, indicesBody,
    indicesBody.elaborate_erase⟩
example : checkHelper vocabulary
    { validator with functions := [⟨"emptyIndices", [], [⟨.data .indices, "indices"⟩], []⟩] }
    [indicesDefinition] "emptyIndices" = .error (.recipe "primitive") := by decide +kernel

-- All existing scalar/vector primitive shapes still pass the codec profile.
example : ([.indexConstant 1, .indexEqual, .indexLess, .indexAdd, .indexSub, .indexMul,
    .indexDiv, .indexMod, .fieldEqual "F", .vectorEmpty "F", .vectorAppend "F",
    .vectorLength "F", .vectorSum "F", .vectorSplit "F", .vectorEqual "F",
    .binaryConstant "F" 0, .booleanNot] : List Primitive).all primitiveDataProfile = true := by
  decide +kernel
example : primitiveDataProfile (.numerical .vectorConcat "F" "F") = true := rfl

private def unsupported : List Primitive :=
  [.numerical .indicesAppend "F" "F", .numerical .polyCoefficients "F" "F",
    .numerical .indicesEmpty "F" "F", .numerical .polyFromCoefficients "F" "F"]
example : unsupported.all (fun primitive => !hasRecipe (.exec primitive)) = true := by
  decide +kernel
example : unsupported.all (fun primitive =>
    !implements (.exec primitive) (.compute (.primitive primitive))) = true := by decide +kernel
example (primitive : Primitive) (outside : primitiveDataProfile primitive = false) :
    walkOperation vocabulary validator (.exec primitive) [] ⟨[], []⟩ [] =
      .error (.recipe "primitive") := by
  simp only [walkOperation, hasRecipe, outside, Bool.false_eq_true, ite_false, operationKind]

-- Numerical checks still validate unused inputs, and retain their actual stop classes.
example : (Primitive.numerical .indicesAt "F" "F").evaluate
    (.cons [indexLimit] (.cons 0 .nil) : Values (assignment ℚ ℚ) [.indices, .index]) =
      .stopped .refused := by rfl
example : (Primitive.numerical .indicesAt "F" "F").evaluate
    (.cons [4] (.cons indexLimit .nil) : Values (assignment ℚ ℚ) [.indices, .index]) =
      .stopped .refused := by rfl
example : (Primitive.numerical .indicesAt "F" "F").evaluate
    (.cons [] (.cons 0 .nil) : Values (assignment ℚ ℚ) [.indices, .index]) =
      .stopped .refused := by rfl
example : (Primitive.numerical .indicesAt "F" "F").evaluate
    (.cons [2, 4] (.cons 1 .nil) : Values (assignment ℚ ℚ) [.indices, .index]) =
      .returned (.cons 4 .nil) := by rfl
example : (Primitive.numerical .indicesLength "F" "F").evaluate
    (.cons [indexLimit] .nil : Values (assignment ℚ ℚ) [.indices]) =
      .stopped .refused := by rfl
example : (Primitive.numerical .indicesLength "F" "F").evaluate
    (.cons [2, 4] .nil : Values (assignment ℚ ℚ) [.indices]) =
      .returned (.cons 2 .nil) := by rfl
example (xs : List ℚ) (large : ¬xs.length < indexLimit) :
    (Primitive.vectorLength "F").evaluate
      (.cons xs .nil : Values (assignment ℚ ℚ) [.vector "F"]) = .stopped .exhausted := by
  simp only [Primitive.evaluate, Primitive.evaluateOn, large, ite_false]
example : (Primitive.binaryConstant "F" 0).evaluate
    (.nil : Values (assignment ℚ ℚ) []) = .stopped .refused := rfl

-- The boundedness theorem remains universal, including codec-refused source primitives.
example (xs : List Nat) (position : Nat)
    (outs : Values (assignment ℚ ℚ) [.index])
    (returned : (Primitive.numerical .indicesAt "F" "F").evaluate
      (.cons xs (.cons position .nil)) = .returned outs) :
    ∀ value ∈ encodeValues outs, ∀ index, value = .index index → index < indexLimit :=
  primitive_bounded _ returned

#print axioms Zkc.Executable.primitive_bounded
#print axioms Zkc.Executable.resultsBounded_sound
#print axioms Zkc.Executable.checkHelper_sound
#print axioms Zkc.Executable.checkHelpers_sound
end Tests.ConsumerContractCodec
