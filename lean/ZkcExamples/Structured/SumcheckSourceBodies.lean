module

public import Zkc.Source.Structured.ProtocolOperations
public import ZkcExamples.Structured.SumcheckHelperBodies
public import ZkcExamples.Structured.SumcheckVerifierBodies

@[expose] public section

/-! Literal full signatures and typed bodies. The corresponding Views module
proves admission of the complete original snapshot. -/
namespace ZkcExamples.Structured.SumcheckSourceBodies
open Zkc.Source Zkc.Source.Structured

abbrev prefixBindings : MultilinearPrefixBodies.Bindings :=
  ⟨"_finite_admission_3", "_mathematical_admission_2"⟩

abbrev valuesRealizationHelper := MultilinearPrefixBodies.valuesRealizationHelper prefixBindings.values
abbrev valuesRealizationBody := MapFirstBodies.valuesRealizationBody

abbrev collectBindings : MultilinearCollectBodies.Bindings where
  collection := "_finite_admission_0"
  domain := "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain"
  callback := "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body"
  computation := "_mathematical_admission_1"

abbrev interpolateRealizationHelper := MultilinearCollectBodies.interpolateRealizationHelper collectBindings
abbrev interpolateRealizationBody := MultilinearCollectBodies.interpolateRealizationBody collectBindings
abbrev mapCallbackHelper := MultilinearCollectBodies.mapCallbackHelper collectBindings
abbrev mapCallbackBody := MultilinearCollectBodies.mapCallbackBody collectBindings

abbrev mapHelper := MultilinearCollectBodies.mapHelper collectBindings
abbrev mapBody := MultilinearCollectBodies.mapBody collectBindings
abbrev mapSpec := MultilinearCollectBodies.collectSpec collectBindings

abbrev tableHelper := MapFirstBodies.tableHelper
abbrev tableBody := MapFirstBodies.tableBody

abbrev shapeHelper := MapFirstBodies.shapeHelper
abbrev shapeBody := MapFirstBodies.shapeBody

abbrev lessHelper := MapFirstBodies.lessHelper
abbrev lessBody := MapFirstBodies.lessBody

abbrev rowsHelper := MapFirstBodies.rowsHelper
abbrev rowsBody := MapFirstBodies.rowsBody

abbrev widthHelper := MapFirstBodies.widthHelper
abbrev widthBody := MapFirstBodies.widthBody

abbrev variablesHelper := MapFirstBodies.variablesHelper
abbrev variablesBody := MapFirstBodies.variablesBody

abbrev emptyHelper := SumcheckHelperBodies.emptyHelper
abbrev emptyBody := SumcheckHelperBodies.emptyBody

abbrev sumsHelper := SumcheckHelperBodies.sumsHelper
abbrev sumsBody := SumcheckHelperBodies.sumsBody

abbrev halvesHelper := MapFirstBodies.halvesHelper
abbrev halvesBody := MapFirstBodies.halvesBody

abbrev firstHelper := MapFirstBodies.firstHelper
abbrev firstBody := MultilinearCollectBodies.firstBody collectBindings

abbrev interpolateHelper := MapFirstBodies.interpolateHelper
abbrev interpolateBody := MapFirstBodies.interpolateBody

abbrev appendHelper := SumcheckHelperBodies.appendHelper
abbrev appendBody := SumcheckHelperBodies.appendBody

abbrev checkHelper := SumcheckHelperBodies.checkHelper
abbrev checkBody := SumcheckHelperBodies.checkBody

abbrev checkTableHelper := SumcheckHelperBodies.checkTableHelper
abbrev checkTableBody := SumcheckHelperBodies.checkTableBody prefixBindings

abbrev prefixHelper := MapPrefixBodies.prefixHelper
abbrev prefixBody := MapPrefixBodies.prefixBody

abbrev stepHelper := MapPrefixBodies.stepHelper
abbrev stepBody := MapPrefixBodies.stepBody

abbrev foldWrapperHelper := MapPrefixBodies.foldWrapperHelper
abbrev foldWrapperBody := MultilinearPrefixBodies.foldWrapperBody prefixBindings.fold

abbrev foldStepHelper := MapPrefixBodies.foldStepHelper
abbrev foldStepBody := MapPrefixBodies.foldStepBody

abbrev foldHelper := MultilinearPrefixBodies.foldHelper prefixBindings.fold
abbrev foldBody := MapPrefixBodies.foldBody

abbrev valuesHelper := MapFirstBodies.valuesHelper
abbrev valuesBody := MapFirstBodies.valuesBody

def runSignature : ProtocolSignature where
  name := "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071"
  roles := ["role00000000", "role00000001"]
  inputs := [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]
  outputs := [.boolean]
  inputScopes := [[0, 1], [1], [0, 1], [1]]
  outputScopes := [[1]]

def reduceSignature : ProtocolSignature where
  name := "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5"
  roles := ["role00000000", "role00000001"]
  inputs := [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]
  outputs := [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr"]
  inputScopes := [[0], [0], [0], [1], [0, 1], [1]]
  outputScopes := [[0], [0], [0], [0], [1], [1]]

/-- The six repeat-carried slots precede the unchanged outer SSA environment. -/
abbrev repeatState : List Ty := SumcheckVerifierBodies.repeatState

/-- The retained return permutation, from the generated shared body. -/
def reduceReturn (tail : List Ty) : Region protocolDialect (repeatState ++ tail)
    reduceSignature.outputs := SumcheckVerifierBodies.reduceReturn tail

/-- The generated shared Reduce body at this unit's repeat maximum. -/
def reduceBody : Region protocolDialect [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"] [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr"] := SumcheckVerifierBodies.reduceBody 2

def runBody : Region protocolDialect [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"] [.boolean] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.localCall tableHelper rfl 0 "s1") (.cons (.there .here) (.cons (.there (.there (.there .here))) (.cons .here .nil))) .nil <|
  .letOp (.mark "label_726564756365") .nil .nil <|
  .letOp (.protocolApply reduceSignature [0, 1] "label_726564756365") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.localCall checkHelper rfl 1 "s7") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .ret (.cons .here .nil)

end ZkcExamples.Structured.SumcheckSourceBodies
