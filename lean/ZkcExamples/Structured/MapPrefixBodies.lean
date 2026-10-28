module

public import ZkcExamples.Structured.MultilinearSourceBindings

public import ZkcExamples.Structured.MultilinearPrefixBodies

@[expose] public section

/-! Transparent typed views of the retained native First/Prefix bodies.
Actual-source equality and admission are proved in the corresponding Views module. -/
namespace ZkcExamples.Structured.MapPrefixBodies
open Zkc.Source Zkc.Source.Structured

abbrev bindings : MultilinearPrefixBodies.Bindings :=
  ⟨"_finite_admission_5", "_mathematical_admission_0"⟩

abbrev mapHelper := MapFirstBodies.mapHelper
abbrev mapBody := MapFirstBodies.mapBody

abbrev interpolateRealizationHelper := MapFirstBodies.interpolateRealizationHelper
abbrev interpolateRealizationBody := MapFirstBodies.interpolateRealizationBody
abbrev mapCallbackHelper := MapFirstBodies.mapCallbackHelper
abbrev mapCallbackBody := MapFirstBodies.mapCallbackBody

abbrev widthRealizationHelper := MapFirstBodies.widthRealizationHelper
abbrev widthRealizationBody := MapFirstBodies.widthRealizationBody

abbrev variablesRealizationHelper := MapFirstBodies.variablesRealizationHelper
abbrev variablesRealizationBody := MapFirstBodies.variablesRealizationBody

abbrev valuesRealizationHelper := MultilinearPrefixBodies.valuesRealizationHelper bindings.values
abbrev valuesRealizationBody := MapFirstBodies.valuesRealizationBody


def entryBody : Region dialect [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"s12h6d61705f6578616d706c65736h707265666978", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

def protocolBody : Region protocolDialect [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall ⟨"s12h6d61705f6578616d706c65736h707265666978", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩ rfl 0 "s0") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev wrapperHelper : Helper := ⟨"s12h6d61705f6578616d706c65736h707265666978", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

def wrapperBody : Region dialect [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke ⟨"zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.invoke ⟨"_mathematical_admission_0", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke ⟨"_mathematical_admission_1", .local, [.vector "bls12-381.fr", .index, .index], [.index]⟩) (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.invoke ⟨"_mathematical_admission_2", .local, [.vector "bls12-381.fr", .index, .index], [.index]⟩) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil))) .nil <|
  .ret (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil)))

abbrev tableHelper := MapFirstBodies.tableHelper
abbrev tableBody := MapFirstBodies.tableBody

abbrev shapeHelper := MapFirstBodies.shapeHelper
abbrev shapeBody := MapFirstBodies.shapeBody

abbrev lessHelper := MapFirstBodies.lessHelper
abbrev lessBody := MapFirstBodies.lessBody

abbrev rowsHelper := MapFirstBodies.rowsHelper
abbrev rowsBody := MapFirstBodies.rowsBody

abbrev prefixHelper : Helper := ⟨"zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

def prefixBody : Region dialect [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  MultilinearBodies.prefixBody "bls12-381.fr" (MultilinearSourceBindings.common)

abbrev stepHelper : Helper := ⟨"zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

def stepBody : Region dialect [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  MultilinearBodies.stepBody "bls12-381.fr" (MultilinearSourceBindings.common)

abbrev firstHelper := MapFirstBodies.firstHelper
abbrev firstBody := MapFirstBodies.firstBody

abbrev halvesHelper := MapFirstBodies.halvesHelper
abbrev halvesBody := MapFirstBodies.halvesBody

abbrev interpolateHelper := MapFirstBodies.interpolateHelper
abbrev interpolateBody := MapFirstBodies.interpolateBody

abbrev foldWrapperHelper := MultilinearPrefixBodies.foldWrapperHelper

abbrev foldWrapperBody := MultilinearPrefixBodies.foldWrapperBody bindings.fold

abbrev foldStepHelper : Helper := ⟨"finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

def foldStepBody : Region dialect [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr", .vector "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  MultilinearBodies.foldStepBody "bls12-381.fr" (MultilinearSourceBindings.common)

abbrev foldHelper := MultilinearPrefixBodies.foldHelper bindings.fold

abbrev foldSpec := MultilinearPrefixBodies.foldSpec

abbrev foldBody := MultilinearPrefixBodies.foldBody

abbrev valuesHelper := MapFirstBodies.valuesHelper
abbrev valuesBody := MapFirstBodies.valuesBody

abbrev variablesHelper := MapFirstBodies.variablesHelper
abbrev variablesBody := MapFirstBodies.variablesBody

abbrev widthHelper := MapFirstBodies.widthHelper
abbrev widthBody := MapFirstBodies.widthBody

end ZkcExamples.Structured.MapPrefixBodies
