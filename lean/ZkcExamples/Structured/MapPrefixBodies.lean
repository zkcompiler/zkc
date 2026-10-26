module

public import ZkcExamples.Structured.MapFirstBodies

@[expose] public section

/-! Transparent typed views of the retained native First/Prefix bodies.
Actual-source equality and admission are proved in the corresponding Views module. -/
namespace ZkcExamples.Structured.MapPrefixBodies
open Zkc.Source Zkc.Source.Structured

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

abbrev valuesRealizationHelper := MapFirstBodies.valuesRealizationHelper
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
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev stepHelper : Helper := ⟨"zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

def stepBody : Region dialect [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨"zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev firstHelper := MapFirstBodies.firstHelper
abbrev firstBody := MapFirstBodies.firstBody

abbrev halvesHelper := MapFirstBodies.halvesHelper
abbrev halvesBody := MapFirstBodies.halvesBody

abbrev interpolateHelper := MapFirstBodies.interpolateHelper
abbrev interpolateBody := MapFirstBodies.interpolateBody

abbrev foldWrapperHelper : Helper := ⟨"zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

def foldWrapperBody : Region dialect [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"_finite_admission_5", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev foldStepHelper : Helper := ⟨"finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

def foldStepBody : Region dialect [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr", .vector "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke ⟨"zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev foldHelper : Helper := ⟨"_finite_admission_5", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩

abbrev foldSpec : FoldSpec :=
  ⟨DomainSpec.elements "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain" [.vector "bls12-381.fr"] (.vector "bls12-381.fr") .here,
    [.vector "bls12-381.fr", .index, .index], [], "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", "", .local⟩

def foldBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.fold foldSpec) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev valuesHelper := MapFirstBodies.valuesHelper
abbrev valuesBody := MapFirstBodies.valuesBody

abbrev variablesHelper := MapFirstBodies.variablesHelper
abbrev variablesBody := MapFirstBodies.variablesBody

abbrev widthHelper := MapFirstBodies.widthHelper
abbrev widthBody := MapFirstBodies.widthBody

end ZkcExamples.Structured.MapPrefixBodies
