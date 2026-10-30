module

public import Zkc.Protocols.Multilinear.Source.CollectBodies
public import Zkc.Protocols.Multilinear.Source.PrimitiveShapeBodies
public import Zkc.Protocols.Multilinear.Source.PrimitiveTableBodies
public import Zkc.Protocols.Multilinear.Source.PrimitiveHalvesBodies

@[expose] public section

/-! Transparent typed views of the retained native First/Prefix bodies.
Actual-source equality and admission are proved in the corresponding Views module. -/
namespace ZkcExamples.Structured.MapFirstBodies
open Zkc.Source Zkc.Source.Structured

def bindings : MultilinearCollectBodies.Bindings where
  collection := "_finite_admission_3"
  domain := "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain"
  callback := "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body"
  computation := "_mathematical_admission_4"

abbrev mapHelper := MultilinearCollectBodies.mapHelper bindings

abbrev interpolateRealizationHelper := MultilinearCollectBodies.interpolateRealizationHelper bindings

abbrev interpolateRealizationBody := MultilinearCollectBodies.interpolateRealizationBody bindings

abbrev mapCallbackHelper := MultilinearCollectBodies.mapCallbackHelper bindings

abbrev mapCallbackBody := MultilinearCollectBodies.mapCallbackBody bindings

abbrev mapSpec := MultilinearCollectBodies.collectSpec bindings

abbrev mapBody := MultilinearCollectBodies.mapBody bindings

abbrev widthRealizationHelper : Helper := ⟨"_mathematical_admission_2", .local, [.vector "bls12-381.fr", .index, .index], [.index]⟩

def widthRealizationBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.index] :=
  .letOp (.invoke ⟨"zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", .math, [.vector "bls12-381.fr", .index, .index], [.index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev variablesRealizationHelper : Helper := ⟨"_mathematical_admission_1", .local, [.vector "bls12-381.fr", .index, .index], [.index]⟩

def variablesRealizationBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.index] :=
  .letOp (.invoke ⟨"zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", .math, [.vector "bls12-381.fr", .index, .index], [.index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev valuesRealizationHelper : Helper := ⟨"_mathematical_admission_0", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩

def valuesRealizationBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr"] :=
  .letOp (.invoke ⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)


def entryBody : Region dialect [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"s12h6d61705f6578616d706c65735h6669727374", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

def protocolBody : Region protocolDialect [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall ⟨"s12h6d61705f6578616d706c65735h6669727374", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩ rfl 0 "s0") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev wrapperHelper : Helper := ⟨"s12h6d61705f6578616d706c65735h6669727374", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

def wrapperBody : Region dialect [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke ⟨"zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.invoke ⟨"_mathematical_admission_0", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke ⟨"_mathematical_admission_1", .local, [.vector "bls12-381.fr", .index, .index], [.index]⟩) (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.invoke ⟨"_mathematical_admission_2", .local, [.vector "bls12-381.fr", .index, .index], [.index]⟩) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil))) .nil <|
  .ret (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil)))

abbrev tableHelper : Helper := ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩

abbrev tableBody := PrimitiveTableViews.tableBody

abbrev shapeHelper : Helper := ⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [.vector "bls12-381.fr", .index, .index], [.boolean]⟩

abbrev shapeBody := PrimitiveShapeViews.shapeBody

abbrev lessHelper : Helper := ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩

abbrev lessBody := PrimitiveShapeViews.lessBody

abbrev rowsHelper : Helper := ⟨"s3h7a6b6311h6d756c74696c696e6561724h726f7773", .local, [.index], [.index]⟩

abbrev rowsBody := PrimitiveShapeViews.rowsBody

abbrev firstHelper : Helper := ⟨"zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

abbrev firstBody := MultilinearCollectBodies.firstBody bindings

abbrev halvesHelper : Helper := ⟨"zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .vector "bls12-381.fr"]⟩

abbrev halvesBody := PrimitiveHalvesViews.halvesBody

abbrev interpolateHelper : Helper := ⟨"zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", .math, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def interpolateBody : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev valuesHelper : Helper := ⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩

def valuesBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr"] :=
  .ret (.cons .here .nil)

abbrev variablesHelper : Helper := ⟨"zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", .math, [.vector "bls12-381.fr", .index, .index], [.index]⟩

def variablesBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.index] :=
  .ret (.cons (.there .here) .nil)

abbrev widthHelper : Helper := ⟨"zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", .math, [.vector "bls12-381.fr", .index, .index], [.index]⟩

def widthBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.index] :=
  .ret (.cons (.there (.there .here)) .nil)

end ZkcExamples.Structured.MapFirstBodies
