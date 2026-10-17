module

public import ZkcExamples.Structured.MapPrefixBodies
public import ZkcExamples.Structured.PrimitiveLibrary
public import Zkc.Source.Structured.PrimitiveLaws

@[expose] public section

/-! Shared typed views of the Sumcheck local helpers. Each source client must
associate these complete trees and signatures with its own imported definitions. -/
namespace ZkcExamples.Structured.SumcheckHelperBodies
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured
open PrimitiveLibrary MapPrefixBodies

abbrev sumsHelper : Helper := ⟨"zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", .local, [vector, .index, .index], [scalar, scalar]⟩
abbrev checkTableHelper : Helper := ⟨"zkl_3b67bb5451d0deeed7ab9379c12e7c154a5c16946b7db9b65bc0d4be6b613f1d", .local, [vector, vector, scalar], [.boolean]⟩
abbrev checkHelper : Helper := ⟨"zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", .local, [vector, vector, scalar], [.boolean]⟩

abbrev emptyHelper : Helper := ⟨"zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46", .local, [], [vector]⟩
abbrev appendHelper : Helper := ⟨"zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58", .local, [vector, scalar], [vector]⟩

def emptyBody : Region dialect [] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .ret (.cons .here .nil)

def appendBody : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

def sumsBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke halvesHelper) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons (.there (.there .here)) .nil) .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))

def checkTableBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean] :=
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.invoke tableHelper) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.invoke prefixHelper) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.invoke valuesRealizationHelper) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.exec (.fieldEqual "bls12-381.fr")) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil)) .nil <|
  .ret (.cons .here .nil)

def checkTrueBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean] :=
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.invoke checkTableHelper) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

def checkFalseBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean] :=
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.booleanConstant false) .nil .nil <|
  .ret (.cons .here .nil)

def checkBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean] :=
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.invoke shapeHelper) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.branch [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))) (.cons checkTrueBody (.cons checkFalseBody .nil)) <|
  .ret (.cons .here .nil)


end ZkcExamples.Structured.SumcheckHelperBodies
