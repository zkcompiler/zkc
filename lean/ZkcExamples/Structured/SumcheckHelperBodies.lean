module

public import ZkcExamples.Structured.MultilinearSourceBindings

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
abbrev checkTableHelper : Helper := ⟨"zkl_967e003dd39c9e1730d1e9e543081e08e351228ff07f85fb14e1e88dbded8a99", .local, [vector, vector, scalar], [.boolean]⟩
abbrev checkHelper : Helper := ⟨"zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", .local, [vector, vector, scalar], [.boolean]⟩

abbrev emptyHelper : Helper := ⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [vector]⟩
abbrev appendHelper : Helper := ⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [vector, scalar], [vector]⟩

def emptyBody : Region dialect [] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .ret (.cons .here .nil)

def appendBody : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

def sumsBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  MultilinearBodies.sumsBody "bls12-381.fr" (MultilinearSourceBindings.common)

def checkTableBody (bindings : MultilinearPrefixBodies.Bindings := MapPrefixBodies.bindings) : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean] :=
  MultilinearBodies.checkTableBody "bls12-381.fr" ({ MultilinearSourceBindings.common with valuesRealization := bindings.values })

def checkTrueBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean] :=
  MultilinearBodies.checkTrueBody "bls12-381.fr" (MultilinearSourceBindings.common)

def checkFalseBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean] :=
  MultilinearBodies.checkFalseBody "bls12-381.fr" (MultilinearSourceBindings.common)

def checkBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean] :=
  MultilinearBodies.checkBody "bls12-381.fr" (MultilinearSourceBindings.common)


end ZkcExamples.Structured.SumcheckHelperBodies
