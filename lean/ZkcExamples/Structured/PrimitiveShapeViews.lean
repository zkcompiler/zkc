module

public import ZkcExamples.Structured.PrimitiveShapeData
public import Zkc.Source.Structured.Linking
public import Zkc.Source.Structured.ClosedProfile

@[expose] public section

/-! Transparent typed views of complete retained original-stage constructor data.
Every view has an exact raw-body equality; the whole snapshot is kernel-admitted.
The original exporter and constructor renderer remain executable trust boundaries. -/

namespace ZkcExamples.Structured.PrimitiveShapeViews
open Zkc.Source Zkc.Source.Structured
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option smartUnfolding false

def program : ClosedProgram :=
  (checkClosed PrimitiveShapeData.snapshot).toOption.get (by decide +kernel)
def imported : ClosedImported PrimitiveShapeData.snapshot := ⟨program, rfl⟩

set_option smartUnfolding true in
def entryBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.boolean] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [.vector "bls12-381.fr", .index, .index], [.boolean]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

theorem entry_exact : program.payload.entry.raw = entryBody.erase := rfl

def shapeDefinition : CheckedDefinition :=
  (program.payload.definitions.find? (·.name == "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655")).get (by decide +kernel)

abbrev shapeHelper : Helper := ⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [.vector "bls12-381.fr", .index, .index], [.boolean]⟩

set_option smartUnfolding true in
def shapeBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.boolean] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.branch [.index] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) .nil)) (.cons (.letOp (.mark "s4") .nil .nil <|
  .letOp (.exec (.indexConstant 64)) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.invoke ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)) (.cons (.letOp (.mark "s7") .nil .nil <|
  .letOp (.booleanConstant false) .nil .nil <|
  .ret (.cons .here .nil)) .nil)) <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.branch [.vector "bls12-381.fr", .index] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) (.cons (.letOp (.mark "s12") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s13") .nil .nil <|
  .letOp (.exec (.indexMod)) (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "s14") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s15") .nil .nil <|
  .letOp (.exec (.indexEqual)) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)) (.cons (.letOp (.mark "s17") .nil .nil <|
  .letOp (.booleanConstant false) .nil .nil <|
  .ret (.cons .here .nil)) .nil)) <|
  .letOp (.mark "s22") .nil .nil <|
  .letOp (.branch [.vector "bls12-381.fr", .index, .index] [.boolean]) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) (.cons (.letOp (.mark "s23") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s24") .nil .nil <|
  .letOp (.exec (.indexDiv)) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark "s25") .nil .nil <|
  .letOp (.invoke ⟨"s3h7a6b6311h6d756c74696c696e6561724h726f7773", .local, [.index], [.index]⟩) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "s26") .nil .nil <|
  .letOp (.exec (.indexEqual)) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)) (.cons (.letOp (.mark "s28") .nil .nil <|
  .letOp (.booleanConstant false) .nil .nil <|
  .ret (.cons .here .nil)) .nil)) <|
  .ret (.cons .here .nil)

theorem shape_exact : shapeDefinition.raw = shapeBody.erase := rfl

def lessDefinition : CheckedDefinition :=
  (program.payload.definitions.find? (·.name == "s3h7a6b637h696e64696365734h6c657373")).get (by decide +kernel)

abbrev lessHelper : Helper := ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩

set_option smartUnfolding true in
def lessBody : Region dialect [.index, .index] [.boolean] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexLess)) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

theorem less_exact : lessDefinition.raw = lessBody.erase := rfl

def rowsDefinition : CheckedDefinition :=
  (program.payload.definitions.find? (·.name == "s3h7a6b6311h6d756c74696c696e6561724h726f7773")).get (by decide +kernel)

abbrev rowsHelper : Helper := ⟨"s3h7a6b6311h6d756c74696c696e6561724h726f7773", .local, [.index], [.index]⟩

set_option smartUnfolding true in
def rowsBody : Region dialect [.index] [.index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 64)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s2_reject") .nil .nil (.stop .reject)) .nil)) <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.loop [.index] []) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil))) (.cons (.letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.indexConstant 2)) .nil .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.exec (.indexMul)) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)) .nil) <|
  .ret (.cons .here .nil)

theorem rows_exact : rowsDefinition.raw = rowsBody.erase := rfl

end ZkcExamples.Structured.PrimitiveShapeViews
