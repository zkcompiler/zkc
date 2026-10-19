module

public import ZkcExamples.Structured.PrimitiveHalvesData
public import Zkc.Source.Structured.UnitViews
public import Zkc.Source.Structured.ClosedProfile

@[expose] public section

/-! Transparent typed views of complete retained original-stage constructor data.
Every view has an exact raw-body equality; the whole snapshot is kernel-admitted.
The original exporter and constructor renderer remain executable trust boundaries. -/

namespace ZkcExamples.Structured.PrimitiveHalvesViews
open Zkc.Source Zkc.Source.Structured
set_option smartUnfolding false

set_option smartUnfolding true in
def entryBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr", .vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨"zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev tableHelper : Helper := ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩

set_option smartUnfolding true in
def tableBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [.vector "bls12-381.fr", .index, .index], [.boolean]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s1_reject") .nil .nil (.stop .reject)) .nil)) <|
  .ret (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))

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

abbrev lessHelper : Helper := ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩

set_option smartUnfolding true in
def lessBody : Region dialect [.index, .index] [.boolean] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexLess)) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

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

abbrev halvesHelper : Helper := ⟨"zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .vector "bls12-381.fr"]⟩

set_option smartUnfolding true in
def halvesBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr", .vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩) (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s3_reject") .nil .nil (.stop .reject)) .nil)) <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there .here)) .nil) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

def protocolSignature : ProtocolSignature where
  name := "s18h7072696d69746976655f6578616d706c657311h5461626c6548616c766573"
  roles := ["role00000000"]
  inputs := [.vector "bls12-381.fr", .index, .index]
  outputs := [.vector "bls12-381.fr", .vector "bls12-381.fr"]
  inputScopes := [[0], [0], [0]]
  outputScopes := [[0], [0]]

set_option smartUnfolding true in
def protocolBody : Region protocolDialect [.vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr", .vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩ rfl 0 "s0") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.localCall ⟨"zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .vector "bls12-381.fr"]⟩ rfl 0 "s2") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

structured_closed_views PrimitiveHalvesData.snapshot
  helpers [table, shape, less, rows, halves]
  protocols [protocol]
  root entryBody

end ZkcExamples.Structured.PrimitiveHalvesViews
