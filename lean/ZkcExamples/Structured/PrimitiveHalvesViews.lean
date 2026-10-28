module

public import ZkcExamples.Structured.MultilinearSourceBindings

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
  MultilinearBodies.tableBody "bls12-381.fr" (MultilinearSourceBindings.common)

abbrev shapeHelper : Helper := ⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [.vector "bls12-381.fr", .index, .index], [.boolean]⟩

set_option smartUnfolding true in
def shapeBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.boolean] :=
  MultilinearBodies.shapeBody "bls12-381.fr" (MultilinearSourceBindings.common)

abbrev lessHelper : Helper := ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩

set_option smartUnfolding true in
def lessBody : Region dialect [.index, .index] [.boolean] :=
  MultilinearBodies.lessBody "bls12-381.fr" (MultilinearSourceBindings.common)

abbrev rowsHelper : Helper := ⟨"s3h7a6b6311h6d756c74696c696e6561724h726f7773", .local, [.index], [.index]⟩

set_option smartUnfolding true in
def rowsBody : Region dialect [.index] [.index] :=
  MultilinearBodies.rowsBody "bls12-381.fr" (MultilinearSourceBindings.common)

abbrev halvesHelper : Helper := ⟨"zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .vector "bls12-381.fr"]⟩

set_option smartUnfolding true in
def halvesBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr", .vector "bls12-381.fr"] :=
  MultilinearBodies.halvesBody "bls12-381.fr" (MultilinearSourceBindings.common)

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
