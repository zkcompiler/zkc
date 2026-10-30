module

public import Zkc.Source.Structured.ProtocolOperations
public import Zkc.Protocols.Multilinear.Source.Bindings

@[expose] public section

/-! Reusable literal multilinear helper bodies, independent of any closed Entry. -/

namespace ZkcExamples.Structured.PrimitiveHalvesViews
open Zkc.Source Zkc.Source.Structured
set_option smartUnfolding false

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

end ZkcExamples.Structured.PrimitiveHalvesViews
