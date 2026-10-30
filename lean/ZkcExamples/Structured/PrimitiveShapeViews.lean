module

public import ZkcExamples.Structured.PrimitiveShapeData
public import Zkc.Protocols.Multilinear.Source.PrimitiveShapeBodies
public import Zkc.Source.Structured.UnitViews
public import Zkc.Source.Structured.ClosedProfile

@[expose] public section

/-! Transparent typed views of complete retained original-stage constructor data.
Every view has an exact raw-body equality; the whole snapshot is kernel-admitted.
The original exporter and constructor renderer remain executable trust boundaries. -/

namespace ZkcExamples.Structured.PrimitiveShapeViews
open Zkc.Source Zkc.Source.Structured
set_option smartUnfolding false

set_option smartUnfolding true in
def entryBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.boolean] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [.vector "bls12-381.fr", .index, .index], [.boolean]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

def protocolSignature : ProtocolSignature where
  name := "s18h7072696d69746976655f6578616d706c65735h5368617065"
  roles := ["role00000000"]
  inputs := [.vector "bls12-381.fr", .index, .index]
  outputs := [.boolean]
  inputScopes := [[0], [0], [0]]
  outputScopes := [[0]]

set_option smartUnfolding true in
def protocolBody : Region protocolDialect [.vector "bls12-381.fr", .index, .index] [.boolean] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall ⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [.vector "bls12-381.fr", .index, .index], [.boolean]⟩ rfl 0 "s0") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

structured_closed_views PrimitiveShapeData.snapshot
  helpers [shape, less, rows]
  protocols [protocol]
  root entryBody

end ZkcExamples.Structured.PrimitiveShapeViews
