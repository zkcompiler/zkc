module

public import ZkcExamples.Structured.PrimitiveTableData
public import Zkc.Protocols.Multilinear.Source.PrimitiveTableBodies
public import Zkc.Source.Structured.UnitViews
public import Zkc.Source.Structured.ClosedProfile

@[expose] public section

/-! Transparent typed views of complete retained original-stage constructor data.
Every view has an exact raw-body equality; the whole snapshot is kernel-admitted.
The original exporter and constructor renderer remain executable trust boundaries. -/

namespace ZkcExamples.Structured.PrimitiveTableViews
open Zkc.Source Zkc.Source.Structured
set_option smartUnfolding false

set_option smartUnfolding true in
def entryBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

def protocolSignature : ProtocolSignature where
  name := "s18h7072696d69746976655f6578616d706c65739h4d616b655461626c65"
  roles := ["role00000000"]
  inputs := [.vector "bls12-381.fr", .index, .index]
  outputs := [.vector "bls12-381.fr", .index, .index]
  inputScopes := [[0], [0], [0]]
  outputScopes := [[0], [0], [0]]

set_option smartUnfolding true in
def protocolBody : Region protocolDialect [.vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩ rfl 0 "s0") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

structured_closed_views PrimitiveTableData.snapshot
  helpers [table, shape, less, rows]
  protocols [protocol]
  root entryBody

end ZkcExamples.Structured.PrimitiveTableViews
