module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal full signatures and typed bodies for the complete application source.
These candidates acquire source authority only through `kernel_admission` in
`ApplicationViews`; their ABI never depends on reducing the whole checker. -/
namespace ZkcExamples.Structured.ApplicationBodies
open Zkc.Source Zkc.Source.Structured

abbrev fieldType : Ty := .field "bls12-381.fr"
abbrev pairTypes : List Ty := [fieldType, fieldType]
abbrev roles : List String := ["role00000000", "role00000001"]

def stepSignature : ProtocolSignature where
  name := "zkl_f39ed99e9ca380a5675dcf66974ff8ba662cf37425e869e7bb6fe866ef82d479"
  roles := roles
  inputs := pairTypes
  outputs := pairTypes
  inputScopes := [[0, 1], [0, 1]]
  outputScopes := [[0], [1]]

def observeSignature : ProtocolSignature where
  name := "s6h73616d706c657h4f627365727665"
  roles := roles
  inputs := []
  outputs := []
  inputScopes := []
  outputScopes := []

def segmentSignature : ProtocolSignature where
  name := "zkl_1029dffd30597bc82f81c8cfdb80d2ccd06b8fc9301525510f4cb8960568b1b0"
  roles := roles
  inputs := pairTypes
  outputs := pairTypes
  inputScopes := [[0, 1], [0, 1]]
  outputScopes := [[0], [1]]

def runSignature : ProtocolSignature where
  name := "s6h73616d706c653h52756e"
  roles := roles
  inputs := pairTypes
  outputs := pairTypes
  inputScopes := [[0, 1], [0, 1]]
  outputScopes := [[0], [1]]

def stepBody : Region protocolDialect pairTypes pairTypes :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl)
    (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl)
    (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))

def observeBody : Region protocolDialect [] [] := .ret .nil

def segmentBody : Region protocolDialect pairTypes pairTypes :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.protocolApply stepSignature [1, 0] "s0")
    (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.protocolApply observeSignature [0, 1] "s3") .nil .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))

def runBody : Region protocolDialect pairTypes pairTypes :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.protocolApply segmentSignature [0, 1] "s0")
    (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

end ZkcExamples.Structured.ApplicationBodies
