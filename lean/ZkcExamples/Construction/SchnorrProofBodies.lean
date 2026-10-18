module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal signatures and typed bodies of the actual `example::Proof` Entry: its
protocol root, which retains the proof statement, and its relation formula.
`SchnorrProof` proves admission of the complete original snapshot from these
bodies. -/
namespace ZkcExamples.Construction.SchnorrProofBodies
open Zkc.Source Zkc.Source.Structured

abbrev formulaHelper : Helper :=
  ⟨"zkf_6d5ed5928b9bea74d6d7736ea8056c9f06e280ffdc4dbcaf2e00bf4f639c1873", .math,
    [.group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr"], [.boolean]⟩

def formulaBody : Region dialect formulaHelper.inputs formulaHelper.outputs :=
  .letOp (.groupScale "bls12-381.g1" "bls12-381.fr") (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.groupEqual "bls12-381.g1") (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def proofSignature : ProtocolSignature where
  name := "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad"
  roles := ["role00000000", "role00000001"]
  inputs := [.group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr",
    .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"]
  outputs := [.boolean]
  inputScopes := [[0, 1], [0, 1], [0], [0], [1]]
  outputScopes := [[1]]

def proofBody : Region protocolDialect proofSignature.inputs proofSignature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.statement "zkl_dcbf81f97f37c181fef011e003f8b5e033842ddeccb04c1dea551fb7bf94978f" [.group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr"] ["role00000001", "role00000001", "role00000000"] 0) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.draw 0 "bls12-381.fr" "s0") (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "label_636f6d6d69746d656e74_0") .nil .nil <|
  .letOp (.exchange (.group "bls12-381.g1") 0 1 "label_636f6d6d69746d656e74_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.group "bls12-381.g1") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "label_6368616c6c656e6765") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil) .nil <|
  .letOp (.mark "label_64656c6976657279_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "label_726573706f6e7365_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726573706f6e7365_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupAdd "bls12-381.g1") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupEqual "bls12-381.g1") rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

end ZkcExamples.Construction.SchnorrProofBodies
