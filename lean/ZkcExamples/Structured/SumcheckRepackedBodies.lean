module

public import ZkcExamples.Structured.SumcheckReduceBodies

@[expose] public section

/-! The repacked Reduction root. Its signature and port order differ from the
retained Reduction root; it applies the same Reduce declaration and helpers. -/
namespace ZkcExamples.Structured.SumcheckRepackedBodies
open Zkc.Source Zkc.Source.Structured SumcheckReduceBodies

/-- The exported root keeps the original declaration symbol even though its
ports moved: a declaration name identifies neither the ABI nor a logical instance. -/
def runSignature : ProtocolSignature where
  name := "zkl_cf3586ba980b617860654dacf2506dd277a78d1dcf5b84bcc6376225e7fe4f45"
  roles := ["role00000000", "role00000001"]
  inputs := [.field "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .service "random.bls12-381.fr/0"]
  outputs := [.vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"]
  inputScopes := [[1], [0, 1], [0], [0], [1]]
  outputScopes := [[1], [1], [0], [0]]

def runBody : Region protocolDialect [.field "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .service "random.bls12-381.fr/0"] [.vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.localCall tableHelper rfl 0 "s1") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there .here))) (.cons .here .nil))) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.protocolApply reduceSignature [0, 1] "s3") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke valuesHelper) rfl) (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .ret (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here (.cons (.there .here) .nil))))

end ZkcExamples.Structured.SumcheckRepackedBodies
