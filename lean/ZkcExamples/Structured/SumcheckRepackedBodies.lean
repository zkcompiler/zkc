module

public import ZkcExamples.Structured.SumcheckReduceBodies

@[expose] public section

/-! Exact caller ABI and body printed from SumcheckRepackedData. -/
namespace ZkcExamples.Structured.SumcheckRepackedBodies
open Zkc.Source Zkc.Source.Structured SumcheckReduceBodies

def runSignature : ProtocolSignature where
  name := "zkl_cf3586ba980b617860654dacf2506dd277a78d1dcf5b84bcc6376225e7fe4f45"
  roles := ["role00000000", "role00000001"]
  inputs := [(.field "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.service "random.bls12-381.fr/0")]
  outputs := [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")]
  inputScopes := [[1], [0, 1], [0], [0], [1]]
  outputScopes := [[1], [1], [0], [0]]

def runBody : Region protocolDialect runSignature.inputs runSignature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper) rfl 0 "s1") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there .here))) (.cons .here .nil))) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", .local, [(.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s3") (.cons (.there (.there (.there (.there .here)))) .nil) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.protocolApply (⟨ "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", ["role00000000", "role00000001"], [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [[0], [0], [0], [1], [1], [0, 1], [1]], [[0], [0], [0], [0], [1], [1]] ⟩ : ProtocolSignature) [0, 1] "s5") (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil))))))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke (⟨ "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) rfl) (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .ret (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here (.cons (.there .here) .nil))))

end ZkcExamples.Structured.SumcheckRepackedBodies
