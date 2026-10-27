module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal typed bodies printed from the admitted snapshot of
`Tests.Generated.CompositeReuseData`. -/
namespace Tests.Generated.CompositeReuseBodies
open Zkc.Source Zkc.Source.Structured

def shiftSignature : ProtocolSignature where
  name := "s9h636f6d706f736974655h5368696674"
  roles := ["role00000000", "role00000001"]
  inputs := [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), .boolean]
  outputs := [(.field "bls12-381.fr")]
  inputScopes := [[0], [0], [0], [0]]
  outputScopes := [[0]]

def shiftBody : Region protocolDialect shiftSignature.inputs shiftSignature.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.guard 0 "s0") (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
  .ret (.cons .here .nil)

def outerSignature : ProtocolSignature where
  name := "s9h636f6d706f736974655h4f75746572"
  roles := ["role00000000", "role00000001"]
  inputs := [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), .boolean]
  outputs := [(.field "bls12-381.fr")]
  inputScopes := [[1], [1], [1], [1], [1]]
  outputScopes := [[1]]

def outerBody : Region protocolDialect outerSignature.inputs outerSignature.outputs :=
  .letOp (.mark "label_6669727374") .nil .nil <|
  .letOp (.protocolApply (⟨ "s9h636f6d706f736974655h5368696674", ["role00000000", "role00000001"], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), .boolean], [(.field "bls12-381.fr")], [[0], [0], [0], [0]], [[0]] ⟩ : ProtocolSignature) [1, 0] "label_6669727374") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) .nil)))) .nil <|
  .letOp (.mark "label_7365636f6e64") .nil .nil <|
  .letOp (.protocolApply (⟨ "s9h636f6d706f736974655h5368696674", ["role00000000", "role00000001"], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), .boolean], [(.field "bls12-381.fr")], [[0], [0], [0], [0]], [[0]] ⟩ : ProtocolSignature) [1, 0] "label_7365636f6e64") (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))) .nil <|
  .ret (.cons .here .nil)

def thirdSignature : ProtocolSignature where
  name := "s9h636f6d706f736974655h5468697264"
  roles := ["role00000000", "role00000001"]
  inputs := [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), .boolean]
  outputs := [(.field "bls12-381.fr")]
  inputScopes := [[1], [1], [1], [1], [1], [1]]
  outputScopes := [[1]]

def thirdBody : Region protocolDialect thirdSignature.inputs thirdSignature.outputs :=
  .letOp (.mark "label_636f6d706f73697465") .nil .nil <|
  .letOp (.protocolApply (⟨ "s9h636f6d706f736974655h4f75746572", ["role00000000", "role00000001"], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), .boolean], [(.field "bls12-381.fr")], [[1], [1], [1], [1], [1]], [[1]] ⟩ : ProtocolSignature) [0, 1] "label_636f6d706f73697465") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))))) .nil <|
  .letOp (.mark "label_6c617374") .nil .nil <|
  .letOp (.protocolApply (⟨ "s9h636f6d706f736974655h5368696674", ["role00000000", "role00000001"], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), .boolean], [(.field "bls12-381.fr")], [[0], [0], [0], [0]], [[0]] ⟩ : ProtocolSignature) [1, 0] "label_6c617374") (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) .nil <|
  .ret (.cons .here .nil)

end Tests.Generated.CompositeReuseBodies
