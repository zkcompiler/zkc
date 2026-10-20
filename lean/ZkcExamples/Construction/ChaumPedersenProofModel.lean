module

public import Zkc.Protocols.Schnorr.Variants

@[expose] public section

/-! The model of the compiled Chaum–Pedersen proof Entry's original validator.

The wiring names the export's prover role, domains and the commitment,
challenge, delivery and response sites of `sigma::ChaumPedersen`. The generated
`ChaumPedersenProof.process_equation` states that the admitted original
validator is the common Chaum–Pedersen verifier, by computation.
-/

namespace ZkcExamples.Construction.ChaumPedersenProof

/-- The wiring of the Chaum–Pedersen verifier the original validator is. -/
def wiring : Zkc.Protocols.Schnorr.Variants.EqualityWiring :=
  ⟨0, "bls12-381.g1", "bls12-381.fr", "label_66697273745f636f6d6d69746d656e74_0",
    "label_7365636f6e645f636f6d6d69746d656e74_0", "label_6368616c6c656e6765", "label_64656c6976657279_0",
    "label_726573706f6e7365_0"⟩

end ZkcExamples.Construction.ChaumPedersenProof
