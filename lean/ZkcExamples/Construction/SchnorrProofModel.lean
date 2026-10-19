module

public import ZkcExamples.NativePrograms.Schnorr

@[expose] public section

/-! The model of the compiled Schnorr proof Entry's original validator.

The common-source Schnorr program of the example fixes the wiring of the
interactive Schnorr verifier: its producer and the commitment, challenge,
delivery and response sites. The generated `SchnorrProof.process_equation`
states that the admitted original validator is that verifier, by computation.
-/

namespace ZkcExamples.Construction.SchnorrProof

/-- The wiring of the interactive Schnorr verifier the original validator is. -/
abbrev wiring := ZkcExamples.NativePrograms.Schnorr.wiring

end ZkcExamples.Construction.SchnorrProof
