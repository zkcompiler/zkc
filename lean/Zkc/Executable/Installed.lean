module

public import Zkc.Executable.Execution

@[expose] public section

/-! The installed vocabulary of the native BLS12-381 proof deployments.

Each row assigns a meaning to an exact contract, static arguments and installed
implementation; each representation row admits a value sort at an installed
representation. These rows are assumptions about native code, not theorems:
the arkworks kernels compute BLS12-381 scalar-field and G1 operations, the
index kernel builds the empty coordinate vector, and the Merlin transcript
kernels absorb canonical encodings of their occurrence and value and derive a
scalar challenge, which the ideal transcript model idealizes. A row absent from
this table makes the lowering rule refuse.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source

/-- The native Fiat–Shamir suite over the BLS12-381 scalar field. -/
abbrev nativeSuite : String := "merlin3.bls12-381.fr64be/0"

def installed : Vocabulary where
  operations := [
    ⟨"indices.empty", [], "native/indices.empty", .indicesEmpty⟩,
    ⟨"transcript.native.indexed.observe.data", [nativeSuite, "group:bls12-381.g1"],
      "arkworks/transcript.native.indexed.observe.data", .observe nativeSuite (.group "bls12-381.g1")⟩,
    ⟨"transcript.native.indexed.observe.data", [nativeSuite, "field:bls12-381.fr"],
      "arkworks/transcript.native.indexed.observe.data", .observe nativeSuite (.field "bls12-381.fr")⟩,
    ⟨"transcript.native.indexed.challenge", [nativeSuite],
      "arkworks/transcript.native.indexed.challenge", .challenge nativeSuite "bls12-381.fr"⟩,
    ⟨"curve.scale", ["bls12-381.g1"], "arkworks/curve.scale",
      .calculate (.groupScale "bls12-381.g1" "bls12-381.fr")⟩,
    ⟨"curve.add", ["bls12-381.g1"], "arkworks/curve.add", .calculate (.groupAdd "bls12-381.g1")⟩,
    ⟨"curve.equal", ["bls12-381.g1"], "arkworks/curve.equal", .calculate (.groupEqual "bls12-381.g1")⟩,
    ⟨"field.add", ["bls12-381.fr"], "arkworks/field.add", .calculate (.fieldAdd "bls12-381.fr")⟩,
    ⟨"field.mul", ["bls12-381.fr"], "arkworks/field.mul", .calculate (.fieldMultiply "bls12-381.fr")⟩]
  representations := [
    (.data (.group "bls12-381.g1"), "arkworks.g1/0"),
    (.data (.field "bls12-381.fr"), "arkworks.fr/0"),
    (.data .boolean, "native.bool/0"),
    (.transcript nativeSuite, "host.resource/0")]

end Zkc.Executable
