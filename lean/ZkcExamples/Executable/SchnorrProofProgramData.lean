module

public import Zkc.Executable.Program

@[expose] public section

/-! Validator data from the retained `zkc.program/0` candidate of the native
deployment. Regenerate with bridges/executable/check.py --write; the Lean rule
and its proofs are separate. The bridge checks exact regeneration against the
compiler. -/

namespace ZkcExamples.Executable.SchnorrProofProgramData
open Zkc.Construction Zkc.Executable

/-- SHA-256 of the exact `zkc.program/0` bytes this data was read from. -/
def program : String := "sha256:e4e3ceccb896909a93fbf4711b60481a2f89ccea7a5c26ecc244e10c1f59efd5"

/-- The local function `_calculation_2`. -/
def function0 : Function :=
  ⟨"_calculation_2", [("v20", ⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩), ("v21", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v22", ⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩), ("v23", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v24", ⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩)], [⟨.data .boolean, "native.bool/0"⟩], [
    .operation "lc_6_kernel_6_kernel_1_0" "_kernel_binding_0" [] ["v20", "v21"] ["v25"],
    .operation "lc_6_kernel_6_kernel_1_1" "_kernel_binding_0" [] ["v22", "v23"] ["v26"],
    .operation "lc_6_kernel_6_kernel_1_2" "_kernel_binding_4" [] ["v24", "v26"] ["v27"],
    .operation "lc_6_kernel_6_kernel_1_3" "_kernel_binding_3" [] ["v25", "v27"] ["v28"],
    .ret ["v28"]]⟩

/-- The local function `_transcript_1`. -/
def function1 : Function :=
  ⟨"_transcript_1", [("v40", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v41", ⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v42"],
    .operation "transition" "_transcript_0" [.template ⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", [], ["message", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_636f6d6d69746d656e74_0", "label_636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩] ["v40", "v41", "v42"] ["v43"],
    .ret ["v43"]]⟩

/-- The local function `_transcript_4`. -/
def function2 : Function :=
  ⟨"_transcript_4", [("v44", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v45"],
    .operation "transition" "_transcript_3" [.template ⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", [], ["query", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_6368616c6c656e6765", "input_4", "random.bls12-381.fr/0", "draw", "role00000001"]⟩] ["v44", "v45"] ["v46", "v47"],
    .ret ["v46", "v47"]]⟩

/-- The local function `_transcript_6`. -/
def function3 : Function :=
  ⟨"_transcript_6", [("v48", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v49", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v50"],
    .operation "transition" "_transcript_5" [.template ⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", [], ["message", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩] ["v48", "v49", "v50"] ["v51"],
    .ret ["v51"]]⟩

/-- The local function `_transcript_7`. -/
def function4 : Function :=
  ⟨"_transcript_7", [("v52", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v53", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v54"],
    .operation "transition" "_transcript_5" [.template ⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", [], ["message", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_726573706f6e7365_0", "label_726573706f6e7365_0", "role00000000", "role00000001"]⟩] ["v52", "v53", "v54"] ["v55"],
    .ret ["v55"]]⟩

def validator : Validator where
  entry := "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad"
  role := "role00000001"
  symbol := "_math_1"
  inputs := [("v29", ⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩), ("v30", ⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩), ("v31", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩)]
  results := [⟨.data .boolean, "native.bool/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩]
  body := [
    .receive "label_636f6d6d69746d656e74_0" "label_636f6d6d69746d656e74_0" "role00000000" "v32" ⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩,
    .call "_transcript_12" "_transcript_1" ["v31", "v32"] ["v33"],
    .call "_transcript_13" "_transcript_4" ["v33"] ["v34", "v35"],
    .call "_transcript_14" "_transcript_6" ["v35", "v34"] ["v36"],
    .receive "label_726573706f6e7365_0" "label_726573706f6e7365_0" "role00000000" "v37" ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩,
    .call "_transcript_15" "_transcript_7" ["v36", "v37"] ["v38"],
    .call "calculation_0" "_calculation_2" ["v29", "v37", "v30", "v34", "v32"] ["v39"],
    .ret ["v39", "v38"]]
  functions := [function0, function1, function2, function3, function4]
  bindings := [
    ⟨"_kernel_binding_3", "curve.equal", ["bls12-381.g1"], "arkworks/curve.equal", []⟩,
    ⟨"_kernel_binding_4", "curve.add", ["bls12-381.g1"], "arkworks/curve.add", []⟩,
    ⟨"_kernel_binding_0", "curve.scale", ["bls12-381.g1"], "arkworks/curve.scale", []⟩,
    ⟨"_transcript_5", "transcript.native.indexed.observe.data", ["merlin3.bls12-381.fr64be/0", "field:bls12-381.fr"], "arkworks/transcript.native.indexed.observe.data", [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩]⟩,
    ⟨"_transcript_3", "transcript.native.indexed.challenge", ["merlin3.bls12-381.fr64be/0"], "arkworks/transcript.native.indexed.challenge", []⟩,
    ⟨"_transcript_2", "indices.empty", [], "native/indices.empty", []⟩,
    ⟨"_transcript_0", "transcript.native.indexed.observe.data", ["merlin3.bls12-381.fr64be/0", "group:bls12-381.g1"], "arkworks/transcript.native.indexed.observe.data", [⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩]⟩]

end ZkcExamples.Executable.SchnorrProofProgramData
