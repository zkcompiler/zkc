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
def program : String := "sha256:e0db02fa6103cc3968350491b21e1c65097c91eb942dce990d08fdc993d5e4e5"

/-- The local function `_calculation_2`. -/
def function0 : Function :=
  ⟨"_calculation_2", [("v0", ⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩), ("v1", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v2", ⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩), ("v3", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v4", ⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩)], [⟨.data .boolean, "native.bool/0"⟩], [
    .operation "lc_11_computation_6_kernel_1_0" "_numerical_binding_0" [] ["v0", "v1"] ["v5"],
    .operation "lc_11_computation_6_kernel_1_1" "_numerical_binding_0" [] ["v2", "v3"] ["v6"],
    .operation "lc_11_computation_6_kernel_1_2" "_numerical_binding_4" [] ["v4", "v6"] ["v7"],
    .operation "lc_11_computation_6_kernel_1_3" "_numerical_binding_3" [] ["v5", "v7"] ["v8"],
    .ret ["v8"]]⟩

/-- The local function `_transcript_0`. -/
def function1 : Function :=
  ⟨"_transcript_0", [("v0", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v1", ⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v2"],
    .operation "lc_10_transition" "_transcript_2" [.template ⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", [], ["message", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_636f6d6d69746d656e74_0", "label_636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩] ["v0", "v1", "v2"] ["v3"],
    .ret ["v3"]]⟩

/-- The local function `_transcript_3`. -/
def function2 : Function :=
  ⟨"_transcript_3", [("v0", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v1"],
    .operation "lc_10_transition" "_transcript_4" [.template ⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", [], ["query", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_6368616c6c656e6765", "input_4", "random.bls12-381.fr/0", "draw", "role00000001"]⟩] ["v0", "v1"] ["v2", "v3"],
    .ret ["v2", "v3"]]⟩

/-- The local function `_transcript_5`. -/
def function3 : Function :=
  ⟨"_transcript_5", [("v0", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v1", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v2"],
    .operation "lc_10_transition" "_transcript_6" [.template ⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", [], ["message", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩] ["v0", "v1", "v2"] ["v3"],
    .ret ["v3"]]⟩

/-- The local function `_transcript_7`. -/
def function4 : Function :=
  ⟨"_transcript_7", [("v0", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v1", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v2"],
    .operation "lc_10_transition" "_transcript_6" [.template ⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", [], ["message", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_726573706f6e7365_0", "label_726573706f6e7365_0", "role00000000", "role00000001"]⟩] ["v0", "v1", "v2"] ["v3"],
    .ret ["v3"]]⟩

def validator : Validator where
  entry := "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad"
  role := "role00000001"
  symbol := "_math_1"
  inputs := [("v12", ⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩), ("v13", ⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩), ("v14", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩)]
  results := [⟨.data .boolean, "native.bool/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩]
  body := [
    .receive "label_636f6d6d69746d656e74_0" "label_636f6d6d69746d656e74_0" "role00000000" "v15" ⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩,
    .call "_transcript_12" "_transcript_0" ["v14", "v15"] ["v16"],
    .call "_transcript_13" "_transcript_3" ["v16"] ["v17", "v18"],
    .call "_transcript_14" "_transcript_5" ["v18", "v17"] ["v19"],
    .receive "label_726573706f6e7365_0" "label_726573706f6e7365_0" "role00000000" "v20" ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩,
    .call "_transcript_15" "_transcript_7" ["v19", "v20"] ["v21"],
    .call "calculation_0" "_calculation_2" ["v12", "v20", "v13", "v17", "v15"] ["v22"],
    .ret ["v22", "v21"]]
  functions := [function0, function1, function2, function3, function4]
  bindings := [
    ⟨"_transcript_6", "transcript.native.indexed.observe.data", ["merlin3.bls12-381.fr64be/0", "field:bls12-381.fr"], "arkworks/transcript.native.indexed.observe.data", [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩]⟩,
    ⟨"_transcript_4", "transcript.native.indexed.challenge", ["merlin3.bls12-381.fr64be/0"], "arkworks/transcript.native.indexed.challenge", []⟩,
    ⟨"_transcript_2", "transcript.native.indexed.observe.data", ["merlin3.bls12-381.fr64be/0", "group:bls12-381.g1"], "arkworks/transcript.native.indexed.observe.data", [⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩]⟩,
    ⟨"_transcript_1", "indices.empty", [], "native/indices.empty", []⟩,
    ⟨"_numerical_binding_0", "curve.scale", ["bls12-381.g1"], "arkworks/curve.scale", []⟩,
    ⟨"_numerical_binding_3", "curve.equal", ["bls12-381.g1"], "arkworks/curve.equal", []⟩,
    ⟨"_numerical_binding_4", "curve.add", ["bls12-381.g1"], "arkworks/curve.add", []⟩]

end ZkcExamples.Executable.SchnorrProofProgramData
