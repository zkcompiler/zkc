module

public import Zkc.Executable.Program

@[expose] public section

/-! Validator data from the retained `zkc.program/0` candidate of the native
deployment. Regenerate with bridges/executable/check.py --write; the Lean rule
and its proofs are separate. The bridge checks exact regeneration against the
compiler. -/

namespace ZkcExamples.Executable.DeferredRoundsProgramData
open Zkc.Construction Zkc.Executable

/-- SHA-256 of the exact `zkc.program/0` bytes this data was read from. -/
def program : String := "sha256:67f185bb68a56002acbe3a44eb9c151d62caa78d7995a718bb3d47f5f904f834"

/-- The local function `_calculation_1`. -/
def function0 : Function :=
  ⟨"_calculation_1", [("v3", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v4", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v5", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v6", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v7", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data .boolean, "native.bool/0"⟩], [
    .operation "lc_11_computation_6_kernel_1_0" "_numerical_binding_0" [] ["v3", "v4"] ["v8"],
    .operation "lc_11_computation_6_kernel_1_1" "_numerical_binding_0" [] ["v8", "v5"] ["v9"],
    .operation "lc_11_computation_6_kernel_1_2" "_numerical_binding_2" [] ["v9", "v6"] ["v10"],
    .operation "lc_11_computation_6_kernel_1_3" "_numerical_binding_0" [] ["v7", "v5"] ["v11"],
    .operation "lc_11_computation_6_kernel_1_4" "_numerical_binding_2" [] ["v11", "v6"] ["v12"],
    .operation "lc_11_computation_6_kernel_1_5" "_numerical_binding_1" [] ["v10", "v12"] ["v13"],
    .ret ["v13"]]⟩

/-- The local function `_transcript_0`. -/
def function1 : Function :=
  ⟨"_transcript_0", [("v14", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v15", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v16"],
    .operation "lc_10_transition" "_transcript_2" [.template ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6d30_0", "label_6d30_0", "role00000000", "role00000001"]⟩] ["v14", "v15", "v16"] ["v17"],
    .ret ["v17"]]⟩

/-- The local function `_transcript_3`. -/
def function2 : Function :=
  ⟨"_transcript_3", [("v18", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v19"],
    .operation "lc_10_transition" "_transcript_4" [.template ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["query", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6330", "input_2", "random.bls12-381.fr/0", "draw", "role00000001"]⟩] ["v18", "v19"] ["v20", "v21"],
    .ret ["v20", "v21"]]⟩

/-- The local function `_transcript_5`. -/
def function3 : Function :=
  ⟨"_transcript_5", [("v22", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v23", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v24"],
    .operation "lc_10_transition" "_transcript_2" [.template ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6430_0", "label_6430_0", "role00000001", "role00000000"]⟩] ["v22", "v23", "v24"] ["v25"],
    .ret ["v25"]]⟩

/-- The local function `_transcript_6`. -/
def function4 : Function :=
  ⟨"_transcript_6", [("v26", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v27", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v28"],
    .operation "lc_10_transition" "_transcript_2" [.template ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6d31_0", "label_6d31_0", "role00000000", "role00000001"]⟩] ["v26", "v27", "v28"] ["v29"],
    .ret ["v29"]]⟩

/-- The local function `_transcript_7`. -/
def function5 : Function :=
  ⟨"_transcript_7", [("v30", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v31"],
    .operation "lc_10_transition" "_transcript_4" [.template ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["query", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6331", "input_2", "random.bls12-381.fr/0", "draw", "role00000001"]⟩] ["v30", "v31"] ["v32", "v33"],
    .ret ["v32", "v33"]]⟩

/-- The local function `_transcript_8`. -/
def function6 : Function :=
  ⟨"_transcript_8", [("v34", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v35", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v36"],
    .operation "lc_10_transition" "_transcript_2" [.template ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6431_0", "label_6431_0", "role00000001", "role00000000"]⟩] ["v34", "v35", "v36"] ["v37"],
    .ret ["v37"]]⟩

def validator : Validator where
  entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b"
  role := "role00000001"
  symbol := "_math_1"
  inputs := [("v12", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v13", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩)]
  results := [⟨.data .boolean, "native.bool/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩]
  body := [
    .receive "label_6d30_0" "label_6d30_0" "role00000000" "v14" ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩,
    .call "_transcript_15" "_transcript_0" ["v13", "v14"] ["v15"],
    .call "_transcript_16" "_transcript_3" ["v15"] ["v16", "v17"],
    .call "_transcript_17" "_transcript_5" ["v17", "v16"] ["v18"],
    .receive "label_6d31_0" "label_6d31_0" "role00000000" "v19" ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩,
    .call "_transcript_18" "_transcript_6" ["v18", "v19"] ["v20"],
    .call "_transcript_19" "_transcript_7" ["v20"] ["v21", "v22"],
    .call "_transcript_20" "_transcript_8" ["v22", "v21"] ["v23"],
    .call "calculation_0" "_calculation_1" ["v14", "v16", "v21", "v12", "v19"] ["v24"],
    .ret ["v24", "v23"]]
  functions := [function0, function1, function2, function3, function4, function5, function6]
  bindings := [
    ⟨"_transcript_4", "transcript.native.indexed.challenge", ["merlin3.bls12-381.fr64be/0"], "arkworks/transcript.native.indexed.challenge", []⟩,
    ⟨"_transcript_2", "transcript.native.indexed.observe.data", ["merlin3.bls12-381.fr64be/0", "field:bls12-381.fr"], "arkworks/transcript.native.indexed.observe.data", [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩]⟩,
    ⟨"_transcript_1", "indices.empty", [], "native/indices.empty", []⟩,
    ⟨"_numerical_binding_0", "field.mul", ["bls12-381.fr"], "arkworks/field.mul", []⟩,
    ⟨"_numerical_binding_1", "field.equal", ["bls12-381.fr"], "arkworks/field.equal", []⟩,
    ⟨"_numerical_binding_2", "field.add", ["bls12-381.fr"], "arkworks/field.add", []⟩]

end ZkcExamples.Executable.DeferredRoundsProgramData
