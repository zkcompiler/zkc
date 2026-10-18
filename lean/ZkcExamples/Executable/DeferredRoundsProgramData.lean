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
def program : String := "sha256:a0e9640b0367f47603565c8abfc4136c35a00d85fa99816feca3b82daf033802"

/-- The local function `_calculation_1`. -/
def function0 : Function :=
  ⟨"_calculation_1", [("v15", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v16", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v17", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v18", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v19", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data .boolean, "native.bool/0"⟩], [
    .operation "value_0" "_calculation_2" [] ["v15", "v16"] ["v20"],
    .operation "value_1" "_calculation_2" [] ["v20", "v17"] ["v21"],
    .operation "value_2" "_calculation_3" [] ["v21", "v18"] ["v22"],
    .operation "value_3" "_calculation_2" [] ["v19", "v17"] ["v23"],
    .operation "value_4" "_calculation_3" [] ["v23", "v18"] ["v24"],
    .operation "value_5" "_calculation_4" [] ["v22", "v24"] ["v25"],
    .ret ["v25"]]⟩

/-- The local function `_transcript_1`. -/
def function1 : Function :=
  ⟨"_transcript_1", [("v39", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v40", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v41"],
    .operation "transition" "_transcript_0" [.template ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6d30_0", "label_6d30_0", "role00000000", "role00000001"]⟩] ["v39", "v40", "v41"] ["v42"],
    .ret ["v42"]]⟩

/-- The local function `_transcript_4`. -/
def function2 : Function :=
  ⟨"_transcript_4", [("v43", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v44"],
    .operation "transition" "_transcript_3" [.template ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["query", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6330", "input_2", "random.bls12-381.fr/0", "draw", "role00000001"]⟩] ["v43", "v44"] ["v45", "v46"],
    .ret ["v45", "v46"]]⟩

/-- The local function `_transcript_5`. -/
def function3 : Function :=
  ⟨"_transcript_5", [("v47", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v48", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v49"],
    .operation "transition" "_transcript_0" [.template ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6430_0", "label_6430_0", "role00000001", "role00000000"]⟩] ["v47", "v48", "v49"] ["v50"],
    .ret ["v50"]]⟩

/-- The local function `_transcript_6`. -/
def function4 : Function :=
  ⟨"_transcript_6", [("v51", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v52", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v53"],
    .operation "transition" "_transcript_0" [.template ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6d31_0", "label_6d31_0", "role00000000", "role00000001"]⟩] ["v51", "v52", "v53"] ["v54"],
    .ret ["v54"]]⟩

/-- The local function `_transcript_7`. -/
def function5 : Function :=
  ⟨"_transcript_7", [("v55", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v56"],
    .operation "transition" "_transcript_3" [.template ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["query", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6331", "input_2", "random.bls12-381.fr/0", "draw", "role00000001"]⟩] ["v55", "v56"] ["v57", "v58"],
    .ret ["v57", "v58"]]⟩

/-- The local function `_transcript_8`. -/
def function6 : Function :=
  ⟨"_transcript_8", [("v59", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v60", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v61"],
    .operation "transition" "_transcript_0" [.template ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6431_0", "label_6431_0", "role00000001", "role00000000"]⟩] ["v59", "v60", "v61"] ["v62"],
    .ret ["v62"]]⟩

def validator : Validator where
  entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b"
  role := "role00000001"
  symbol := "_math_1"
  inputs := [("v26", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v27", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩)]
  results := [⟨.data .boolean, "native.bool/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩]
  body := [
    .receive "label_6d30_0" "label_6d30_0" "role00000000" "v28" ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩,
    .call "_transcript_15" "_transcript_1" ["v27", "v28"] ["v29"],
    .call "_transcript_16" "_transcript_4" ["v29"] ["v30", "v31"],
    .call "_transcript_17" "_transcript_5" ["v31", "v30"] ["v32"],
    .receive "label_6d31_0" "label_6d31_0" "role00000000" "v33" ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩,
    .call "_transcript_18" "_transcript_6" ["v32", "v33"] ["v34"],
    .call "_transcript_19" "_transcript_7" ["v34"] ["v35", "v36"],
    .call "_transcript_20" "_transcript_8" ["v36", "v35"] ["v37"],
    .call "calculation_0" "_calculation_1" ["v28", "v30", "v35", "v26", "v33"] ["v38"],
    .ret ["v38", "v37"]]
  functions := [function0, function1, function2, function3, function4, function5, function6]
  bindings := [
    ⟨"_calculation_4", "field.equal", ["bls12-381.fr"], "arkworks/field.equal"⟩,
    ⟨"_calculation_3", "field.add", ["bls12-381.fr"], "arkworks/field.add"⟩,
    ⟨"_calculation_2", "field.mul", ["bls12-381.fr"], "arkworks/field.mul"⟩,
    ⟨"_transcript_3", "transcript.native.indexed.challenge", ["merlin3.bls12-381.fr64be/0"], "arkworks/transcript.native.indexed.challenge"⟩,
    ⟨"_transcript_2", "indices.empty", [], "native/indices.empty"⟩,
    ⟨"_transcript_0", "transcript.native.indexed.observe.data", ["merlin3.bls12-381.fr64be/0", "field:bls12-381.fr"], "arkworks/transcript.native.indexed.observe.data"⟩]

end ZkcExamples.Executable.DeferredRoundsProgramData
