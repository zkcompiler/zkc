import Tools.Artifact.Inputs

set_option autoImplicit false

namespace Tools.Artifact
open Lean (Json)
open Tools.Interactive

def reference (source descriptor inputs : Json) (proof : ByteArray) (answers : Json) (transcriptBudget : Nat := 100000) : Result Json := do
  ensure (proof.size ≤ byteLimit) "proof-limit"
  let invocation ← prepare source descriptor inputs
  let answers ← decodeAnswers answers
  let initial : State := {
    cursor := ⟨proof, 0⟩
    root := invocation.root
    configuration := invocation.configuration
    answers := answers
    setups := invocation.setups
    transcriptBudget := transcriptBudget }
  let (outcome, state) := (run invocation).run initial
  let outcome ← match outcome with
    | .ok values => do
        pure (.arr #[.str "accepted", .arr (← values.mapM (fun v => observedValue v)).toArray])
    | .error failure => pure (.arr #[.str failure.reason, .str failure.detail, failure.request])
  return .arr #[.str "zkc.artifact-observation/1", outcome, .arr state.events, .arr state.requests,
    .str (toString state.cursor.position), .str (toString state.draws),
    .str (toString state.transcriptActions), .str (hex invocation.root),
    .arr #[.str "original-source-validator", .str "independent-control-and-framing",
      .str "exact-public-primitive-cache", .str "external-crypto-contract",
      .str "no-native-or-backend-FV", .str "no-FS-security-theorem"]]

def readBytes (path : System.FilePath) (bound : Nat) : IO (Result ByteArray) :=
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    while bytes.size ≤ bound do
      let chunk ← handle.read (min 65536 (bound + 1 - bytes.size)).toUSize
      if chunk.isEmpty then break
      bytes := bytes ++ chunk
    return if bytes.size ≤ bound then .ok bytes else .error "byte-limit"

def readJson (path : System.FilePath) (bound : Nat) : IO (Result Json) := do
  let bytes ← readBytes path bound
  return do
    let some text := String.fromUTF8? (← bytes) | throw "invalid-utf8"
    -- Keep the carrier grammar and depth check shared with source admission;
    -- only the byte ceiling differs for public inputs and reply caches.
    Decode.preflight text bound
    (Json.parse text).mapError fun _ => "invalid-json"

def dispatch (args : List String) : IO (Result Json) := do
  match args with
  | "identity" :: sourcePath :: descriptorPath :: configurationPaths =>
      let source ← Decode.read sourcePath
      let descriptor ← Decode.read descriptorPath
      let configuration : Result (Option Json) ← match configurationPaths with
        | [] => pure (.ok none)
        | [path] => do
            let json ← readJson path byteLimit
            match json with
            | .ok value => pure (.ok (some value))
            | .error code => pure (.error code)
        | _ => pure (.error "identity-arguments")
      return do
        let prepared ← Identity.prepare (← source) (← descriptor)
        match ← configuration with
        | none => return prepared.inspection
        | some configuration =>
            let configuration ← prepared.configuration configuration
            let source := prepared.resolvedSource
            let binding ← source.binding (← lookup prepared.descriptor.entry source.entries)
            let definition ← source.protocol binding.protocol
            let _ ← decodeConfiguration source prepared.descriptor binding definition configuration
            return .arr #[.str "zkc.identity-inspection/1", prepared.resolution.carrier.json,
              prepared.descriptor.json, prepared.normalized, configuration]
  | "reference" :: sourcePath :: descriptorPath :: inputPath :: proofPath :: repliesPath :: policy =>
      let source ← Decode.read sourcePath
      let descriptor ← Decode.read descriptorPath
      let inputs ← readJson inputPath byteLimit
      let proof ← readBytes proofPath byteLimit
      let replies ← readJson repliesPath (4*byteLimit)
      return do
        let budget ← match policy with
          | [] => pure 100000
          | [budget] => Decode.natural (.str budget)
          | _ => throw "reference-policy"
        reference (← source) (← descriptor) (← inputs) (← proof) (← replies) budget
  | ["encode", jsonPath] =>
      let json ← Decode.read jsonPath
      return do pure (.str (hex (← treeBytes (← json))))
  | _ => return .error "usage: identity SOURCE DESCRIPTOR [CONFIGURATION] | reference SOURCE DESCRIPTOR INPUTS PROOF REPLIES [TRANSCRIPT_BUDGET] | encode JSON"

def cli (args : List String) : IO UInt32 := do
  try
    match ← dispatch args with
    | .error code =>
        IO.println (Json.arr #[.str "refused", .str code]).compress
        return 1
    | .ok result =>
        IO.println result.compress
        return 0
  catch _ =>
    IO.println (Json.arr #[.str "refused", .str "io-error"]).compress
    return 1

end Tools.Artifact
