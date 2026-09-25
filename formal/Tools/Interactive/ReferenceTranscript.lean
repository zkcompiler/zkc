import Tools.Interactive.ReferenceResources
import Tools.Artifact.Transcript

/-! Transcript state owns its root and ordered history. Hash replies supply only
64 bytes; source origins, canonical message encoding, consuming transitions and
suite-specific field reduction are computed here. The hash service is conditional.
-/

set_option autoImplicit false

namespace Tools.Interactive.Reference
open Lean (Json)

/-- Recover every child target from the original source before encoding a native
logical origin. The common-control path deliberately has no generated names. -/
private def pathFrom (source : Source) (binding : Instance) (body : List Instruction) :
    List Control.Frame → Result (Name × List Json)
  | [] => .ok (binding.name, [])
  | .localCall site function :: rest => do
      ensure (rest.isEmpty && body.any (fun i => match i with
        | .localCall s _ f .. => s == site && f == function
        | _ => false)) "transcript-source-path"
      return (binding.name, [])
  | .localMatch .. :: _ | .localBranch .. :: _ | .localIteration .. :: _ => .error "transcript-source-path"
  | .call site :: rest => do
      let some (.call _ dependency ..) := body.find? (fun i => match i with
        | .call s .. => s == site | _ => false) | throw "transcript-source-path"
      let child ← source.binding (← lookup dependency binding.dependencies)
      let some nested := (← source.protocol child.protocol).body | throw "external-protocol"
      let (leaf, suffix) ← pathFrom source child nested rest
      return (leaf, .arr #[.str "call", .str site, .str child.name] :: suffix)
  | .iteration site index :: rest => do
      let some (.loop _ count _ _ nested _) := body.find? (fun i => match i with
        | .loop s .. => s == site | _ => false) | throw "transcript-source-path"
      ensure (index < (← binding.count count)) "transcript-source-path"
      let (leaf, suffix) ← pathFrom source binding nested rest
      return (leaf, .arr #[.str "loop", .str site, .str (toString index)] :: suffix)

def interactionPath (source : Source) (location : Location) : Result (Array Json) := do
  let root ← source.binding (← lookup location.entry source.entries)
  let some body := (← source.protocol root.protocol).body | throw "external-protocol"
  let (leaf, path) ← pathFrom source root body location.scope.path
  ensure (leaf == location.scope.binding) "transcript-source-path"
  return path.toArray

def transcriptOrigin (location : Location) (kind : String) (attributes : List String) : Result ByteArray := do
  ensure (Bindings.validTranscriptAttributes attributes) "transcript-origin"
  -- Like the selected contract, excludes session, executor role and local frame.
  -- Attribute correspondence is a separate construction judgment.
  Tools.Artifact.treeBytes (.arr #[.str "zkc.logical-origin/1", .str location.entry,
    .str location.scope.binding, .arr location.interactionPath,
    .arr ((kind :: attributes).map Json.str).toArray])

private def takeTranscript (location : Location) (suite : String)
    (identity : Name) (generation : Nat) : RunM (ByteArray × Array Json) := do
  let payload ← consumeResource location "transcript" identity generation suite
  match payload with
  | .transcript _ root history => return (root, history)
  | _ => failAt location "refused" "capability-kind"

def transcriptObserve (location : Location) (attributes : List String)
    (identity : Name) (generation : Nat) (value : Value)
    (suite : String := Bindings.transcriptIdentity) : RunM (List Value) := do
  let origin ← checked location (transcriptOrigin location "message" attributes)
  let bytes ← checked location value.wire
  let (root, history) ← takeTranscript location suite identity generation
  let history := history.push (.arr #[.str "message", .str (Tools.Artifact.hex origin),
    .str (Tools.Artifact.hex bytes)])
  updateResource identity fun r => { r with payload := .transcript suite root history }
  return [.transcript suite identity (generation + 1)]

def transcriptRequest (root : ByteArray) (history : Array Json)
    (suite : String := Bindings.transcriptIdentity) : Result Json :=
  Tools.Artifact.transcriptRequest root history suite

def transcriptChallenge (location : Location) (attributes : List String)
    (identity : Name) (generation : Nat) (suite : String := Bindings.transcriptIdentity)
    (bound : Option Nat := none) : RunM (List Value) := do
  if let some n := bound then
    require location (suite == Bindings.extensionTranscript && Sampling.validBound n) "query-bound"
  let origin ← checked location (transcriptOrigin location "challenge" attributes)
  let (root, history) ← takeTranscript location suite identity generation
  let action := match bound with
    | none => Json.arr #[.str "challenge", .str (Tools.Artifact.hex origin)]
    | some n => .arr #[.str "index", .str (Tools.Artifact.hex origin), .str (toString n)]
  let mut history := history.push action
  let mut coordinates := []
  for attempt in [0:16] do
    if attempt > 0 then history := history.push (.arr #[.str "challenge-continuation"])
    updateResource identity fun r => { r with payload := .transcript suite root history }
    let request ← checked location (transcriptRequest root history suite)
    let encoded ← checked location (Tools.Artifact.treeBytes request)
    let reply ← successfulReply location (← oracle location request (1 + encoded.size))
    let bytes ← checked location (Tools.Artifact.unhex (← checked location (Decode.string reply)))
    require location (bytes.size == 64) "transcript-challenge-width"
    let successor := Value.transcript suite identity (generation + 1)
    if let some n := bound then
      return [Value.fromArithmetic .bls (.index (← checked location (Sampling.index bytes n))), successor]
    if suite == Bindings.extensionTranscript then
      coordinates := coordinates ++ Sampling.coordinates bytes
      if let some value := Sampling.extension coordinates then return [.extension (.field value), successor]
    else
      let field ← checked location (Bindings.associatedIdentity suite "ChallengeField")
      let domain ← checked location (ServiceDomain.parse field)
      let integer := if domain == .ristretto then Tools.Artifact.valueLE bytes
        else bytes.toList.foldl (fun n b => 256 * n + b.toNat) 0
      return [Value.fromArithmetic domain.scalar (.field (integer : ScalarReference.Scalar domain.scalar)), successor]
  failAt location "exhausted" "challenge-rejection-limit"

end Tools.Interactive.Reference
