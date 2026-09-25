import Zkc.Compiler.RegionArtifact
import Zkc.Source.InputBinding
import Tools.JsonSupport

/-! Shared executable consumer plumbing. Policy selection and native-provider
correspondence remain outside this module. Source and candidate checking uses the
maintained proved rules; finite sources reuse their compact embedding. -/
set_option autoImplicit false
namespace Zkc.Tools.SourceConsumer
open Lean Source Compiler

structure Checked (language : Language) where
  context : CompilationContext language.Ty
  region : Region language (context.inputs.map (·.type)) context.resultType
  work : Nat

def check {language : Language} [DecidableEq language.Ty] [DecidableEq language.Op]
    (types : Format.Codec language.Ty) (operations : Format.Codec language.Op)
    (dependencies : List DefinitionRef) (source plan : Json) :
    Except String (Checked language) := do
  if source.getArr?.toOption.bind (·[2]?) == some (.str RegionArtifact.semanticsVersion) then
    let request ← (RegionArtifact.request types operations 256).decode source |>.mapError (·.code)
    let candidate ← (RegionArtifact.candidate types operations 256).decode plan |>.mapError (·.code)
    if request.context.dependencies != dependencies then throw "unresolved-dependency"
    let accepted ← RegionArtifact.check (language := language) request candidate |>.mapError (·.code)
    return ⟨request.context, accepted.region, candidate.body.workBound⟩
  else
    let request ← (ArtifactFormat.request types operations 256).decode source |>.mapError (·.code)
    let candidate ← (ArtifactFormat.candidate types operations 256).decode plan |>.mapError (·.code)
    if request.context.dependencies != dependencies then throw "unresolved-dependency"
    let accepted ← checkCandidate (language := language) request candidate |>.mapError (·.code)
    -- The accepted direct plan preserves this source. toRegion preserves its
    -- denotation and never duplicates a shared continuation.
    return ⟨request.context, accepted.source.toRegion, workBound candidate.body⟩

structure InvocationCodec {Ty : Type} (Value : Ty → Type) (State Event : Type) where
  suppliedInput : Json → Except String (SuppliedInput Value)
  decodeState : Json → Except String State
  valueJson : (ty : Ty) → Value ty → Json
  stateJson : State → Json
  eventJson : Event → Json

def execute {Ty State Event : Type} [DecidableEq Ty] {Value : Ty → Type}
    (codec : InvocationCodec Value State Event) (context : CompilationContext Ty)
    (validateEntry : String → State → Except String Unit)
    (run : Environment Value (context.inputs.map (·.type)) → State →
      PIR.Execution State Event (Value context.resultType)) (invocation : Json) : Except String Json := do
  let (inputs, state) ← match invocation.getArr? with
    | .ok #[inputs, state] => pure (inputs, state)
    | _ => throw "invalid-invocation"
  let state ← codec.decodeState state
  validateEntry context.role state
  let inputs ← inputs.getArr?.mapError (fun _ => "invalid-inputs")
  let supplied ← inputs.toList.mapM codec.suppliedInput
  let values ← bindInputs context.role context.inputs supplied |>.mapError (·.code)
  let result := run values.get state
  let outcome := match result.outcome with
    | .returned value => .arr #[.str "returned", codec.valueJson context.resultType value]
    | .stopped reason => .arr #[.str "stopped", Format.stop.encode reason]
  return Json.mkObj [("status", .str "executed"), ("outcome", outcome),
    ("state", codec.stateJson result.state), ("events", .arr (result.events.map codec.eventJson).toArray)]

def load (path : String) : IO Json := do
  match ← readJson path with
  | .ok value => return value
  | .error code => throw (IO.userError code)

def report (result : Except String Json) : IO UInt32 := do
  match result with
  | .error code => refused code
  | .ok value => emit value; return 0

def checked (extra : List (String × Json) := []) : IO UInt32 := do
  emit (Json.mkObj ([("status", .str "checked"), ("claim", .str "complete-logical-execution"),
    ("realization", .str "direct-logical-plan")] ++ extra))
  return 0
end Zkc.Tools.SourceConsumer
