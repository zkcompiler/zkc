import Examples.TablePhysical.Checking
import Examples.TableProtocol.Format
import Zkc.Compiler.RegionArtifact

/-! Physical scalar wire formats. The reference-only profile remains separate
from native admission; both decode the same operation and control meaning.
-/

set_option autoImplicit false
namespace TablePhysical
open Lean TableProtocol Zkc.Source Zkc.Compiler

def modeName : Mode → String | .lazy => "lazy" | .materialized => "materialized"
def decodeMode : String → Except String Mode
  | "lazy" => .ok .lazy
  | "materialized" => .ok .materialized
  | _ => .error "unsupported-preparation-mode"

def operations : Format.Codec Operation where
  encode
    | .invoke op => .arr #[.str "invoke", TableProtocol.operations.encode op]
    | .prepare mode d n => .arr #[.str "prepare", .str (modeName mode), .str (domainName d), toJson n]
  decode json := do
    match ← Format.array json with
    | [.str "invoke", op] => return .invoke (← TableProtocol.operations.decode op)
    | [.str "prepare", .str mode, domain, rank] =>
      let mode ← (decodeMode mode).mapError (fun _ => Format.Error.unknownOperation)
      return .prepare mode (← decodeDomain domain) (← Format.natural rank)
    | _ => throw .unknownOperation

inductive Profile where
  | reference
  | native
  deriving DecidableEq

def Profile.realization : Profile → String
  | .reference => "table-physical-reference"
  | .native => "table-physical-plan"

def Profile.formatName (profile : Profile) : String := "zkc-" ++ profile.realization

structure Candidate where
  context : CompilationContext Ty
  body : RawRegion Ty Operation
  profile : Profile := .reference

def candidateCodec : Format.Codec Candidate where
  encode candidate := .arr #[.str candidate.profile.formatName, toJson (1 : Nat),
    (ArtifactFormat.context types).encode candidate.context,
    RegionFormat.encode types operations candidate.body]
  decode json := do
    match ← Format.array json with
    | [.str name, version, context, body] =>
      let profile ← match name with
        | "zkc-table-physical-reference" => pure Profile.reference
        | "zkc-table-physical-plan" => pure Profile.native
        | _ => throw Format.Error.shape
      if (← Format.natural version) != 1 then throw .shape
      return ⟨← (ArtifactFormat.context types).decode context,
        ← RegionFormat.decode types operations 256 body, profile⟩
    | _ => throw .shape

/-- Admit both existing source grammars without flattening shared regions. -/
def source (json : Json) : Except String (RegionArtifact.Request Ty Protocol.Operation) := do
  if json.getArr?.toOption.bind (·[2]?) == some (.str RegionArtifact.semanticsVersion) then
    return ← (RegionArtifact.request types TableProtocol.operations 256).decode json |>.mapError (·.code)
  let request ← TableProtocol.requestCodec.decode json |>.mapError (·.code)
  let region ← request.source.elaborate (language := Protocol.language)
    (request.context.inputs.map (·.type)) request.context.resultType |>.mapError (fun _ => "malformed-source")
  return ⟨request.context, request.permittedRequirements, region.toRegion.erase⟩

def admit (request : RegionArtifact.Request Ty Protocol.Operation) (candidate : Candidate) :
    Except String (Checked (request.context.inputs.map (·.type)) request.context.resultType
      request.source candidate.body) := do
  if request.context.dependencies != dependencies then throw "unresolved-dependency"
  if candidate.context != request.context then throw "context-mismatch"
  -- The request context must be valid, as for direct plans
  -- (docs/spec/profiles/compiler/direct-plan.md).
  if !validContext request.context then throw "invalid-context"
  check (request.context.inputs.map (·.type)) request.context.resultType request.source candidate.body

end TablePhysical
