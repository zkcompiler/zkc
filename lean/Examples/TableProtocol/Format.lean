import Examples.TableProtocol.Language
import Zkc.Compiler.ArtifactFormat

/-! Versioned descriptors for the finite table protocol interpretation. -/

set_option autoImplicit false
namespace TableProtocol
open Lean Zkc.Source Zkc.Compiler

def domainName : Domain → String | .two => "f2" | .seven => "f7"
def decodeDomain : Json → Except Format.Error Domain
  | .str "f2" => .ok .two
  | .str "f7" => .ok .seven
  | _ => .error .unknownType

def types : Format.Codec Ty where
  encode
    | .boolean => toJson (["bool"] : List String)
    | .digest => toJson (["digest"] : List String)
    | .summary => toJson (["summary"] : List String)
    | .scalar d => .arr #[.str "scalar", .str (domainName d)]
    | .point d => .arr #[.str "point", .str (domainName d)]
    | .table d n => .arr #[.str "table", .str (domainName d), toJson n]
    | .residual d n => .arr #[.str "residual", .str (domainName d), toJson n]
  decode json := do
    match ← Format.array json with
    | [.str "bool"] => return .boolean
    | [.str "digest"] => return .digest
    | [.str "summary"] => return .summary
    | [.str "scalar", d] => return .scalar (← decodeDomain d)
    | [.str "point", d] => return .point (← decodeDomain d)
    | [.str "table", d, n] => return .table (← decodeDomain d) (← Format.natural n)
    | [.str "residual", d, n] => return .residual (← decodeDomain d) (← Format.natural n)
    | _ => throw .unknownType

private def boolean (json : Json) : Except Format.Error Bool :=
  json.getBool?.mapError (fun _ => .shape)

def operations : Format.Codec Protocol.Operation where
  encode
    | .base (.view d n) => .arr #[.str "view", .str (domainName d), toJson n]
    | .base (.restrict d n) => .arr #[.str "restrict", .str (domainName d), toJson n]
    | .base (.evaluate d n) => .arr #[.str "evaluate", .str (domainName d), toJson n]
    | .base (.add d) => .arr #[.str "add", .str (domainName d)]
    | .base (.record d) => .arr #[.str "record", .str (domainName d)]
    | .base (.abortWrite d) => .arr #[.str "abort_write", .str (domainName d)]
    | .base .orderedPair => toJson (["ordered_pair"] : List String)
    | .base .pack => toJson (["pack"] : List String)
    | .endpointPoint one => .arr #[.str "endpoint_point", toJson one]
    | .parent left => .arr #[.str "parent", toJson left]
    | .send => toJson (["send"] : List String)
    | .draw => toJson (["draw"] : List String)
    | .linear => toJson (["linear"] : List String)
    | .point => toJson (["point"] : List String)
    | .equal => toJson (["equal"] : List String)
    | .digestEqual => toJson (["digest_equal"] : List String)
  decode json := do
    match ← Format.array json with
    | [.str "view", d, n] => return .base (.view (← decodeDomain d) (← Format.natural n))
    | [.str "restrict", d, n] => return .base (.restrict (← decodeDomain d) (← Format.natural n))
    | [.str "evaluate", d, n] => return .base (.evaluate (← decodeDomain d) (← Format.natural n))
    | [.str "add", d] => return .base (.add (← decodeDomain d))
    | [.str "record", d] => return .base (.record (← decodeDomain d))
    | [.str "abort_write", d] => return .base (.abortWrite (← decodeDomain d))
    | [.str "ordered_pair"] => return .base .orderedPair
    | [.str "pack"] => return .base .pack
    | [.str "endpoint_point", one] => return .endpointPoint (← boolean one)
    | [.str "parent", left] => return .parent (← boolean left)
    | [.str "send"] => return .send
    | [.str "draw"] => return .draw
    | [.str "linear"] => return .linear
    | [.str "point"] => return .point
    | [.str "equal"] => return .equal
    | [.str "digest_equal"] => return .digestEqual
    | _ => throw .unknownOperation

def dependencies : List DefinitionRef := [⟨"table-protocol", "1"⟩]
def requestCodec := ArtifactFormat.request types operations 256
def candidateCodec := ArtifactFormat.candidate types operations 256

end TableProtocol
