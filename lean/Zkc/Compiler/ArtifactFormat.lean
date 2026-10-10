import Zkc.Compiler.Artifact
import Zkc.Source.Format

/-! Exact external envelopes for a retained request and a candidate plan.

The request must come from the consumer. A producer-supplied copy cannot stand
in for it. These codecs do not resolve dependencies or accept private values.
-/

set_option autoImplicit false

namespace Zkc.Compiler.ArtifactFormat

open Lean Source Source.Format

def reference : Codec DefinitionRef where
  encode ref := .arr #[.str ref.name, .str ref.revision]
  decode json := do
    match ← array json with
    | [name, revision] => return ⟨← string name, ← string revision⟩
    | _ => .error .shape

def inputAccess : Codec InputAccess where
  encode
    | .shared => .arr #[.str "shared"]
    | .privateTo role => .arr #[.str "private", .str role]
  decode json := do
    match ← array json with
    | [.str "shared"] => return .shared
    | [.str "private", role] => return .privateTo (← string role)
    | _ => .error .shape

def inputKind : Codec InputKind where
  encode
    | .argument => .str "argument"
    | .capture => .str "capture"
  decode
    | .str "argument" => .ok .argument
    | .str "capture" => .ok .capture
    | _ => .error .shape

variable {Ty Op : Type}

def input (types : Codec Ty) : Codec (InputDeclaration Ty) where
  encode decl := .arr #[.str decl.name, types.encode decl.type,
    inputAccess.encode decl.access, inputKind.encode decl.kind]
  decode json := do
    match ← array json with
    | [name, type, access, kind] =>
      return ⟨← string name, ← types.decode type, ← inputAccess.decode access, ← inputKind.decode kind⟩
    | _ => .error .shape

def context (types : Codec Ty) : Codec (CompilationContext Ty) where
  encode ctx := .arr #[.str ctx.role, .arr (ctx.inputs.map (input types).encode).toArray,
    types.encode ctx.resultType, .arr (ctx.dependencies.map reference.encode).toArray]
  decode json := do
    match ← array json with
    | [role, inputs, result, dependencies] =>
      return ⟨← string role, ← (← array inputs).mapM (input types).decode, ← types.decode result,
        ← (← array dependencies).mapM reference.decode⟩
    | _ => .error .shape

def claim : Codec Claim where
  encode value := .arr #[.str value.relation, .str value.observation, .str value.scope]
  decode json := do
    match ← array json with
    | [relation, observation, scope] =>
      return ⟨← string relation, ← string observation, ← string scope⟩
    | _ => .error .shape

def request (types : Codec Ty) (operations : Codec Op) (depth : Nat) : Codec (Request Ty Op) where
  encode value := .arr #[.str "zkc-request", toJson formatVersion, .str semanticsVersion,
    (context types).encode value.context, .arr (value.permittedRequirements.map reference.encode).toArray,
    encodeProgram types operations value.source]
  decode json := do
    match ← array json with
    | [.str "zkc-request", version, semantics, ctx, permitted, source] =>
      if (← natural version) != formatVersion || (← string semantics) != semanticsVersion then
        throw .shape
      return ⟨← (context types).decode ctx, ← (← array permitted).mapM reference.decode,
        ← decodeProgram types operations depth source⟩
    | _ => .error .shape

def candidate (types : Codec Ty) (operations : Codec Op) (depth : Nat) : Codec (Candidate Ty Op) where
  encode value := .arr #[.str "zkc-plan", toJson value.format, .str value.semantics,
    toJson value.capabilities, .str value.realization, .str value.rule, claim.encode value.claim,
    (context types).encode value.context, .arr (value.requirements.map reference.encode).toArray,
    encodeProgram types operations value.body]
  decode json := do
    match ← array json with
    | [.str "zkc-plan", version, semantics, capabilities, realization, rule, property, ctx,
        requirements, body] =>
      return ⟨← natural version, ← string semantics, ← (← array capabilities).mapM string,
        ← string realization, ← string rule, ← claim.decode property, ← (context types).decode ctx,
        ← (← array requirements).mapM reference.decode, ← decodeProgram types operations depth body⟩
    | _ => .error .shape

end Zkc.Compiler.ArtifactFormat
