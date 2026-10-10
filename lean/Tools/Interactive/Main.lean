import Tools.Interactive.Projection
import Tools.Interactive.Encode
import Tools.Interactive.GenericValidation
import Tools.Interactive.GenericReference
import Tools.Interactive.PhysicalLocal

set_option autoImplicit false

namespace Tools.Interactive
open Lean

def dispatch (args : List String) : IO (Result Json) := do
  match args with
  | ["--physical-local-reference", sourcePath, candidatePath, inputPath, storagePath] =>
      let source ← Decode.read sourcePath
      let candidate ← Decode.read candidatePath
      let inputs ← Decode.read inputPath
      let storage ← Decode.read storagePath
      return do PhysicalLocal.reference (← source) (← candidate) (← inputs) (← storage)
  | ["--generic-reference", sourcePath, inputPath] =>
      let source ← Decode.read sourcePath
      let inputs ← Decode.read inputPath
      return do Reference.reference (← source) (← inputs) none
  | ["--generic-role", sourcePath, inputPath, role] =>
      let source ← Decode.read sourcePath
      let inputs ← Decode.read inputPath
      return do Reference.reference (← source) (← inputs) (some role)
  | ["--check-generic", sourcePath, candidatePath] =>
      let source ← Decode.read sourcePath
      let candidate ← Decode.read candidatePath
      return do
        let checked ← Generic.validate (← source) (← candidate)
        let ports := checked.ports.map fun p => Json.arr #[.str p.binding, .str p.role, .str p.participant,
          Encode.pairs Json.str Json.str p.arguments]
        let calls := checked.calls.map fun (binding, role, call) => Json.arr #[.str binding, .str role,
          .str call.site, .str call.configuration, .str call.function]
        return .arr #[.str "checked", .str "generic-structural-correspondence",
          .arr ports.toArray, .arr calls.toArray, .str "no-elaboration-adequacy-proof"]
  | ["--generic-declarations", sourcePath] =>
      let source ← Decode.read sourcePath
      return do
        let _ ← Generic.library (← source)
        return .arr #[.str "checked", .str "generic-local-formation", .str "not-whole-source-admission"]
  | ["--check-local", sourcePath, configuration, candidatePath, function] =>
      let source ← Decode.read sourcePath
      let candidate ← Decode.read candidatePath
      return do
        let _ ← Generic.validateLocal (← Generic.library (← source)) configuration
          (← Explicit.candidateLocals (← candidate)) function
        return .arr #[.str "checked", .str "generic-local-correspondence", .str "not-whole-source-admission"]
  | ["--admit", sourcePath] =>
      let source ← Decode.read sourcePath
      return do
        admitSource (← Generic.prepareSource (← source)).source
        return .arr #[.str "checked", .str "explicit-source-admission", .str "no-elaboration-adequacy-proof"]
  | ["--declarations", sourcePath] =>
      let source ← Decode.read sourcePath
      return do
        admitSource (← Generic.prepareSource (← source) false).source false
        return .arr #[.str "checked", .str "explicit-declaration-admission", .str "not-executable-admission"]
  | ["--check", sourcePath, candidatePath] =>
      let source ← Decode.read sourcePath
      let candidate ← Decode.read candidatePath
      return do
        let source ← source
        let candidate ← candidate
        let _ ← Generic.validate source candidate
        return .arr #[.str "checked", .str "generic-structural-correspondence", .str "no-elaboration-adequacy-proof"]
  | ["--reference", sourcePath, inputPath] =>
      let source ← Decode.read sourcePath
      let inputs ← Decode.read inputPath
      return do Reference.reference (← source) (← inputs) none
  | _ => return .error "usage: --check SOURCE CANDIDATE | --check-generic SOURCE CANDIDATE | --admit SOURCE | --declarations SOURCE | --generic-declarations SOURCE | --check-local SOURCE CONFIGURATION CANDIDATE FUNCTION | --reference SOURCE INPUTS | --generic-reference SOURCE INPUTS | --generic-role SOURCE INPUTS ROLE | --physical-local-reference SOURCE CANDIDATE INPUTS STORAGE"

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

end Tools.Interactive
