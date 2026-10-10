import Tools.Interactive.Bindings
import Lean

/-! Bounded observations of the independent Lean admission and interpretation
signatures. Requests contain no signature, permission or installation claims. -/

set_option autoImplicit false

open Lean Tools.Interactive

namespace Tools.ContractConformance

def refused : Json := Json.mkObj [("accepted", toJson false)]

abbrev Resolver := Bool → Bindings.Declaration → Result Bindings.Signature

/-- Observe Lean-owned registration directly; no inspection of resolver syntax
or compiler-supplied identity list participates in this observation. -/
def implementationCandidates : Result Json := do
  let entries := (← Bindings.installation).implementations
  return Json.mkObj [("accepted", toJson true), ("discovery", toJson "physical-registry"),
    ("implementations", toJson (entries.map fun (contract, implementation) =>
      Json.mkObj [("contract", toJson contract), ("implementation", toJson implementation)]))]

/-- Test-only drift after ordinary admission, preserving installed names and
generic shapes. Physical signatures and every other resolver are unchanged. -/
def divergentLogicalResolver (physical : Bool) (binding : Bindings.Declaration) :
    Result Bindings.Signature := do
  let signature ← Bindings.resolve physical binding
  if !physical && binding.contract == "field.add" then
    let boolean ← Bindings.valueType false "bool"
    return { signature with outputs := [boolean] }
  return signature

def envelope (text : String) : Except String Nat := do
  let mut quoted := false
  let mut escaped := false
  let mut depth := 0
  let mut fields := 0
  for c in text.toList do
    if c.toNat > 127 || (c.toNat < 32 && c != '\t' && c != '\r') then throw "envelope"
    if quoted then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then quoted := false
    else if c == '"' then quoted := true
    else if c == '{' || c == '[' then
      depth := depth + 1
      if depth > 8 then throw "envelope"
    else if c == '}' || c == ']' then
      if depth == 0 then throw "envelope"
      depth := depth - 1
    else if c == ':' then fields := fields + 1
  if quoted || depth != 0 then throw "envelope"
  return fields

def respond (resolve : Resolver) (text : String) : Except String Json := do
  let fields ← envelope text
  let request ← Json.parse text
  let object ← request.getObj?
  let size := object.foldl (fun n _ _ => n + 1) 0
  if size != fields then throw "envelope"
  if size == 1 && (request.getObjValAs? Bool "implementations").toOption == some true then
    return ← implementationCandidates
  if size == 1 && (request.getObjVal? "physical_type").isOk then
    let ty ← Bindings.valueType true (← request.getObjValAs? String "physical_type")
    return Json.mkObj [("accepted", toJson true), ("canonical", toJson ty.spelling)]
  if size == 1 then
    let spelling ← request.getObjValAs? String "type"
    let ty ← Bindings.valueType false spelling
    let permissions := Logical.permissions ty.spelling
    let selected := {ty with representation := ty.defaultRepresentation}
    let physical := if selected.valid true then toJson selected.spelling else Json.null
    return Json.mkObj [("accepted", toJson true), ("canonical", toJson ty.spelling),
      ("copy", toJson permissions.copy), ("drop", toJson permissions.drop),
      ("serializable", toJson permissions.isPublic), ("default_physical", physical)]
  if size == 2 then
    let contract ← request.getObjValAs? String "facets"
    let arguments ← request.getObjValAs? (Array String) "arguments"
    if arguments.size > 16 then throw "envelope"
    let _ ← resolve false ⟨"conformance", contract, arguments.toList, ""⟩
    return Json.mkObj [("accepted", toJson true),
      ("facets", Json.mkObj [("history", toJson (Bindings.historyContract contract))]),
      ("unsupported", toJson (["publicReplay", "sampling", "observation", "acceptanceGuard",
        "conjunction", "unclassifiedProviderEffect"] : List String))]
  if size != 4 then throw "envelope"
  let contract ← request.getObjValAs? String "contract"
  let arguments ← request.getObjValAs? (Array String) "arguments"
  if arguments.size > 16 then throw "envelope"
  let implementation ← request.getObjValAs? String "implementation"
  let physical ← request.getObjValAs? Bool "physical"
  let signature ← resolve physical ⟨"conformance", contract, arguments.toList, implementation⟩
  return Json.mkObj [("accepted", toJson true), ("physical", toJson physical),
    ("inputs", toJson (signature.inputs.map (·.spelling))),
    ("outputs", toJson (signature.outputs.map (·.spelling)))]

def emit (resolve : Resolver) (output : IO.FS.Stream) (line : ByteArray)
    (oversized : Bool) : IO Unit := do
  let result := if oversized then refused else
    match String.fromUTF8? line with
    | none => refused
    | some text => (respond resolve text).toOption.getD refused
  output.putStrLn result.compress
  output.flush

end Tools.ContractConformance

def main (arguments : List String) : IO UInt32 := do
  let resolve : Tools.ContractConformance.Resolver ← match arguments with
    | [] => pure Bindings.resolve
    | ["--divergent-logical-field-add"] => pure Tools.ContractConformance.divergentLogicalResolver
    | _ =>
      (← IO.getStderr).putStrLn "usage: contract-conformance [--divergent-logical-field-add]"
      return 2
  let input ← IO.getStdin
  let output ← IO.getStdout
  let mut line := ByteArray.empty
  let mut oversized := false
  repeat
    let chunk ← input.read 4096
    if chunk.isEmpty then break
    for byte in chunk do
      if byte == 10 then
        Tools.ContractConformance.emit resolve output line oversized
        line := ByteArray.empty
        oversized := false
      else if line.size < 16384 then line := line.push byte
      else oversized := true
  if !line.isEmpty || oversized then
    Tools.ContractConformance.emit resolve output line oversized
  return 0
