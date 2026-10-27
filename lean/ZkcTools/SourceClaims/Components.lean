module

public import Zkc.Source.Structured.ComponentExport
public import ZkcTools.JsonSupport

@[expose] public section

/-! The component part of source-claims/0. Other claim requests keep their owning
resolver. This reader admits the original before recomputing routes; it does not
accept a security theorem or a mathematical catalogue entry. -/
namespace ZkcTools.SourceClaims.Components
open Lean Zkc.Source Zkc.Source.Structured

/-- Detect duplicate object keys before Lean's JSON object representation can
collapse them. Keys are decoded, so escaped spellings cannot hide duplicates. -/
def uniqueKeys (text : String) : Except String Unit := do
  let chars := text.toList.toArray
  let mut frames : List (Option (List String)) := []
  let mut index := 0
  while index < chars.size do
    let char := chars[index]!
    if char == '{' then
      frames := some [] :: frames
      index := index + 1
    else if char == '[' then
      frames := none :: frames
      index := index + 1
    else if char == '}' || char == ']' then
      frames := frames.tail
      index := index + 1
    else if char == '"' then
      let start := index
      index := index + 1
      let mut escaped := false
      let mut closed := false
      while index < chars.size && !closed do
        let next := chars[index]!
        index := index + 1
        if escaped then escaped := false
        else if next == '\\' then escaped := true
        else if next == '"' then closed := true
      let mut after := index
      while after < chars.size && chars[after]!.isWhitespace do after := after + 1
      if after < chars.size && chars[after]! == ':' then
        let keyText := String.ofList (chars.extract start index).toList
        let key ← (← Json.parse keyText).getStr?
        let some (some keys) := frames.head? | throw "source-claim-shape"
        if key.utf8ByteSize > 512 || keys.length ≥ 512 then throw "source-claim-limit"
        if keys.contains key then throw "source-claim-duplicate"
        frames := some (key :: keys) :: frames.tail
    else index := index + 1
    if frames.length > 256 then throw "source-claim-depth"

def parse (text : String) : Except String Json := do
  if text.utf8ByteSize > 16 * 1024 * 1024 then throw "source-claim-limit"
  Zkc.Source.Format.checkNumbers text |>.mapError (fun _ => "source-claim-number")
  uniqueKeys text
  Json.parse text |>.mapError (fun _ => "source-claim-json")

def object (json : Json) (fields : List String) : Except String Unit := do
  let value ← json.getObj?.mapError fun _ => "source-claim-shape"
  let actual := value.toList.map Prod.fst
  unless actual.length == fields.length && actual.all fields.contains do throw "source-claim-fields"

def field (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name |>.mapError fun _ => "source-claim-fields"

def decode (snapshot : Snapshot) (json : Json) : Except String ComponentExport.Export := do
  object json ["format", "entry", "registry_resolution", "admission", "claims", "proposals", "seams"]
  unless (← field json "format") == .str "zkc.source-claims/0" &&
      (← field json "registry_resolution") == .str "deferred-to-lean" do throw "source-claim-format"
  let _ ← Format.string (← field json "entry")
  let admission ← field json "admission"
  object admission ["format", "original_sha256", "interface_sha256", "protocol_symbol", "capture", "installation"]
  unless (← field admission "format") == .str "zkc.structured-source/0" &&
      (← field admission "original_sha256") == .str snapshot.source &&
      (← field admission "protocol_symbol") == .str snapshot.entry do throw "source-claim-original"
  for name in ["interface_sha256", "capture", "installation"] do
    let _ ← Format.string (← field admission name) true
  for claim in ← Format.array (← field json "claims") do
    object claim ["request", "attachment", "method", "site_bindings"]
  ComponentExport.decode (← field json "proposals") (← field json "seams")

def check (snapshot : Snapshot) (text : String) : Except String Unit := do
  let _ ← Zkc.Source.Structured.check snapshot
  ComponentExport.check snapshot (← decode snapshot (← parse text))

def readText (path : System.FilePath) : IO (Except String String) := do
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    while bytes.size ≤ 16 * 1024 * 1024 do
      let chunk ← handle.read (min 65536 (16 * 1024 * 1024 + 1 - bytes.size)).toUSize
      if chunk.isEmpty then break
      bytes := bytes ++ chunk
    if bytes.size > 16 * 1024 * 1024 then return .error "source-claim-limit"
    return match String.fromUTF8? bytes with
      | some text => .ok text | none => .error "invalid-utf8"

def run (args : List String) : IO UInt32 := do
  let [snapshotPath, claimsPath] := args | return ← Zkc.Tools.refused "source-claim-arguments"
  let snapshotText ← readText snapshotPath
  let claimsText ← readText claimsPath
  let checked := do
    let snapshot ← Format.snapshot (← Format.parse (← snapshotText))
    check snapshot (← claimsText)
  match checked with
  | .error code => Zkc.Tools.refused code
  | .ok () =>
    Zkc.Tools.emit (Json.mkObj [("status", .str "associated"),
      ("mathematical_obligations", .str "unresolved")])
    return 0

end ZkcTools.SourceClaims.Components
