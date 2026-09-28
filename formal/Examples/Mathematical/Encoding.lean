import Tools.Artifact.Codec

/-! Independent conversion of already parsed values for canonical golden checks.
This fixture tool is not a hostile JSON parser or a typed subject decoder. -/

set_option autoImplicit false
namespace Examples.Mathematical.Encoding
open Lean (Json)

private def utf8Less (left right : String) : Bool :=
  decide (List.Lex (fun a b : UInt8 => a.toNat < b.toNat) left.toUTF8.toList right.toUTF8.toList)

def tree : Nat → Json → Except String Json
  | 0, _ => .error "depth"
  | fuel + 1, value => do
      match value with
      | .null => throw "null"
      | .bool b => return .arr #[.str "boolean", .str (if b then "true" else "false")]
      | .num _ =>
          let n ← value.getNat?
          if n ≥ 2^64 || value.compress != toString n then throw "natural"
          return .arr #[.str "natural", .str (toString n)]
      | .str s => return .arr #[.str "string", .str s]
      | .arr values =>
          if values.size > 32767 then throw "items"
          return .arr (#[.str "array"] ++ (← values.mapM (tree fuel)))
      | .obj values =>
          let entries := values.toArray.qsort (fun a b => utf8Less a.1 b.1)
          if entries.size > 16383 then throw "fields"
          let mut result := #[.str "object"]
          for (key, item) in entries do
            result := result.push (.str key)
            result := result.push (← tree fuel item)
          return .arr result

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "expected one JSON vector file")
  let input ← IO.FS.readFile path
  if input.utf8ByteSize > 1048576 then throw (IO.userError "JSON bytes")
  let value ← IO.ofExcept (Json.parse input)
  let converted ← IO.ofExcept (tree 65 value)
  let encoded ← IO.ofExcept (Tools.Artifact.treeBytes converted)
  IO.println (Tools.Artifact.hex encoded)
  return 0

end Examples.Mathematical.Encoding
