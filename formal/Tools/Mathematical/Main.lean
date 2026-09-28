import Tools.Mathematical.SchemaEncoding
import Tools.Mathematical.InstallationDescriptors
import Zkc.Source.Mathematical.BlsAdmission
import Examples.Mathematical.SigmaSubject

set_option autoImplicit false
namespace Tools.Mathematical

private def readBytes (path : System.FilePath) : IO (Except String ByteArray) :=
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    while bytes.size ≤ Codec.byteLimit do
      let chunk ← handle.read (min 65536 (Codec.byteLimit + 1 - bytes.size)).toUSize
      if chunk.isEmpty then break
      bytes := bytes ++ chunk
    return if bytes.size ≤ Codec.byteLimit then .ok bytes else .error "math-resource-limit"

private def hex (bytes : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toUTF8
  let mut result := ByteArray.empty
  for byte in bytes do
    result := (result.push digits[byte.toNat / 16]!).push digits[byte.toNat % 16]!
  return String.fromUTF8! result

private def dispatch (mode : String) (bytes : ByteArray) : Except String ByteArray := do
  let value ← Codec.decode bytes
  match mode with
  | "binary" => Codec.encode value
  | "schema" => Codec.encode (← SchemaEncoding.encode (← Schema.decode value))
  | "admit" =>
      let subject ← Schema.decode value
      let admitted ← (Zkc.Source.Mathematical.BlsAdmission.admit subject 10000000).mapError
        (fun reason => "math-admission-refused: " ++ reprStr reason)
      Codec.encode (.array [.string "admitted", .string "zkc.math.bls/1",
        .natural admitted.assembly.table.records.length])
  | _ => throw "usage: mathematical-reference (binary|schema|admit) FILE"

def main (args : List String) : IO UInt32 := do
  if args == ["sigma"] then
    match SchemaEncoding.encode Examples.Mathematical.SigmaSubject.subject >>= Codec.encode with
    | .ok bytes => IO.println (hex bytes); return 0
    | .error code => (← IO.getStderr).putStrLn code; return 1
  if args == ["installation"] then
    match InstallationDescriptors.encoded with
    | .ok bytes => IO.println (hex bytes); return 0
    | .error code => (← IO.getStderr).putStrLn code; return 1
  let [mode, path] := args | do
    (← IO.getStderr).putStrLn "usage: mathematical-reference (binary|schema|admit) FILE | installation | sigma"
    return 2
  let input ← readBytes path
  match input.bind (dispatch mode) with
  | .ok bytes => IO.println (hex bytes); return 0
  | .error code => (← IO.getStderr).putStrLn code; return 1

end Tools.Mathematical
