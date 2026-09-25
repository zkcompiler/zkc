import Tools.RequirementChecker.Transport

set_option autoImplicit false

def main : IO UInt32 := do
  let input ← IO.getStdin
  let limit := 16 * 1024 * 1024
  let mut bytes := ByteArray.empty
  while bytes.size ≤ limit do
    let chunk ← input.read (min 65536 (limit + 1 - bytes.size)).toUSize
    if chunk.isEmpty then break
    bytes := bytes ++ chunk
  if bytes.size > limit then
    IO.println "[\"refused\",\"requirements-bytes\"]"
    return 1
  let some line := String.fromUTF8? bytes | do
    IO.println "[\"refused\",\"requirements-utf8\"]"
    return 1
  match Tools.RequirementChecker.dispatch line with
  | .ok result => IO.println result.compress; return 0
  | .error reason =>
      IO.println (Lean.Json.arr #[.str "refused", .str reason]).compress
      return 1
