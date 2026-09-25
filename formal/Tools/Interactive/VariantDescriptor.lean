import Lean.Data.Json
import Std.Data.HashMap

/-! Canonical, self-contained local sum descriptors. Parsing grants no wire
codec and makes no claim about a cryptographic implementation. -/
set_option autoImplicit false
namespace Tools.Interactive.Variant
open Lean (Json)

structure Descriptor where
  nominal : Json
  alternatives : List (String × List String)
  deriving BEq

instance : Repr Descriptor where
  reprPrec d _ := repr (d.nominal.compress, d.alternatives)

private def require (b : Bool) : Except String Unit :=
  if b then .ok () else .error "variant-descriptor"

private def letter (c : Char) : Bool := c.isAlpha && c.toNat < 128

def name (s : String) (bound : Nat := 128) : Bool :=
  s.utf8ByteSize ≤ bound && match s.toList with
  | [] => false
  | first :: rest => (letter first || first == '_') &&
      rest.all (fun c => letter c || c.isDigit || c == '_' || c == '.' || c == '-')

def hex (bytes : ByteArray) : String :=
  String.ofList (bytes.data.toList.flatMap fun b =>
    let digits := "0123456789abcdef".toList.toArray
    [digits[b.toNat / 16]!, digits[b.toNat % 16]!])

private def unhex (s : String) : Except String ByteArray := do
  require (s.length % 2 == 0 && s.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')))
  let digits := s.toUTF8
  let digit (b : UInt8) := if b.toNat ≤ 57 then b.toNat - 48 else b.toNat - 87
  let mut bytes := ByteArray.emptyWithCapacity (digits.size / 2)
  for i in List.range (digits.size / 2) do
    bytes := bytes.push (UInt8.ofNat (digit digits[2*i]! * 16 + digit digits[2*i+1]!))
  return bytes

/-- Reject non-array/string JSON before the general parser can expand numeric
exponents, and bound hostile nesting independently of descriptor validation. -/
private def preflight (text : String) : Except String Unit := do
  let mut quoted := false
  let mut escaped := false
  let mut depth := 0
  for c in text.toList do
    if quoted then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then quoted := false
    else if c == '"' then quoted := true
    else if c == '[' then
      depth := depth + 1
      require (depth ≤ 64)
    else if c == ']' then
      require (depth > 0)
      depth := depth - 1
    else require (c == ',' || c == ' ' || c == '\n' || c == '\r' || c == '\t')
  require (!quoted && depth == 0)

private structure Packing where
  nodes : Array Json := #[]
  ids : Std.HashMap String Nat := {}
  visits : Nat := 0
  encodedBytes : Nat := 0

private def intern : Nat → Json → StateT Packing (Except String) Nat
  | 0, _ => throw "variant-descriptor"
  | fuel + 1, tree => do
    let state ← get
    if state.visits ≥ 200000 then throw "variant-descriptor"
    set { state with visits := state.visits + 1 }
    let node ← match tree with
      | .str s => do
        if s.utf8ByteSize > 256 * 1024 ||
            !s.toList.all (fun c => 32 ≤ c.toNat && c.toNat ≤ 126) then
          throw "variant-descriptor"
        pure tree
      | .arr a => do
        let refs ← a.mapM fun child => do pure (Json.str (toString (← intern fuel child)))
        pure (.arr refs)
      | _ => throw "variant-descriptor"
    let state ← get
    let key := node.compress
    if let some id := state.ids[key]? then return id
    if state.nodes.size ≥ 16384 then throw "variant-descriptor"
    let encodedBytes := state.encodedBytes + key.utf8ByteSize + 1
    if encodedBytes > (256 * 1024 - 8) / 2 then throw "variant-descriptor"
    let id := state.nodes.size
    set { state with nodes := state.nodes.push node, ids := state.ids.insert key id, encodedBytes }
    return id

private def packJson (tree : Json) : Except String Json := do
  let (_, state) ← (intern 64 tree).run {}
  let result := Json.arr #[.str "zkc.variant/1", .arr state.nodes]
  require (result.compress.utf8ByteSize ≤ (256 * 1024 - 8) / 2)
  return result

private def pack (tree : Json) : Except String String := do
  return "variant:" ++ hex (← packJson tree).compress.toUTF8

private def unpack (text : String) : Except String Json := do
  require (text.startsWith "variant:" && text.utf8ByteSize ≤ 256 * 1024)
  let bytes ← unhex (text.drop 8).toString
  let some decoded := String.fromUTF8? bytes | throw "variant-descriptor"
  preflight decoded
  let json ← (Json.parse decoded).mapError fun _ => "variant-descriptor"
  let .arr #[.str "zkc.variant/1", .arr nodes] := json | throw "variant-descriptor"
  require (!nodes.isEmpty && nodes.size ≤ 16384)
  let mut values : Array Json := #[]
  let mut sizes : Array Nat := #[]
  let mut counts : Array Nat := #[]
  let mut depths : Array Nat := #[]
  let byteBudget := min (8 * 1024 * 1024) (512 * text.utf8ByteSize)
  let nodeBudget := min 200000 (512 * text.utf8ByteSize)
  let mut totalBytes := 0
  let mut totalNodes := 0
  for node in nodes do
    let mut bytes := 2
    let mut count := 1
    let mut depth := 1
    let decoded ← match node with
      | .str _ => do
        bytes := node.compress.utf8ByteSize
        pure node
      | .arr refs => do
        let mut indices : Array Nat := #[]
        for ref in refs do
          let .str s := ref | throw "variant-descriptor"
          let some index := s.toNat? | throw "variant-descriptor"
          require (toString index == s && index < values.size)
          bytes := bytes + sizes[index]! + (if indices.isEmpty then 0 else 1)
          count := count + counts[index]!
          depth := max depth (depths[index]! + 1)
          require (bytes ≤ byteBudget && count ≤ nodeBudget && depth ≤ 64)
          indices := indices.push index
        require (totalBytes + bytes ≤ byteBudget && totalNodes + count ≤ nodeBudget)
        pure (.arr (indices.map fun i => values[i]!))
      | _ => throw "variant-descriptor"
    totalBytes := totalBytes + bytes
    totalNodes := totalNodes + count
    require (totalBytes ≤ byteBudget && totalNodes ≤ nodeBudget)
    values := values.push decoded
    sizes := sizes.push bytes
    counts := counts.push count
    depths := depths.push depth
  let tree := values.back!
  require ((← pack tree) == text)
  return tree

private def descriptorTree (d : Descriptor) : Except String Json := do
  let arms ← d.alternatives.mapM fun (label, payload) => do
    let payload ← payload.mapM fun ty =>
      if ty.startsWith "variant:" then unpack ty else pure (Json.str ty)
    return Json.arr #[.str label, .arr payload.toArray]
  return .arr #[d.nominal, .arr arms.toArray]

def Descriptor.json (d : Descriptor) : Json :=
  ((descriptorTree d).bind packJson).toOption.getD (.arr #[])

def Descriptor.identity (d : Descriptor) : String := hex d.json.compress.toUTF8

def Descriptor.spelling (d : Descriptor) : String := "variant:" ++ d.identity

private def fromTree : Nat → Json → Except String Descriptor
  | 0, _ => .error "variant-descriptor"
  | fuel + 1, tree => do
    let .arr #[nominal, .arr alternatives] := tree | throw "variant-descriptor"
    require (nominal != .str "" && alternatives.size > 0 && alternatives.size ≤ 32)
    let alternatives ← alternatives.toList.mapM fun arm => do
      let .arr #[.str label, .arr payload] := arm | throw "variant-descriptor"
      require (name label && payload.size ≤ 128)
      let payload ← payload.toList.mapM fun j => match j with
        | .str ty => do
          require (!ty.startsWith "variant:" && !(ty.contains '@'))
          pure ty
        | .arr _ => do
          let _ ← fromTree fuel j
          pack j
        | _ => throw "variant-descriptor"
      return (label, payload)
    require ((alternatives.map Prod.fst).eraseDups.length == alternatives.length)
    return ⟨nominal, alternatives⟩

/-- Canonical exact self-contained graph; the binding owner checks ordinary leaves. -/
def parse (text : String) : Except String Descriptor := do
  fromTree 8 (← unpack text)

/-- Permissions include every alternative, including inactive alternatives. -/
def allLeaves (leaf : String → Bool) : Nat → String → Bool
  | 0, _ => false
  | depth + 1, ty =>
    if ty.startsWith "variant:" then
      match parse ((ty.splitOn "@").head!) with
      | .error _ => false
      | .ok d => d.alternatives.all fun arm => arm.2.all fun t =>
          if t.startsWith "variant:" then allLeaves leaf depth t else leaf t
    else leaf ty

end Tools.Interactive.Variant
