module

public import Zkc.Source.Structured.ProtocolAdmission

@[expose] public section

/-! Resolution of retained protocol Oracle descriptors. The same source lookup supplies
the declaration signature and the structural construction site; callers cannot install a
replacement body. This module does not itself grant whole-unit availability. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

def Descriptor.protocolLogicalTransport : Descriptor → Bool
  | .oracle _ | .protocolApply .. | .protocolRepeat .. => true
  | _ => false

/-- Stored instruction coordinates, including callback positions. Fuel is the independently
checked syntax depth, not an execution bound. Named construction sites are unique per body. -/
def Block.siteRows : Nat → Block → List Nat → List (String × List Nat)
  | 0, _, _ => []
  | depth + 1, .block instructions _, path =>
    instructions.zipIdx.flatMap fun (.instruction _ _ _ regions site, index) ↦
      let row := path ++ [1, index]
      (site, row) :: (regions.zipIdx.flatMap fun (.region _ _ body, child) ↦
        body.siteRows depth (row ++ [4, child, 3]))

/-- Oracle-only preorder agrees with lowering, which resolves an instruction before its
callbacks. Unnamed pure occurrences therefore retain their own position as well. -/
def Block.oracleRows : Nat → Block → List Nat → List (OracleDescriptor × List Nat)
  | 0, _, _ => []
  | depth + 1, .block instructions _, path =>
    instructions.zipIdx.flatMap fun (.instruction descriptor _ _ regions _, index) ↦
      let row := path ++ [1, index]
      (match descriptor with | .oracle op => [(op, row)] | _ => []) ++
        regions.zipIdx.flatMap (fun (.region _ _ body, child) ↦
          body.oracleRows depth (row ++ [4, child, 3]))

def sourceOracleLocation (snapshot : Snapshot) (function : Function)
    (cursor : Nat) (descriptor : OracleDescriptor) :
    Except String OracleLocation := do
  let definition := snapshot.definitions.findIdx (·.name == function.name)
  if definition ≥ snapshot.definitions.length then throw "oracle-protocol-source"
  let some (original, row) := (function.body.oracleRows Limits.nesting [7])[cursor]?
    | throw "oracle-protocol-site"
  if original != descriptor then throw "oracle-protocol-occurrence"
  return ⟨⟨definition, []⟩, definition, row⟩

def resolveOracleProtocolOp (snapshot : Snapshot) (interface : ProtocolInterface)
    (descriptor : OracleDescriptor) : Except String OracleOp := do
  let role := resolveRole interface.roles
  let pair := fun holder receivers ↦ do
    let holder ← role holder
    let receivers ← resolveScope interface.roles receivers
    if receivers.contains holder then throw "oracle-protocol-holder"
    return (holder, receivers)
  match descriptor with
  | .input holder receivers type bounds =>
    let some sort := OracleLogicalSort.ofType type | throw "oracle-protocol-sort"
    let (holder, receivers) ← pair holder receivers
    return .input sort holder receivers bounds
  | .send holder receivers kind dimensions bounds =>
    if dimensions != kind.shape.map Prod.fst then throw "oracle-protocol-shape"
    let (holder, receivers) ← pair holder receivers
    return .send kind holder receivers bounds
  | .query owner kind =>
    let some owner := owner | throw "oracle-protocol-inherited-owner"
    return .query kind (some (← role owner))
  | .contents owner kind => return .contents kind (← role owner)
  | .components holder receivers type =>
    let some sort := OracleLogicalSort.ofType type | throw "oracle-protocol-sort"
    let (holder, receivers) ← pair holder receivers
    return .components sort holder receivers
  | .shape kind dimension =>
    if !(kind.shape.map Prod.fst).contains dimension then throw "oracle-protocol-shape"
    return .shape kind dimension
  | .forgetShape source target =>
    let .table row (some _) := source | throw "oracle-protocol-shape"
    if target != .table row none then throw "oracle-protocol-shape"
    return .forgetShape source target
  | .virtual name holder receivers kind =>
    let .oracle declaration ← lookupDefinition snapshot name | throw "oracle-protocol-declaration"
    if declaration.kind != kind then throw "oracle-protocol-declaration"
    let (holder, receivers) ← pair holder receivers
    return .virtual declaration.signature holder receivers
  | .sequenceEmpty kind maximum =>
    -- Empty has no owner or effects in original PIR. It is a pure constant at the
    -- current roster; the first append checks its actual participating roles.
    return .sequenceEmpty kind maximum (List.range interface.roles.length)
  | .sequenceAppend kind maximum roles =>
    return .sequenceAppend kind maximum (← resolveScope interface.roles roles)
  | .sequenceAt kind maximum roles =>
    return .sequenceAt kind maximum (← resolveScope interface.roles roles)
  | .sequenceLength kind maximum => return .sequenceLength kind maximum

end Zkc.Source.Structured
