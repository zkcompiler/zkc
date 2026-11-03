module

public import Zkc.Source.Structured.ContractAdmission

@[expose] public section

/-! Retained frontend declaration context. It fixes linearity and source port
boundaries before native flattening. Admission checks the native association;
source-to-IR correspondence remains the existing frontend assurance boundary. -/
namespace Zkc.Source.Structured

namespace SourceDeclarations

def record? (source : SourceDeclarations) (type : OriginTerm) : Option SourceRecord :=
  source.records.find? (·.type == type)

def isLinear (source : SourceDeclarations) (type : OriginTerm) : Bool :=
  (source.record? type).any (·.resource == "linear")

/-- What one native leaf of a source port holds: data of an exact type, or the
custody permission of a closed resource record. -/
inductive LeafKind where
  | data (type : Ty)
  | custody (owner : OriginTerm)
  deriving BEq, Repr

/-- One ordered native leaf of a source port: what it holds, its effective
placement and its path of field names, array positions and tuple positions
below the port. An ordinary record places every leaf, private fields included,
at the port's roles. -/
structure Leaf where
  kind : LeafKind
  path : List String
  deriving BEq, Repr

/-- Reconstruct ordered leaves with each resource record's custody prefix.
Zero-length arrays retain their element's declaration obligations. Distributed
and variant semantics require separate admission beyond reading their metadata. -/
def leaves (source : SourceDeclarations) : Nat → OriginTerm → List String → Except String (List Leaf)
  | 0, _, _ => .error "component-declaration-depth"
  | depth + 1, term, path => do
    match term with
    | .boolean => return [⟨.data .boolean, path⟩]
    | .index => return [⟨.data .index, path⟩]
    | .field name => return [⟨.data (.field name), path⟩]
    | .group name => return [⟨.data (.group name), path⟩]
    | .unit => return []
    | .tuple fields =>
      return (← fields.zipIdx.mapM fun (field, position) =>
        leaves source depth field (path ++ [toString position])).flatten
    | .array element count =>
      let some count := count.toNat? | throw "component-declaration-type"
      if count > 512 then throw "component-declaration-limit"
      let template ← leaves source depth element path
      if template.length * count > 512 then throw "component-declaration-limit"
      return (← (List.range count).mapM fun position =>
        leaves source depth element (path ++ [toString position])).flatten
    | .builtin "vector" [.field name] | .builtin "field_array" [.field name, _] =>
      return [⟨.data (.vector name), path⟩]
    | .nominal .record _ _ =>
      let record ← requireSome (source.record? term) "component-declaration-record"
      let .fields fields := record.members | throw "component-declaration-record"
      let custody := if record.slot.isSome then [⟨LeafKind.custody term, path⟩] else []
      return custody ++ (← fields.mapM fun field =>
        leaves source depth field.type (path ++ [field.name])).flatten
    | .nominal .logicalRecord _ _ => throw "component-declaration-distributed"
    | _ => throw "component-declaration-type"

/-- Check one port list against the native signature and scopes, returning the
custody slots its leaves exhibit for their owners. A custody leaf is a native
`resource_unit` of one holder; a data leaf has its exact type. -/
def checkPorts (source : SourceDeclarations) (signature : ProtocolSignature)
    (ports : List SourcePort) (types : List Ty) (scopes : List (List Nat))
    (services : Bool) : Except String (List (OriginTerm × String)) := do
  let mut offset := 0
  let mut slots : List (OriginTerm × String) := []
  let names := ports.map (·.name)
  if names.eraseDups.length != names.length then throw "component-declaration-duplicate"
  for port in ports do
    if port.offset != offset then throw "component-declaration-port"
    let .data placed := port.placement | throw "component-declaration-distributed"
    if placed != port.roles || signature.roles.filter port.roles.contains != port.roles then
      throw "component-declaration-placement"
    let described ← source.leaves Limits.nesting port.type [port.name]
    if described.length != port.count then throw "component-declaration-type"
    let roles ← port.roles.mapM (resolveRole signature.roles)
    if roles.eraseDups.length != roles.length then throw "component-declaration-role"
    for (leaf, index) in described.zipIdx do
      let some native := types[offset + index]? | throw "component-declaration-type"
      match leaf.kind with
      | .data type => if native != type then throw "component-declaration-type"
      | .custody owner =>
        let .resourceUnit slot := native | throw "component-declaration-custody"
        let record ← requireSome (source.record? owner) "component-declaration-record"
        if record.slot != some slot then throw "component-declaration-custody-identity"
        if roles.length != 1 then throw "component-declaration-custody-holder"
        slots := (owner, slot) :: slots
      if scopes[offset + index]? != some roles then throw "component-declaration-role"
    offset := offset + port.count
  if services then
    if !(types.drop offset).all Ty.isService then throw "component-declaration-port"
  else if offset != types.length then throw "component-declaration-port"
  return slots

/-- Declared custody slots associate closed resource records with native types.
Every stored custody type must belong to a row, including helper-local values
that never reach an external port. Slot digests are not recomputed here. -/
def checkSlots (snapshot : Snapshot) (slots : List (OriginTerm × String)) : Except String Unit := do
  for (owner, slot) in slots do
    for (other, otherSlot) in slots do
      if (owner == other) != (slot == otherSlot) then throw "component-declaration-custody-identity"
  for type in snapshot.storedTypes do
    if let .resourceUnit slot := type then
      if !slots.any (·.2 == slot) then throw "component-declaration-custody-association"

/-- A linear port carries one claim holder. This is a property of the claim
association, separate from layout and placement admission. -/
def checkLinearHolders (source : SourceDeclarations) (ports : List SourcePort) :
    Except String Unit := do
  for port in ports do
    if source.isLinear port.type && (port.roles.length != 1 || port.count == 0) then
      throw "component-claim-role"

/-- Locate the unique retained relation on a linear source port. The relation
comes from checked clauses, never from a field name or a proposal. -/
def relations (contract : ProtocolContract) (port : SourcePort) (direction : ContractDirection) :
    List String :=
  contract.clauses.flatMap fun clause =>
    (clause.subject :: clause.residual.toList).filterMap fun application =>
      if application.selectors.any (fun selector => selector.direction == direction &&
          port.offset ≤ selector.port && selector.port < port.offset + port.count) then
        some application.relation else none

/-- Selection fixes the protocol under study, including a library root with
linear inputs or residual outputs. Concrete Entry target and acceptance
selection are separate obligations; these declarations only associate ports. -/
def check (source : SourceDeclarations) (snapshot : Snapshot)
    (headers : List ProtocolSignature) : Except String Unit := do
  source.checkShape
  if source.records.isEmpty && source.protocols.isEmpty then return
  if source.records.length > Limits.tableEntries || source.protocols.length > Limits.tableEntries then
    throw "component-declaration-limit"
  let keys := source.records.map (·.type)
  if keys.eraseDups.length != keys.length then throw "component-declaration-duplicate"
  for record in source.records do
    match record.type with
    | .nominal .record _ _ => pure ()
    | .nominal .logicalRecord _ _ => throw "component-declaration-distributed"
    | .nominal .variant _ _ => throw "component-declaration-variant"
    | _ => throw "component-declaration-record"
    -- Sealing restricts source access; it is independent of the resource tag.
    unless ["ordinary", "affine", "linear"].contains record.resource do throw "component-declaration"
    let names := record.members.allFields.map (·.name)
    if names.eraseDups.length != names.length then throw "component-declaration-duplicate"
    let _ ← source.leaves Limits.nesting record.type []
  let owners := source.protocols.map (·.name)
  if owners.eraseDups.length != owners.length || owners.length != headers.length then
    throw "component-declaration-owner"
  let mut meanings : List (OriginTerm × String) := []
  let slots := source.records.filterMap fun record => record.slot.map (record.type, ·)
  for protocol in source.protocols do
    let header ← requireSome (headers.find? (·.name == protocol.name)) "component-declaration-owner"
    discard <| source.checkPorts header protocol.inputs header.inputs header.inputScopes true
    discard <| source.checkPorts header protocol.outputs header.outputs header.outputScopes false
    source.checkLinearHolders protocol.inputs
    source.checkLinearHolders protocol.outputs
    let contract ← requireSome (snapshot.contracts.find? (·.owner == protocol.name)) "component-declaration-owner"
    for (direction, ports) in [(ContractDirection.input, protocol.inputs), (.output, protocol.outputs)] do
      for port in ports do
        if source.isLinear port.type then
          -- A clause-free wrapper exposes a resource boundary without asserting
          -- a relation. Contracted protocols must cover every linear port.
          if contract.clauses.isEmpty then continue
          let relations := (relations contract port direction).eraseDups
          let [relation] := relations | throw "component-claim-relation"
          let key := port.type
          if let some (_, previous) := meanings.find? (·.1 == key) then
            if previous != relation then throw "component-claim-relation"
          else meanings := (key, relation) :: meanings
  checkSlots snapshot slots

end SourceDeclarations
end Zkc.Source.Structured
