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

/-- Only the advertised data fragment is reconstructed. Unknown carriers and
recursive declarations refuse rather than being assigned a guessed meaning. -/
def flatten (source : SourceDeclarations) : Nat → OriginTerm → Except String (List Ty)
  | 0, _ => .error "component-declaration-depth"
  | depth + 1, term => do
    match term with
    | .boolean => return [.boolean]
    | .index => return [.index]
    | .field name => return [.field name]
    | .group name => return [.group name]
    | .unit => return []
    | .tuple fields => return (← fields.mapM (flatten source depth)).flatten
    | .array element count =>
      let some count := count.toNat? | throw "component-declaration-type"
      if count > 512 then throw "component-declaration-limit"
      let fields ← flatten source depth element
      if fields.length * count > 512 then throw "component-declaration-limit"
      return (List.replicate count fields).flatten
    | .builtin "vector" [.field name] | .builtin "field_array" [.field name, _] =>
      return [.vector name]
    | .nominal .record _ _ =>
      let record ← requireSome (source.record? term) "component-declaration-record"
      return (← record.fields.mapM (fun field => flatten source depth field.2)).flatten
    | _ => throw "component-declaration-type"

def checkPorts (source : SourceDeclarations) (signature : ProtocolSignature)
    (ports : List SourcePort) (types : List Ty) (scopes : List (List Nat))
    (services : Bool) : Except String Unit := do
  let mut offset := 0
  let names := ports.map (·.name)
  if names.eraseDups.length != names.length then throw "component-declaration-duplicate"
  for port in ports do
    if port.offset != offset then throw "component-declaration-port"
    let flat ← source.flatten Limits.nesting port.type
    if flat.length != port.count || (types.drop offset).take port.count != flat then
      throw "component-declaration-type"
    let roles ← port.roles.mapM (resolveRole signature.roles)
    if roles.eraseDups.length != roles.length then throw "component-declaration-role"
    for index in List.range port.count do
      if scopes[offset + index]? != some roles then throw "component-declaration-role"
    if source.isLinear port.type && (roles.length != 1 || port.count == 0) then
      throw "component-claim-role"
    offset := offset + port.count
  if services then
    if !(types.drop offset).all Ty.isService then throw "component-declaration-port"
  else if offset != types.length then throw "component-declaration-port"

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
  if source.records.isEmpty && source.protocols.isEmpty then return
  if source.records.length > Limits.tableEntries || source.protocols.length > Limits.tableEntries then
    throw "component-declaration-limit"
  let keys := source.records.map (·.type)
  if keys.eraseDups.length != keys.length then throw "component-declaration-duplicate"
  for record in source.records do
    let .nominal .record _ _ := record.type | throw "component-declaration-record"
    unless ["ordinary", "affine", "linear"].contains record.resource do throw "component-declaration"
    if record.resource == "linear" && !record.sealed then throw "component-declaration-record"
    let names := record.fields.map Prod.fst
    if names.eraseDups.length != names.length then throw "component-declaration-duplicate"
    let _ ← source.flatten Limits.nesting record.type
  let owners := source.protocols.map (·.name)
  if owners.eraseDups.length != owners.length || owners.length != headers.length then
    throw "component-declaration-owner"
  let mut meanings : List (OriginTerm × String) := []
  for protocol in source.protocols do
    let header ← requireSome (headers.find? (·.name == protocol.name)) "component-declaration-owner"
    source.checkPorts header protocol.inputs header.inputs header.inputScopes true
    source.checkPorts header protocol.outputs header.outputs header.outputScopes false
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

end SourceDeclarations
end Zkc.Source.Structured
