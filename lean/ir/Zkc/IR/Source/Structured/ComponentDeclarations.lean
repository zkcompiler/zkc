module

public import Zkc.IR.Source.Structured.SourcePlacementShape

@[expose] public section

/-! Retained frontend declaration context. It fixes linearity and source port
boundaries before native flattening. Admission checks the native association;
source-to-IR correspondence remains the existing frontend assurance boundary. -/
namespace Zkc.Source.Structured

namespace SourceDeclarations

/-- The exact native type selected by one retained leaf, including custody identity. -/
def Leaf.nativeType (source : SourceDeclarations) (leaf : Leaf) : Except String Ty := do
  match leaf.kind with
  | .data type | .holderData type | .receiverHandle type => return type
  | .custody owner =>
    let record ← requireSome (source.record? owner) "component-declaration-record"
    let slot ← requireSome record.slot "component-declaration-custody-identity"
    return .resourceUnit slot

/-- A single checked association, shared by every placement and source category. -/
def associateLeaf (source : SourceDeclarations) (roster : List String) (leaf : PlacedLeaf)
    (native : Ty) (scope : List Nat) : Except String Unit := do
  let expected ← leaf.leaf.nativeType source
  if native != expected then
    match leaf.leaf.kind with
    | .custody _ => throw "component-declaration-custody-identity"
    | _ => throw "component-declaration-type"
  let roles ← leaf.roles.mapM (resolveRole roster)
  if roles != scope then throw "component-declaration-role"

/-- Successful association reads back the exact type and oriented role scope.
This structural fact asserts neither frontend correctness nor custody conservation. -/
theorem associateLeaf_readback {source : SourceDeclarations} {roster : List String}
    {leaf : PlacedLeaf} {native : Ty} {scope : List Nat}
    (accepted : associateLeaf source roster leaf native scope = .ok ()) :
    leaf.leaf.nativeType source = .ok native ∧
      leaf.roles.mapM (resolveRole roster) = .ok scope := by
  unfold associateLeaf at accepted
  cases typeEq : leaf.leaf.nativeType source with
  | error code => simp [typeEq, bind, Except.bind] at accepted
  | ok expected =>
    simp only [typeEq, bind, Except.bind] at accepted
    split at accepted
    · cases kindEq : leaf.leaf.kind <;> simp [kindEq, throw] at accepted
    · rename_i same
      have equality : native = expected := by simpa using same
      subst expected
      cases roleEq : leaf.roles.mapM (resolveRole roster) with
      | error code => simp [roleEq] at accepted
      | ok roles =>
        simp only [roleEq] at accepted
        split at accepted
        · contradiction
        · rename_i sameRoles
          have equality : roles = scope := by simpa using sameRoles
          subst roles
          exact ⟨rfl, rfl⟩

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
  if scopes.length != types.length then throw "component-declaration-role"
  for port in ports do
    if port.offset != offset then throw "component-declaration-port"
    let summary := rosterSet signature.roles port.placement.roles
    if summary != port.roles then throw "component-declaration-placement"
    let described ← source.placedLeaves signature.roles port
    if described.length != port.count then throw "component-declaration-type"
    for (leaf, index) in described.zipIdx do
      let some native := types[offset + index]? | throw "component-declaration-type"
      let some scope := scopes[offset + index]? | throw "component-declaration-role"
      source.associateLeaf signature.roles leaf native scope
      if let .custody owner := leaf.leaf.kind then
        let .resourceUnit slot := native | throw "component-declaration-custody"
        slots := (owner, slot) :: slots
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
    -- The current CLAIM relation has a single holder, whereas a distributed
    -- linear record has one custody fragment per telescope role. Keep this
    -- claim boundary explicit even inside structural products.
    for leaf in ← source.leaves Limits.nesting port.type [] do
      if let .custody owner := leaf.kind then
        if let some row := source.record? owner then
          if row.resource == "linear" then
            if !row.roles.isEmpty then
              throw "component-claim-distributed-custody-profile"
            if port.roles.length != 1 && !source.isLinear port.type then
              throw "component-claim-fragmented-custody-profile"
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
    | .nominal .logicalRecord _ _ => pure ()
    | .nominal .variant _ _ => throw "component-declaration-variant"
    | _ => throw "component-declaration-record"
    -- Sealing restricts source access; it is independent of the resource tag.
    unless ["ordinary", "affine", "linear"].contains record.resource do throw "component-declaration"
    let names := record.members.allFields.map (·.name)
    if names.eraseDups.length != names.length then throw "component-declaration-duplicate"
    source.checkRecordPlacement record
  let owners := source.protocols.map (·.name)
  if owners.eraseDups.length != owners.length || owners.length != headers.length then
    throw "component-declaration-owner"
  let mut meanings : List (OriginTerm × String) := []
  let slots := source.records.filterMap fun record => record.slot.map (record.type, ·)
  for protocol in source.protocols do
    let header ← requireSome (headers.find? (·.name == protocol.name)) "component-declaration-owner"
    if protocol.name == snapshot.entry && header.inputs.any (fun type => match type with
        | .oracleSequence .. => true | _ => false) then throw "oracle-root-sequence-ingress"
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
