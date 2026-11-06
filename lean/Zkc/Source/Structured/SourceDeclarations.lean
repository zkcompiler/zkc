module

public import Zkc.Source.Structured.Origin
public import Zkc.Source.LogicalFormat

@[expose] public section

/-! Retained source declarations and their current wire carrier. Shape checking
is independent of native layout admission. Authority revisions are retained and
checked for exact coverage, not recomputed from source bytes by this reader. -/
namespace Zkc.Source.Structured
open Lean

inductive SourcePlacement where
  | data (roles : List String)
  | oracle (holder : String) (receivers : List String)
  | product (arguments : List String) (fields : List SourcePlacement)
  deriving Repr

mutual
  /-- Source admission compares whole placement trees in the kernel, including
  receiver order and every child of a product. -/
  def SourcePlacement.decEq (a b : SourcePlacement) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | exact isFalse (SourcePlacement.noConfusion ·) | skip
    case data.data a b =>
      exact decidable_of_iff (a = b) (by simp only [SourcePlacement.data.injEq])
    case oracle.oracle h r h' r' =>
      exact decidable_of_iff (h = h' ∧ r = r') (by simp only [SourcePlacement.oracle.injEq])
    case product.product a xs b ys =>
      letI : Decidable (xs = ys) := SourcePlacement.listDecEq xs ys
      exact decidable_of_iff (a = b ∧ xs = ys) (by simp only [SourcePlacement.product.injEq])

  def SourcePlacement.listDecEq : (xs ys : List SourcePlacement) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro same; cases same)
    | _ :: _, [] => isFalse (by intro same; cases same)
    | x :: xs, y :: ys => by
      letI : Decidable (x = y) := SourcePlacement.decEq x y
      letI : Decidable (xs = ys) := SourcePlacement.listDecEq xs ys
      exact decidable_of_iff (x = y ∧ xs = ys) (by simp only [List.cons.injEq])
end

instance : DecidableEq SourcePlacement := SourcePlacement.decEq
instance : BEq SourcePlacement := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq SourcePlacement where
  eq_of_beq := of_decide_eq_true
  rfl := by intro placement; exact decide_eq_true rfl

/-- The top-level participant summary. Product arguments preserve telescope
order; child roles are checked separately and never added to this summary. -/
def SourcePlacement.roles : SourcePlacement → List String
  | .data roles => roles
  | .oracle holder receivers => holder :: receivers
  | .product arguments _ => arguments

structure SourceField where
  name : String
  type : OriginTerm
  placement : Option SourcePlacement
  deriving BEq, Repr

inductive SourceMembers where
  | fields (values : List SourceField)
  | alternatives (values : List (String × List SourceField))
  deriving BEq, Repr

def SourceMembers.allFields : SourceMembers → List SourceField
  | .fields values => values
  | .alternatives values => values.flatMap Prod.snd

structure SourceRecord where
  type : OriginTerm
  resource : String
  sealed : Bool
  members : SourceMembers
  roles : List String
  slot : Option String
  deriving BEq, Repr

structure SourcePort where
  name : String
  type : OriginTerm
  roles : List String
  offset : Nat
  count : Nat
  placement : SourcePlacement
  deriving BEq, Repr

structure SourceProtocol where
  name : String
  inputs : List SourcePort
  outputs : List SourcePort
  deriving BEq, Repr

structure SourceDeclarations where
  records : List SourceRecord := []
  protocols : List SourceProtocol := []
  authorities : List (String × Option String) := []
  deriving BEq, Repr

namespace SourceDeclarations

def namesValid (names : List String) (limit : Nat) : Bool :=
  names.length ≤ limit && names.all originStringValid && names.eraseDups.length == names.length

def revisionValid (value : String) : Bool :=
  value.length == 64 && value.toList.all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f'))

def slotValid (value : String) : Bool :=
  "zkl_resource_".toList.isPrefixOf value.toList && Source.LogicalFormat.slotIdentityValid value

def SourcePlacement.check (telescope : Option (List String)) : Nat → SourcePlacement → Except String Unit
  | 0, _ => .error "component-declaration-limit"
  | depth + 1, value => do
    let roles := value.roles
    unless namesValid roles Limits.protocolRoles do throw "component-declaration-role"
    if let some scope := telescope then
      unless roles.all scope.contains do throw "component-declaration-role"
    if let .product _ fields := value then
      if fields.length > Limits.listEntries then throw "component-declaration-limit"
      fields.forM (SourcePlacement.check telescope depth)

/-- All origin terms directly retained in the declarations. Nominal arguments
are traversed below, including phantom and zero-length children. -/
def terms (source : SourceDeclarations) : List OriginTerm :=
  source.records.flatMap (fun row => row.type :: row.members.allFields.map (·.type)) ++
    source.protocols.flatMap (fun row => (row.inputs ++ row.outputs).map (·.type))

def termChildren : OriginTerm → List OriginTerm
  | .tuple values | .nominal _ _ values | .builtin _ values | .formal _ values => values
  | .array value _ => [value]
  | _ => []

def termNominals : Nat → OriginTerm → List (OriginNominalKind × String × OriginTerm)
  | 0, _ => []
  | depth + 1, value =>
    let own := match value with
      | .nominal kind path _ => [(kind, path, value)]
      | _ => []
    own ++ (termChildren value).flatMap (termNominals depth)

def checkFields (placed : Bool) (roles : List String) (fields : List SourceField) : Except String Unit := do
  unless namesValid (fields.map (·.name)) Limits.listEntries do throw "component-declaration-duplicate"
  for field in fields do
    unless field.type.valid Limits.nesting do throw "component-declaration-type"
    if field.placement.isSome != placed then throw "component-declaration-placement"
    if let some placement := field.placement then
      SourcePlacement.check (some roles) Limits.nesting placement

/-- Check the producer's required order directly; no sorting implementation is
part of this public, kernel-reducible admission computation. -/
def authorityOrder : List String → Bool
  | [] | [_] => true
  | first :: second :: rest => first < second && authorityOrder (second :: rest)

/-- Shared shape obligations also apply to directly constructed Lean data.
Semantic admission additionally checks the native signature and placement. -/
def checkShape (source : SourceDeclarations) : Except String Unit := do
  if source.records.length > Limits.tableEntries || source.protocols.length > Limits.tableEntries then
    throw "component-declaration-limit"
  let types := source.records.map (·.type)
  if types.eraseDups.length != types.length then throw "component-declaration-duplicate"
  for row in source.records do
    unless row.type.valid Limits.nesting do throw "component-declaration-type"
    let .nominal kind _ _ := row.type | throw "component-declaration-record"
    unless [OriginNominalKind.record, .logicalRecord, .variant].contains kind do
      throw "component-declaration-record"
    unless ["ordinary", "affine", "linear"].contains row.resource do throw "component-declaration"
    if row.slot.isSome != (row.resource != "ordinary") || !row.slot.all slotValid then
      throw "component-declaration-slot"
    unless namesValid row.roles Limits.recordRoles do throw "component-declaration-role"
    if kind != .logicalRecord && !row.roles.isEmpty then throw "component-declaration-role"
    match kind, row.members with
    | .variant, .alternatives alternatives =>
      unless namesValid (alternatives.map Prod.fst) Limits.listEntries do
        throw "component-declaration-duplicate"
      alternatives.forM fun (_, fields) => checkFields false [] fields
    | .record, .fields fields | .logicalRecord, .fields fields =>
      checkFields (!row.roles.isEmpty) row.roles fields
    | _, _ => throw "component-declaration-record"
  unless namesValid (source.protocols.map (·.name)) Limits.tableEntries do
    throw "component-declaration-owner"
  for protocol in source.protocols do
    for ports in [protocol.inputs, protocol.outputs] do
      unless namesValid (ports.map (·.name)) Limits.listEntries do
        throw "component-declaration-duplicate"
      for port in ports do
        unless port.type.valid Limits.nesting do throw "component-declaration-type"
        unless namesValid port.roles Limits.protocolRoles do throw "component-declaration-role"
        if port.count > Limits.listEntries || port.offset > Limits.instructions then
          throw "component-declaration-limit"
        SourcePlacement.check none Limits.nesting port.placement
        let roles := port.placement.roles
        if roles.length != port.roles.length || !roles.all port.roles.contains then
          throw "component-declaration-placement"
  let terms := source.terms
  unless terms.all (·.valid Limits.nesting) do throw "component-declaration-type"
  let nominals := terms.flatMap (termNominals Limits.nesting)
  for (kind, path, term) in nominals do
    if [OriginNominalKind.record, .logicalRecord, .variant].contains kind then
      unless types.contains term do throw "component-declaration-record"
      unless source.records.all (fun row => match row.type with
        | .nominal other name _ => name != path || other == kind
        | _ => false) do throw "component-declaration-record"
  let paths := (nominals.filterMap fun (kind, path, _) =>
    if kind == .associated then none else some path).eraseDups
  let published := source.authorities.map Prod.fst
  unless authorityOrder published && published.length == paths.length &&
      paths.all published.contains do throw "component-declaration-authority"
  unless source.authorities.all (fun (_, revision) => revision.all revisionValid) do
    throw "component-declaration-authority"

end SourceDeclarations

namespace DeclarationFormat
open OriginFormat

def placement : Nat → Json → Except String SourcePlacement
  | 0, _ => .error "component-declaration-limit"
  | depth + 1, value => do
    match ← array value 3 with
    | [.str "data", roles] => return .data (← (← array roles Limits.protocolRoles).mapM string)
    | [.str "oracle", holder, receivers] =>
      return .oracle (← string holder) (← (← array receivers Limits.protocolRoles).mapM string)
    | [.str "product", arguments, fields] =>
      return .product (← (← array arguments Limits.protocolRoles).mapM string)
        (← (← array fields Limits.listEntries).mapM (placement depth))
    | _ => throw "component-declaration-placement"

def optional {α : Type} (decode : Json → Except String α) : Json → Except String (Option α)
  | .null => pure none
  | value => some <$> decode value

def field (value : Json) : Except String SourceField := do
  let [name, type, placed] ← array value 3 | throw "component-declaration"
  return ⟨← string name, ← term Limits.nesting type, ← optional (placement Limits.nesting) placed⟩

def record (value : Json) : Except String SourceRecord := do
  let [type, .str resource, .bool sealed, fields, roles, slot] ← array value 6 |
    throw "component-declaration"
  let type ← term Limits.nesting type
  let members ← match type with
    | .nominal .variant _ _ => do
      let values ← (← array fields Limits.listEntries).mapM fun alternative => do
        let [name, fields] ← array alternative 2 | throw "component-declaration"
        return (← string name, ← (← array fields Limits.listEntries).mapM field)
      pure (SourceMembers.alternatives values)
    | _ => SourceMembers.fields <$> (← array fields Limits.listEntries).mapM field
  return ⟨type, resource, sealed, members,
    ← (← array roles Limits.recordRoles).mapM string, ← optional string slot⟩

def natural (value : Json) (limit : Nat) : Except String Nat := do
  let result ← (Source.Format.natural value).mapError fun _ => "component-declaration"
  if result > limit then throw "component-declaration-limit"
  return result

def port (value : Json) : Except String SourcePort := do
  let [name, type, roles, offset, count, placed] ← array value 6 | throw "component-declaration"
  return ⟨← string name, ← term Limits.nesting type,
    ← (← array roles Limits.protocolRoles).mapM string,
    ← natural offset Limits.instructions, ← natural count Limits.listEntries,
    ← placement Limits.nesting placed⟩

def decode (value : Json) : Except String SourceDeclarations := do
  let [records, protocols, authorities] ← array value 3 | throw "component-declaration"
  let records ← (← array records Limits.tableEntries).mapM record
  let protocols ← (← array protocols Limits.tableEntries).mapM fun value => do
    let [name, inputs, outputs] ← array value 3 | throw "component-declaration"
    return SourceProtocol.mk (← string name) (← (← array inputs Limits.listEntries).mapM port)
      (← (← array outputs Limits.listEntries).mapM port)
  let authorities ← (← array authorities Limits.parsedBytes).mapM fun value => do
    let [path, revision] ← array value 2 | throw "component-declaration-authority"
    return (← string path, ← optional string revision)
  let result : SourceDeclarations := ⟨records, protocols, authorities⟩
  result.checkShape
  return result

end DeclarationFormat
end Zkc.Source.Structured
