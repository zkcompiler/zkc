module

public import Zkc.Source.Structured.ContractAdmission

@[expose] public section

/-! Declaration shapes and the single source-placement traversal. Shapes retain
zero-array templates and nominal custody; placed leaves are checked against the
native header by ComponentDeclarations. No execution or security law is asserted. -/
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
  | holderData (type : Ty)
  | receiverHandle (type : Ty)
  deriving BEq, Repr

/-- One ordered native leaf of a source port: what it holds, its effective
placement and its path of field names, array positions and tuple positions
below the port. An ordinary record places every leaf, private fields included,
at the port's roles. -/
structure Leaf where
  kind : LeafKind
  path : List String
  deriving BEq, Repr

/-- A declaration tree before placement. Arrays retain one element template. -/
inductive PlacementShape where
  | data (type : Ty)
  | unit
  | oracle (data handle : Ty)
  | tuple (fields : List PlacementShape)
  | array (element : PlacementShape) (count : Nat)
  | record (declaration : SourceRecord) (fields : List PlacementShape)
  deriving BEq, Repr

abbrev PlacementCheck := StateT Nat (Except String)

/-- A cumulative visit budget also bounds repeated, phantom and zero-storage expansion. -/
def chargePlacement : PlacementCheck Unit := do
  let remaining ← get
  if remaining == 0 then throw "component-declaration-limit"
  set (remaining - 1)

def PlacementShape.logical : Nat → PlacementShape → Bool
  | 0, _ => true
  | depth + 1, .tuple fields => fields.any (logical depth)
  | depth + 1, .array element _ => logical depth element
  | _, .oracle .. => true
  | _, .record row _ => match row.type with
    | .nominal .logicalRecord _ _ => true
    | _ => false
  | _, _ => false

def PlacementShape.shared : Nat → PlacementShape → Bool
  | 0, _ => false
  | _, .data type => !type.containsPolynomial && !type.isHandle
  | _, .unit => true
  | depth + 1, .tuple fields => fields.all (shared depth)
  | depth + 1, .array element _ => shared depth element
  | depth + 1, .record row fields =>
    row.slot.isNone && !PlacementShape.logical (depth + 1) (.record row fields) &&
      fields.all (shared depth)
  | _, _ => false

/-- Reconstruct the source shape once, refusing ordinary carriers of logical
values even when the offending child has no storage. -/
def buildPlacementShape (source : SourceDeclarations) :
    Nat → OriginTerm → PlacementCheck PlacementShape
  | 0, _ => throw "component-declaration-depth"
  | depth + 1, term => do
    chargePlacement
    match term with
    | .boolean => return .data .boolean
    | .index => return .data .index
    | .field name => return .data (.field name)
    | .group name => return .data (.group name)
    | .unit => return .unit
    | .tuple fields => return .tuple (← fields.mapM (buildPlacementShape source depth))
    | .array element count =>
      let some count := count.toNat? | throw "component-declaration-type"
      if count > Limits.listEntries then throw "component-declaration-limit"
      return .array (← buildPlacementShape source depth element) count
    | .builtin "indices" [] => return .data .indices
    | .builtin "polynomial" [.field name] => return .data (.polynomial name)
    | .builtin "vector" [.field name] | .builtin "field_array" [.field name, _] =>
      return .data (.vector name)
    | .nominal kind _ _ =>
      unless kind == .record || kind == .logicalRecord do
        throw "component-declaration-type"
      let some row := source.record? term | throw "component-declaration-record"
      let .fields fields := row.members | throw "component-declaration-record"
      let children ← fields.mapM fun field => buildPlacementShape source depth field.type
      if kind == .record && children.any (PlacementShape.logical depth) then
        throw "component-declaration-logical-field"
      if kind == .logicalRecord && row.roles.isEmpty then
        if row.slot.isSome || row.resource != "ordinary" then
          throw "component-declaration-logical-field"
        let mut handle := false
        for child in children do
          match child with
          | .oracle .. => handle := true
          | _ => unless child.shared depth do throw "component-declaration-logical-field"
        unless handle do throw "component-declaration-logical-field"
      return .record row children
    | .builtin head [kind] | .builtin head [kind, .natural _] =>
      let (row, fixed) ← match kind with
        | .builtin "oracle.table" [row] => pure (row, none)
        | .builtin "oracle.table" [row, .natural decimal] => do
          let some rows := decimal.toNat? | throw "component-declaration-type"
          if rows ≥ indexLimit then throw "component-declaration-type"
          pure (row, some rows)
        | _ => throw "component-declaration-type"
      let .data rowType ← buildPlacementShape source depth row
        | throw "component-declaration-oracle-row"
      if rowType.isHandle then throw "component-declaration-oracle-row"
      let kind := OracleKind.table rowType fixed
      match head, term with
      | "oracle", .builtin _ [_] => return .oracle kind.data (.oracle kind)
      | "oracle_sequence", .builtin _ [_, .natural decimal] =>
        let some maximum := decimal.toNat? | throw "component-declaration-type"
        if maximum ≥ indexLimit then throw "component-declaration-type"
        return .oracle (.sequence kind.data) (.oracleSequence kind maximum)
      | _, _ => throw "component-declaration-type"
    | _ => throw "component-declaration-type"

def placementShape (source : SourceDeclarations) (depth : Nat) (term : OriginTerm) :
    Except String PlacementShape :=
  (buildPlacementShape source depth term).run' Limits.originTerms

/-- Canonicalize a role SET only, preserving the roster's order. -/
def rosterSet (roster roles : List String) : List String := roster.filter roles.contains

def checkRoleSet (roster roles : List String) : Except String Unit := do
  unless namesValid roles Limits.protocolRoles && !roles.isEmpty &&
      rosterSet roster roles == roles do throw "component-declaration-placement"

def checkArguments (roster arguments : List String) : Except String Unit := do
  unless namesValid arguments Limits.protocolRoles && arguments.all roster.contains do
    throw "component-declaration-placement"

/-- Telescope substitution sorts data/receiver sets, never nominal arguments. -/
def substituteSourcePlacement (roster telescope arguments : List String) :
    Nat → SourcePlacement → PlacementCheck SourcePlacement
  | 0, _ => throw "component-declaration-depth"
  | depth + 1, value => do
    chargePlacement
    let replace := fun role => do
      let some (_, actual) := (telescope.zip arguments).find? (·.1 == role)
        | throw "component-declaration-placement"
      pure actual
    match value with
    | .data roles => return .data (rosterSet roster (← roles.mapM replace))
    | .oracle holder receivers =>
      return .oracle (← replace holder) (rosterSet roster (← receivers.mapM replace))
    | .product roles fields =>
      return .product (← roles.mapM replace)
        (← fields.mapM (substituteSourcePlacement roster telescope arguments depth))

/-- Normalize only an EXPECTED formula's structural product sets against its
shape. Candidate trees are compared exactly and are never repaired. -/
def PlacementShape.canonicalFormula :
    Nat → List String → PlacementShape → SourcePlacement → PlacementCheck SourcePlacement
  | 0, _, _, _ => throw "component-declaration-depth"
  | depth + 1, roster, shape, value => do
    chargePlacement
    let .product arguments fields := value | return value
    let children ← match shape with
      | .tuple children => pure children
      | .array element _ => pure [element]
      | .record _ children => pure children
      | _ => throw "component-declaration-placement"
    if children.length != fields.length then throw "component-declaration-placement"
    let fields ← (children.zip fields).mapM fun (child, field) =>
      child.canonicalFormula depth roster field
    let structural := match shape with | .tuple _ | .array .. => true | _ => false
    return .product (if structural then rosterSet roster arguments else arguments) fields

/-- One source leaf with its exact effective role set. Oracle data precedes
receiver handles physically, irrespective of roster or telescope order. -/
structure PlacedLeaf where
  leaf : Leaf
  roles : List String
  deriving BEq, Repr

/-- Read shape or checked placement through the same traversal. `none` is used
only for declaration readback; native association always supplies placement. -/
def PlacementShape.emit : Nat → List String → PlacementShape → List String →
    Option SourcePlacement → PlacementCheck (List PlacedLeaf)
  | 0, _, _, _, _ => throw "component-declaration-depth"
  | depth + 1, roster, shape, path, placed => do
    chargePlacement
    if let some value := placed then
      match value with
      | .data roles =>
        checkRoleSet roster roles
        if shape.logical (depth + 1) then throw "component-declaration-placement"
        if roles.length > 1 && !shape.shared (depth + 1) then
          throw "component-declaration-custody-holder"
      | .oracle holder receivers =>
        checkRoleSet roster receivers
        if !roster.contains holder || receivers.contains holder then
          throw "component-declaration-placement"
      | .product arguments fields =>
        checkArguments roster arguments
        if !(fields.flatMap SourcePlacement.roles).all arguments.contains then
          throw "component-declaration-placement"
    let dataRoles ← match placed with
      | none => pure []
      | some (.data roles) => pure roles
      | _ => pure []
    match shape with
    | .data type =>
      if placed.isSome && !(placed.any fun p => match p with | .data _ => true | _ => false) then
        throw "component-declaration-placement"
      return [⟨⟨.data type, path⟩, dataRoles⟩]
    | .unit =>
      if placed.isSome && !(placed.any fun p => match p with | .data _ => true | _ => false) then
        throw "component-declaration-placement"
      return []
    | .oracle dataType handleType =>
      let (holder, receivers) ← match placed with
        | none => pure ([], [])
        | some (.oracle holder receivers) => pure ([holder], receivers)
        | _ => throw "component-declaration-placement"
      return [⟨⟨.holderData dataType, path⟩, holder⟩,
        ⟨⟨.receiverHandle handleType, path⟩, receivers⟩]
    | .tuple children | .record _ children =>
      let row := match shape with | .record row _ => some row | _ => none
      let logical := row.any fun r => match r.type with
        | .nominal .logicalRecord _ _ => true | _ => false
      let formulas := row.map (·.members.allFields) |>.getD []
      let telescope := row.map (·.roles) |>.getD []
      let (arguments, placements) ← match placed with
        | none => pure (telescope, children.map fun _ => none)
        | some (.data _) =>
          if logical then throw "component-declaration-placement"
          pure ([], children.map fun _ => placed)
        | some (.product arguments fields) =>
          if row.isSome && !logical then throw "component-declaration-placement"
          if fields.length != children.length then throw "component-declaration-placement"
          if logical && !telescope.isEmpty then
            if arguments.length != telescope.length then throw "component-declaration-placement"
            for ((child, field), formula) in (children.zip fields).zip formulas do
              let some formula := formula.placement | throw "component-declaration-placement"
              let expected ← substituteSourcePlacement roster telescope arguments depth formula
              let expected ← child.canonicalFormula depth roster expected
              if expected != field then throw "component-declaration-formula"
          else
            if arguments != rosterSet roster (fields.flatMap SourcePlacement.roles) then
              throw "component-declaration-placement"
          if logical && telescope.isEmpty then
            let mut family : Option SourcePlacement := none
            for (child, field) in children.zip fields do
              match child, field with
              | .oracle .., .oracle .. =>
                if family.isSome && family != some field then
                  throw "component-declaration-logical-family"
                family := some field
              | _, .data roles =>
                if roles != arguments then throw "component-declaration-logical-family"
              | _, _ => throw "component-declaration-logical-family"
            let some selectedFamily := family | throw "component-declaration-logical-family"
            if rosterSet roster selectedFamily.roles != arguments then
              throw "component-declaration-logical-family"
          pure (arguments, fields.map some)
        | _ => throw "component-declaration-placement"
      let mut result := []
      if let some row := row then
        if row.slot.isSome then
          let holders := if logical then arguments.map List.singleton else [dataRoles]
          for holder in holders do
            chargePlacement
            if placed.isSome && holder.length != 1 then
              throw "component-declaration-custody-holder"
            result := result ++ [⟨⟨.custody row.type, path⟩, holder⟩]
      if result.length > Limits.listEntries then throw "component-declaration-limit"
      for ((child, placement), index) in (children.zip placements).zipIdx do
        let name := (formulas[index]?).map (·.name) |>.getD (toString index)
        result := result ++ (← child.emit depth roster (path ++ [name]) placement)
        if result.length > Limits.listEntries then throw "component-declaration-limit"
      return result
    | .array element count =>
      let child ← match placed with
        | none => pure none
        | some (.data _) => pure placed
        | some (.product arguments [field]) =>
          if arguments != rosterSet roster field.roles then throw "component-declaration-placement"
          pure (some field)
        | _ => throw "component-declaration-placement"
      -- Validate the element even when no native storage is materialized.
      let template ← element.emit depth roster (path ++ ["0"]) child
      if template.length * count > Limits.listEntries then throw "component-declaration-limit"
      let mut result := if count == 0 then [] else template
      for index in List.range (count - 1) do
        result := result ++ (← element.emit depth roster (path ++ [toString (index + 1)]) child)
      return result

/-- Reconstruct ordered leaves with each resource record's custody prefix.
Zero-length arrays retain their element's declaration obligations. Distributed
and variant semantics require separate admission beyond reading their metadata. -/
def leaves (source : SourceDeclarations) (depth : Nat) (term : OriginTerm) (path : List String) :
    Except String (List Leaf) := do
  let shape ← source.placementShape depth term
  return (← (shape.emit depth [] path none).run' Limits.originTerms).map (·.leaf)

def placedLeaves (source : SourceDeclarations) (roster : List String) (port : SourcePort) :
    Except String (List PlacedLeaf) := do
  SourcePlacement.check none Limits.nesting port.placement
  let shape ← source.placementShape Limits.nesting port.type
  (shape.emit Limits.nesting roster [port.name] (some port.placement)).run' Limits.originTerms

/-- Validate declaration-local formulas even for unused or phantom records. -/
def checkRecordPlacement (source : SourceDeclarations) (record : SourceRecord) :
    Except String Unit := do
  let shape ← source.placementShape Limits.nesting record.type
  if !record.roles.isEmpty then
    let formulas ← record.members.allFields.mapM fun field =>
      requireSome field.placement "component-declaration-placement"
    discard <| (shape.emit Limits.nesting record.roles []
      (some (.product record.roles formulas))).run' Limits.originTerms
  else discard <| (shape.emit Limits.nesting [] [] none).run' Limits.originTerms

end SourceDeclarations
end Zkc.Source.Structured
