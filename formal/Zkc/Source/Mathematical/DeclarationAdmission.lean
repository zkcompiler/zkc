import Zkc.Source.Mathematical.RegistryAdmission
import Zkc.Source.Mathematical.PortAdmission
import Zkc.Source.Mathematical.CapabilityRoots

/-! The mathematical module header, including unused declarations.

Every operation, wire and service is instantiated in its own symbolic static
scope and checked against the manifest-selected contract. Capability roots are
closed, literal-instantiated services with canonical module-role permissions.
Relations, definition bodies and reachable call closure are separate checks.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.DeclarationAdmission
open RegistryAdmission

inductive Error where
  | resource | roles | rootStatic
  | manifest (reason : ManifestAdmission.Error)
  | type (reason : TypeAdmission.Error)
  | signature (reason : SignatureAdmission.Error)
  | registry (reason : RegistryAdmission.Error)
  | port (reason : PortAdmission.Error)
  deriving DecidableEq, Repr

abbrev Admission := StateT Nat (Except Error)

private def consume (amount : Nat := 1) : Admission Unit := do
  let remaining ← get
  if amount > remaining then throw .resource
  set (remaining - amount)

private def liftManifest {α : Type} (action : ManifestAdmission.Admission α) : Admission α :=
  fun remaining => (action remaining).mapError Error.manifest

private def liftSignature {α : Type} (action : SignatureAdmission.Admission α) : Admission α :=
  fun remaining => (action remaining).mapError Error.signature

private def liftRegistry {α : Type} (action : RegistryAdmission.Admission α) : Admission α :=
  fun remaining => (action remaining).mapError Error.registry

def parameters (count : Nat) : Fin count → Static.Expression count := Static.Expression.parameter

def arguments (count : Nat) : List Static.Raw := (List.range count).map Static.Raw.parameter

private def collect {α : Type} {Entry : α → Type} (action : (index : α) → Admission (Entry index)) :
    (indices : List α) → Admission (Values Entry indices)
  | [] => return .nil
  | first :: rest => do
      consume
      let first ← action first
      let rest ← collect action rest
      return .cons first rest

private theorem sameSelection {α : Type} {values : List α} {index : Nat}
    (first second : SignatureAdmission.Selected values index) : first.value = second.value :=
  Option.some.inj (first.selected.symm.trans second.selected)

variable {Payload : ManifestAdmission.Category → Type} {contracts : Contracts Payload}
  {manifest : Raw.Manifest} (context : Context contracts manifest)
  (module : Raw.Module) (types : TypeAdmission.Table context.meaning module.types)

structure Service (index : Nat) where
  statics : Nat
  signature : SignatureAdmission.Capability context.meaning types (parameters statics)
    module.capabilityTypes manifest ⟨⟨index⟩, arguments statics⟩
  arity : signature.declaration.value.statics = statics
  registered : RegistryAdmission.Service context types signature

def service (index : Nat) : Admission (Service context module types index) := do
  let declaration ← liftSignature (SignatureAdmission.select module.capabilityTypes index)
  let count := declaration.value.statics
  consume count
  let signature ← liftSignature (SignatureAdmission.capability context.meaning types (parameters count)
    module.capabilityTypes manifest ⟨⟨index⟩, arguments count⟩)
  let registered ← liftRegistry (RegistryAdmission.service context types signature)
  return ⟨count, signature, congrArg Raw.CapabilityType.statics (sameSelection signature.declaration declaration), registered⟩

structure Operation (index : Nat) where
  statics : Nat
  signature : SignatureAdmission.Operation context.meaning types (parameters statics) module manifest index (arguments statics)
  arity : signature.declaration.value.statics = statics
  registered : RegistryAdmission.Operation context types signature

def operation (index : Nat) : Admission (Operation context module types index) := do
  let declaration ← liftSignature (SignatureAdmission.select module.operations index)
  let count := declaration.value.statics
  consume count
  let signature ← liftSignature (SignatureAdmission.operation context.meaning types (parameters count)
    module manifest index (arguments count) rfl)
  let registered ← liftRegistry (RegistryAdmission.operation context types signature)
  return ⟨count, signature, congrArg Raw.Operation.statics (sameSelection signature.declaration declaration), registered⟩

structure Wire (index : Nat) where
  statics : Nat
  signature : SignatureAdmission.Wire context.meaning types (parameters statics) module.wires manifest index (arguments statics)
  arity : signature.declaration.value.statics = statics
  registered : RegistryAdmission.Wire context types signature

def wire (index : Nat) : Admission (Wire context module types index) := do
  let declaration ← liftSignature (SignatureAdmission.select module.wires index)
  let count := declaration.value.statics
  consume count
  let signature ← liftSignature (SignatureAdmission.wire context.meaning types (parameters count)
    module.wires manifest index (arguments count))
  let registered ← liftRegistry (RegistryAdmission.wire context types signature)
  return ⟨count, signature, congrArg Raw.Wire.statics (sameSelection signature.declaration declaration), registered⟩

def literal : Static.Raw → Bool
  | .literal _ => true
  | _ => false

def closed : Fin 0 → Static.Expression 0 := Fin.elim0

structure Root (source : Raw.Permission) where
  literals : source.signature.statics.all literal = true
  signature : SignatureAdmission.Capability context.meaning types closed module.capabilityTypes manifest source.signature
  roles : PortAdmission.Roles module.roles.length 0 source.roles
  registered : RegistryAdmission.Service context types signature

def root (source : Raw.Permission) : Admission (Root context module types source) := do
  consume source.signature.statics.length
  if literals : source.signature.statics.all literal = true then
    let signature ← liftSignature (SignatureAdmission.capability context.meaning types closed
      module.capabilityTypes manifest source.signature)
    let roles ← fun remaining => (PortAdmission.roles module.roles.length 0 source.roles remaining).mapError Error.port
    let registered ← liftRegistry (RegistryAdmission.service context types signature)
    return ⟨literals, signature, roles, registered⟩
  else throw .rootStatic

/-- Indices and source permissions are retained by the heterogeneous tables.
Their lengths cover the complete authored lists, including dormant entries. -/
structure Header (contracts : Contracts Payload) (source : Raw.Subject) where
  context : Context contracts source.manifest
  roleBound : source.module.roles.length < 32768
  uniqueRoles : source.module.roles.Nodup
  types : TypeAdmission.Table context.meaning source.module.types
  domains : @types.domainCheck = @context.domainCheck
  services : Values (Service context source.module types) (List.range source.module.capabilityTypes.length)
  operations : Values (Operation context source.module types) (List.range source.module.operations.length)
  wires : Values (Wire context source.module types) (List.range source.module.wires.length)
  roots : Values (Root context source.module types) source.module.roots

/-- Root identities are their authored table positions, even when two entries
have identical service signatures and permissions. -/
def rootCapabilities {sources : List Raw.Permission} (start : Nat) :
    Values (Root context module types) sources →
      List (Protocol.Capability Nat (SignatureAdmission.MeasuredService manifest.domains.length 0))
  | .nil => []
  | .cons first rest => ⟨⟨first.signature.service, first.roles.values⟩, start⟩ ::
      rootCapabilities (start + 1) rest

theorem rootCapabilities_indices {sources : List Raw.Permission} (start : Nat)
    (roots : Values (Root context module types) sources) :
    (rootCapabilities context module types start roots).map Protocol.Capability.root = List.range' start sources.length := by
  induction roots generalizing start with
  | nil => rfl
  | cons first rest ih => simp [rootCapabilities, ih, List.range'_succ]

def Header.capabilities {contracts source} (header : Header (Payload := Payload) contracts source) :=
  rootCapabilities header.context source.module header.types 0 header.roots

theorem Header.capabilities_length {contracts source} (header : Header (Payload := Payload) contracts source) :
    header.capabilities.length = source.module.roots.length := by
  have indices := rootCapabilities_indices header.context source.module header.types 0 header.roots
  simpa [Header.capabilities] using congrArg List.length indices

theorem Header.rootTable {contracts source} (header : Header (Payload := Payload) contracts source) :
    Protocol.RootTable header.capabilities := by
  have indices := rootCapabilities_indices header.context source.module header.types 0 header.roots
  have length := congrArg List.length indices
  simp only [List.length_map, List.length_range'] at length
  simpa [Protocol.RootTable, Header.capabilities, length, List.range_eq_range'] using indices

theorem Header.rooted {contracts source} (header : Header (Payload := Payload) contracts source) :
    Protocol.Rooted header.capabilities header.capabilities := header.rootTable.rooted

def admit (contracts : Contracts Payload) (source : Raw.Subject) : Admission (Header contracts source) := do
  let manifest ← liftManifest (ManifestAdmission.admit contracts.installation source.manifest)
  let context : Context contracts source.manifest := ⟨manifest⟩
  consume source.module.roles.length
  let bytes := source.module.roles.foldl (fun bytes name => bytes + name.utf8ByteSize) 0
  consume (bytes * (source.module.roles.length + 1))
  if roleBound : source.module.roles.length < 32768 then
    if uniqueRoles : source.module.roles.Nodup then
      let checkedTypes ← fun remaining =>
        (TypeAdmission.declarationsChecked context.meaning context.domainCheck source.module.types remaining).mapError Error.type
      let types := checkedTypes.val
      -- Charge indices before allocating their ranges. Per-entry checks share
      -- the remaining allowance with type expansion and static normalization.
      consume (source.module.capabilityTypes.length + source.module.operations.length + source.module.wires.length)
      let services ← collect (service context source.module types) (List.range source.module.capabilityTypes.length)
      let operations ← collect (operation context source.module types) (List.range source.module.operations.length)
      let wires ← collect (wire context source.module types) (List.range source.module.wires.length)
      let roots ← collect (root context source.module types) source.module.roots
      return ⟨context, roleBound, uniqueRoles, types, checkedTypes.property, services, operations, wires, roots⟩
    else throw .roles
  else throw .roles

end Zkc.Source.Mathematical.DeclarationAdmission
