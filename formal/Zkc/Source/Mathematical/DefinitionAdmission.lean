import Zkc.Source.Mathematical.DataBounds
import Zkc.Source.Mathematical.RelationAdmission

/-! Certified definition signatures and relation bindings.

The local role arity is checked against the actual positional binding. Ports and
capability permissions share canonical availability substitution. A relation
binding selects its actual declaration and typed definition arguments, while
preserving the authored operand order. Binding a relation does not prove it.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.DefinitionAdmission

inductive Error where
  | resource | roles
  | capability (reason : Protocol.Error)
  | port (reason : PortAdmission.Error)
  | signature (reason : SignatureAdmission.Error)
  | registry (reason : RegistryAdmission.Error)
  | relation (reason : RelationAdmission.Error)
  | argument (reason : Graph.Error)
  | body (reason : ProtocolResolution.Error)
  deriving Repr

abbrev Admission := StateT Nat (Except Error)

private def consume (amount : Nat := 1) : Admission Unit := do
  let remaining ← get
  if amount > remaining then throw .resource
  set (remaining - amount)

private def liftPort {α : Type} (action : StateT Nat (Except PortAdmission.Error) α) : Admission α :=
  fun remaining => (action remaining).mapError Error.port

private def liftSignature {α : Type} (action : SignatureAdmission.Admission α) : Admission α :=
  fun remaining => (action remaining).mapError Error.signature

private def liftRegistry {α : Type} (action : RegistryAdmission.Admission α) : Admission α :=
  fun remaining => (action remaining).mapError Error.registry

private def liftRelation {α : Type} (action : RelationAdmission.Admission α) : Admission α :=
  fun remaining => (action remaining).mapError Error.relation

variable {Payload : ManifestAdmission.Category → Type} {contracts : RegistryAdmission.Contracts Payload}
  {source : Raw.Subject} (header : DeclarationAdmission.Header contracts source)
  {arity target : Nat} (parameters : Fin arity → Static.Expression target) (binding : RoleResolution.Binding)

abbrev PortEntry := PortAdmission.Instantiated header.context.meaning header.types parameters binding

abbrev Ports (sources : List Raw.Port) := Values (PortEntry header parameters binding) sources

def Ports.values {sources} : Ports header parameters binding sources →
    List (Port Nat (TypeExpansion.Shape source.manifest.domains.length target))
  | .nil => []
  | .cons first rest => first.port :: Ports.values rest

def ports : (sources : List Raw.Port) → Admission (Ports header parameters binding sources)
  | [] => return .nil
  | first :: rest => do
      consume
      let first ← liftPort (PortAdmission.instantiate header.context.meaning header.types parameters binding first)
      let rest ← ports rest
      return .cons first rest

structure Permission (raw : Raw.Permission) where
  signature : SignatureAdmission.Capability header.context.meaning header.types parameters
    source.module.capabilityTypes source.manifest raw.signature
  registered : RegistryAdmission.Service header.context header.types signature
  availability : PortAdmission.Availability binding raw.roles

def Permission.value {raw} (permission : Permission header parameters binding raw) :
    Protocol.Permission Nat (SignatureAdmission.MeasuredService source.manifest.domains.length target) :=
  ⟨permission.signature.service, permission.availability.mapped.binding.participants⟩

def permission (raw : Raw.Permission) : Admission (Permission header parameters binding raw) := do
  let signature ← liftSignature (SignatureAdmission.capability header.context.meaning header.types parameters
    source.module.capabilityTypes source.manifest raw.signature)
  let registered ← liftRegistry (RegistryAdmission.service header.context header.types signature)
  let availability ← liftPort (PortAdmission.availability binding raw.roles)
  return ⟨signature, registered, availability⟩

abbrev Permissions (sources : List Raw.Permission) := Values (Permission header parameters binding) sources

def Permissions.values {sources} : Permissions header parameters binding sources →
    List (Protocol.Permission Nat (SignatureAdmission.MeasuredService source.manifest.domains.length target))
  | .nil => []
  | .cons first rest => first.value :: Permissions.values rest

def permissions : (sources : List Raw.Permission) → Admission (Permissions header parameters binding sources)
  | [] => return .nil
  | first :: rest => do
      consume
      let first ← permission header parameters binding first
      let rest ← permissions rest
      return .cons first rest

variable {binding}

structure Relation (arguments : List (Port Nat (TypeExpansion.Shape source.manifest.domains.length target)))
    (raw : Raw.RelationBinding) where
  selected : RelationAdmission.Use header parameters raw.relation raw.statics
  publicInputs : Inputs arguments selected.checked.publicInputs.shapes
  publicErasure : Graph.inputIndices (algebra := (RegisteredVocabulary.vocabulary header target).toAlgebra) publicInputs = raw.publicInputs.map (·.index)
  witnessInputs : Inputs arguments selected.checked.witnessInputs.shapes
  witnessErasure : Graph.inputIndices (algebra := (RegisteredVocabulary.vocabulary header target).toAlgebra) witnessInputs = raw.witnessInputs.map (·.index)

def relation (arguments : List (Port Nat (TypeExpansion.Shape source.manifest.domains.length target)))
    (raw : Raw.RelationBinding) : Admission (Relation header parameters arguments raw) := do
  consume (1 + (raw.publicInputs.length + raw.witnessInputs.length) * (arguments.length + 1))
  let selected ← liftRelation (RelationAdmission.use header parameters raw.relation raw.statics)
  let publicInputs ← (Graph.selectInputs (algebra := (RegisteredVocabulary.vocabulary header target).toAlgebra)
    arguments selected.checked.publicInputs.shapes (raw.publicInputs.map (·.index))).mapError Error.argument
  let witnessInputs ← (Graph.selectInputs (algebra := (RegisteredVocabulary.vocabulary header target).toAlgebra)
    arguments selected.checked.witnessInputs.shapes (raw.witnessInputs.map (·.index))).mapError Error.argument
  return ⟨selected, publicInputs.val, publicInputs.property, witnessInputs.val, witnessInputs.property⟩

def relations (arguments : List (Port Nat (TypeExpansion.Shape source.manifest.domains.length target))) :
    (sources : List Raw.RelationBinding) → Admission (Values (Relation header parameters arguments) sources)
  | [] => return .nil
  | first :: rest => do
      let first ← relation header parameters arguments first
      let rest ← relations arguments rest
      return .cons first rest

structure Signature (declaration : Raw.Definition)
    (parameters : Fin declaration.statics → Static.Expression target) (binding : RoleResolution.Binding) where
  roleArity : binding.roles.length = declaration.roles
  arguments : Ports header parameters binding declaration.arguments
  results : Ports header parameters binding declaration.results
  capabilities : Permissions header parameters binding declaration.capabilities
  relations : Values (Relation header parameters (Ports.values header parameters binding arguments)) declaration.relations

def Signature.value {declaration parameters binding} (checked : Signature header (target := target) declaration parameters binding) :
    Protocol.Signature Nat (RegisteredVocabulary.vocabulary header target) :=
  ⟨binding.participants, (Permissions.values header parameters binding checked.capabilities), (Ports.values header parameters binding checked.arguments), (Ports.values header parameters binding checked.results)⟩

def signature (declaration : Raw.Definition)
    (parameters : Fin declaration.statics → Static.Expression target) (binding : RoleResolution.Binding) :
    Admission (Signature header declaration parameters binding) := do
  consume (binding.roles.length + 1)
  if roleArity : binding.roles.length = declaration.roles then
    let arguments ← ports header parameters binding declaration.arguments
    let results ← ports header parameters binding declaration.results
    let capabilities ← permissions header parameters binding declaration.capabilities
    let relations ← relations header parameters (Ports.values header parameters binding arguments) declaration.relations
    return ⟨roleArity, arguments, results, capabilities, relations⟩
  else throw .roles

/-- Symbolic roots name capability parameters. They carry no claim that future
actual state roots will differ. Only formed template bodies use this table. -/
def parameterCapabilities {Service : Type} : Nat → List (Protocol.Permission Nat Service) →
    List (Protocol.Capability Nat Service)
  | _, [] => []
  | index, first :: rest => ⟨first, index⟩ :: parameterCapabilities (index + 1) rest

theorem parameterCapabilities_permissions {Service : Type} (start : Nat)
    (permissions : List (Protocol.Permission Nat Service)) :
    (parameterCapabilities start permissions).map Protocol.Capability.toPermission = permissions := by
  induction permissions generalizing start with
  | nil => rfl
  | cons first rest ih => simp [parameterCapabilities, ih]

structure Template (declaration : Raw.Definition) (binding : RoleResolution.Binding)
    (calls : RegisteredVocabulary.Calls)
    (scope : List (Protocol.Signature Nat (RegisteredVocabulary.vocabulary header declaration.statics))) where
  signature : Signature header declaration (DeclarationAdmission.parameters declaration.statics) binding
  body : ProtocolResolution.Formed
    (RegisteredVocabulary.protocol header (DeclarationAdmission.parameters declaration.statics) binding calls)
    binding.participants (parameterCapabilities 0 signature.value.capabilities) scope
    signature.value.arguments signature.value.results declaration.body

def template (declaration : Raw.Definition) (binding : RoleResolution.Binding)
    (calls : RegisteredVocabulary.Calls)
    (scope : List (Protocol.Signature Nat (RegisteredVocabulary.vocabulary header declaration.statics))) :
    Admission (Template header declaration binding calls scope) := do
  let parameters := DeclarationAdmission.parameters declaration.statics
  consume declaration.statics
  let signature ← signature header declaration parameters binding
  let capabilities := parameterCapabilities 0 signature.value.capabilities
  let resolver := RegisteredVocabulary.protocol header parameters binding calls
  let body ← fun remaining => (ProtocolResolution.form resolver binding.participants capabilities scope
    Data.capacity (fun _ => true) signature.value.arguments signature.value.results declaration.body
      (RegisteredVocabulary.signatureMeasurements header declaration.statics) remaining).mapError Error.body
  return ⟨signature, body⟩

/-- A bound body preserves the exact selected caller roots and restricts each
parameter to its declared permission. The caller table must itself come from
root/closure admission. This object forms a body; root discharge is subsequent. -/
structure Bound (declaration : Raw.Definition)
    (parameters : Fin declaration.statics → Static.Expression target) (binding : RoleResolution.Binding)
    (calls : RegisteredVocabulary.Calls)
    (scope : List (Protocol.Signature Nat (RegisteredVocabulary.vocabulary header target)))
    (available : List (Protocol.Capability Nat (RegisteredVocabulary.vocabulary header target).Service))
    (indices : List Nat) where
  signature : Signature header declaration parameters binding
  selected : Protocol.CapabilityBindings (vocabulary := RegisteredVocabulary.vocabulary header target)
    available signature.value.capabilities
  erasure : selected.indices = indices
  body : ProtocolResolution.Formed (RegisteredVocabulary.protocol header parameters binding calls)
    binding.participants selected.bound scope signature.value.arguments signature.value.results declaration.body

theorem Bound.rooted {declaration parameters binding calls scope available indices}
    (checked : Bound header (target := target) declaration parameters binding calls scope available indices)
    {table : List (Protocol.Capability Nat (RegisteredVocabulary.vocabulary header target).Service)}
    (rooted : Protocol.Rooted table available) : Protocol.Rooted table checked.selected.bound :=
  checked.selected.bound_rooted rooted

def bind (declaration : Raw.Definition)
    (parameters : Fin declaration.statics → Static.Expression target) (binding : RoleResolution.Binding)
    (calls : RegisteredVocabulary.Calls)
    (scope : List (Protocol.Signature Nat (RegisteredVocabulary.vocabulary header target)))
    (available : List (Protocol.Capability Nat (RegisteredVocabulary.vocabulary header target).Service))
    (indices : List Nat) : Admission (Bound header declaration parameters binding calls scope available indices) := do
  let signature ← signature header declaration parameters binding
  consume (indices.length * (available.length + 1))
  let selected ← (Protocol.selectCapabilities (vocabulary := RegisteredVocabulary.vocabulary header target)
    available signature.value.capabilities indices).mapError Error.capability
  let resolver := RegisteredVocabulary.protocol header parameters binding calls
  let body ← fun remaining => (ProtocolResolution.form resolver binding.participants selected.val.bound scope
    Data.capacity (fun _ => true) signature.value.arguments signature.value.results declaration.body
      (RegisteredVocabulary.signatureMeasurements header target) remaining).mapError Error.body
  return ⟨signature, selected.val, selected.property, body⟩

end Zkc.Source.Mathematical.DefinitionAdmission
