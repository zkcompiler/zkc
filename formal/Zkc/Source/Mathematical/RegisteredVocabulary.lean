import Zkc.Source.Mathematical.DeclarationAdmission
import Zkc.Source.Mathematical.ProtocolResolution

/-! The intrinsic vocabulary of an admitted mathematical module header.

Operations and wires use canonical data keys with proof-irrelevant certificates
of actual declaration instantiation and selected registry evidence. Exact root
measurements remain available at runtime; their uniqueness makes equality depend
only on the key. The vocabulary is independent of the caller's static arity,
so all closed instances use one protocol language. Resolvers additionally prove
selection under the current caller's exact parameter tuple. Call closure owns
only call selection; it cannot replace the operation, wire or port checkers.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.RegisteredVocabulary

variable {Payload : ManifestAdmission.Category → Type} {contracts : RegistryAdmission.Contracts Payload}
  {source : Raw.Subject} (header : DeclarationAdmission.Header contracts source) (target : Nat)

/-- Operational identity contains only normalized signature data and opaque
attributes. Authored spelling and construction evidence cannot affect meaning. -/
structure OperationKey (domains target : Nat) where
  declaration : Nat
  signature : SignatureAdmission.OperationSignature domains target
  facts : RegistryAdmission.OperationFacts
  attributes : Raw.Attribute
  deriving DecidableEq

structure WireKey (domains target : Nat) where
  declaration : Nat
  identity : Raw.Identity
  statics : List (Static.Expression target)
  payload : TypeExpansion.Shape domains target
  deriving DecidableEq

def OperationResolvesKey {arity : Nat} (parameters : Fin arity → Static.Expression target)
    (raw : GraphResolution.OperationUse) (key : OperationKey source.manifest.domains.length target) : Prop :=
  ∃ (signature : SignatureAdmission.Operation header.context.meaning header.types parameters
      source.module source.manifest raw.operation.index raw.statics)
    (registered : RegistryAdmission.Operation header.context header.types signature),
    AttributeAdmission.canonical raw.attributes = true ∧
    contracts.attributes source.manifest registered.selected.package.interpretation signature.signature raw.attributes = true ∧
    key = ⟨raw.operation.index, signature.signature, registered.facts, raw.attributes⟩

def WireResolvesKey {arity : Nat} (parameters : Fin arity → Static.Expression target)
    (raw : ProtocolResolution.WireUse) (key : WireKey source.manifest.domains.length target) : Prop :=
  ∃ (signature : SignatureAdmission.Wire header.context.meaning header.types parameters
      source.module.wires source.manifest raw.wire.index raw.statics)
    (_registered : RegistryAdmission.Wire header.context header.types signature),
    key = ⟨raw.wire.index, signature.identity.value, signature.arguments.values, signature.payload.expanded.shape⟩

structure Operation where
  val : OperationKey source.manifest.domains.length target
  property : ∃ (arity : Nat) (parameters : Fin arity → Static.Expression target) (raw : GraphResolution.OperationUse),
    OperationResolvesKey header target parameters raw val
  measured : SignatureAdmission.OperationMeasurement val.signature

structure Wire where
  val : WireKey source.manifest.domains.length target
  property : ∃ (arity : Nat) (parameters : Fin arity → Static.Expression target) (raw : ProtocolResolution.WireUse),
    WireResolvesKey header target parameters raw val
  measured : TypeMeasurement Data.Shape.nodes Data.Shape.height val.payload

theorem operation_ext {first second : Operation header target} (same : first.val = second.val) : first = second := by
  cases first with
  | mk first firstProof firstMeasurement =>
    cases second with
    | mk second secondProof secondMeasurement =>
      cases same
      cases Subsingleton.elim firstMeasurement secondMeasurement
      rfl

theorem wire_ext {first second : Wire header target} (same : first.val = second.val) : first = second := by
  cases first with
  | mk first firstProof firstMeasurement =>
    cases second with
    | mk second secondProof secondMeasurement =>
      cases same
      cases Subsingleton.elim firstMeasurement secondMeasurement
      rfl

instance : DecidableEq (Operation header target) := fun first second =>
  if same : first.val = second.val then isTrue (operation_ext header target same)
  else isFalse (fun equal => same (congrArg Operation.val equal))

instance : DecidableEq (Wire header target) := fun first second =>
  if same : first.val = second.val then isTrue (wire_ext header target same)
  else isFalse (fun equal => same (congrArg Wire.val equal))

theorem operation_distinct (operation : Operation header target) :
    RegistryAdmission.Distinct operation.val.signature.capabilities.length operation.val.facts.distinct := by
  obtain ⟨arity, parameters, raw, signature, registered, _, _, same⟩ := operation.property
  rw [same]
  simpa [SignatureAdmission.Operation.signature, SignatureAdmission.Capabilities.length] using registered.distinct

theorem operation_attributes (operation : Operation header target) :
    AttributeAdmission.canonical operation.val.attributes = true := by
  obtain ⟨arity, parameters, raw, signature, registered, canonical, _, same⟩ := operation.property
  simpa [same] using canonical

abbrev vocabulary : Protocol.Vocabulary where
  Ty := TypeExpansion.Shape source.manifest.domains.length target
  Count := Static.Expression target
  Op := { operation : Operation header target // operation.val.facts.purity = .total }
  arguments operation := operation.val.val.signature.arguments
  result operation := operation.val.val.signature.result
  index := .fin
  condition := .fin (.literal ⟨2, by decide⟩)
  Wire type := { wire : Wire header target // wire.val.payload = type }
  product := .product
  vector := .vector
  Service := SignatureAdmission.MeasuredService source.manifest.domains.length target
  serviceArguments service := service.val.arguments
  serviceResult service := service.val.result
  Local := { operation : Operation header target // operation.val.facts.purity = .ordered }
  localCapabilities operation := SignatureAdmission.measuredServices operation.val.measured.capabilities
  localArguments operation := operation.val.val.signature.arguments
  localResult operation := operation.val.val.signature.result
  localDistinct operation := operation.val.val.facts.distinct

/-- Field access reuses the counters retained by declaration instantiation.
No key lookup, type walk, or certificate-tree comparison occurs here. -/
def signatureMeasurements : Protocol.SignatureMeasurements (vocabulary := vocabulary header target) Data.Shape.nodes Data.Shape.height where
  graph operation := some operation.val.measured.signatureTypes
  localOperation operation := some operation.val.measured.signatureTypes
  service service := some service.measured
  wire wire := some (wire.property ▸ wire.val.measured)

private def liftError {α E : Type} [Repr E] (action : StateT Nat (Except E) α) : StateT Nat (Except String) α :=
  fun remaining => (action remaining).mapError (fun error => toString (repr error))

variable {target} {arity : Nat} (parameters : Fin arity → Static.Expression target)

def OperationResolves (raw : GraphResolution.OperationUse) (operation : Operation header target) : Prop :=
  OperationResolvesKey header target parameters raw operation.val

def operation (raw : GraphResolution.OperationUse) : StateT Nat (Except String)
    { operation : Operation header target // OperationResolves header parameters raw operation } := do
  let signature ← liftError (SignatureAdmission.operation header.context.meaning header.types parameters
    source.module source.manifest raw.operation.index raw.statics rfl)
  let registered ← liftError (RegistryAdmission.operation header.context header.types signature)
  let attributes ← liftError (RegistryAdmission.attributes header.context header.types registered raw.attributes)
  let key : OperationKey source.manifest.domains.length target :=
    ⟨raw.operation.index, signature.signature, registered.facts, raw.attributes⟩
  have valid : OperationResolvesKey header target parameters raw key := ⟨signature, registered, attributes.down.1, attributes.down.2, rfl⟩
  return ⟨⟨key, ⟨arity, parameters, raw, valid⟩, signature.measurements⟩, valid⟩

def graph : GraphResolution.Resolver (vocabulary header target).toAlgebra where
  OperationValid raw operation := OperationResolves header parameters raw operation.val
  CountValid := Static.Resolves parameters
  operation raw := do
    let selected ← operation header parameters raw
    if pureOperation : selected.val.val.facts.purity = .total then
      return ⟨⟨selected.val, pureOperation⟩, selected.property⟩
    else throw "math-purity"
  count raw := do
    let selected ← liftError (Static.resolve parameters raw)
    return ⟨selected.normalized.expression, selected.valid⟩

def WireResolves (raw : ProtocolResolution.WireUse) (wire : Wire header target) : Prop :=
  WireResolvesKey header target parameters raw wire.val

def wire (raw : ProtocolResolution.WireUse) : StateT Nat (Except String)
    { wire : Wire header target // WireResolves header parameters raw wire } := do
  let signature ← liftError (SignatureAdmission.wire header.context.meaning header.types parameters
    source.module.wires source.manifest raw.wire.index raw.statics)
  let registered ← liftError (RegistryAdmission.wire header.context header.types signature)
  let key : WireKey source.manifest.domains.length target :=
    ⟨raw.wire.index, signature.identity.value, signature.arguments.values, signature.payload.expanded.shape⟩
  have valid : WireResolvesKey header target parameters raw key := ⟨signature, registered, rfl⟩
  return ⟨⟨key, ⟨arity, parameters, raw, valid⟩,
    Data.capacity.measurement signature.payload.expanded.measured⟩, valid⟩

structure Calls where
  Valid : ProtocolResolution.CallUse → Nat → Prop
  resolve : (raw : ProtocolResolution.CallUse) → StateT Nat (Except String) { index : Nat // Valid raw index }

def protocol (roles : RoleResolution.Binding) (calls : Calls) : ProtocolResolution.Resolver (vocabulary header target) where
  roles := roles
  graph := graph header parameters
  LocalValid raw operation := OperationResolves header parameters raw operation.val
  WireValid raw wire := WireResolves header parameters raw wire.2.val
  CallValid := calls.Valid
  PortValid raw port := ∃ checked : PortAdmission.Instantiated header.context.meaning header.types parameters roles raw,
    checked.port = port
  localOperation raw := do
    let selected ← operation header parameters raw
    if orderedOperation : selected.val.val.facts.purity = .ordered then
      return ⟨⟨selected.val, orderedOperation⟩, selected.property⟩
    else throw "math-purity"
  wire raw := do
    let selected ← wire header parameters raw
    return ⟨⟨selected.val.val.payload, ⟨selected.val, rfl⟩⟩, selected.property⟩
  call := calls.resolve
  port raw := do
    let selected ← liftError (PortAdmission.instantiate header.context.meaning header.types parameters roles raw)
    return ⟨selected.port, ⟨selected, rfl⟩⟩

end Zkc.Source.Mathematical.RegisteredVocabulary
