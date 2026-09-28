import Zkc.Source.Mathematical.TypeAdmission
import Zkc.Source.Mathematical.StaticResolution

/-! Instantiation of authored declaration signatures.

These objects resolve actual earlier type declarations and actual manifest
service indices. Registry selection remains an explicit owner obligation:
formation of a signature does not grant operation purity, service behavior,
wire correctness, or a law. The objects retain the selected raw declarations
and every substituted type's semantic and domain-formation certificates.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.SignatureAdmission

inductive Error where
  | resource | reference
  | static (reason : Static.ResolutionError)
  | type (reason : TypeAdmission.Error)
  deriving DecidableEq, Repr

abbrev Admission := StateT Nat (Except Error)

private def consume (amount : Nat := 1) : Admission Unit := do
  let remaining ← get
  if amount > remaining then throw .resource
  set (remaining - amount)

private def liftStatic {α : Type} (action : StateT Nat (Except Static.ResolutionError) α) : Admission α :=
  fun remaining => (action remaining).mapError Error.static

private def liftType {α : Type} (action : StateT Nat (Except TypeAdmission.Error) α) : Admission α :=
  fun remaining => (action remaining).mapError Error.type

/-- Lookup follows the authored index, with no signature-based deduplication. -/
structure Selected {α : Type} (values : List α) (index : Nat) where
  value : α
  selected : values[index]? = some value

theorem Selected.unique {α : Type} {values : List α} {index : Nat}
    (first second : Selected values index) : first = second := by
  cases first with
  | mk first selected =>
      cases second with
      | mk second other =>
          have same := Option.some.inj (selected.symm.trans other)
          subst second
          rfl

def select {α : Type} (values : List α) (index : Nat) : Admission (Selected values index) := do
  consume (1 + min index values.length)
  match selected : values[index]? with
  | none => throw .reference
  | some value => return ⟨value, selected⟩

variable {domains : Nat} (meaning : TypeSyntax.Interpretation domains)
  {rawTypes : List Raw.TypeTemplate} (table : TypeAdmission.Table meaning rawTypes)

inductive Types {arity target : Nat} (parameters : Fin arity → Static.Expression target) : List Raw.TypeUse → Type where
  | nil : Types parameters []
  | cons {source rest} (first : TypeAdmission.Instantiated meaning table parameters source)
      (tail : Types parameters rest) : Types parameters (source :: rest)

def Types.shapes {domains meaning rawTypes table arity target parameters} : {sources : List Raw.TypeUse} →
    Types (domains := domains) meaning (rawTypes := rawTypes) table
      (arity := arity) (target := target) parameters sources → List (TypeExpansion.Shape domains target)
  | _, .nil => []
  | _, .cons first tail => first.expanded.shape :: tail.shapes

/-- Reuse the counters already certified by type expansion. No structural type
walk is needed to extract a signature's root measurements. -/
def Types.measurements {domains meaning rawTypes table arity target parameters} : {sources : List Raw.TypeUse} →
    (types : Types (domains := domains) meaning (rawTypes := rawTypes) table
      (arity := arity) (target := target) parameters sources) →
      Values (TypeMeasurement Data.Shape.nodes Data.Shape.height) types.shapes
  | _, .nil => .nil
  | _, .cons first tail => .cons (Data.capacity.measurement first.expanded.measured) tail.measurements

theorem Types.formed {arity target parameters sources}
    (types : Types meaning table (arity := arity) (target := target) parameters sources) :
    ∀ shape ∈ types.shapes, TypeExpansion.Formed table.domainCheck shape := by
  induction types with
  | nil => simp [Types.shapes]
  | cons first tail ih => simpa [Types.shapes] using And.intro first.expanded.formed ih

def types {arity target : Nat} (parameters : Fin arity → Static.Expression target) :
    (sources : List Raw.TypeUse) → Admission (Types meaning table parameters sources)
  | [] => return .nil
  | first :: rest => do
      consume
      let first ← liftType (TypeAdmission.instantiate meaning table parameters first)
      let rest ← types parameters rest
      return .cons first rest

structure ServiceSignature (domains target : Nat) where
  identity : Raw.Identity
  statics : List (Static.Expression target)
  arguments : List (TypeExpansion.Shape domains target)
  result : TypeExpansion.Shape domains target
  deriving DecidableEq

abbrev ServiceMeasurement {domains target : Nat} (signature : ServiceSignature domains target) :=
  Data.capacity.SignatureMeasurement signature.arguments signature.result

structure MeasuredService (domains target : Nat) where
  val : ServiceSignature domains target
  measured : ServiceMeasurement val

theorem MeasuredService.ext {domains target : Nat} {first second : MeasuredService domains target}
    (same : first.val = second.val) : first = second := by
  cases first with
  | mk first measured =>
    cases second with
    | mk second other =>
      cases same
      cases Subsingleton.elim measured other
      rfl

instance {domains target : Nat} : DecidableEq (MeasuredService domains target) := fun first second =>
  if same : first.val = second.val then isTrue (MeasuredService.ext same)
  else isFalse (fun equal => same (congrArg MeasuredService.val equal))

def measuredServices {domains target : Nat} {signatures : List (ServiceSignature domains target)} :
    Values ServiceMeasurement signatures → List (MeasuredService domains target)
  | .nil => []
  | .cons first rest => ⟨_, first⟩ :: measuredServices rest

theorem measuredServices_keys {domains target : Nat} {signatures : List (ServiceSignature domains target)}
    (measured : Values ServiceMeasurement signatures) :
    (measuredServices measured).map MeasuredService.val = signatures := by
  induction measured with
  | nil => rfl
  | cons first rest ih => simp [measuredServices, ih]

structure Capability {arity target : Nat} (parameters : Fin arity → Static.Expression target)
    (declarations : List Raw.CapabilityType) (manifest : Raw.Manifest) (source : Raw.CapabilityUse) where
  declaration : Selected declarations source.type.index
  identity : Selected manifest.services declaration.value.identity.index
  arguments : Static.Tuple parameters declaration.value.statics source.statics
  inputs : Types meaning table arguments.parameters declaration.value.arguments
  output : TypeAdmission.Instantiated meaning table arguments.parameters declaration.value.result

def Capability.signature {domains meaning rawTypes table arity target parameters declarations manifest source}
    (capability : Capability (domains := domains) meaning (rawTypes := rawTypes) table
      (arity := arity) (target := target) parameters declarations manifest source) : ServiceSignature domains target :=
  ⟨capability.identity.value, capability.arguments.values,
    capability.inputs.shapes, capability.output.expanded.shape⟩

def Capability.measurements {domains meaning rawTypes table arity target parameters declarations manifest source}
    (capability : Capability (domains := domains) meaning (rawTypes := rawTypes) table
      (arity := arity) (target := target) parameters declarations manifest source) :
    ServiceMeasurement capability.signature :=
  ⟨capability.inputs.measurements, Data.capacity.measurement capability.output.expanded.measured⟩

def Capability.service {domains meaning rawTypes table arity target parameters declarations manifest source}
    (capability : Capability (domains := domains) meaning (rawTypes := rawTypes) table
      (arity := arity) (target := target) parameters declarations manifest source) :
    MeasuredService domains target :=
  ⟨capability.signature, capability.measurements⟩

def capability {arity target : Nat} (parameters : Fin arity → Static.Expression target)
    (declarations : List Raw.CapabilityType) (manifest : Raw.Manifest) (source : Raw.CapabilityUse) :
    Admission (Capability meaning table parameters declarations manifest source) := do
  let declaration ← select declarations source.type.index
  let identity ← select manifest.services declaration.value.identity.index
  let arguments ← liftStatic (Static.tuple parameters declaration.value.statics source.statics)
  let inputs ← types meaning table arguments.parameters declaration.value.arguments
  let output ← liftType (TypeAdmission.instantiate meaning table arguments.parameters declaration.value.result)
  return ⟨declaration, identity, arguments, inputs, output⟩

inductive Capabilities {arity target : Nat} (parameters : Fin arity → Static.Expression target)
    (declarations : List Raw.CapabilityType) (manifest : Raw.Manifest) : List Raw.CapabilityUse → Type where
  | nil : Capabilities parameters declarations manifest []
  | cons {source rest} (first : Capability meaning table parameters declarations manifest source)
      (tail : Capabilities parameters declarations manifest rest) :
      Capabilities parameters declarations manifest (source :: rest)

def Capabilities.signatures {domains meaning rawTypes table arity target parameters declarations manifest} :
    {sources : List Raw.CapabilityUse} → Capabilities (domains := domains) meaning (rawTypes := rawTypes) table
      (arity := arity) (target := target) parameters declarations manifest sources → List (ServiceSignature domains target)
  | _, .nil => []
  | _, .cons first tail => first.signature :: tail.signatures

def Capabilities.measurements {domains meaning rawTypes table arity target parameters declarations manifest} :
    {sources : List Raw.CapabilityUse} →
    (capabilities : Capabilities (domains := domains) meaning (rawTypes := rawTypes) table
      (arity := arity) (target := target) parameters declarations manifest sources) →
      Values ServiceMeasurement capabilities.signatures
  | _, .nil => .nil
  | _, .cons first tail => .cons first.measurements tail.measurements

theorem Capabilities.length {domains meaning rawTypes table arity target parameters declarations manifest sources}
    (capabilities : Capabilities (domains := domains) meaning (rawTypes := rawTypes) table
      (arity := arity) (target := target) parameters declarations manifest sources) :
    capabilities.signatures.length = sources.length := by
  induction capabilities with
  | nil => rfl
  | cons first rest ih => simp [signatures, ih]

def capabilities {arity target : Nat} (parameters : Fin arity → Static.Expression target)
    (declarations : List Raw.CapabilityType) (manifest : Raw.Manifest) : (sources : List Raw.CapabilityUse) →
    Admission (Capabilities meaning table parameters declarations manifest sources)
  | [] => return .nil
  | first :: rest => do
      consume
      let first ← capability meaning table parameters declarations manifest first
      let rest ← capabilities parameters declarations manifest rest
      return .cons first rest

structure OperationSignature (domains target : Nat) where
  identity : Raw.Identity
  statics : List (Static.Expression target)
  capabilities : List (ServiceSignature domains target)
  arguments : List (TypeExpansion.Shape domains target)
  result : TypeExpansion.Shape domains target
  deriving DecidableEq

/-- Runtime root counters accompany the signature without entering its key.
Every field is mathematically fixed by the signature it measures. -/
structure OperationMeasurement {domains target : Nat} (signature : OperationSignature domains target) where
  signatureTypes : Data.capacity.SignatureMeasurement signature.arguments signature.result
  capabilities : Values ServiceMeasurement signature.capabilities

instance {domains target : Nat} {signature : OperationSignature domains target} :
    Subsingleton (OperationMeasurement signature) where
  allEq first second := by
    cases first with
    | mk types capabilities =>
      cases second with
      | mk otherTypes otherCapabilities =>
        cases Subsingleton.elim types otherTypes
        cases Subsingleton.elim capabilities otherCapabilities
        rfl

structure Operation {arity target : Nat} (parameters : Fin arity → Static.Expression target)
    (module : Raw.Module) (manifest : Raw.Manifest) (index : Nat) (actuals : List Static.Raw) where
  typeTable : module.types = rawTypes
  declaration : Selected module.operations index
  identity : Selected manifest.operations declaration.value.identity.index
  arguments : Static.Tuple parameters declaration.value.statics actuals
  capabilities : Capabilities meaning table arguments.parameters module.capabilityTypes manifest declaration.value.capabilities
  inputs : Types meaning table arguments.parameters declaration.value.arguments
  output : TypeAdmission.Instantiated meaning table arguments.parameters declaration.value.result

def Operation.signature {domains meaning rawTypes table arity target parameters module manifest index actuals}
    (operation : Operation (domains := domains) meaning (rawTypes := rawTypes) table
      (arity := arity) (target := target) parameters module manifest index actuals) : OperationSignature domains target :=
  ⟨operation.identity.value, operation.arguments.values,
    operation.capabilities.signatures, operation.inputs.shapes, operation.output.expanded.shape⟩

def Operation.measurements {domains meaning rawTypes table arity target parameters module manifest index actuals}
    (operation : Operation (domains := domains) meaning (rawTypes := rawTypes) table
      (arity := arity) (target := target) parameters module manifest index actuals) :
    OperationMeasurement operation.signature :=
  ⟨⟨operation.inputs.measurements, Data.capacity.measurement operation.output.expanded.measured⟩,
    operation.capabilities.measurements⟩

def operation {arity target : Nat} (parameters : Fin arity → Static.Expression target)
    (module : Raw.Module) (manifest : Raw.Manifest) (index : Nat) (actuals : List Static.Raw)
    (typeTable : module.types = rawTypes) :
    Admission (Operation meaning table parameters module manifest index actuals) := do
  let declaration ← select module.operations index
  let identity ← select manifest.operations declaration.value.identity.index
  let arguments ← liftStatic (Static.tuple parameters declaration.value.statics actuals)
  let capabilities ← capabilities meaning table arguments.parameters module.capabilityTypes manifest declaration.value.capabilities
  let inputs ← types meaning table arguments.parameters declaration.value.arguments
  let output ← liftType (TypeAdmission.instantiate meaning table arguments.parameters declaration.value.result)
  return ⟨typeTable, declaration, identity, arguments, capabilities, inputs, output⟩

structure Wire {arity target : Nat} (parameters : Fin arity → Static.Expression target)
    (declarations : List Raw.Wire) (manifest : Raw.Manifest) (index : Nat) (actuals : List Static.Raw) where
  declaration : Selected declarations index
  identity : Selected manifest.wires declaration.value.identity.index
  arguments : Static.Tuple parameters declaration.value.statics actuals
  payload : TypeAdmission.Instantiated meaning table arguments.parameters declaration.value.type

def wire {arity target : Nat} (parameters : Fin arity → Static.Expression target)
    (declarations : List Raw.Wire) (manifest : Raw.Manifest) (index : Nat) (actuals : List Static.Raw) :
    Admission (Wire meaning table parameters declarations manifest index actuals) := do
  let declaration ← select declarations index
  let identity ← select manifest.wires declaration.value.identity.index
  let arguments ← liftStatic (Static.tuple parameters declaration.value.statics actuals)
  let payload ← liftType (TypeAdmission.instantiate meaning table arguments.parameters declaration.value.type)
  return ⟨declaration, identity, arguments, payload⟩

end Zkc.Source.Mathematical.SignatureAdmission
