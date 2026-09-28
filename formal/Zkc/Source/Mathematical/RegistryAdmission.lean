import Zkc.Source.Mathematical.ManifestAdmission
import Zkc.Source.Mathematical.SignatureAdmission
import Zkc.Source.Mathematical.AttributeAdmission

/-! Join authored signatures to the actual manifest-selected installation.

Installed contracts are consumer definitions, never subject data. The result
retains the selected package, its acceptance of the expanded signature, and
equality between its facts and the authored declaration. Domain interpretation
and formation are selected from the same admitted manifest. Operational
interpretation and algebraic laws still require the selected package's semantic
implementation; signature acceptance alone supplies neither.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.RegistryAdmission
open ManifestAdmission SignatureAdmission

structure OperationFacts where
  purity : Raw.Purity
  distinct : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- An installed vocabulary supplies its own exact signature and attribute
checks. Each check sees the actual subject manifest, so dependencies cannot be
silently replaced by another domain or service with the same shape. -/
structure Contracts (Payload : Category → Type) where
  installation : Installation Payload
  nominal : Payload .domain → String → List Nat → Type
  polynomial : Payload .domain → Nat → Nat → Raw.Degree → Type
  residual : Payload .domain → Nat → Nat → Type
  domain : {domains arity : Nat} → Raw.Manifest → Payload .domain → TypeExpansion.Atom domains arity → Bool
  service : {domains target : Nat} → Raw.Manifest → Payload .service → ServiceSignature domains target → Bool
  operation : {domains target : Nat} → Raw.Manifest → Payload .operation → OperationSignature domains target →
    Option OperationFacts
  wire : {domains target : Nat} → Raw.Manifest → Payload .wire → List (Static.Expression target) →
    TypeExpansion.Shape domains target → Bool
  attributes : {domains target : Nat} → Raw.Manifest → Payload .operation → OperationSignature domains target →
    Raw.Attribute → Bool

structure Context {Payload : Category → Type} (contracts : Contracts Payload) (source : Raw.Manifest) where
  manifest : Admitted contracts.installation source

variable {Payload : Category → Type} {contracts : Contracts Payload} {source : Raw.Manifest}

def Context.domain (context : Context contracts source) (index : Fin source.domains.length) : Payload .domain :=
  ((context.manifest.selected .domain).get index).package.interpretation

def Context.meaning (context : Context contracts source) : TypeSyntax.Interpretation source.domains.length where
  nominal index := contracts.nominal (context.domain index)
  polynomial index := contracts.polynomial (context.domain index)
  residual index := contracts.residual (context.domain index)

def Context.domainCheck (context : Context contracts source) : TypeExpansion.DomainCheck source.domains.length :=
  fun atom =>
    let index := match atom with
      | .nominal index .. | .polynomial index .. | .residual index .. => index
    contracts.domain source (context.domain index) atom

inductive Error where
  | resource | service | operation | wire | purity | distinct | attributes
  deriving DecidableEq, Repr

abbrev Admission := StateT Nat (Except Error)

private def consume (amount : Nat := 1) : Admission Unit := do
  let remaining ← get
  if amount > remaining then throw .resource
  set (remaining - amount)

/-- Retrieve the already selected package at the authored index. No second
name-based resolution can choose another interpretation. -/
def Context.selected (context : Context contracts source) (category : Category)
    {index : Nat} (identity : SignatureAdmission.Selected (table source category) index) :
    ManifestAdmission.Selected contracts.installation source category identity.value := by
  have bound : index < (table source category).length := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp identity.selected
    exact bound
  have same : (table source category)[index] = identity.value := by
    obtain ⟨_, same⟩ := List.getElem?_eq_some_iff.mp identity.selected
    exact same
  exact same ▸ (context.manifest.selected category).get ⟨index, bound⟩

/-- Canonical distinctness contracts refer to two different capability ports,
in increasing order, and contain no repeated or reordered pairs. -/
def Distinct (count : Nat) (pairs : List (Nat × Nat)) : Prop :=
  (∀ pair ∈ pairs, pair.1 < pair.2 ∧ pair.2 < count) ∧ pairs.Pairwise (fun a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2))

instance {count pairs} : Decidable (Distinct count pairs) := by unfold Distinct; infer_instance

def Purity (facts : OperationFacts) (capabilities : Nat) : Prop :=
  facts.purity = .total → capabilities = 0 ∧ facts.distinct = []

instance {facts capabilities} : Decidable (Purity facts capabilities) :=
  by unfold Purity; infer_instance

variable (context : Context contracts source)
  {rawTypes : List Raw.TypeTemplate} (types : TypeAdmission.Table context.meaning rawTypes)

structure Service {arity target : Nat} {parameters : Fin arity → Static.Expression target}
    {declarations : List Raw.CapabilityType} {use : Raw.CapabilityUse}
    (signature : SignatureAdmission.Capability context.meaning types parameters declarations source use) where
  selected : ManifestAdmission.Selected contracts.installation source .service signature.identity.value
  accepted : contracts.service source selected.package.interpretation signature.signature = true

def service {arity target : Nat} {parameters : Fin arity → Static.Expression target}
    {declarations : List Raw.CapabilityType} {use : Raw.CapabilityUse}
    (signature : SignatureAdmission.Capability context.meaning types parameters declarations source use) :
    Admission (Service context types signature) := do
  consume
  let selected := context.selected .service signature.identity
  if accepted : contracts.service source selected.package.interpretation signature.signature = true then
    return ⟨selected, accepted⟩
  else throw .service

inductive Services {arity target : Nat} {parameters : Fin arity → Static.Expression target}
    {declarations : List Raw.CapabilityType} : {uses : List Raw.CapabilityUse} →
    Capabilities context.meaning types parameters declarations source uses → Type where
  | nil : Services .nil
  | cons {use uses} {first : SignatureAdmission.Capability context.meaning types parameters declarations source use}
      {rest : Capabilities context.meaning types parameters declarations source uses}
      (service : Service context types first) (tail : Services rest) : Services (.cons first rest)

def services {arity target : Nat} {parameters : Fin arity → Static.Expression target}
    {declarations : List Raw.CapabilityType} : {uses : List Raw.CapabilityUse} →
    (signatures : Capabilities context.meaning types parameters declarations source uses) →
    Admission (Services context types signatures)
  | _, .nil => return .nil
  | _, .cons first rest => do
      let first ← service context types first
      let rest ← services rest
      return .cons first rest

structure Operation {arity target : Nat} {parameters : Fin arity → Static.Expression target}
    {module : Raw.Module} {index : Nat} {actuals : List Static.Raw}
    (signature : SignatureAdmission.Operation context.meaning types parameters module source index actuals) where
  selected : ManifestAdmission.Selected contracts.installation source .operation signature.identity.value
  facts : OperationFacts
  accepted : contracts.operation source selected.package.interpretation signature.signature = some facts
  exactPurity : facts.purity = signature.declaration.value.purity
  exactDistinct : facts.distinct = signature.declaration.value.distinct
  distinct : Distinct signature.declaration.value.capabilities.length facts.distinct
  purity : Purity facts signature.declaration.value.capabilities.length
  services : Services context types signature.capabilities

def operation {arity target : Nat} {parameters : Fin arity → Static.Expression target}
    {module : Raw.Module} {index : Nat} {actuals : List Static.Raw}
    (signature : SignatureAdmission.Operation context.meaning types parameters module source index actuals) :
    Admission (Operation context types signature) := do
  consume
  let services ← services context types signature.capabilities
  let selected := context.selected .operation signature.identity
  match accepted : contracts.operation source selected.package.interpretation signature.signature with
  | none => throw .operation
  | some facts =>
      consume (1 + facts.distinct.length + signature.declaration.value.distinct.length)
      if exactPurity : facts.purity = signature.declaration.value.purity then
        if exactDistinct : facts.distinct = signature.declaration.value.distinct then
          consume (facts.distinct.length * facts.distinct.length)
          if distinct : Distinct signature.declaration.value.capabilities.length facts.distinct then
            if purity : Purity facts signature.declaration.value.capabilities.length then
              return ⟨selected, facts, accepted, exactPurity, exactDistinct, distinct, purity, services⟩
            else throw .purity
          else throw .distinct
        else throw .operation
      else throw .operation

structure Wire {arity target : Nat} {parameters : Fin arity → Static.Expression target}
    {declarations : List Raw.Wire} {index : Nat} {actuals : List Static.Raw}
    (signature : SignatureAdmission.Wire context.meaning types parameters declarations source index actuals) where
  selected : ManifestAdmission.Selected contracts.installation source .wire signature.identity.value
  accepted : contracts.wire source selected.package.interpretation signature.arguments.values signature.payload.expanded.shape = true

def wire {arity target : Nat} {parameters : Fin arity → Static.Expression target}
    {declarations : List Raw.Wire} {index : Nat} {actuals : List Static.Raw}
    (signature : SignatureAdmission.Wire context.meaning types parameters declarations source index actuals) :
    Admission (Wire context types signature) := do
  consume
  let selected := context.selected .wire signature.identity
  if accepted : contracts.wire source selected.package.interpretation signature.arguments.values signature.payload.expanded.shape = true then
    return ⟨selected, accepted⟩
  else throw .wire

/-- Attributes are checked at each use against the actual selected operation,
after static substitution. They cannot modify its registered signature. -/
def attributes {arity target : Nat} {parameters : Fin arity → Static.Expression target}
    {module : Raw.Module} {index : Nat} {actuals : List Static.Raw}
    {signature : SignatureAdmission.Operation context.meaning types parameters module source index actuals}
    (operation : Operation context types signature) (value : Raw.Attribute) : Admission
      (PLift (AttributeAdmission.canonical value = true ∧
        contracts.attributes source operation.selected.package.interpretation signature.signature value = true)) := do
  AttributeAdmission.charge Error.resource 65 value
  if canonical : AttributeAdmission.canonical value = true then
    if accepted : contracts.attributes source operation.selected.package.interpretation signature.signature value = true then
      return ⟨canonical, accepted⟩
    else throw .attributes
  else throw .attributes

end Zkc.Source.Mathematical.RegistryAdmission
