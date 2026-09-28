import Zkc.Source.Mathematical.Raw

/-! Explicit selection of installed interpretation packages.

A manifest identity only selects a package already installed by the consumer.
The selected payload and exact identity equality remain in the admitted result.
Prerequisites refer to complete identities in the actual subject manifest;
their presence is checked even for packages unused by an entry body.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.ManifestAdmission

inductive Category where
  | domain | operation | wire | service | law
  deriving DecidableEq, Repr

def table (source : Raw.Manifest) : Category → List Raw.Identity
  | .domain => source.domains
  | .operation => source.operations
  | .wire => source.wires
  | .service => source.services
  | .law => source.laws

def key (identity : Raw.Identity) : String × String := (identity.name, identity.version)

def validDigest (identity : Raw.Identity) : Bool :=
  identity.digest.utf8ByteSize == 64 && identity.digest.toList.all
    (fun ch => ('0' ≤ ch && ch ≤ '9') || ('a' ≤ ch && ch ≤ 'f'))

structure Requirement where
  category : Category
  identity : Raw.Identity
  deriving DecidableEq, Repr

structure Package (Payload : Category → Type) (category : Category) where
  identity : Raw.Identity
  interpretation : Payload category
  prerequisites : List Requirement

/-- This table belongs to a consumer installation. Its uniqueness condition
prevents lookup order from choosing between meanings with one name/version. -/
structure InstalledTable (Payload : Category → Type) (category : Category) where
  packages : List (Package Payload category)
  unique : (packages.map (fun package => key package.identity)).Nodup

abbrev Installation (Payload : Category → Type) := (category : Category) → InstalledTable Payload category

inductive Error where
  | resource | digest | duplicate | package | prerequisite
  deriving DecidableEq, Repr

abbrev Admission := StateT Nat (Except Error)

private def consume (amount : Nat := 1) : Admission Unit := do
  let available ← get
  if amount > available then throw .resource
  set (available - amount)

private def identityCost (identity : Raw.Identity) : Nat :=
  1 + identity.name.utf8ByteSize + identity.version.utf8ByteSize + identity.digest.utf8ByteSize

/-- Charge bytes before equality. The installation is finite, but its size is
not assumed free when resolving untrusted subject identities. -/
def select {Payload category} (source : Raw.Identity) :
    (packages : List (Package Payload category)) → Admission
      { package : Package Payload category // package ∈ packages ∧ package.identity = source }
  | [] => throw .package
  | first :: rest => do
      consume (identityCost source + identityCost first.identity)
      if same : first.identity = source then
        return ⟨first, by simp [same]⟩
      else
        let selected ← select source rest
        return ⟨selected.val, List.mem_cons_of_mem _ selected.property.1, selected.property.2⟩

private def present (identity : Raw.Identity) : (identities : List Raw.Identity) → Admission
    (PLift (identity ∈ identities))
  | [] => throw .prerequisite
  | first :: rest => do
      consume (identityCost identity + identityCost first)
      if same : identity = first then return ⟨List.mem_cons.mpr (.inl same)⟩
      else
        let member ← present identity rest
        return ⟨List.mem_cons_of_mem _ member.down⟩

private def prerequisites (source : Raw.Manifest) : (required : List Requirement) → Admission
    (PLift (∀ requirement ∈ required, requirement.identity ∈ table source requirement.category))
  | [] => return ⟨by simp⟩
  | first :: rest => do
      consume
      let member ← present first.identity (table source first.category)
      let tail ← prerequisites source rest
      return ⟨by
        intro requirement included
        rcases List.mem_cons.mp included with same | included
        · subst requirement; exact member.down
        · exact tail.down requirement included⟩

structure Selected {Payload : Category → Type} (installation : Installation Payload)
    (source : Raw.Manifest) (category : Category) (identity : Raw.Identity) where
  package : Package Payload category
  registered : package ∈ (installation category).packages
  exactIdentity : package.identity = identity
  digest : validDigest identity = true
  requirements : ∀ requirement ∈ package.prerequisites,
    requirement.identity ∈ table source requirement.category

private def resolve {Payload : Category → Type} (installation : Installation Payload)
    (source : Raw.Manifest) (category : Category) (identity : Raw.Identity) :
    Admission (Selected installation source category identity) := do
  consume (identityCost identity)
  if digest : validDigest identity = true then
    let selected ← select identity (installation category).packages
    let requirements ← prerequisites source selected.val.prerequisites
    return ⟨selected.val, selected.property.1, selected.property.2, digest, requirements.down⟩
  else throw .digest

/-- A typed list retains one selected interpretation at every authored index. -/
inductive Selections {Payload : Category → Type} (installation : Installation Payload)
    (source : Raw.Manifest) (category : Category) : List Raw.Identity → Type where
  | nil : Selections installation source category []
  | cons {identity rest} (first : Selected installation source category identity)
      (tail : Selections installation source category rest) :
      Selections installation source category (identity :: rest)

def Selections.get {Payload installation source category identities}
    (selected : Selections (Payload := Payload) installation source category identities)
    (index : Fin identities.length) : Selected installation source category identities[index] :=
  match selected, index with
  | .cons first _, ⟨0, _⟩ => first
  | .cons _ rest, ⟨index + 1, bound⟩ => rest.get ⟨index, Nat.lt_of_succ_lt_succ bound⟩

private def resolveAll {Payload : Category → Type} (installation : Installation Payload)
    (source : Raw.Manifest) (category : Category) : (identities : List Raw.Identity) → Admission
    (Selections installation source category identities)
  | [] => return .nil
  | first :: rest => do
      let first ← resolve installation source category first
      let rest ← resolveAll installation source category rest
      return .cons first rest

structure Admitted {Payload : Category → Type} (installation : Installation Payload) (source : Raw.Manifest) where
  unique : ∀ category, ((table source category).map key).Nodup
  selected : ∀ category, Selections installation source category (table source category)

private def admitTable {Payload : Category → Type} (installation : Installation Payload)
    (source : Raw.Manifest) (category : Category) : Admission
    (((table source category).map key).Nodup ×' Selections installation source category (table source category)) := do
  let identities := table source category
  consume identities.length
  let bytes := identities.foldl (fun total identity => total + identityCost identity) 0
  -- Structural duplicate comparison can scan the full strings for each pair.
  consume (bytes * (identities.length + 1))
  if unique : (identities.map key).Nodup then
    let selected ← resolveAll installation source category identities
    return ⟨unique, selected⟩
  else throw .duplicate

def admit {Payload : Category → Type} (installation : Installation Payload) (source : Raw.Manifest) :
    Admission (Admitted installation source) := do
  let domains ← admitTable installation source .domain
  let operations ← admitTable installation source .operation
  let wires ← admitTable installation source .wire
  let services ← admitTable installation source .service
  let laws ← admitTable installation source .law
  return {
    unique := fun category => match category with
      | .domain => domains.1 | .operation => operations.1 | .wire => wires.1
      | .service => services.1 | .law => laws.1
    selected := fun category => match category with
      | .domain => domains.2 | .operation => operations.2 | .wire => wires.2
      | .service => services.2 | .law => laws.2 }

end Zkc.Source.Mathematical.ManifestAdmission
