import Zkc.Source.Mathematical.DefinitionAdmission

/-! Source call selection for symbolic definition formation.

Every call selects an earlier authored definition, substitutes its static
arguments and positional roles, and retains the resulting signature. The finite
call table supplies exactly those signatures to intrinsic body checking. Actual
root binding and closed instance reuse belong to closed closure admission.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.DefinitionCalls

inductive Error where
  | resource | depth | forward
  | signature (reason : SignatureAdmission.Error)
  | static (reason : Static.ResolutionError)
  | roles (reason : String)
  | definition (reason : DefinitionAdmission.Error)
  deriving Repr

abbrev Admission := StateT Nat (Except Error)

private def consume (amount : Nat := 1) : Admission Unit := do
  let remaining ← get
  if amount > remaining then throw .resource
  set (remaining - amount)

variable {Payload : ManifestAdmission.Category → Type} {contracts : RegistryAdmission.Contracts Payload}
  {source : Raw.Subject} (header : DeclarationAdmission.Header contracts source)
  {arity target : Nat} (parameters : Fin arity → Static.Expression target)
  (roles : RoleResolution.Binding) (before : Nat)

structure Entry where
  raw : ProtocolResolution.CallUse
  earlier : raw.definition.index < before
  declaration : SignatureAdmission.Selected source.module.definitions raw.definition.index
  statics : Static.Tuple parameters declaration.value.statics raw.statics
  binding : RoleResolution.Composed roles declaration.value.roles raw.roles
  signature : DefinitionAdmission.Signature header declaration.value statics.parameters binding.binding

def entry (raw : ProtocolResolution.CallUse) : Admission (Entry header parameters roles before) := do
  consume
  if earlier : raw.definition.index < before then
    let declaration ← fun remaining =>
      (SignatureAdmission.select source.module.definitions raw.definition.index remaining).mapError Error.signature
    let statics ← fun remaining =>
      (Static.tuple parameters declaration.value.statics raw.statics remaining).mapError Error.static
    let binding ← fun remaining =>
      (RoleResolution.compose roles declaration.value.roles raw.roles remaining).mapError Error.roles
    let signature ← fun remaining =>
      (DefinitionAdmission.signature header declaration.value statics.parameters binding.binding remaining).mapError Error.definition
    return ⟨raw, earlier, declaration, statics, binding, signature⟩
  else throw .forward

mutual
  def collectBody : Nat → Raw.Body → Admission (List (Entry header parameters roles before))
    | 0, _ => throw .depth
    | fuel + 1, .mk steps _ => do
        consume
        collectSteps (fuel + 1) steps
  termination_by _ body => sizeOf body
  def collectSteps (fuel : Nat) : List Raw.Step → Admission (List (Entry header parameters roles before))
    | [] => return []
    | first :: rest => do
        consume
        let first ← match first with
          | .invoke _ definition statics callRoles capabilities _ => do
              let checked ← entry header parameters roles before ⟨definition, statics, callRoles, capabilities⟩
              pure [checked]
          | .repeat _ _ _ _ _ body => collectBody (fuel - 2) body
          | _ => pure []
        let rest ← collectSteps fuel rest
        consume first.length
        return first ++ rest
  termination_by steps => sizeOf steps
end

variable {header parameters roles before}

def scope (entries : List (Entry header parameters roles before)) :=
  entries.map fun entry => entry.signature.value

def Selected (entries : List (Entry header parameters roles before))
    (raw : ProtocolResolution.CallUse) (index : Nat) : Prop :=
  ∃ entry, entries[index]? = some entry ∧ entry.raw = raw

private def resolve (raw : ProtocolResolution.CallUse) :
    (entries : List (Entry header parameters roles before)) → StateT Nat (Except String)
      { index : Nat // Selected entries raw index }
  | [] => throw "call-scope"
  | first :: rest => do
      let remaining ← get
      let cost := 1 + raw.statics.length + raw.roles.length + raw.capabilities.length
      if cost > remaining then throw "call-resource"
      set (remaining - cost)
      if same : first.raw = raw then
        return ⟨0, first, rfl, same⟩
      else
        let tail ← resolve raw rest
        return ⟨tail.val + 1, by
          obtain ⟨entry, selected, same⟩ := tail.property
          exact ⟨entry, by simpa using selected, same⟩⟩

def resolver (entries : List (Entry header parameters roles before)) : RegisteredVocabulary.Calls where
  Valid := Selected entries
  resolve raw := resolve raw entries

theorem selected_signature {entries : List (Entry header parameters roles before)}
    {raw index} (selected : (resolver entries).Valid raw index) :
    ∃ entry : Entry header parameters roles before, entry.raw = raw ∧ (scope entries)[index]? = some entry.signature.value ∧
      raw.definition.index < before := by
  obtain ⟨entry, lookup, same⟩ := selected
  refine ⟨entry, same, ?_, ?_⟩
  · simp [scope, List.getElem?_map, lookup]
  · rw [← same]
    exact entry.earlier

variable (header)

/-- The caller index selects the body being formed. The same index bounds every
callee lookup, so a supplied limit cannot silently authorize recursion. -/
structure Template (index : Nat) where
  declaration : SignatureAdmission.Selected source.module.definitions index
  roles : RoleResolution.Binding
  roleIdentity : roles.roles = List.range declaration.value.roles
  calls : List (Entry header (DeclarationAdmission.parameters declaration.value.statics) roles index)
  body : DefinitionAdmission.Template header declaration.value roles (resolver calls) (scope calls)

def template (index : Nat) : Admission (Template header index) := do
  let declaration ← fun remaining =>
    (SignatureAdmission.select source.module.definitions index remaining).mapError Error.signature
  let roles ← fun remaining => (RoleResolution.initialChecked declaration.value.roles remaining).mapError Error.roles
  let calls ← collectBody header (DeclarationAdmission.parameters declaration.value.statics) roles.val index (FormationLimits.bodyDepth + 1) declaration.value.body
  let body ← fun remaining =>
    (DefinitionAdmission.template header declaration.value roles.val (resolver calls) (scope calls) remaining).mapError Error.definition
  return ⟨declaration, roles.val, roles.property, calls, body⟩

def all : (indices : List Nat) → Admission (Values (Template header) indices)
  | [] => return .nil
  | first :: rest => do
      let first ← template header first
      let rest ← all rest
      return .cons first rest

def declarations : Admission (Values (Template header) (List.range source.module.definitions.length)) := do
  consume source.module.definitions.length
  all header (List.range source.module.definitions.length)

end Zkc.Source.Mathematical.DefinitionCalls
