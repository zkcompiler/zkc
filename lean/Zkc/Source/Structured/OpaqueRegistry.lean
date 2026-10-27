module

public import Zkc.Source.Structured.RelationChecking

@[expose] public section
set_option autoImplicit false
namespace Zkc.Source.Structured

/-- The registry fixes the full ordered signature, including logical purposes. -/
structure OpaqueInstance (Value : Ty → Type) where
  inputs : List Ty
  outputs : List Ty := [.boolean]
  purposes : List String
  holds : Values Value inputs → Prop

/-- A family owns one partial, explicitly typed instantiation function. It may
refuse unsupported domains or static arguments. Source contains no Lean names. -/
structure OpaqueFamily (Value : Ty → Type) where
  identity : OpaqueFamilyIdentity
  instantiate : List OriginTerm → Option (OpaqueInstance Value)

/-- Registry selection precedes evidence. Duplicate family identities are
excluded even when their predicates happen to be extensionally equal. -/
structure OpaqueRegistry (Value : Ty → Type) where
  families : List (OpaqueFamily Value)
  unique : (families.map (·.identity)).Nodup

namespace OpaqueRegistry
variable {Value : Ty → Type}

def empty : OpaqueRegistry Value := ⟨[], by simp⟩

/-- Build an ordinary explicit registry, refusing duplicate family ownership. -/
def ofFamilies (families : List (OpaqueFamily Value)) : Except String (OpaqueRegistry Value) :=
  if unique : (families.map (·.identity)).Nodup then .ok ⟨families, unique⟩
  else .error "opaque-registry-duplicate-family"

def lookup (registry : OpaqueRegistry Value) (identity : OpaqueIdentity) :
    Option (OpaqueInstance Value) := do
  let family ← registry.families.find? (fun family => family.identity == identity.family)
  family.instantiate identity.arguments

/-- Evidence carries only the result of fixed lookup and exact ABI equalities;
it cannot supply a predicate. Captured and formula relations cannot bind here. -/
structure Binding (registry : OpaqueRegistry Value) (relation : Relation) where
  instantiation : OpaqueInstance Value
  selected : registry.lookup relation.opaqueIdentity = some instantiation
  inputs : instantiation.inputs = relation.inputs
  outputs : instantiation.outputs = relation.outputs
  purposes : instantiation.purposes = relation.purposes
  opaqueKind : relation.isOpaque = true
  noFormula : relation.formula = none

def Binding.Holds {registry : OpaqueRegistry Value} {relation : Relation}
    (binding : Binding registry relation) (arguments : Values Value relation.inputs) : Prop :=
  binding.instantiation.holds (binding.inputs.symm ▸ arguments)

/-- Exact lookup is the adapter law for consumers of a registered predicate. -/
theorem Binding.holds_exact {registry : OpaqueRegistry Value} {relation : Relation}
    (binding : Binding registry relation) (arguments : Values Value relation.inputs) :
    binding.Holds arguments ↔ binding.instantiation.holds (binding.inputs.symm ▸ arguments) := Iff.rfl

/-- Different evidence records for one identity and signature cannot swap meaning. -/
theorem Binding.unique_meaning {registry : OpaqueRegistry Value} {relation : Relation}
    (first second : Binding registry relation) (arguments : Values Value relation.inputs) :
    first.Holds arguments ↔ second.Holds arguments := by
  have same : first.instantiation = second.instantiation := Option.some.inj (first.selected.symm.trans second.selected)
  cases first
  cases second
  cases same
  rfl

def resolve (registry : OpaqueRegistry Value) (relation : Relation) :
    Option (Binding registry relation) :=
  if relation.staticArgumentsValid then
    if opaqueKind : relation.isOpaque = true then
      if noFormula : relation.formula = none then
        match selected : registry.lookup relation.opaqueIdentity with
        | none => none
        | some instantiation =>
          if inputs : instantiation.inputs = relation.inputs then
            if outputs : instantiation.outputs = relation.outputs then
              if purposes : instantiation.purposes = relation.purposes then
                some ⟨instantiation, selected, inputs, outputs, purposes, opaqueKind, noFormula⟩
              else none
            else none
          else none
      else none
    else none
  else none

/-- Meaning admission is separate from structural source import. Every opaque
row, including an unused one, must resolve in the caller's fixed registry. -/
def check (registry : OpaqueRegistry Value) (relations : List Relation) : Bool :=
  relations.all (fun relation => !relation.isOpaque || (registry.resolve relation).isSome)

end OpaqueRegistry

/-- An admitted registry environment has no independently chosen predicates. -/
structure RegisteredRelations (Value : Ty → Type) (relations : List Relation) where
  registry : OpaqueRegistry Value
  admitted : ∀ index : Fin relations.length,
    (relations.get index).isOpaque = true → (registry.resolve (relations.get index)).isSome = true

namespace RegisteredRelations
variable {Value : Ty → Type} {relations : List Relation}

def meanings (environment : RegisteredRelations Value relations)
    (index : Fin relations.length) (arguments : Values Value (relations.get index).inputs) : Prop :=
  if opaqueKind : (relations.get index).isOpaque = true then
    ((environment.registry.resolve (relations.get index)).get (environment.admitted index opaqueKind)).Holds arguments
  else False

/-- Fixed typed adapter: the indexed environment denotes exactly the selected
registry binding, with no consumer-supplied predicate or adequacy premise. -/
theorem meanings_exact (environment : RegisteredRelations Value relations)
    (index : Fin relations.length)
    (binding : OpaqueRegistry.Binding environment.registry (relations.get index))
    (arguments : Values Value (relations.get index).inputs) :
    environment.meanings index arguments ↔ binding.Holds arguments := by
  unfold meanings
  rw [dite_eq_left binding.opaqueKind]
  exact OpaqueRegistry.Binding.unique_meaning _ binding arguments

/-- Formula-only units need no opaque entries; their meanings are helper bodies. -/
def formulaOnly (noOpaque : ∀ relation ∈ relations, relation.isOpaque = false) :
    RegisteredRelations Value relations where
  registry := .empty
  admitted index opaqueKind := by
    have absent := noOpaque (relations.get index) (List.get_mem ..)
    exact Bool.noConfusion (absent.symm.trans opaqueKind)

/-- Check success supplies exactly the admission used by the environment. -/
def ofChecked (registry : OpaqueRegistry Value)
    (checked : registry.check relations = true) : RegisteredRelations Value relations where
  registry := registry
  admitted index opaqueKind := by
    have all := List.all_eq_true.mp checked (relations.get index) (List.get_mem ..)
    change (!((relations.get index).isOpaque) || (registry.resolve (relations.get index)).isSome) = true at all
    simpa only [opaqueKind, Bool.not_true, Bool.false_or] using all

end RegisteredRelations
end Zkc.Source.Structured
