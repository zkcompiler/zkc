import Zkc.Source.Mathematical.DataBounds
import Zkc.Source.Mathematical.RegisteredVocabulary

/-! Admission of relation predicates through the installed mathematical graph
vocabulary. Every listed law is selected from the actual admitted manifest.
A listed law remains an assumption; its identity alone proves no proposition.
Public and witness inputs retain their separate signatures and ordered layout.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.RelationAdmission

inductive Error where
  | resource | result
  | signature (reason : SignatureAdmission.Error)
  | graph (reason : GraphResolution.Error)
  | static (reason : Static.ResolutionError)
  deriving Repr

abbrev Admission := StateT Nat (Except Error)

private def consume (amount : Nat := 1) : Admission Unit := do
  let remaining ← get
  if amount > remaining then throw .resource
  set (remaining - amount)

private def liftSignature {α : Type} (action : SignatureAdmission.Admission α) : Admission α :=
  fun remaining => (action remaining).mapError Error.signature

variable {Payload : ManifestAdmission.Category → Type} {contracts : RegistryAdmission.Contracts Payload}
  {source : Raw.Subject} (header : DeclarationAdmission.Header contracts source)

structure Law (reference : Raw.Reference .law) where
  identity : SignatureAdmission.Selected source.manifest.laws reference.index
  selected : ManifestAdmission.Selected contracts.installation source.manifest .law identity.value
  exactSelection : selected = header.context.selected .law identity

def law (reference : Raw.Reference .law) : Admission (Law header reference) := do
  let identity ← liftSignature (SignatureAdmission.select source.manifest.laws reference.index)
  return ⟨identity, header.context.selected .law identity, rfl⟩

def laws : (references : List (Raw.Reference .law)) → Admission (Values (Law header) references)
  | [] => return .nil
  | first :: rest => do
      consume
      let first ← law header first
      let rest ← laws rest
      return .cons first rest

def inputs {domains target : Nat} (publicTypes witnessTypes : List (TypeExpansion.Shape domains target)) :=
  (publicTypes ++ witnessTypes).map fun type => (⟨[0], type⟩ : Port Nat _)

structure Instance {target : Nat} (declaration : Raw.Relation)
    (parameters : Fin declaration.statics → Static.Expression target) where
  publicInputs : SignatureAdmission.Types header.context.meaning header.types parameters declaration.publicInputs
  witnessInputs : SignatureAdmission.Types header.context.meaning header.types parameters declaration.witnessInputs
  assumptions : Values (Law header) declaration.assumptions
  body : GraphResolution.Admitted (RegisteredVocabulary.graph header parameters) [0]
    (inputs publicInputs.shapes witnessInputs.shapes) declaration.body
  result : body.graph.ports.map Port.ty = [(RegisteredVocabulary.vocabulary header target).condition]

def instantiate {target : Nat} (declaration : Raw.Relation)
    (parameters : Fin declaration.statics → Static.Expression target) : Admission (Instance header declaration parameters) := do
  consume
  let publicInputs ← liftSignature (SignatureAdmission.types header.context.meaning header.types parameters declaration.publicInputs)
  let witnessInputs ← liftSignature (SignatureAdmission.types header.context.meaning header.types parameters declaration.witnessInputs)
  let assumptions ← laws header declaration.assumptions
  let resolver := RegisteredVocabulary.graph header parameters
  let resolved ← fun remaining => (GraphResolution.region resolver (FormationLimits.regionDepth + 1) declaration.body remaining).mapError Error.graph
  let captured ← (Graph.selectOperands (inputs publicInputs.shapes witnessInputs.shapes) resolved.val.captures)
    |>.mapError (fun reason => Error.graph (.graph reason))
  let graph ← (Graph.decode [0] Data.capacity (fun _ => true) (FormationLimits.regionDepth + 1) captured.ports resolved.val.lower)
    |>.mapError (fun reason => Error.graph (.graph reason))
  let body : GraphResolution.Admitted resolver [0] (inputs publicInputs.shapes witnessInputs.shapes) declaration.body :=
    ⟨resolved.val, resolved.property, captured, graph⟩
  if result : body.graph.ports.map Port.ty = [(RegisteredVocabulary.vocabulary header target).condition] then
    return ⟨publicInputs, witnessInputs, assumptions, body, result⟩
  else throw .result

def symbolic (declaration : Raw.Relation) : Admission
    (Instance header declaration (DeclarationAdmission.parameters declaration.statics)) := do
  consume declaration.statics
  instantiate header declaration (DeclarationAdmission.parameters declaration.statics)

def all : (declarations : List Raw.Relation) → Admission
    (Values (fun declaration => Instance header declaration (DeclarationAdmission.parameters declaration.statics)) declarations)
  | [] => return .nil
  | first :: rest => do
      let first ← symbolic header first
      let rest ← all rest
      return .cons first rest

structure Use {arity target : Nat} (parameters : Fin arity → Static.Expression target)
    (reference : Raw.Reference .relation) (actuals : List Static.Raw) where
  declaration : SignatureAdmission.Selected source.module.relations reference.index
  arguments : Static.Tuple parameters declaration.value.statics actuals
  checked : Instance header declaration.value arguments.parameters

def use {arity target : Nat} (parameters : Fin arity → Static.Expression target)
    (reference : Raw.Reference .relation) (actuals : List Static.Raw) : Admission (Use header parameters reference actuals) := do
  let declaration ← liftSignature (SignatureAdmission.select source.module.relations reference.index)
  let arguments ← fun remaining => (Static.tuple parameters declaration.value.statics actuals remaining).mapError Error.static
  let checked ← instantiate header declaration.value arguments.parameters
  return ⟨declaration, arguments, checked⟩

end Zkc.Source.Mathematical.RelationAdmission
