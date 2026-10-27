module

public import Zkc.Source.Structured.Vocabulary

@[expose] public section
namespace Zkc.Source.Structured

/-- Registry-owned kinds exclude source formulas and captured assets. -/
def Relation.isOpaque (relation : Relation) : Bool :=
  !(relation.kind.toList.take 4 == ['z', 'k', 'c', '.'])

structure OpaqueFamilyIdentity where
  kind : String
  key : String
  revision : String
  deriving DecidableEq, Repr

structure OpaqueIdentity where
  family : OpaqueFamilyIdentity
  arguments : List OriginTerm
  deriving DecidableEq, Repr

def Relation.opaqueIdentity (relation : Relation) : OpaqueIdentity :=
  ⟨⟨relation.kind, relation.key, relation.revision⟩, relation.staticArguments⟩

def Relation.staticArgumentsValid (relation : Relation) : Bool :=
  relation.staticArguments.length ≤ Limits.originBindings &&
  relation.staticArguments.all (OriginTerm.valid Limits.nesting) &&
  originTermsWithin Limits.originTerms relation.staticArguments &&
  (relation.isOpaque || relation.staticArguments.isEmpty)

/-- Static domains are checked even when no runtime input mentions them. -/
def OriginTerm.checkCatalogue (exported environment : Catalogue) : Nat → OriginTerm → Except String Unit
  | 0, _ => throw "structured-relation-static-depth"
  | _ + 1, .field identity => do
    discard <| exported.expect identity .field
    discard <| environment.expect identity .field
  | _ + 1, .group identity => do
    discard <| exported.expect identity .group
    discard <| environment.expect identity .group
  | _ + 1, .domain sort identity => do
    let row ← exported.find identity
    let admitted ← environment.find identity
    if row.sort.spelling != sort || admitted != row then throw "structured-relation-static-domain"
  | depth + 1, .tuple arguments | depth + 1, .nominal _ _ arguments
  | depth + 1, .builtin _ arguments | depth + 1, .formal _ arguments =>
    arguments.forM (OriginTerm.checkCatalogue exported environment depth)
  | depth + 1, .array element _ => element.checkCatalogue exported environment depth
  | _ + 1, _ => pure ()

/-- Aliases cannot change a closed identity's ordered ABI or purposes. -/
def checkRelationIdentities (relations : List Relation) : Except String Unit := do
  for relation in relations do
    unless relation.staticArgumentsValid do throw "structured-relation-static-arguments"
    for previous in relations do
      if relation.opaqueIdentity == previous.opaqueIdentity &&
          (relation.inputs != previous.inputs || relation.outputs != previous.outputs ||
           relation.purposes != previous.purposes) then
        throw "structured-relation-conflict"

end Zkc.Source.Structured
