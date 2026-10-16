module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Formed declarations and structural linking evidence, independent of source
parsing, lowering and preparation admission. -/

namespace Zkc.Source.Structured

/-- One formed body per declaration. Its exact lowered tree is retained, while
the full original metadata remains in `Program.snapshot`. -/
structure CheckedDefinition where
  name : String
  kind : HelperKind
  inputs : List Ty
  outputs : List Ty
  raw : RawRegion Ty Op
  body : Region dialect inputs outputs
  formed : raw.elaborate (dialect := dialect) inputs outputs = .ok body

def CheckedDefinition.helper (definition : CheckedDefinition) : Helper :=
  ⟨definition.name, definition.kind, definition.inputs, definition.outputs⟩

theorem CheckedDefinition.exactBody (definition : CheckedDefinition) :
    definition.body.erase = definition.raw :=
  RawRegion.erase_of_elaborate (dialect := dialect) definition.raw definition.formed

/-- Recover a typed body from its exact raw tree without unfolding admission. -/
theorem CheckedDefinition.body_eq_of_raw (definition : CheckedDefinition)
    (body : Region dialect definition.inputs definition.outputs)
    (same : definition.raw = body.erase) : definition.body = body := by
  have formed := definition.formed
  rw [same, Region.elaborate_erase (dialect := dialect) body] at formed
  exact (Except.ok.inj formed).symm

/-- Dependency authority is the formed operation tree, not separately recorded
names. This includes references in every nested callback and suffix. -/
def CheckedDefinition.helpers (definition : CheckedDefinition) : List Helper :=
  definition.raw.operations.flatMap Op.helpers

theorem CheckedDefinition.helpers_eq_body (definition : CheckedDefinition) :
    definition.helpers = definition.body.erase.operations.flatMap Op.helpers := by
  rw [definition.exactBody]
  rfl

def CheckedDefinition.dependencies (definition : CheckedDefinition) : List String :=
  definition.helpers.map (·.name)

def CheckedDefinition.instructionCount (definition : CheckedDefinition) : Nat :=
  definition.raw.operations.length

/-- Every reference resolves with its complete signature in the strict prefix.
Names remain unique even for declarations with different types. The traversal
also checks references in dormant callbacks through `CheckedDefinition.helpers`.
-/
def DeclarationsLinked (available : List Helper) : List CheckedDefinition → Prop
  | [] => True
  | definition :: rest =>
      definition.name ∉ available.map (·.name) ∧
      (∀ helper ∈ definition.helpers, helper ∈ available) ∧
      DeclarationsLinked (definition.helper :: available) rest

instance declarationsLinkedDecidable (available : List Helper) (definitions : List CheckedDefinition) :
    Decidable (DeclarationsLinked available definitions) :=
  match definitions with
  | [] => isTrue trivial
  | definition :: rest =>
    let _ := declarationsLinkedDecidable (definition.helper :: available) rest
    inferInstanceAs (Decidable
      (definition.name ∉ available.map (·.name) ∧
       (∀ helper ∈ definition.helpers, helper ∈ available) ∧
       DeclarationsLinked (definition.helper :: available) rest))

/-- A closed profile root is separate from the named helper table. -/
structure ClosedRoot where
  name : String
  inputs : List Ty
  outputs : List Ty
  raw : RawRegion Ty Op
  body : Region dialect inputs outputs
  formed : raw.elaborate (dialect := dialect) inputs outputs = .ok body

def ClosedRoot.helpers (root : ClosedRoot) : List Helper :=
  root.raw.operations.flatMap Op.helpers

theorem ClosedRoot.body_eq_of_raw (root : ClosedRoot)
    (body : Region dialect root.inputs root.outputs) (same : root.raw = body.erase) :
    root.body = body := by
  have formed := root.formed
  rw [same, Region.elaborate_erase (dialect := dialect) body] at formed
  exact (Except.ok.inj formed).symm

structure Payload where
  definitions : List CheckedDefinition
  entry : ClosedRoot
  linked : DeclarationsLinked [] definitions
  entryLinked : ∀ helper ∈ entry.helpers, helper ∈ definitions.map CheckedDefinition.helper

def findEntry (name : String) (definitions : List CheckedDefinition) :
    Except String (Fin definitions.length) := do
  let index := definitions.findIdx (·.name == name)
  if h : index < definitions.length then return ⟨index, h⟩
  else throw "structured-entry"

/-- Independently validate a proposed declaration order and exact signatures.
The resulting proof is erased at execution time; lookup remains name-based. -/
def linkPayload (entry : String) (definitions : List CheckedDefinition) : Except String Payload := do
  if linked : DeclarationsLinked [] definitions then
    let definition := definitions.get (← findEntry entry definitions)
    let root : ClosedRoot := ⟨definition.name, definition.inputs, definition.outputs,
      definition.raw, definition.body, definition.formed⟩
    if entryLinked : ∀ helper ∈ root.helpers, helper ∈ definitions.map CheckedDefinition.helper then
      return ⟨definitions, root, linked, entryLinked⟩
    else throw "structured-root-link"
  else throw "structured-helper-link"

structure CheckedProtocol extends ProtocolSignature where
  raw : RawRegion Ty ProtocolOp
  body : Region protocolDialect inputs outputs
  formed : raw.elaborate (dialect := protocolDialect) inputs outputs = .ok body

def CheckedProtocol.signature (definition : CheckedProtocol) : ProtocolSignature :=
  definition.toProtocolSignature

theorem CheckedProtocol.exactBody (definition : CheckedProtocol) :
    definition.body.erase = definition.raw :=
  RawRegion.erase_of_elaborate (dialect := protocolDialect) definition.raw definition.formed

def CheckedProtocol.protocols (definition : CheckedProtocol) : List ProtocolSignature :=
  definition.raw.operations.flatMap ProtocolOp.protocols

def CheckedProtocol.dependencies (definition : CheckedProtocol) : List String :=
  definition.protocols.map (·.name)

def CheckedProtocol.helpers (root : CheckedProtocol) : List Helper :=
  root.raw.operations.flatMap ProtocolOp.helpers

theorem CheckedProtocol.body_eq_of_raw (root : CheckedProtocol)
    (body : Region protocolDialect root.inputs root.outputs) (same : root.raw = body.erase) :
    root.body = body := by
  have formed := root.formed
  rw [same, Region.elaborate_erase (dialect := protocolDialect) body] at formed
  exact (Except.ok.inj formed).symm

end Zkc.Source.Structured
