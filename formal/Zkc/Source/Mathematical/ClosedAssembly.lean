import Zkc.Source.Mathematical.InstanceProvenance
import Zkc.Source.Mathematical.StoredDefinitions

/-! Source-certified assembly of closed typed bodies.

The execution table keeps callees before callers. Each stored body retains its
actual authored declaration, closed parameter tuple, positional role mapping,
header-root binding, resolved source body and intrinsic erasure certificate.
Call resolution selects an exact closed instance key in the earlier table.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.ClosedAssembly
open ClosedInstances (Key Instance Node)

variable {Payload : ManifestAdmission.Category → Type} {contracts : RegistryAdmission.Contracts Payload}
  {source : Raw.Subject} (header : DeclarationAdmission.Header contracts source)

abbrev Vocabulary := RegisteredVocabulary.vocabulary header 0

structure Record where
  key : Key
  target : Protocol.Target Nat (Vocabulary header)

def recordKeys (records : List (Record header)) := records.map (·.key)
def recordTargets (records : List (Record header)) := records.map (·.target)
def scope (records : List (Record header)) := (recordTargets header records).map Protocol.Target.signature

theorem recordTargets_snoc (records : List (Record header)) (record : Record header) :
    recordTargets header (records ++ [record]) = recordTargets header records ++ [record.target] := by
  simp [recordTargets]

def CallValid {key} (parent : Instance source key) (records : List (Record header))
    (raw : ProtocolResolution.CallUse) (index : Nat) : Prop :=
  ∃ site, ∃ edge : ClosedInstances.Call parent site,
    site.use = raw ∧ (recordKeys header records)[index]? = some edge.target

private def resolve {key} (parent : Instance source key) (records : List (Record header))
    (raw : ProtocolResolution.CallUse) : {sites : List ClosedInstances.CallSite} →
      Values (ClosedInstances.Call parent) sites → StateT Nat (Except String)
        { index : Nat // CallValid header parent records raw index }
  | _, .nil => throw "closed-call-source"
  | _, .cons (ty := site) first rest => do
      let remaining ← get
      let cost := 1 + raw.statics.length + raw.roles.length + raw.capabilities.length
      if cost > remaining then throw "closed-call-resource"
      set (remaining - cost)
      if same : site.use = raw then
        let remaining ← get
        if records.length > remaining then throw "closed-call-resource"
        set (remaining - records.length)
        let selected ← fun remaining =>
          (ClosedInstances.find first.target (recordKeys header records) remaining).mapError (fun _ => "closed-call-resource")
        let some selected := selected | throw "closed-call-target"
        return ⟨selected.val, site, first, same, selected.property⟩
      else resolve parent records raw rest

def resolver {key} (node : Node source key) (records : List (Record header)) : RegisteredVocabulary.Calls where
  Valid := CallValid header node.checked records
  resolve raw := resolve header node.checked records raw node.children

inductive Error where
  | resource | roots | calls | mapping
  | definition (reason : DefinitionAdmission.Error)
  | entry (reason : Protocol.Error)
  | closure (reason : ClosedInstances.Error)
  deriving Repr

abbrev Admission := StateT Nat (Except Error)

private def consume (amount : Nat := 1) : Admission Unit := do
  let remaining ← get
  if amount > remaining then throw .resource
  set (remaining - amount)

structure Prepared (records : List (Record header)) (key : Key) (node : Node source key) where
  bound : DefinitionAdmission.Bound header node.checked.declaration.value node.checked.parameters node.checked.binding
    (resolver header node records) (scope header records) header.capabilities key.roots
  roots : bound.body.checked.program.rootsValid = true
  calls : bound.body.checked.program.callsMatch (Protocol.targetRoots (targets := recordTargets header records)) = true

def Prepared.target {records key node} (prepared : Prepared header records key node) :
    Protocol.Target Nat (Vocabulary header) :=
  ⟨node.checked.binding.participants, prepared.bound.selected.bound,
    prepared.bound.signature.value.arguments, prepared.bound.signature.value.results⟩

def Prepared.record {records key node} (prepared : Prepared header records key node) : Record header :=
  ⟨key, prepared.target⟩

theorem Prepared.target_roots {records key node} (prepared : Prepared header records key node) :
    prepared.target.capabilities.map Protocol.Capability.root = key.roots :=
  prepared.bound.selected.bound_roots.trans
    ((prepared.bound.selected.roots_eq_indices header.rootTable).trans prepared.bound.erasure)

theorem Prepared.target_signature {records key node} (prepared : Prepared header records key node) :
    prepared.target.signature = prepared.bound.signature.value := by
  simp [Prepared.target, Protocol.Target.signature, DefinitionAdmission.Signature.value]
  exact prepared.bound.selected.bound_permissions

theorem Prepared.source_erasure {records key node} (prepared : Prepared header records key node) :
    prepared.bound.body.resolved.erase = node.checked.declaration.value.body := prepared.bound.body.erasure

theorem Prepared.typed_erasure {records key node} (prepared : Prepared header records key node) :
    prepared.bound.body.checked.program.erase = prepared.bound.body.resolved.lower := prepared.bound.body.checked.erasure

theorem selected_definition {key} {node : Node source key} {records raw index}
    (valid : (resolver header node records).Valid raw index) :
    ∃ selected : Key, (recordKeys header records)[index]? = some selected ∧ selected.definition = raw.definition.index := by
  obtain ⟨site, edge, same, lookup⟩ := valid
  exact ⟨edge.target, lookup, edge.exactDefinition.trans (congrArg (fun call => call.definition.index) same)⟩

def prepare (records : List (Record header)) (key : Key) (node : Node source key) :
    Admission (Prepared header records key node) := do
  let bound ← fun remaining =>
    (DefinitionAdmission.bind header node.checked.declaration.value node.checked.parameters node.checked.binding
      (resolver header node records) (scope header records) header.capabilities key.roots remaining).mapError Error.definition
  consume (1 + bound.body.checked.program.sites.length * (key.roots.length + records.length + 1))
  if roots : bound.body.checked.program.rootsValid = true then
    if calls : bound.body.checked.program.callsMatch (Protocol.targetRoots (targets := recordTargets header records)) = true then
      return ⟨bound, roots, calls⟩
    else throw .calls
  else throw .roots

/-- The constructor derives the stored record from its source-bound body;
neither the record's key nor the executable body can be supplied independently. -/
inductive History : List (Record header) → Type where
  | nil : History []
  | snoc {records key node} (previous : History records) (prepared : Prepared header records key node) :
      History (records ++ [prepared.record])

def History.definitions : {records : List (Record header)} → History header records →
    Protocol.Definitions header.capabilities (recordTargets header records)
  | _, .nil => .nil
  | _, .snoc previous prepared =>
      (Protocol.Definitions.snoc (previous.definitions) prepared.target prepared.bound.body.checked.program
        (DefinitionAdmission.Bound.rooted header prepared.bound header.rooted) prepared.roots prepared.calls).reindex
          (recordTargets_snoc header _ _).symm

structure Table where
  records : List (Record header)
  history : History header records

def append (table : Table header) (packed : ClosedInstances.Packed source) : Admission (Table header) := do
  let prepared ← prepare header table.records packed.1 packed.2
  consume (table.records.length + 1)
  return ⟨table.records ++ [prepared.record], .snoc table.history prepared⟩

def build (table : Table header) : List (ClosedInstances.Packed source) → Admission (Table header)
  | [] => return table
  | first :: rest => do
      let table ← append header table first
      build table rest

/-- Both directions retain exact keys. Together with uniqueness, these maps
give the checked bijection between preorder IDs and execution-table positions. -/
structure Positions (graph : ClosedInstances.Graph source) (records : List (Record header)) where
  unique : (recordKeys header records).Nodup
  forward : Values (ClosedInstances.Reference (recordKeys header records)) (ClosedInstances.keys graph.nodes)
  backward : Values (ClosedInstances.Reference (ClosedInstances.keys graph.nodes)) (recordKeys header records)

def Positions.toStored {graph records} (positions : Positions header graph records) :=
  ClosedInstances.indexMap positions.forward

def Positions.toSource {graph records} (positions : Positions header graph records) :=
  ClosedInstances.indexMap positions.backward

theorem Positions.source_roundtrip {graph records} (positions : Positions header graph records)
    (index : Fin (ClosedInstances.keys graph.nodes).length) :
    Positions.toSource header positions (Positions.toStored header positions index) = index :=
  ClosedInstances.indexMap_inverse graph.unique positions.forward positions.backward index

theorem Positions.stored_roundtrip {graph records} (positions : Positions header graph records)
    (index : Fin (recordKeys header records).length) :
    Positions.toStored header positions (Positions.toSource header positions index) = index :=
  ClosedInstances.indexMap_inverse positions.unique positions.backward positions.forward index

def positions (graph : ClosedInstances.Graph source) (records : List (Record header)) :
    Admission (Positions header graph records) := do
  let keys := recordKeys header records
  consume ((keys.foldl (fun total key => total + key.cost) 1) * (keys.length + 1))
  if unique : keys.Nodup then
    let forward ← fun remaining =>
      (ClosedInstances.references keys (ClosedInstances.keys graph.nodes) remaining).mapError Error.closure
    let backward ← fun remaining =>
      (ClosedInstances.references (ClosedInstances.keys graph.nodes) keys remaining).mapError Error.closure
    return ⟨unique, forward, backward⟩
  else throw .mapping

structure Result where
  graph : ClosedInstances.Graph source
  table : Table header
  positions : Positions header graph table.records
  entryPosition : ClosedInstances.Reference (recordKeys header table.records) (ClosedInstances.entryKey source)
  entry : Protocol.Entry header.capabilities (recordTargets header table.records)
    entryPosition.val (source.module.entry.capabilities.map (·.index))

def Result.closed (result : Result header) : Protocol.Closed (vocabulary := Vocabulary header) header.capabilities :=
  ⟨header.rootTable, recordTargets header result.table.records, result.table.history.definitions,
    result.entryPosition.val, source.module.entry.capabilities.map (·.index), result.entry⟩

def assemble (graph : ClosedInstances.Graph source) : Admission (Result header) := do
  -- Sorting affects only the proof table. The source graph retains native IDs.
  -- Every call decreases the authored definition index, including same-key reuse.
  consume (graph.nodes.length * (graph.nodes.length + 1))
  let ordered := graph.nodes.mergeSort (fun left right => left.1.definition ≤ right.1.definition)
  let table ← build header ⟨[], .nil⟩ ordered
  let positions ← positions header graph table.records
  let graphEntry : Fin (ClosedInstances.keys graph.nodes).length := ⟨graph.entry.val, graph.entry.bound⟩
  let position := Positions.toStored header positions graphEntry
  let entryPosition : ClosedInstances.Reference (recordKeys header table.records) (ClosedInstances.entryKey source) :=
    ⟨position.val, (ClosedInstances.indexMap_key positions.forward graphEntry).trans graph.entry.property⟩
  let entry ← fun remaining =>
    (Protocol.entry header.capabilities (recordTargets header table.records) entryPosition.val
      (source.module.entry.capabilities.map (·.index)) remaining).mapError Error.entry
  return ⟨graph, table, positions, entryPosition, entry⟩

end Zkc.Source.Mathematical.ClosedAssembly
