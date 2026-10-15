module

public import Zkc.Source.Structured.Admission
public import Zkc.Specification

@[expose] public section

namespace Zkc.Source.Structured

/-- One formed body per declaration. Its exact lowered tree is retained, while
the full original metadata remains in `Program.snapshot`. -/
structure CheckedDefinition where
  name : String
  inputs : List Ty
  outputs : List Ty
  raw : RawRegion Ty Op
  body : Region dialect inputs outputs
  formed : raw.elaborate (dialect := dialect) inputs outputs = .ok body
  dependencies : List String
  instructionCount : Nat

theorem CheckedDefinition.exactBody (definition : CheckedDefinition) :
    definition.body.erase = definition.raw :=
  RawRegion.erase_of_elaborate (dialect := dialect) definition.raw definition.formed

def checkDefinition (snapshot : Snapshot) (domains : List DomainSpec)
    (summaries : IdentitySummaries) (definition : Definition) : Except String CheckedDefinition := do
  let (raw, state) ← match definition with
    | .function f =>
      (lowerBlock snapshot domains summaries f.kind 64 f.inputs
        (f.preconditions.map fun bound => (bound.index, bound.container)) .function f.body).run {}
    | .finite f => do
      let spec ← resolveFold snapshot domains .local f.domain f.step f.predicate
        f.inputs f.outputs (List.range f.inputs.length) []
      let dependencies := [f.step] ++ if f.predicate.isEmpty then [] else [f.predicate]
      let raw : RawRegion Ty Op := .letOp (.fold spec) (List.range f.inputs.length)
        f.outputs .nil (.ret (List.range f.outputs.length))
      pure (raw, { dependencies, instructions := 1 : LowerState })
  match formed : raw.elaborate (dialect := dialect) definition.inputs definition.outputs with
  | .error _ => throw "structured-formation"
  | .ok body => return ⟨definition.name, definition.inputs, definition.outputs,
      raw, body, formed, state.dependencies, state.instructions⟩

structure OrderedDefinition where
  definition : CheckedDefinition
  depth : Nat

/-- Kahn ordering over the stored definitions. The recursion bound is the number
of declarations, not evaluation fuel. Shared dependencies are never expanded. -/
def orderDefinitions : Nat → List CheckedDefinition → List OrderedDefinition →
    Except String (List OrderedDefinition)
  | _, [], ordered => .ok ordered
  | 0, _ :: _, _ => .error "structured-helper-cycle"
  | remaining + 1, pending, ordered => do
    let ready := pending.find? fun definition =>
      definition.dependencies.all fun name => ordered.any (·.definition.name == name)
    let some next := ready | throw "structured-helper-cycle"
    let dependencies : List OrderedDefinition ← next.dependencies.mapM fun name =>
      requireSome (ordered.find? (·.definition.name == name)) "structured-helper-resolution"
    let depth : Nat := (dependencies.map (·.depth + 1)).foldl max 0
    if depth > 64 then throw "structured-reference-depth"
    orderDefinitions remaining (pending.filter (·.name != next.name))
      (ordered ++ [⟨next, depth⟩])

structure Payload where
  definitions : List CheckedDefinition
  entryIndex : Fin definitions.length

def Payload.entry (payload : Payload) : CheckedDefinition :=
  payload.definitions.get payload.entryIndex

def findEntry (name : String) (definitions : List CheckedDefinition) :
    Except String (Fin definitions.length) := do
  let index := definitions.findIdx (·.name == name)
  if h : index < definitions.length then return ⟨index, h⟩
  else throw "structured-entry"

def check_payload (snapshot : Snapshot) : Except String Payload := do
  if !Format.digestValid snapshot.source || !validString snapshot.entry ||
      !validString snapshot.role then throw "structured-identity"
  if snapshot.domains.length > 128 || snapshot.definitions.length > 128 then
    throw "structured-table-limit"
  let names := snapshot.domains.map (·.name) ++ snapshot.definitions.map (·.name)
  if names.eraseDups.length != names.length then throw "structured-duplicate-symbol"
  if !snapshot.definitions.all Definition.headerValid then throw "structured-header"
  if !snapshot.instructionsWithin 4096 then throw "structured-instruction-limit"
  let entry ← lookupDefinition snapshot snapshot.entry
  if entry.kind != .protocol then throw "structured-entry-kind"
  let domains ← snapshot.domains.mapM Domain.resolve
  let summaries ← snapshot.identitySummaries
  let definitions ← snapshot.definitions.mapM (checkDefinition snapshot domains summaries)
  if (definitions.map (·.instructionCount)).foldl (· + ·) 0 > 4096 then
    throw "structured-instruction-limit"
  if (definitions.map (·.dependencies.length)).foldl (· + ·) 0 > 100000 then
    throw "structured-reference-visits"
  let ordered ← orderDefinitions definitions.length definitions []
  let definitions := ordered.map (·.definition)
  return ⟨definitions, ← findEntry snapshot.entry definitions⟩

structure Program where
  snapshot : Snapshot
  payload : Payload

def check (snapshot : Snapshot) : Except String Program :=
  match check_payload snapshot with
  | .error error => .error error
  | .ok payload => .ok ⟨snapshot, payload⟩

/-- Exact raw constructor data is the proof subject, including metadata that
logical execution does not observe. The digest's relation to MLIR is external. -/
abbrev Imported (snapshot : Snapshot) := Verification.Imported check snapshot

/-- Convenience constructor for externally generated, transparent snapshot data.
Concrete clients can discharge the Boolean premise with `decide +kernel`. -/
def importedOfIsOk (snapshot : Snapshot) (accepted : (check snapshot).isOk = true) :
    Imported snapshot :=
  match result : check snapshot with
  | .ok program => ⟨program, result⟩
  | .error error => False.elim (by simp [result, Except.isOk, Except.toBool] at accepted)

theorem check_parts (snapshot : Snapshot) (payload : Payload)
    (accepted : check_payload snapshot = .ok payload) :
    check snapshot = .ok ⟨snapshot, payload⟩ := by
  simp [check, accepted]

/-- Inversion of successful admission: retain the exact snapshot and the
successful computational checks. This does not prove their semantic soundness. -/
theorem check_ok_inversion {snapshot : Snapshot} {program : Program}
    (accepted : check snapshot = .ok program) :
    program.snapshot = snapshot ∧ check_payload snapshot = .ok program.payload := by
  cases h : check_payload snapshot with
  | error error => simp [check, h] at accepted
  | ok payload =>
    have same : (⟨snapshot, payload⟩ : Program) = program := by simpa [check, h] using accepted
    cases same
    exact ⟨rfl, rfl⟩

theorem Imported.exactSubject {snapshot : Snapshot} (imported : Imported snapshot) :
    imported.program.snapshot = snapshot := (check_ok_inversion imported.admitted).1

theorem Imported.admission {snapshot : Snapshot} (imported : Imported snapshot) :
    check_payload snapshot = .ok imported.program.payload := (check_ok_inversion imported.admitted).2

def decode (text : String) : Except String Program := do
  check (← Format.snapshot (← Format.parse text))

end Zkc.Source.Structured
