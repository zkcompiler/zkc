module

public import Std.Data.HashSet
public import Zkc.Frontend.Environment.Intern
public import Zkc.Frontend.Environment.Query
public import Zkc.Frontend.Typed.Signature
public import Zkc.Frontend.Typed.Checked
public import Zkc.Frontend.Typed.Summary
public import Zkc.Frontend.Emit.Reports

@[expose] public section

set_option autoImplicit false

/-!
# The store of results

What a program computes from static values, kept for the whole run and keyed by what was asked.
An instance belongs to no file: an instance of a declaration of a library at the arguments of a
program is reached from the program. So these tables are of the program, not of a file:

- `signatures`: a declaration at static values gives its closed signature. The number of the
  entry is the number of the instance;
- `bodies`: an instance gives what its body came to and what is kept of it beside its tree
  (`Typing.BodyState`): the summary that callers, packages, schemes and tools read;
- `trees`: an instance gives the typed tree of its body, which emission reads;
- `checked`: a protocol instance gives its tree with the tables of the passes.

A package is emitted per root, from the trees: no table holds a place in a package.

The closed types and the static values are interned here, and the roots are listed in the order
they were asked for. The store also holds what the typing of bodies and the check of instances
make beside the bodies: the rows that bodies apply, the order in which bodies were finished, the
obligations of laws, what was reported without a refusal, the default instances of each
declaration, and the schemes.
-/

namespace Zkc.Frontend

structure ResultStore where
  types : Interner ClosedType := {}
  values : Interner StaticValue := {}
  signatures : QueryTable InstanceKey Typed.Signature := {}
  bodies : QueryTable InstanceId Typing.BodyState := {}
  /-- The typed tree of each instance: what the passes, the check of its facts and the
  emission of a package read. -/
  trees : QueryTable InstanceId Typed.Definition := {}
  checked : QueryTable InstanceId Typed.Checked := {}
  /-- The instances that the run was asked for, in order, with why. -/
  roots : Array (InstanceId × Emit.EntryKind) := #[]
  /-- The instances first asked for as default instances (SP7). -/
  defaultInstances : Std.HashSet InstanceId := {}
  /-- The rows that bodies apply, by their identity. -/
  rows : Array Typing.Row := #[]
  rowIndex : Std.HashMap Typing.RowKey Typing.RowId := {}
  /-- The function instances in the order their typing finished. -/
  finished : Array InstanceId := #[]
  /-- The obligations of the laws typed, in the order they were typed. -/
  obligations : Array Typing.Obligation := #[]
  /-- What is reported without refusing: a row of a project, a declaration without default
  instance. -/
  reports : Array String := #[]
  /-- The default instances of each declaration that has static parameters (SP7). -/
  defaults : Array DefaultReport := #[]
  /-- The schemes of the files given, in the order of the program. -/
  schemes : Array SchemeEntry := #[]
  /-- The package of each root that is a function or a protocol, and what the core made of it,
  in the order of the roots. -/
  packageReports : Array PackageReport := #[]
  /-- What became of each scheme, in the order of the schemes. -/
  schemeReports : Array SchemeReport := #[]
  deriving Inhabited

namespace ResultStore

/-- The key of an instance. -/
def key? (store : ResultStore) (id : InstanceId) : Option InstanceKey :=
  (store.signatures.entries[id]?).map (·.key)

def signature? (store : ResultStore) (id : InstanceId) : Option Typed.Signature :=
  match store.signatures.entries[id]? with
  | some { state := .done signature, .. } => some signature
  | _ => none

/-- The content of an instance whose signature is done: a type, a static name, a module, or the
types of a head. -/
def content? (store : ResultStore) (id : InstanceId) : Option InstanceContent :=
  match store.signature? id with
  | some (.data content) => some content
  | _ => none

/-- The instance of a key, when it was asked for. -/
def instance? (store : ResultStore) (key : InstanceKey) : Option InstanceId :=
  store.signatures.find? key

/-- The number of instances asked for. -/
def instanceCount (store : ResultStore) : Nat := store.signatures.entries.size

/-- Whether an instance was first asked for as a default instance. -/
def isDefault (store : ResultStore) (id : InstanceId) : Bool := store.defaultInstances.contains id

/-- What the typing of an instance's body has come to: absent before it is asked for. -/
def body? (store : ResultStore) (id : InstanceId) : Option Typing.BodyState :=
  match store.bodies.entry? id with
  | some { state := .inProgress, .. } => some .inProgress
  | some { state := .done body, .. } => some body
  | some { state := .failed, .. } => some .failed
  | some { state := .skipped, .. } => none
  | some { state := .waiting reason, .. } => some (.waiting reason)
  | some { state := .exhausted exhaustion, .. } => some (.exhausted exhaustion)
  | none => none

/-- The number of a row, entering it when it is new. -/
def internRow (store : ResultStore) (row : Typing.Row) : ResultStore × Typing.RowId :=
  match store.rowIndex[row.key]? with
  | some id => (store, id)
  | none =>
    let rows := store.rows
    let rowIndex := store.rowIndex
    let store := { store with rows := #[], rowIndex := {} }
    let id := rows.size
    ({ store with rows := rows.push row, rowIndex := rowIndex.insert row.key id }, id)

def checked? (store : ResultStore) (id : InstanceId) : Option Typed.Checked :=
  store.checked.result? id

/-- The requests that the computation of a request made. -/
def requestsOf (store : ResultStore) (request : QueryRef) : Array QueryRef :=
  match request.kind with
  | .signature => ((store.signatures.entries[request.instance]?).map (·.requests)).getD #[]
  | .body => ((store.bodies.entry? request.instance).map (·.requests)).getD #[]
  | .tree => ((store.trees.entry? request.instance).map (·.requests)).getD #[]
  | .checked => ((store.checked.entry? request.instance).map (·.requests)).getD #[]

/-- What was asked and where it was first asked from. -/
def requested? (store : ResultStore) (request : QueryRef) : Option ChainFrame :=
  match request.kind with
  | .signature => (store.signatures.entries[request.instance]?).map (·.requested)
  | .body => (store.bodies.entry? request.instance).map (·.requested)
  | .tree => (store.trees.entry? request.instance).map (·.requested)
  | .checked => (store.checked.entry? request.instance).map (·.requested)

/-! The changes of a table take it out of the store first, so that a store that no one else
holds is changed in place rather than copied. -/

@[inline] def modifySignatures (store : ResultStore)
    (change : QueryTable InstanceKey Typed.Signature → QueryTable InstanceKey Typed.Signature) :
    ResultStore :=
  let table := store.signatures
  let store := { store with signatures := {} }
  { store with signatures := change table }

@[inline] def modifyBodies (store : ResultStore)
    (change : QueryTable InstanceId Typing.BodyState → QueryTable InstanceId Typing.BodyState) :
    ResultStore :=
  let table := store.bodies
  let store := { store with bodies := {} }
  { store with bodies := change table }

@[inline] def modifyTrees (store : ResultStore)
    (change : QueryTable InstanceId Typed.Definition → QueryTable InstanceId Typed.Definition) :
    ResultStore :=
  let table := store.trees
  let store := { store with trees := {} }
  { store with trees := change table }

@[inline] def modifyChecked (store : ResultStore)
    (change : QueryTable InstanceId Typed.Checked → QueryTable InstanceId Typed.Checked) :
    ResultStore :=
  let table := store.checked
  let store := { store with checked := {} }
  { store with checked := change table }

/-- One more root of a kind. -/
def addRoot (store : ResultStore) (inst : InstanceId) (kind : Emit.EntryKind) : ResultStore :=
  let roots := store.roots
  let store := { store with roots := #[] }
  { store with roots := roots.push (inst, kind) }

/-- One more function instance whose typing finished. -/
def addFinished (store : ResultStore) (inst : InstanceId) : ResultStore :=
  let finished := store.finished
  let store := { store with finished := #[] }
  { store with finished := finished.push inst }

/-- One more request made by the computation of `requester`. -/
def addRequest (store : ResultStore) (requester request : QueryRef) : ResultStore :=
  match requester.kind with
  | .signature =>
    match store.key? requester.instance with
    | some key => store.modifySignatures (·.addRequest key request)
    | none => store
  | .body => store.modifyBodies (·.addRequest requester.instance request)
  | .tree => store.modifyTrees (·.addRequest requester.instance request)
  | .checked => store.modifyChecked (·.addRequest requester.instance request)

/-- Every request that the given ones reach through the requests recorded, themselves
included. -/
partial def reach (store : ResultStore) (start : Array QueryRef) : Std.HashSet QueryRef :=
  go start {}
where
  go (pending : Array QueryRef) (seen : Std.HashSet QueryRef) : Std.HashSet QueryRef :=
    match pending.back? with
    | none => seen
    | some request =>
      if seen.contains request then go pending.pop seen
      else go (pending.pop ++ store.requestsOf request) (seen.insert request)

/-- The instances that the given instances reach: every instance about which a request was
made, directly or through others, for the signature, the body, the tree or the passes of one
of them. -/
def reachedInstances (store : ResultStore) (start : Array InstanceId) : Std.HashSet InstanceId :=
  let requests := start.flatMap fun id =>
    #[⟨.signature, id⟩, ⟨.body, id⟩, ⟨.tree, id⟩, ⟨.checked, id⟩]
  (store.reach requests).fold (init := {}) fun reached request => reached.insert request.instance

/-- The declarations that have an instance. After the roots are elaborated these are the
declarations that a root reached (SP7). -/
def reachedDeclarations (store : ResultStore) : Std.HashSet DeclarationId :=
  store.signatures.entries.foldl (init := {}) fun reached entry =>
    reached.insert entry.key.declaration

end ResultStore

end Zkc.Frontend
