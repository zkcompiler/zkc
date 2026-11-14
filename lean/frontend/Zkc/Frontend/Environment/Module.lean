module

public import Std.Data.HashSet
public import Zkc.Frontend.Lowered.Declaration
public import Zkc.Frontend.Semantics.Resolution

@[expose] public section

set_option autoImplicit false

/-!
# The store of files

What is known of each file of a program before any instance exists, indexed by file module: its
syntax, its namespaces and what they export, its parameter scopes, its declarations as written,
its table of resolutions, and its lowered declarations. Nothing here depends on a static value,
so the record of a file is a function of the file and of the records of the files its `use`
lines name. It is what another file may depend on, and what a file on disk would hold.

The declarations, namespaces, scopes and imports of every file are numbered in tables of the
whole program, so that a reference is one number. Each file owns a range of each
table: the numbers given to it when it was added. A reference that leaves the run names the
owner by its module path, which no two files of a program share, with the offset in its range
(`ModuleRef`): it depends neither on the order in which files were added nor on the run.
-/

namespace Zkc.Frontend

/-- A file module of the program. -/
abbrev ModuleId := FileId

/-- A run of consecutive numbers of a table. -/
structure IdRange where
  start : Nat := 0
  size : Nat := 0
  deriving Inhabited, BEq, Repr

namespace IdRange

def contains (range : IdRange) (id : Nat) : Bool := range.start ≤ id && id < range.start + range.size

/-- The place of a number in the range. -/
def offset? (range : IdRange) (id : Nat) : Option Nat :=
  if range.contains id then some (id - range.start) else none

end IdRange

/-- A reference to an entry of a file that does not depend on the run: the file by its module
path, written `a::b::c`, and the place of the entry among the file's entries of its table. -/
structure ModuleRef where
  «module» : String
  offset : Nat
  deriving Inhabited, BEq, Hashable, Repr

/-- The record of one file. -/
structure ModuleRecord where
  /-- The source: the name it was read under, the module path, the tree, and whether it came
  from the library. -/
  source : SourceUnit
  /-- The file modules that its `use` lines name, in order, the prelude first. -/
  imports : Array ModuleId := #[]
  /-- The ranges of the program's tables that are its own. -/
  declarations : IdRange := {}
  namespaces : IdRange := {}
  scopes : IdRange := {}
  uses : IdRange := {}
  /-- What each written path of the file stands for, by the byte at which it starts. The lowered
  declarations hold the same resolutions in place; the table is what a tool prints. -/
  resolutions : FileResolutions := {}
  /-- The lowered scopes and declarations, in the order of their ranges. Empty until the file
  is lowered. -/
  loweredScopes : Array Lowered.Scope := #[]
  lowered : Array Lowered.Declaration := #[]
  /-- The lowered path and listed name of each `use` line, in the order of its range. -/
  loweredUses : Array (Array Lowered.Expr) := #[]
  /-- The file was refused by the lexer or the parser, or a path to it was. Nothing reached
  through it is refused again. -/
  poisoned : Bool := false
  deriving Inhabited

/-- What another file may depend on: the names a file exports, and its lowered scopes and
declarations. A file that changes without changing this leaves the files that use it as they
are. -/
structure ModuleInterface where
  path : Array String
  /-- The public names of the file's namespaces, each with the namespace and what it is bound
  to, as references that do not depend on the run. -/
  exports : Array (ModuleRef × String × ModuleRef)
  scopes : Array Lowered.Scope
  declarations : Array Lowered.Declaration
  deriving Inhabited

/-- What the program's declarations give at once, read off the tables after resolution: the
sorts of `zkc::algebra` by declaration, the declarations of every namespace in the order of the
text, the name the program gives each row of the vocabulary (for messages), the declaration
whose own scope each scope is, and, for each interface, the modules that name it in their bound,
the given files first (SP7). -/
structure ProgramIndexes where
  sortNames : Std.HashMap DeclarationId String := {}
  members : Std.HashMap NamespaceId (Array DeclarationId) := {}
  rowNames : Std.HashMap String String := {}
  scopeOwners : Std.HashMap ScopeId DeclarationId := {}
  implementers : Std.HashMap DeclarationId (Array DeclarationId) := {}
  deriving Inhabited

/-- The records of every file of the program, and the tables their entries are numbered in. -/
structure ModuleStore where
  records : Array ModuleRecord := #[]
  /-- The file modules by their path, written `a::b::c`. -/
  byPath : Std.HashMap String ModuleId := {}
  /-- The declarations, namespaces, parameter scopes and imports of every file. -/
  program : Program := {}
  /-- Module paths whose file the parser refused or whose header names another path: a path
  to one of them stands for nothing, and is not refused again. -/
  unreadable : Std.HashSet String := {}
  /-- The static terms of the comments `// instantiate: m<args>`, with their file. -/
  instantiations : Array (FileId × Syntax.Expr) := #[]
  /-- The same terms, lowered. -/
  loweredInstantiations : Array (FileId × Lowered.Expr) := #[]
  indexes : ProgramIndexes := {}
  deriving Inhabited

namespace ModuleStore

def record? (store : ModuleStore) (id : ModuleId) : Option ModuleRecord := store.records[id]?

/-- The resolution of a path of a file, by the byte at which it starts. -/
def resolution? (store : ModuleStore) (file : FileId) (path : Syntax.Path) : Option Resolution :=
  match path with
  | .path span _ => (store.records[file]?).bind fun record => record.resolutions[span.startByte]?

/-- The resolution of the name or path that starts at a byte of a file. -/
def resolutionAt? (store : ModuleStore) (file : FileId) (byte : UInt32) : Option Resolution :=
  (store.records[file]?).bind fun record => record.resolutions[byte]?

/-- The tables of resolutions of every file, as one value. -/
def resolutions (store : ModuleStore) : Resolutions := { files := store.records.map (·.resolutions) }



/-- The file that owns a declaration. -/
def owner? (store : ModuleStore) (id : DeclarationId) : Option ModuleId :=
  (store.program.declarations[id]?).map (·.file)

/-- A declaration as a reference that does not depend on the run. -/
def declarationRef? (store : ModuleStore) (id : DeclarationId) : Option ModuleRef := do
  let «module» ← store.owner? id
  let record ← store.records[«module»]?
  return { «module» := pathText record.source.path, offset := ← record.declarations.offset? id }

/-- The declaration that a reference names in this run. -/
def declarationOf? (store : ModuleStore) (reference : ModuleRef) : Option DeclarationId := do
  let record ← store.records[← store.byPath[reference.module]?]?
  if reference.offset < record.declarations.size then
    return record.declarations.start + reference.offset
  else none

/-- The lowered form of a parameter scope, once its file is lowered. -/
def loweredScope? (store : ModuleStore) (id : ScopeId) : Option Lowered.Scope := do
  let scope ← store.program.scopes[id]?
  let record ← store.records[scope.file]?
  record.loweredScopes[← record.scopes.offset? id]?

/-- The tables of resolutions of every file, in the order of the files. -/
def tables (store : ModuleStore) : Array FileResolutions := store.records.map (·.resolutions)

/-- The lowered form of a declaration, once its file is lowered. -/
def lowered? (store : ModuleStore) (id : DeclarationId) : Option Lowered.Declaration := do
  let «module» ← store.owner? id
  let record ← store.records[«module»]?
  record.lowered[← record.declarations.offset? id]?

/-- The record of a file with its ranges, added after the files before it. The tables of the
program already hold its entries. -/
def add (store : ModuleStore) (record : ModuleRecord) : ModuleStore × ModuleId :=
  let id := store.records.size
  ({ store with records := store.records.push record
                byPath := store.byPath.insert (pathText record.source.path) id }, id)

/-- The lowered declarations of a file, set once. -/
def setLowered (store : ModuleStore) (id : ModuleId) (scopes : Array Lowered.Scope)
    (declarations : Array Lowered.Declaration) : ModuleStore :=
  { store with records := store.records.modify id fun record =>
      { record with loweredScopes := scopes, lowered := declarations } }

/-- Every file with the lowered declarations, scopes and `use` lines of its ranges, from those of
the program by number. -/
def withLowered (store : ModuleStore) (declarations : Array Lowered.Declaration)
    (scopes : Array Lowered.Scope) (uses : Array (Array Lowered.Expr))
    (instantiations : Array (FileId × Lowered.Expr)) : ModuleStore :=
  { store with loweredInstantiations := instantiations, records := store.records.map fun record =>
      { record with
        lowered := declarations.extract record.declarations.start
          (record.declarations.start + record.declarations.size)
        loweredScopes := scopes.extract record.scopes.start (record.scopes.start + record.scopes.size)
        loweredUses := uses.extract record.uses.start (record.uses.start + record.uses.size) } }

/-- What another file may depend on of a file. -/
def interface? (store : ModuleStore) (id : ModuleId) : Option ModuleInterface := do
  let record ← store.records[id]?
  let mut exports := #[]
  for offset in [0:record.namespaces.size] do
    let some found := store.program.namespaces[record.namespaces.start + offset]? | continue
    for (name, binding) in found.names.toArray.qsort (·.1 < ·.1) do
      let .declaration declaration := binding | continue
      let some target := store.declarationRef? declaration | continue
      if (store.program.declarations[declaration]?).any (·.pub) then
        exports := exports.push ({ «module» := pathText record.source.path, offset }, name, target)
  return { path := record.source.path, exports, scopes := record.loweredScopes
           declarations := record.lowered }

/-- The range of a table that the entries of a file occupy, when they are consecutive. -/
def rangeOf {α : Type} [Inhabited α] (entries : Array α) (fileOf : α → FileId) (file : FileId) :
    IdRange := Id.run do
  let mut start : Option Nat := none
  let mut size := 0
  for index in [0:entries.size] do
    if fileOf entries[index]! == file then
      if start.isNone then start := some index
      size := size + 1
  return { start := start.getD 0, size }

/-- The store of a program whose files are assembled and whose names are resolved: one record
per file, with its ranges of the program's tables and its table of resolutions. -/
def ofProgram (program : Program) (resolutions : Resolutions) (unreadable : Std.HashSet String)
    (instantiations : Array (FileId × Syntax.Expr)) : ModuleStore := Id.run do
  let mut store : ModuleStore := { program, unreadable, instantiations }
  for file in [0:program.files.size] do
    let record : ModuleRecord :=
      { source := program.files[file]!
        declarations := rangeOf program.declarations (·.file) file
        namespaces := rangeOf program.namespaces (·.file) file
        scopes := rangeOf program.scopes (·.file) file
        uses := rangeOf program.imports (·.file) file
        resolutions := (resolutions.files[file]?).getD {} }
    store := (store.add record).1
  return store

end ModuleStore

end Zkc.Frontend
