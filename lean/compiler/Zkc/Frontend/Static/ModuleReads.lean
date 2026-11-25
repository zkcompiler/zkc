module

public import Zkc.Frontend.Static.Basic

@[expose] public section
namespace Zkc.Frontend.Static

open Syntax

mutual
  /-- A real instance contains neither a module stand-in nor a fresh type, including
  inside the arguments of a type or another instance (SP12). -/
  partial def realInstance (state : Compile.State) (id : InstanceId) :
      StateM (Std.HashSet InstanceId) Bool := do
    if (← get).contains id then return true
    let some instanceKey := state.table.allocatedKey? id | return false
    if instanceKey.opaqueFor.isSome then return false
    modify (·.insert id)
    instanceKey.arguments.allM (realValue state)

  partial def realValue (state : Compile.State) :
      StaticValue → StateM (Std.HashSet InstanceId) Bool
    | .natural _ => pure true
    | .«module» id => realInstance state id
    | .type ty => realType state ty

  partial def realType (state : Compile.State) :
      ClosedType → StateM (Std.HashSet InstanceId) Bool
    | .opaque .. => pure false
    | .nonzero t | .seq t _ => realType state t
    | .tuple ts _ => ts.allM (realType state)
    | .nominal _ args => args.allM (realValue state)
    | .record id | .variant id | .specification id => realInstance state id
    | .bool | .nat | .rational | .index _ => pure true
end

/-- A solved declaration path can cross applied modules even when the leaf, such as
an interface or a scheme, has no signature instance of its own. -/
def enclosingModules (id : DeclarationId) (arguments : Array StaticValue) (place : Span) :
    CompileM (Array InstanceKey) := do
  let s ← get
  let some child := s.program.declarations[id]? | return #[]
  let mut cursor := s.program.namespaces[child.namespace]?
  unless cursor.any (·.parent.isSome) do return #[]
  let mut owners := #[]
  let values := ((deployedParameters s.program child).zip arguments).foldl
    (init := ({} : StaticEnvironment)) fun env ((ref, _), value) => env.insert ref value
  while let some ns := cursor do
    let some outer := ns.parent | break
    if let some owner := s.program.declarations[ns.owner]? then
      if owner.kind == .«module» then
        let mut args := #[]
        for (ref, parameter) in deployedParameters s.program owner do
          let some value := values[ref]?
            | refuse "SP6" place s!"cannot infer `{parameter.name.text}` of enclosing module `{s.program.nameOf ns.owner}`"
          args := args.push value
        let concrete : Bool := (args.allM (realValue s)).run' {}
        if concrete then
          owners := owners.push { declaration := ns.owner, arguments := args }
    cursor := s.program.namespaces[outer]?
  return owners

def observeEnclosingModules (id : DeclarationId) (arguments : Array StaticValue) (place : Span) :
    CompileM Unit := do
  for key in ← enclosingModules id arguments place do
    modify fun state => { state with moduleReads := state.moduleReads.push (.owner key place) }

/-- A projection also requires the concrete receiver whose table it reads. -/
def observeMember (inst : InstanceId) (place : Span) (receiver : Bool := false) : CompileM Unit := do
  let s ← get
  let some key := s.table.allocatedKey? inst | return
  if key.opaqueFor.isSome || key.view.isSome then return
  if receiver && (s.program.declarations[key.declaration]?).any (·.kind == .«module») &&
      (key.arguments.allM (realValue s)).run' {} then
    modify fun state => { state with moduleReads := state.moduleReads.push (.owner
      { declaration := key.declaration, arguments := key.arguments } place) }
  observeEnclosingModules key.declaration key.arguments place

/-- Passing a formed module by value uses its implementation. A primitive awaiting its
member table can still be named by identity. -/
def observeModuleValue (inst : InstanceId) (place : Span) : CompileM Unit := do
  if let some (.«module» ..) := (← get).table.content? inst then
    observeMember inst place (receiver := true)

/-- A solved static argument can use a module directly even if no member is selected. -/
def observeModuleArguments (values : Array StaticValue) (place : Span) : CompileM Unit := do
  for value in values do
    if let .«module» actual := value then observeModuleValue actual place

/-- Read the concrete owners of a declaration with no stored signature, including an
interface application or a binding that lowers directly to a core operation. -/
def observeDeclarationApplication (id : DeclarationId) (values : Array StaticValue) (place : Span) :
    CompileM Unit := do
  observeEnclosingModules id values place
  observeModuleArguments values place

/-- Read the concrete owners of a stored signature. -/
def observeApplication (inst : InstanceId) (place : Span) : CompileM Unit := do
  observeMember inst place
  if let some key := (← get).table.allocatedKey? inst then observeModuleArguments key.arguments place

mutual
  /-- A snapshot's argument can be reused directly when all its nominal identities already
  exist in the original, shared prefix. Reserved signature numbers have no entry. -/
  partial def sharedValue (table : SignatureTable InstanceKey Typed.Signature) (bound : Nat) :
      StaticValue → Bool
    | .natural _ => true
    | .«module» id => id < bound && (table.entryAt? id).isSome
    | .type ty => sharedType table bound ty

  partial def sharedType (table : SignatureTable InstanceKey Typed.Signature) (bound : Nat) :
      ClosedType → Bool
    | .record id | .variant id | .specification id => id < bound && (table.entryAt? id).isSome
    | .opaque .. => false
    | .nonzero ty | .seq ty _ => sharedType table bound ty
    | .tuple ts _ => ts.all (sharedType table bound)
    | .nominal _ args => args.all (sharedValue table bound)
    | .bool | .nat | .rational | .index _ => true
end

/-- Keep only the reads of a successful computation whose instance table will be discarded.
A nominal argument beyond the common prefix must be reconstructed in the checking table. -/
def detachedModuleReads (saved after : Compile.State) (reads : Array Compile.ModuleRead) :
    Array Compile.ModuleRead := Id.run do
  let mut pending := reads.toList
  let mut seen : Std.HashSet QueryRef := {}
  let mut localKeys : Std.HashSet InstanceKey := {}
  let mut result := #[]
  let shared := saved.table.allocatedCount
  while let item :: rest := pending do
    pending := rest
    match item with
    | .query ref =>
      unless seen.contains ref do
        seen := seen.insert ref
        if let some more := after.readsOfQuery[ref]? then pending := more.toList ++ pending
    | .owner key place none =>
      unless localKeys.contains key do
        localKeys := localKeys.insert key
        let source := if key.arguments.all (sharedValue saved.table shared) then none
          else some (shared, after.table)
        result := result.push (.owner key place source)
    | .owner key place (some (n, table)) =>
      result := result.push (.owner key place (some (min n shared, table)))
  return result

end Zkc.Frontend.Static
