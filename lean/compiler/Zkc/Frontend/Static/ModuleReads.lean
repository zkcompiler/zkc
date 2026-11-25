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

/-- The source modules enclosing a solved reference. A projection through a module value also
requires the receiver itself. File namespaces and opaque typing stand-ins create no obligations. -/
def observeMember (inst : InstanceId) (place : Span) (receiver : Bool := false) : CompileM Unit := do
  let s ← get
  let some key := s.table.allocatedKey? inst | return
  let some child := s.program.declarations[key.declaration]? | return
  if key.opaqueFor.isSome || key.view.isSome then return
  let mut cursor := s.program.namespaces[child.namespace]?
  unless (receiver && child.kind == .«module») || cursor.any (·.parent.isSome) do return
  let real : Bool := (key.arguments.allM (realValue s)).run' {}
  unless real do return
  if receiver && child.kind == .«module» then
    modify fun state => { state with moduleReads := state.moduleReads.push (.owner
      { declaration := key.declaration, arguments := key.arguments } place) }
  let values := ((deployedParameters s.program child).zip key.arguments).foldl
    (init := ({} : StaticEnvironment)) fun env ((ref, _), value) => env.insert ref value
  while let some ns := cursor do
    let some outer := ns.parent | break
    if let some owner := s.program.declarations[ns.owner]? then
      if owner.kind == .«module» then
        if let some args := (deployedParameters s.program owner).mapM (fun (ref, _) => values[ref]?) then
          let applied : InstanceKey := { declaration := ns.owner, arguments := args }
          modify fun state => { state with moduleReads := state.moduleReads.push (.owner applied place) }
    cursor := s.program.namespaces[outer]?

/-- A solved application also consumes its concrete module arguments. A provisional
receiver or a primitive with an unavailable member table can still be passed by identity. -/
def observeApplication (inst : InstanceId) (place : Span) : CompileM Unit := do
  observeMember inst place
  let state ← get
  let some key := state.table.allocatedKey? inst | return
  for value in key.arguments do
    if let .«module» actual := value then
      if let some (.«module» ..) := state.table.content? actual then
        observeMember actual place (receiver := true)

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
