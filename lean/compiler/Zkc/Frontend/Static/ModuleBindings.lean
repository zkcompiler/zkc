module

public import Zkc.Frontend.Static.ModuleReads

@[expose] public section

set_option autoImplicit false

/-! # Module header bindings and provisional interface checks (SP7, SP8) -/

namespace Zkc.Frontend.Static

open Syntax

def appliedMemberName (state : Compile.State) (qualified : Bool)
    (application : AppliedInterface) (member : String) : String :=
  let name := qualifiedName state.program application.1
  let args := application.2.toList.map (renderValueWith state qualified)
  let receiver := if args.isEmpty then name else s!"{name}<{", ".intercalate args}>"
  s!"{receiver}::{member}"

/-- The first two distinct applications declaring a member in a module header. -/
structure MemberConflict where
  member : String
  first : AppliedInterface × Path
  second : AppliedInterface × Path

/-- Two distinct declarations or static values can have the same fully qualified name.
In that case point to the two applications as the module author wrote them. -/
def MemberConflict.message (conflict : MemberConflict) (state : Compile.State)
    (moduleName : String) : String := Id.run do
  let ⟨member, (first, firstPath), (second, secondPath)⟩ := conflict
  let display qualified app := appliedMemberName state qualified app member
  let mut left := display false first
  let mut right := display false second
  if left == right then
    left := display true first
    right := display true second
  let origin (path : Path) :=
    let site := path.span
    let source := Layout.flatten (Printer.atoms (Printer.path path))
    s!" from `{source}` at {site.file}:{site.startLine}:{site.startColumn}"
  let (fromLeft, fromRight) :=
    if left == right then (origin firstPath, origin secondPath) else ("", "")
  return s!"module `{moduleName}` has two declarations of `{member}`: `{left}`{fromLeft} and `{right}`{fromRight}"

/-- The conditions of a directly named interface that apply to its implementing module. -/
def interfaceConstraints (state : Compile.State) (interface : DeclarationId) : Array Lowered.Constraint :=
  let scope := state.program.declarations[interface]?.bind (·.ownScope)
  ((scope.bind state.env.modules.loweredScope?).map (·.constraints)).getD #[]

/-- Bind each member once, recording the first conflict in header and declaration order.
An unresolved default can read a value defined in its suite even if a law also occupies its name. -/
def bindModuleMembers (written : Array (AppliedInterface × Path)) :
    CompileM (ModuleMemberBindings × Option MemberConflict) := do
  let state ← get
  let mut bindings : ModuleMemberBindings := {}
  let mut conflict : Option MemberConflict := none
  for h : index in [:written.size] do
    let (app, path) := written[index]
    let mut functions := 0
    let ids := ((← declaration app.1).inner.bind fun inner => state.members[inner]?).getD #[]
    for id in ids do
      let decl ← declaration id
      unless decl.node matches .member _ do continue
      if decl.kind == .functionMember then functions := functions + 1
      let name := state.program.nameOf id
      if let some prior := bindings.find? name then
        if conflict.isNone then
          conflict := some ⟨name, written[prior.application]!, (app, path)⟩
        unless (← declaration prior.declaration).kind == .lawMember && decl.kind != .lawMember do continue
      bindings := { bindings with
        entries := bindings.entries.push ⟨index, id⟩
        byName := bindings.byName.insert name bindings.entries.size }
    bindings := { bindings with functionCounts := bindings.functionCounts.push functions }
  return (bindings, conflict)

/-- Retain observations while forgetting the query results from a trial. Messages are
rendered against the environment in which they were issued. -/
def restoreObservations (saved checked : Compile.State) (reports : Bool := true) : CompileM (Exhaustion → Exhaustion) := do
  let renderer := checked.env.renderer
  let frame (f : ChainFrame) := { f with subject := .ofText (f.subject.renderWith renderer false) }
  let exhaustion (e : Exhaustion) := { e with request := frame e.request }
  let freezeEntries (prior after : DiagnosticLog) : DiagnosticLog := Id.run do
    let mut entries := prior.entries
    for d in after.entries[prior.entries.size...*] do
      entries := entries.push { d with
        message := .ofText (d.message.render renderer)
        chain := d.chain.map frame
        exhaustion := d.exhaustion.map exhaustion
        notes := d.notes.map fun note => { note with message := .ofText (note.message.render renderer) } }
    return {after with entries}
  let log := {checked.log with
    toDiagnosticLog := freezeEntries saved.log.toDiagnosticLog checked.log.toDiagnosticLog
    moduleDepthRetry := checked.log.moduleDepthRetry.map fun retry =>
      let prior := (saved.log.moduleDepthRetry.map (·.retained)).getD saved.log.toDiagnosticLog
      {retry with retained := freezeEntries prior retry.retained}}
  let mut traces := saved.traces
  for entry in checked.traces[saved.traces.size...*] do
    traces := traces.push { entry with message := .ofText (entry.message.render renderer) }
  set { saved with log, traces, staticSteps := checked.staticSteps }
  if reports then modifyResults fun results => { results with reports := checked.results.reports }
  return exhaustion

/-- A provisional receiver can be reached through signatures, bodies and generated views.
Commit their results together. On failure retain observations and the numbers of emitted definitions. -/
def withModuleConditions {α : Type} (check : CompileM α) : CompileM α := do
  let saved ← get
  let (outcome, checked) := check.run (← read) saved
  match outcome with
  | .ok value => set checked; return value
  | .error failure =>
    let freeze ← restoreObservations saved checked
    modifyResults (·.modifySignatures (·.reserveNewKeys checked.table))
    match failure with
    | .exhausted e => throw (.exhausted (freeze e))
    | other => throw other

/-- A preparation can offer a receiver to keep, or decline it after allocating signature keys.
Only a successful offer commits the checked state. All other preparations contribute their
key numbers to the enclosing search, without publishing a request, diagnostic or budget result. -/
def prepareModuleMembers (make : CompileM (Option InstanceContent)) : CompileM (Option InstanceContent) := do
  let saved ← get
  let (outcome, checked) := make.run (← read) saved
  match outcome with
  | .ok (some value) =>
    if checked.log.errors == saved.log.errors && checked.log.incomplete == saved.log.incomplete then
      set checked
      return some value
  | .error (.defect reason) => throw (.defect reason)
  | .error (.staticIndex name) => throw (.staticIndex name)
  | _ => pure ()
  modifyResults (·.modifySignatures (·.reserveNewKeys checked.table))
  return none

/-- Publish laws newly typed in a private checking state. Their identities and display
text were captured while that state's nominal references could still be resolved. -/
def publishValidationObligations (saved checked : Compile.State) : CompileM Unit := do
  let start := saved.results.obligations.size
  unless start == checked.results.obligations.size do
    modifyResults fun results => Id.run do
      let mut results := results
      for law in checked.results.obligations[start...*] do
        results := results.addObligation law
      return results

/-- A successful concrete check may reach declarations exclusively in its private table.
Keep those uses for default selection, including observations made in nested checks. -/
def publishDetachedObservations (saved checked : Compile.State)
    (reads : Array Compile.ModuleRead) : CompileM Unit := do
  let reached := checked.results.reachedDeclarations checked.validationDeclarations
    saved.table.requestedIds.size
  let detached := detachedModuleReads saved checked reads
  modify fun s => { s with validationDeclarations := reached, moduleReads := s.moduleReads ++ detached }
  publishValidationObligations saved checked

/-- Export a judgment and its observations without publishing any query derived from the
receiver. Module formation preserves its historical key allocations. Call-site preconditions
introduce new queries whose numbers must stay private to the judgment. -/
def checkIsolatedConditions (check : CompileM Unit) (reserveKeys : Bool := false) : CompileM Unit := do
  let saved ← get
  let (outcome, checked) := (captureModuleReads check).run (← read) saved
  let freeze ← restoreObservations saved checked
  if reserveKeys then modifyResults (·.modifySignatures (·.reserveNewKeys checked.table))
  match outcome with
  | .ok (_, reads) =>
    unless reserveKeys do publishDetachedObservations saved checked reads
  | .error (.exhausted e) => throw (.exhausted (freeze e))
  | .error failure => throw failure

/-- Resolve a concrete member through its bound owner. The opaque typing of SP12
reads the first declaration of the name from its ordered interfaces. -/
def declaredMember? (program : Program) (interfaces : ModuleInterfaces) (name : String) :
    Option (DeclarationId × DeclarationId × Declaration × Array StaticValue) := do
  let bound : Option (AppliedInterface × DeclarationId) := match interfaces with
    | .concrete apps members => do
      let member ← members.find? name
      pure (← apps[member.application]?, member.declaration)
    | .ordered applications => applications.findSome? fun app => do
      let inner ← program.declarations[app.1]?.bind (·.inner)
      let .declaration id ← program.namespaces[inner]?.bind (·.names[name]?) | none
      return (app, id)
  let (app, id) ← bound
  return (app.1, id, ← program.declarations[id]?, app.2)

end Zkc.Frontend.Static
