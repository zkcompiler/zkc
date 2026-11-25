module

public import Zkc.Frontend.Written.Selection
public import Zkc.Frontend.Driver.SourcePhases

@[expose] public section
namespace Zkc.Frontend.Written

/-- Settle previously recorded reads. A batch of directives can span several files, so the
diagnostic and its instantiation chain identify the failing read. -/
def checkSelectionReads (state : Compile.State) (reads : Array Compile.ModuleRead) :
    ExportM Compile.State := do
  let (outcome, after) := (Typing.checkModuleReads reads).run sourceContext state
  if let some diag := after.log.entries.find? (fun d => d.isError || d.isIncomplete) then
    refuse diag.span "WK-TYPE" (diag.render after.env.renderer)
  match outcome with
  | .ok () => return after
  | .error (.exhausted e) => refuse e.request.span "WK-TYPE" s!"not checked: {e.describe}"
  | .error why => throw s!"WK-TYPE: {Driver.describeInterrupt why}"

def sourceState (assembly : Assembly) (names : Driver.Phase := Driver.resolve) : ExportM Compile.State := do
  let mut state : Compile.State := {}
  for phase in Driver.sourcePhases assembly names do
    let (report, next) := phase.runIn sourceContext state
    state := next
    if let some diag := state.log.entries.find? (fun d => d.isError || d.isIncomplete) then
      throw s!"{diag.span.file}:{diag.render state.env.renderer}"
    if let some skipped := report.interrupted then throw s!"WK-FRONTEND: {skipped}"
  checkSelectionReads state state.directiveReads

/-- A resolved source for named goal requests. A goal's own name refusal follows the
declaration through selection, admission and subsequent reads of goals on the same root. -/
structure GoalSource where
  state : Compile.State
  refusals : Std.HashMap Names.Owner Diagnostic := {}

def resolveGoals (assembly : Assembly) : ExportM GoalSource := do
  let resolved := resolveProgram assembly
  let shared := resolved.refusalsByOwner.filter fun owner _ => match owner with
    | .declaration id => !(assembly.program.declarations[id]?).any (·.kind == .goal)
    | _ => true
  let names := { Driver.resolve with
    run := Driver.installResolution { resolved with refusalsByOwner := shared } }
  return ⟨← sourceState assembly names, resolved.refusalsByOwner⟩

def GoalSource.selectId (source : GoalSource) (id : DeclarationId) (kind : GoalKind) :
    ExportM (Selection × GoalSource) := do
  if let some why := source.refusals[Names.Owner.declaration id]? then
    throw s!"{why.span.file}:{why.render source.state.env.renderer}"
  let (selected, closed) ← selectGoalId source.state id kind
  return (selected, {source with state := closed})

def GoalSource.selectNamed (source : GoalSource) (name : String) (kind : GoalKind) :
    ExportM (Selection × GoalSource) := do
  let (id, _) ← selectDeclaration source.state .goal name "WK-GOAL"
  source.selectId id kind

structure AdmittedRoot where
  id : InstanceId
  state : Compile.State
  emission : Emit.RootEmission
  emitted : Typing.emitRoot state id = .ok emission
  evidence : (emission.package ⟨[],[],[],[],[]⟩).Admission
  goalRefusals : Std.HashMap Names.Owner Diagnostic := {}

def AdmittedRoot.goalSource (root : AdmittedRoot) : GoalSource :=
  ⟨root.state, root.goalRefusals⟩

private def admitFromReads (source : GoalSource) (reads : Array Compile.ModuleRead)
    (id : InstanceId) (place : Syntax.Span) : ExportM AdmittedRoot := do
  let checked ← checkSelectionReads source.state reads
  let (_, s) ← evaluate checked place do
    Static.observeApplication id place
    useQueryReads ⟨.signature, id⟩
    Typing.typeBody id place
  if let some diag := s.log.entries.find? (fun d => d.isError || d.isIncomplete) then
    throw s!"{diag.span.file}:{diag.render s.env.renderer}"
  match emitted : Typing.emitRoot s id with
  | .error (.exhausted exhaustion) => refuse place "WK-CORE" s!"not checked: {exhaustion.describe}"
  | .error _ => refuse place "WK-CORE" "protocol did not emit"
  | .ok emission =>
    let .ok evidence := (emission.package ⟨[],[],[],[],[]⟩).checkEvidence
      | refuse place "WK-CORE" "admission refused the emitted program"
    return { id, state := s, emission, emitted, evidence, goalRefusals := source.refusals }

/-- A scheme selects its own source dependencies even if a sibling closes to the same protocol. -/
@[no_expose] def GoalSource.admitScheme (source : GoalSource) (scheme : SchemeEntry) : ExportM AdmittedRoot :=
  admitFromReads source (source.state.schemeReads.getD scheme.declaration #[]) scheme.protocol scheme.span

/-- A caller selecting an instance number consumes all recorded selections of that root.
Named goals have their own scheme selection and settle only its reads. -/
@[no_expose] def admitInstance (state : Compile.State) (id : InstanceId) (place : Syntax.Span) :
    ExportM AdmittedRoot :=
  admitFromReads {state} (state.rootSelectionReads.getD id #[]) id place

/-- Compile an assembly with one protocol root and retain the source state that produced
the admitted term for subsequent clause lookup. -/
def admitSource (assembly : Assembly) : ExportM AdmittedRoot := do
  let state ← sourceState assembly
  let #[id] := state.roots | throw "expected one source protocol root"
  let place := ((state.table.entryAt? id).map (·.requested.span)).getD default
  admitInstance state id place

end Zkc.Frontend.Written
