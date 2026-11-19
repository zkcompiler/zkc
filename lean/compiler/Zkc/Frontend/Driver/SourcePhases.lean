module

public import Zkc.Frontend.Names.Module
public import Zkc.Frontend.Semantics.Instances
public import Zkc.Frontend.Driver.Bodies

@[expose] public section

set_option autoImplicit false

/-!
# Source phases

Assembly, name resolution and signature instantiation share a phase runner with the later
checks of bodies, root packages and schemes. The instance phase records the roots and their
closed signatures, including roots selected by a source scheme.
-/

namespace Zkc.Frontend.Driver

/-- A part of the environment. -/
inductive Component where
  /-- The sources of the program, parsed. -/
  | sources
  /-- The records of the files and the tables of the program. -/
  | files
  /-- The lowered declarations and the tables of resolutions. -/
  | lowered
  | signatures
  | bodies
  | checked
  | package
  deriving Inhabited, BEq, Repr

structure Phase where
  name : String
  reads : Array Component
  writes : Array Component
  run : CompileM Unit
  deriving Inhabited

/-- What running a phase left besides the state. -/
structure PhaseReport where
  name : String
  /-- The duration by the caller's clock, in its unit; 0 when no clock was given. -/
  duration : Nat := 0
  /-- The errors logged by the phase. -/
  errors : Nat := 0
  /-- The diagnostics of every severity logged by the phase. -/
  diagnostics : Nat := 0
  /-- The place in the log of the first diagnostic of the phase. -/
  firstDiagnostic : Nat := 0
  /-- The interrupt that ended the phase, when one did. -/
  interrupted : Option String := none
  /-- The lines of the traces that were on. -/
  traces : Array Compile.TraceEntry := #[]
  deriving Inhabited

def describeInterrupt : Interrupt → String
  | .abandoned => "abandoned after an error"
  | .waiting reason => s!"waiting: {reason}"
  | .skipped => "skipped"
  | .exhausted exhaustion => s!"not checked: {exhaustion.budget.describe} reaches its budget of {exhaustion.limit}"
  | .staticIndex binder => s!"a static index outside its loop (binder {binder})"
  | .defect message => s!"defect: {message}"

namespace Phase

/-- Runs a phase from a state. The traces of the phase are moved into its report. -/
def runIn (phase : Phase) (context : Compile.Context) (state : Compile.State) :
    PhaseReport × Compile.State :=
  let (outcome, after) := phase.run.run (Typing.withProtocolBodies context) { state with traces := #[] }
  let interrupted := match outcome with
    | .ok _ => none
    | .error interrupt => some (describeInterrupt interrupt)
  ({ name := phase.name
     errors := after.log.errors - state.log.errors
     diagnostics := after.log.entries.size - state.log.entries.size
     firstDiagnostic := state.log.entries.size
     interrupted, traces := after.traces },
   { after with traces := state.traces, stack := #[] })

/-- Runs a phase between two readings of a clock. -/
def runTimed {m : Type → Type} [Monad m] (clock : m Nat) (phase : Phase)
    (context : Compile.Context) (state : Compile.State) : m (PhaseReport × Compile.State) := do
  let start ← clock
  let (report, after) := phase.runIn context state
  let stop ← clock
  return ({ report with duration := stop - start }, after)

end Phase

/-- The program, as loading assembled it, enters the store of files, with the diagnostics of
assembly. -/
def assemble (assembly : Assembly) : Phase where
  name := "assemble"
  reads := #[.sources]
  writes := #[.files]
  run := do
    modifyModules fun _ => ModuleStore.ofProgram assembly.program {} assembly.unreadable #[]
    modify fun state =>
      { state with log := assembly.log.entries.foldl (init := state.log) fun log entry => log.add entry }

/-- Every written name of the program is resolved and lowered in one walk: the lowered form of
every declaration, scope, `use` and comment `// instantiate:`, the table of resolutions of each
file read off it, and the first refusal of each declaration. Two nodes of the lowered form that
say different things at one place are a defect. -/
def resolve : Phase where
  name := "names"
  reads := #[.files]
  writes := #[.lowered]
  run := do
    let modules ← getModules
    let resolved := resolveProgram { program := modules.program, log := {}, unreadable := modules.unreadable }
    modifyModules fun _ => (ModuleStore.ofProgram modules.program resolved.resolutions
      modules.unreadable resolved.instantiations).withLowered resolved.lowered resolved.loweredScopes
      resolved.loweredUses resolved.loweredInstantiations
    modify fun state =>
      { state with log := resolved.refusals.foldl (init := state.log) fun log entry => log.add entry }
    unless resolved.conflicts.isEmpty do
      let places := (resolved.conflicts.toList.take 5).map fun (file, byte) => s!"{file}@{byte}"
      logError "defect" default (.ofText
        s!"a defect of the frontend: the lowered form says two things at {resolved.conflicts.size} places: {", ".intercalate places}")
        (origin := .names)

/-- A refusal is always reported. An instance whose signature or body is refused has a
diagnostic in the log; when the log has no error and an instance is refused all the same, the
frontend dropped a part of the program without saying so. That is a defect of the frontend, and
it is logged as one, so that such a program is not accepted. -/
def reportSilentRefusals : CompileM Unit := do
  let state ← get
  if state.log.errors != 0 then return
  let mut silent : Array String := #[]
  for index in [0:state.table.entries.size] do
    let entry := state.table.entries[index]!
    let refused := match entry.state, state.results.body? index with
      | .failed, _ | _, some .failed => true
      | _, _ => false
    if refused then
      silent := silent.push (← Static.describeInstance entry.key.declaration entry.key.arguments
        entry.key.specification entry.key.owner)
  unless silent.isEmpty do
    logError "defect" default (.ofText
      s!"a defect of the frontend: {silent.size} instances are refused and no refusal is reported: {", ".intercalate ((silent.toList.take 5).map (s!"`{·}`"))}")
      (origin := .instances)

/-- The checks of declarations, the roots and their instances, and the instances that comments
ask for. -/
def instances : Phase where
  name := "instances"
  reads := #[.lowered]
  writes := #[.signatures]
  run := do
    Instances.instantiateProgram
    reportSilentRefusals

/-- The shared prefix through selection of roots and instantiation of their signatures. -/
def sourcePhases (assembly : Assembly) : Array Phase := #[assemble assembly, resolve, instances]

end Zkc.Frontend.Driver
