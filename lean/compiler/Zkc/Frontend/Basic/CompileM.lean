module

public import Zkc.Frontend.Basic.Log
public import Zkc.Frontend.Basic.Options
public import Zkc.Frontend.Environment.Basic
public import Zkc.Frontend.Semantics.Vocabulary

@[expose] public section

set_option autoImplicit false

/-!
# The bottom layer

`CompileM` is the monad under every phase. Its context is what a run is given and does not
change: the options and the vocabulary. Its state is what a run accumulates: the environment,
the log of diagnostics, the requests being computed, and the traces. Every other layer is a
reader and a state over it, with the state of one item of its phase; that state is made fresh
for each item and dropped after it.

A diagnostic is logged, here, when it is made. An exception carries no message: it only
abandons the item being computed, up to the nearest place that recovers. The state of this layer
is under the exception, so what was logged and what was added to the environment before an item
was abandoned stays; the state of a layer above is over it, so the half-made state of the
abandoned item is dropped with it.

The library reads no file. The files of a program are loaded before this monad runs, by a
function that is generic in the monad of the loader.

`request` is the one way to ask for something that depends on static values. It looks the key
up in the table of its kind, computes it when it is new, records the request with the request
being computed, and refuses a request that reaches itself. A request made deeper than the budget
of the chain of instantiations is not computed: it is exhausted, an incomplete check that
refuses nothing (SP10), and so is every request that was computing when it ran out.
-/

namespace Zkc.Frontend

open Syntax

/-- Why the computation of an item ends early. -/
inductive Interrupt where
  /-- An error was logged and the item cannot go on. -/
  | abandoned
  /-- The item needs a form of a layer that is not elaborated yet: it waits. -/
  | waiting (reason : String)
  /-- A default instance whose `where` does not hold: it is skipped (SP7). -/
  | skipped
  /-- A budget of the compiler ran out: the item is not checked to the end, and is not refused
  (SP10). The incomplete check is logged where the budget ran out. -/
  | exhausted (exhaustion : Exhaustion)
  /-- The index of a loop typed once stands as the position of a tuple: the loop is typed per
  iteration (TY10). The loop that binds the index, named here, takes this up. -/
  | staticIndex (name : String)
  /-- A defect of the frontend. -/
  | defect (message : String)
  deriving Inhabited

namespace Compile

structure Context where
  options : Options := {}
  vocabulary : Vocabulary
  deriving Inhabited

/-- What is being computed: a request, or a part of a computation that a chain names on its own
(the opaque typing of a definition, the check of a type of the vocabulary against a sort). -/
inductive StackEntry where
  | request (reference : QueryRef)
  | frame (frame : ChainFrame)
  deriving Inhabited

/-- A line of a trace: the class it belongs to and what it says. -/
structure TraceEntry where
  traceClass : String
  message : Message
  deriving Inhabited

structure State where
  env : Environment := {}
  log : Log := {}
  /-- What is being computed, outermost first. -/
  stack : Array StackEntry := #[]
  traces : Array TraceEntry := #[]
  /-- The steps spent so far by the outermost static term being evaluated, and how many
  evaluations of static terms are under way (TY2). -/
  staticSteps : Nat := 0
  staticDepth : Nat := 0
  deriving Inhabited

end Compile

abbrev CompileM := ReaderT Compile.Context (ExceptT Interrupt (StateM Compile.State))

instance {α : Type} : Inhabited (CompileM α) := ⟨throw .abandoned⟩

namespace CompileM

/-- Runs an action from a state: its value or the interrupt that ended it, and the state it
left, which holds everything logged either way. -/
def run {α : Type} (action : CompileM α) (context : Compile.Context) (state : Compile.State) :
    Except Interrupt α × Compile.State :=
  Id.run (StateT.run (ExceptT.run (ReaderT.run action context)) state)

end CompileM

/-! ## The environment -/

def getEnv : CompileM Environment := return (← get).env

/-- Changes the environment in place: it is taken out of the state before it is changed. -/
def modifyEnv (change : Environment → Environment) : CompileM Unit :=
  modify fun state =>
    let env := state.env
    let state := { state with env := {} }
    { state with env := change env }

def getResults : CompileM ResultStore := return (← get).env.results

/-- Changes the store of results in place, with a value: it is taken out of the state first. -/
def modifyGetResults {α : Type} (change : ResultStore → α × ResultStore) : CompileM α :=
  modifyGet fun state =>
    let env := state.env
    let state := { state with env := {} }
    let results := env.results
    let env := { env with results := {} }
    let (value, results) := change results
    (value, { state with env := { env with results } })

/-- Changes the store of results in place: it is taken out of the environment first. -/
def modifyResults (change : ResultStore → ResultStore) : CompileM Unit :=
  modifyEnv fun environment =>
    let results := environment.results
    let environment := { environment with results := {} }
    { environment with results := change results }

def getModules : CompileM ModuleStore := return (← get).env.modules

def modifyModules (change : ModuleStore → ModuleStore) : CompileM Unit :=
  modifyEnv fun environment =>
    let modules := environment.modules
    let environment := { environment with modules := {} }
    { environment with modules := change modules }

def getOptions : CompileM Options := return (← read).options

def getVocabulary : CompileM Vocabulary := return (← read).vocabulary

namespace Compile.State

def program (state : State) : Program := state.env.modules.program

def results (state : State) : ResultStore := state.env.results

def modules (state : State) : ModuleStore := state.env.modules

end Compile.State

/-! ## Diagnostics -/

/-- The line of a chain for an entry of the stack: what a request asked for and the place it was
first asked from, or the frame itself. -/
def Compile.State.frameOf (state : Compile.State) : StackEntry → Option ChainFrame
  | .request reference => state.env.results.requested? reference
  | .frame frame => some frame

/-- The chain of what is being computed, innermost first: one line per entry of the stack (SP7). -/
def Compile.State.chain (state : Compile.State) : Array ChainFrame :=
  state.stack.reverse.filterMap state.frameOf

def currentChain : CompileM (Array ChainFrame) := return (← get).chain

/-- The request being computed, innermost. -/
def currentRequest? : CompileM (Option QueryRef) := do
  return (← get).stack.reverse.findSome? fun
    | .request reference => some reference
    | .frame _ => none

/-- Runs the computation of a request with the request on the stack. -/
def withRequest {α : Type} (reference : QueryRef) (action : CompileM α) : CompileM α := do
  modify fun state => { state with stack := state.stack.push (.request reference) }
  try
    let result ← action
    modify fun state => { state with stack := state.stack.pop }
    return result
  catch interrupt =>
    modify fun state => { state with stack := state.stack.pop }
    throw interrupt

/-- Runs an action with a line of its own on the chain: a part of a computation that is no
request. -/
def withChainFrame {α : Type} (frame : ChainFrame) (action : CompileM α) : CompileM α := do
  modify fun state => { state with stack := state.stack.push (.frame frame) }
  try
    let result ← action
    modify fun state => { state with stack := state.stack.pop }
    return result
  catch interrupt =>
    modify fun state => { state with stack := state.stack.pop }
    throw interrupt

/-- Logs a diagnostic with the current chain. -/
def logAt (severity : Severity) (origin : DiagnosticOrigin) (rule : String) (span : Span)
    (message : Message) (notes : Array Note := #[]) : CompileM Unit := do
  let chain ← currentChain
  modify fun state =>
    { state with log := state.log.add { severity, origin, rule, span, message, chain, notes } }

/-- Logs an error and goes on. -/
def logError (rule : String) (span : Span) (message : Message)
    (origin : DiagnosticOrigin := .elaboration) (notes : Array Note := #[]) : CompileM Unit :=
  logAt .error origin rule span message notes

/-- Logs an error and abandons the item being computed. -/
def throwError {α : Type} (rule : String) (span : Span) (message : Message)
    (origin : DiagnosticOrigin := .elaboration) (notes : Array Note := #[]) : CompileM α := do
  logError rule span message origin notes
  throw .abandoned

/-- The item waits for a form of a later layer. -/
def waitFor {α : Type} (reason : String) : CompileM α := throw (.waiting reason)

/-- Logs that a budget ran out when something was asked for: an incomplete check, with the
budget, its value and the request, at the place of the request. -/
def logExhaustion (budget : Budget) (requested : ChainFrame) : CompileM Exhaustion := do
  let limit := (← read).options.budgets.limit budget
  let exhaustion : Exhaustion := { budget, limit, request := requested }
  let subject := requested.subject.renderWith Renderer.plain false
  let chain ← currentChain
  let diagnostic : Diagnostic :=
    { severity := .incomplete, origin := .instances, rule := budget.rule
      span := requested.span, chain, exhaustion := some exhaustion
      message := .ofText s!"`{subject}` is not checked: {budget.describe} reaches its budget of {limit}; the check is incomplete, and refuses nothing" }
  modify fun state => { state with log := state.log.add diagnostic }
  return exhaustion

/-- Whether a request made now is deeper than the budget of the chain of instantiations. -/
def beyondDepth : CompileM Bool :=
  return (← read).options.budgets.instantiationDepth ≤ (← get).stack.size

/-- The number of errors logged so far: a mark to compare with later. -/
def errorMark : CompileM Nat := return (← get).log.errors

/-- Whether an error was logged since a mark. -/
def hasErrorsSince (mark : Nat) : CompileM Bool := return (← get).log.hasErrorsSince mark

/-- Runs an action; when it ends because a refusal was logged (`abandoned`), or, where the
caller says so, because a default instance is skipped (`skipped`) or because it waits for a
later layer (`waits`), runs `fallback` with what ended it. Everything else goes on: a budget that
ran out, a defect of the frontend, a static index in a static position, and a skip or a wait the
caller did not ask for. None of them is a refusal. -/
def recoverWith {m : Type → Type} {α : Type} [Monad m] [MonadExceptOf Interrupt m]
    (action : m α) (fallback : Interrupt → m α) (skipped waits : Bool := false) : m α :=
  tryCatchThe Interrupt action fun interrupt =>
    match interrupt with
    | .abandoned => fallback interrupt
    | .skipped => if skipped then fallback interrupt else throwThe Interrupt interrupt
    | .waiting _ => if waits then fallback interrupt else throwThe Interrupt interrupt
    | .exhausted _ | .defect _ | .staticIndex _ => throwThe Interrupt interrupt

/-- `recoverWith` with a fallback that does not read what ended the action. -/
def recover {m : Type → Type} {α : Type} [Monad m] [MonadExceptOf Interrupt m]
    (action fallback : m α) (skipped waits : Bool := false) : m α :=
  recoverWith action (fun _ => fallback) skipped waits

/-- Ends an item of a phase and goes on to the next, once what ended it is recorded: a refusal
and a budget that ran out are logged where they happen; a skipped default instance and a wait
are the item's own state. A defect of the frontend, and a static index that no loop took up,
are logged here as errors, so that none ends an item silently. -/
def endItem (action : CompileM Unit) : CompileM Unit :=
  tryCatchThe Interrupt action fun interrupt =>
    match interrupt with
    | .abandoned | .skipped | .waiting _ | .exhausted _ => pure ()
    | .defect message =>
      logError "defect" default (.ofText s!"a defect of the frontend: {message}") (origin := .instances)
    | .staticIndex name =>
      logError "defect" default
        (.ofText s!"a defect of the frontend: the index `{name}` in a static position, outside its loop")
        (origin := .instances)

/-! ## Traces -/

/-- Adds a line to the trace of a class when the class is on. The message is built only
then. -/
def trace (traceClass : String) (message : Unit → Message) : CompileM Unit := do
  if (← read).options.traces? traceClass then
    modify fun state =>
      { state with traces := state.traces.push { traceClass, message := message () } }

/-! ## Requests -/

/-- A kind of request: its table in the store of results, the instance a key is about, and how
a new entry is computed. `compute` is given the number of the entry and its key. -/
structure Query (κ ρ : Type) [BEq κ] [Hashable κ] where
  kind : QueryKind
  table : ResultStore → QueryTable κ ρ
  setTable : ResultStore → QueryTable κ ρ → ResultStore
  /-- The instance that the entry with a number and a key is about. -/
  instanceOf : Nat → κ → Nat
  compute : Nat → κ → CompileM ρ

section Request

variable {κ ρ : Type} [BEq κ] [Hashable κ]

/-- Asks for a key and returns the number of its entry and the state it is in afterwards. A
new key is entered as in progress and computed with the request on the stack; when the
computation is abandoned or waits, the entry says so and the interrupt stops here. The request
is recorded with the request being computed, whatever its state. -/
@[inline] def request (query : Query κ ρ) (key : κ) (requested : ChainFrame) :
    CompileM (Nat × QueryState ρ) := do
  let requester ← currentRequest?
  let depth := (← get).stack.size
  -- the key is entered, and the request recorded with the request that makes it; the table is
  -- taken out of the store while it changes, so that it changes in place
  let (id, isNew) ← modifyGetResults fun results =>
    let table := query.table results
    let results := query.setTable results {}
    let (table, id, isNew) := table.intern key requested requester
    let results := query.setTable results table
    let reference : QueryRef := ⟨query.kind, query.instanceOf id key⟩
    let results := match requester with
      | some requester => results.addRequest requester reference
      | none => results
    ((id, isNew), results)
  let reference : QueryRef := ⟨query.kind, query.instanceOf id key⟩
  let setState (outcome : QueryState ρ) : CompileM Unit :=
    modifyResults fun results =>
      let table := query.table results
      let results := query.setTable results {}
      query.setTable results (table.setState id outcome)
  unless isNew do
    let found := ((query.table (← getResults)).entries[id]?).map (·.state)
    return (id, found.getD .failed)
  if (← read).options.budgets.instantiationDepth ≤ depth then
    let exhaustion ← logExhaustion .instantiationDepth requested
    setState (.exhausted exhaustion)
    return (id, .exhausted exhaustion)
  modify fun state => { state with stack := state.stack.push (.request reference) }
  let finish (outcome : QueryState ρ) : CompileM (Nat × QueryState ρ) := do
    modify fun state => { state with stack := state.stack.pop }
    setState outcome
    return (id, outcome)
  tryCatch (do finish (.done (← query.compute id key))) fun
    | .abandoned => finish .failed
    | .waiting reason => finish (.waiting reason)
    | .exhausted exhaustion => finish (.exhausted exhaustion)
    | other => do
      let _ ← finish .failed
      throw other

/-- Refuses a request that reaches itself (NL1): the lines of the chain from the first that is
the description of what was asked, and that description. -/
def refuseRecursion {α : Type} (description : String) (span : Span) : CompileM α := do
  let text (frame : ChainFrame) : String := frame.subject.renderWith Renderer.plain false
  let lines := ((← get).chain.reverse).map text
  let start := (lines.findIdx? (· == description)).getD lines.size
  let through := (lines.extract (start + 1) lines.size).push description
  throwError "NL1" span
    (.ofText s!"`{description}` refers to itself through {" → ".intercalate (through.toList.map (s!"`{·}`"))}; a definition cannot be recursive")
    (origin := .instances)

/-- Asks for a key and returns the number of its entry and its result. A request that is in
progress reaches itself: it is refused with the requests it went through (NL1). A request that
failed abandons the item that asks, without a diagnostic of its own; one that waits makes the
item wait; one that is exhausted leaves the item that asks not checked either. -/
@[inline] def ask (query : Query κ ρ) (key : κ) (requested : ChainFrame) : CompileM (Nat × ρ) := do
  match ← request query key requested with
  | (id, .done result) => return (id, result)
  | (_, .inProgress) =>
    refuseRecursion (requested.subject.renderWith Renderer.plain false) requested.span
  | (_, .failed) => throw .abandoned
  | (_, .skipped) => throw .skipped
  | (_, .waiting reason) => throw (.waiting reason)
  | (_, .exhausted exhaustion) => throw (.exhausted exhaustion)

end Request

end Zkc.Frontend
