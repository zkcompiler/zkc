import Std

/-! Dead discardable local storage can be erased without changing logical execution.

This finite named local language has opaque effectful kernels, ordered reads and
multi-result definitions, and a final return. Physical bindings are separate from
logical state and a ghost ledger of all successfully retained local bindings.
Release changes only the physical map: no tick, event, kernel or logical refund.

This is a local semantic law, not admission or native-code correctness. Values
are mathematical immutable discardable values; resources and observable destruction
are outside this model. Native realization additionally needs allocation success
(or matched allocator outcomes), inert Drop, and kernels unable to observe map
ownership, addresses or Arc reference counts. Native OOM is not equated.
-/

set_option autoImplicit false

namespace Zkc.Compiler.Storage

variable {Name Value Op State Event Error : Type}

abbrev Environment (Name Value : Type) := Name → Option Value

/-- Exact errors include missing reads, output arity, and opaque backend/policy errors. -/
inductive Fault (Name Error : Type) where
  | missing (name : Name)
  | arity
  | external (error : Error)
  deriving DecidableEq, Repr

/-- Failure retains the final state and the full ordered observation prefix. -/
structure Execution (State Event Error Value : Type) where
  outcome : Except Error Value
  state : State
  events : List Event
  deriving Repr

def Execution.pure (value : Value) (state : State) : Execution State Event Error Value :=
  ⟨.ok value, state, []⟩

def Execution.fail (error : Error) (state : State) : Execution State Event Error Value :=
  ⟨.error error, state, []⟩

def Execution.bind {Next : Type} (first : Execution State Event Error Value)
    (next : Value → State → Execution State Event Error Next) : Execution State Event Error Next :=
  match first.outcome with
  | .error error => ⟨.error error, first.state, first.events⟩
  | .ok value =>
      let tail := next value first.state
      ⟨tail.outcome, tail.state, first.events ++ tail.events⟩

/-- Counts original retained bindings, including aliases and physically erased entries. -/
structure Charges where
  count : Nat := 0
  bytes : Nat := 0
  deriving DecidableEq, Repr

structure LogicalState (State : Type) where
  core : State
  ghost : Charges := {}
  deriving Repr

/-- The policy sees logical state, never the physical environment. `core` must
carry every logical counter, backend state, failure detail and policy input.
`kernel` includes input validation. After the explicit result-arity check,
`retain` receives the operation for output validation and batch charging. A failed
retain adds no local ghost charge. `Op` can carry sites, attributes and signatures.
`leave` refunds the entire ghost ledger on both success and failure. Its native
adequacy, like that of the other callbacks, is a separate bridge obligation. -/
structure Semantics (Name Value Op State Event Error : Type) where
  tick : State → Execution State Event (Fault Name Error) Unit
  kernel : Op → List Value → State → Execution State Event (Fault Name Error) (List Value)
  retain : Op → List Value → State → Execution State Event (Fault Name Error) Unit
  bytes : Value → Nat
  leave : Charges → State → State

inductive Instruction (Name Op : Type) where
  | kernel (op : Op) (inputs outputs : List Name)
  | release (names : List Name)
  deriving DecidableEq, Repr

variable [DecidableEq Name]

def erase (env : Environment Name Value) (names : List Name) : Environment Name Value :=
  fun name => if name ∈ names then none else env name

def write (env : Environment Name Value) (name : Name) (value : Value) : Environment Name Value :=
  fun query => if query = name then some value else env query

def bindValues (env : Environment Name Value) : List Name → List Value → Environment Name Value
  | name :: names, value :: values => bindValues (write env name value) names values
  | _, _ => env

def read (env : Environment Name Value) : List Name → Except (Fault Name Error) (List Value)
  | [] => .ok []
  | name :: names => do
      match env name with
      | none => .error (.missing name)
      | some value => return value :: (← read env names)

/-- Agreement includes absence; hence missing-read failures are preserved too. -/
def Agree (names : List Name) (left right : Environment Name Value) : Prop :=
  ∀ name, name ∈ names → left name = right name

@[simp] theorem erase_lookup_of_not_mem (env : Environment Name Value)
    (names : List Name) (name : Name) (dead : name ∉ names) :
    erase env names name = env name := by simp [erase, dead]

@[simp] theorem erase_lookup_of_mem (env : Environment Name Value)
    (names : List Name) (name : Name) (member : name ∈ names) :
    erase env names name = none := by simp [erase, member]

theorem agree_erase (needed names : List Name) (left right : Environment Name Value)
    (agree : Agree needed left right) (dead : ∀ name ∈ names, name ∉ needed) :
    Agree needed (erase left names) right := by
  intro name member
  have absent : name ∉ names := fun present => dead name present member
  rw [erase_lookup_of_not_mem _ _ _ absent]
  exact agree name member

omit [DecidableEq Name] in
theorem read_eq (names : List Name) (left right : Environment Name Value)
    (agree : Agree names left right) :
    read (Error := Error) left names = read right names := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      have head := agree name (by simp)
      have tail := ih (fun n hn => agree n (by simp [hn]))
      simp only [read, head, tail]

/-- Definitions kill old needs only after their inputs have been read. -/
theorem bindValues_agree (needed names : List Name) (values : List Value)
    (left right : Environment Name Value) (arity : names.length = values.length)
    (agree : Agree (needed.filter fun name => name ∉ names) left right) :
    Agree needed (bindValues left names values) (bindValues right names values) := by
  induction names generalizing values left right with
  | nil =>
      cases values with
      | nil =>
          intro name member
          exact agree name (by simp [member])
      | cons value values => simp at arity
  | cons name names ih =>
      cases values with
      | nil => simp at arity
      | cons value values =>
          apply ih values (write left name value) (write right name value) (by simpa using arity)
          intro query member
          by_cases equal : query = name
          · simp [write, equal]
          · have neededMember : query ∈ needed := (List.mem_filter.mp member).1
            have absent : query ∉ names := by simpa using (List.mem_filter.mp member).2
            have old := agree query (by simp [neededMember, equal, absent])
            simpa [write, equal] using old

/-- Backward liveness for the ordered program and its actual return operands.
Release does not remove a need. Later definitions remove only the old binding's
need, so this also handles ordered redefinition (native SSA admission is stricter). -/
def needed : List (Instruction Name Op) → List Name → List Name
  | [], returns => returns
  | .kernel _ inputs outputs :: rest, returns =>
      inputs ++ (needed rest returns).filter (fun name => name ∉ outputs)
  | .release _ :: rest, returns => needed rest returns

/-- Semantic release safety; availability, discardable types, unique SSA definitions,
and release shape are additional admission obligations for a native adapter. -/
def Safe : List (Instruction Name Op) → List Name → Prop
  | [], _ => True
  | .kernel _ _ _ :: rest, returns => Safe rest returns
  | .release names :: rest, returns =>
      (∀ name ∈ names, name ∉ needed rest returns) ∧ Safe rest returns

def eraseReleases : List (Instruction Name Op) → List (Instruction Name Op)
  | [] => []
  | .kernel op inputs outputs :: rest => .kernel op inputs outputs :: eraseReleases rest
  | .release _ :: rest => eraseReleases rest

@[simp] theorem needed_eraseReleases (code : List (Instruction Name Op)) (returns : List Name) :
    needed (eraseReleases code) returns = needed code returns := by
  induction code with
  | nil => rfl
  | cons instruction rest ih => cases instruction <;> simp [eraseReleases, needed, ih]

/-- Lift an effect while preserving the independent local ledger on every result. -/
def lift (effect : State → Execution State Event Error Value)
    (state : LogicalState State) : Execution (LogicalState State) Event Error Value :=
  let result := effect state.core
  ⟨result.outcome, ⟨result.state, state.ghost⟩, result.events⟩

def retain (semantics : Semantics Name Value Op State Event Error) (op : Op) (values : List Value)
    (state : LogicalState State) :
    Execution (LogicalState State) Event (Fault Name Error) Unit :=
  (lift (semantics.retain op values) state).bind fun _ next =>
    .pure () { next with ghost :=
      ⟨next.ghost.count + values.length, next.ghost.bytes + (values.map semantics.bytes).sum⟩ }

omit [DecidableEq Name] in
/-- Failed validation/retention preserves the ghost ledger even if the callback
mutates its logical core or emits observations before failing. -/
theorem retain_failure_ghost (semantics : Semantics Name Value Op State Event Error)
    (op : Op) (values : List Value) (state : LogicalState State) (error : Fault Name Error)
    (failed : (semantics.retain op values state.core).outcome = .error error) :
    (retain semantics op values state).state.ghost = state.ghost := by
  simp [retain, lift, Execution.bind, failed]

omit [DecidableEq Name] in
/-- Every successful batch is charged once per binding, including equal values;
this ledger contains no references keeping physical backing alive. -/
theorem retain_success_ghost (semantics : Semantics Name Value Op State Event Error)
    (op : Op) (values : List Value) (state : LogicalState State)
    (success : (semantics.retain op values state.core).outcome = .ok ()) :
    (retain semantics op values state).state.ghost =
      ⟨state.ghost.count + values.length, state.ghost.bytes + (values.map semantics.bytes).sum⟩ := by
  simp [retain, lift, Execution.bind, Execution.pure, success]

/-- A real evaluator. Every kernel and the return tick; release merely erases.
Kernel/retention failures preserve their post-state/events and suppress the suffix. -/
def run (semantics : Semantics Name Value Op State Event Error) :
    List (Instruction Name Op) → List Name → Environment Name Value → LogicalState State →
    Execution (LogicalState State) Event (Fault Name Error) (List Value)
  | [], returns, env, state =>
      (lift semantics.tick state).bind fun _ next => ⟨read env returns, next, []⟩
  | .release names :: rest, returns, env, state =>
      run semantics rest returns (erase env names) state
  | .kernel op inputs outputs :: rest, returns, env, state =>
      (lift semantics.tick state).bind fun _ next =>
        match read env inputs with
        | .error error => .fail error next
        | .ok arguments =>
            (lift (semantics.kernel op arguments) next).bind fun values afterKernel =>
              if outputs.length = values.length then
                (retain semantics op values afterKernel).bind fun _ afterRetain =>
                  run semantics rest returns (bindValues env outputs values) afterRetain
              else .fail .arity afterKernel

/-- Core storage law: environments need agree only where the ordered body reads
before definition. The conclusion is equality of returned outputs OR exact errors,
full final logical state (including the ghost ledger), and all kernel/policy events.
There is no premise assuming equality of evaluator executions or kernel purity. -/
theorem run_eraseReleases (semantics : Semantics Name Value Op State Event Error)
    (code : List (Instruction Name Op)) (returns : List Name)
    (safe : Safe code returns) (left right : Environment Name Value)
    (agree : Agree (needed code returns) left right) (state : LogicalState State) :
    run semantics code returns left state =
      run semantics (eraseReleases code) returns right state := by
  induction code generalizing left right state with
  | nil =>
      simp only [run, eraseReleases]
      have reads := read_eq (Error := Error) returns left right agree
      simp only [reads]
  | cons instruction rest ih =>
      cases instruction with
      | release names =>
          exact ih safe.2 (erase left names) right
            (agree_erase _ _ _ _ agree safe.1) state
      | kernel op inputs outputs =>
          have inputsAgree : Agree inputs left right := by
            intro name member
            exact agree name (List.mem_append_left _ member)
          have suffixAgree : Agree ((needed rest returns).filter fun name => name ∉ outputs)
              left right := by
            intro name member
            exact agree name (List.mem_append_right _ member)
          simp only [run, eraseReleases, read_eq inputs left right inputsAgree]
          congr 1
          funext ignored next
          cases read (Error := Error) right inputs with
          | error error => rfl
          | ok arguments =>
              dsimp only
              congr 1
              funext values afterKernel
              split
              · rename_i arity
                congr 1
                funext ignored afterRetain
                exact ih safe _ _ (bindValues_agree _ _ _ _ _ arity suffixAgree) afterRetain
              · rfl

/-- Scope exit refunds the original local ledger, even after a failed execution.
The physical environment is deliberately unavailable to the cleanup policy. -/
def runScoped (semantics : Semantics Name Value Op State Event Error)
    (code : List (Instruction Name Op)) (returns : List Name)
    (env : Environment Name Value) (state : LogicalState State) :
    Execution (LogicalState State) Event (Fault Name Error) (List Value) :=
  let result := run semantics code returns env state
  { result with state := ⟨semantics.leave result.state.ghost result.state.core, {}⟩ }

theorem runScoped_eraseReleases (semantics : Semantics Name Value Op State Event Error)
    (code : List (Instruction Name Op)) (returns : List Name)
    (safe : Safe code returns) (left right : Environment Name Value)
    (agree : Agree (needed code returns) left right) (state : LogicalState State) :
    runScoped semantics code returns left state =
      runScoped semantics (eraseReleases code) returns right state := by
  unfold runScoped
  rw [run_eraseReleases semantics code returns safe left right agree state]

end Zkc.Compiler.Storage
