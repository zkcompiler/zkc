import Tools.Interactive.Admission

/-! One source control traversal for the independent explicit-binding references.

The service owns values, primitive execution, messages and failures. The walker
owns role-local stores, child-instance resolution, loop carries and source scope.
It never traverses projected participants or selected physical operations.
-/

set_option autoImplicit false

namespace Tools.Interactive.Control

inductive Frame where
  | call (site : Name)
  | iteration (site : Name) (index : Nat)
  | localCall (site function : Name)
  | localMatch (site alternative : Name)
  | localBranch (site : Name) (selected : Bool)
  | localIteration (site : Name) (index : Nat)
  deriving BEq, Repr

structure Scope where
  binding : Name
  path : List Frame
  site : Name
  role : Name
  deriving BEq, Repr

abbrev ValueEnvironment (Value : Type) := List (Name × Value)
abbrev RoleEnvironments (Value : Type) := List (Name × ValueEnvironment Value)

structure Services (Value : Type) (m : Type → Type) where
  typeOf : Value → Ty
  fail {α : Type} : Scope → String → String → m α
  charge : Scope → m Unit
  iteration : Scope → m Unit
  executeLocal : Scope → Function → List Value → m (List Value)
  send : Scope → Name → Name → Value → m Unit
  received : Scope → Name → Name → Value → m Unit
  receive : Scope → Name → Name → Ty → m Value
  enterRegion : Scope → RoleEnvironments Value → m Unit
  exitRegion : Scope → List (Name × Value) → m Unit

def Services.checked {Value : Type} {m : Type → Type} [Monad m]
    (services : Services Value m) {α : Type} (scope : Scope) : Result α → m α
  | .ok value => pure value
  | .error code => services.fail scope "refused" code

variable {Value : Type}

def active (selected : Option Name) (role : Name) : Bool :=
  match selected with
  | none => true
  | some self => role == self

def readValues (env : ValueEnvironment Value) (names : List Name) : Result (List Value) :=
  names.mapM fun n => lookup n env

def bindValues (env : ValueEnvironment Value) (names : List Name) (values : List Value) : Result (ValueEnvironment Value) := do
  ensure (names.length == values.length) "runtime-result-arity"
  ensure (unique names && names.all (fun n => !(env.any fun p => p.1 == n))) "runtime-ssa-rebinding"
  return names.zip values ++ env

def roleStore (env : RoleEnvironments Value) (owner : Name) : ValueEnvironment Value :=
  (env.find? fun p => p.1 == owner).map Prod.snd |>.getD []

def replaceStore (env : RoleEnvironments Value) (owner : Name) (values : ValueEnvironment Value) : RoleEnvironments Value :=
  (owner, values) :: env.filter (fun p => p.1 != owner)

def readPorts (selected : Option Name) (context : Context) (env : RoleEnvironments Value)
    (names : List Name) : Result (List Value) := do
  let ports ← context.read names
  let owned := ports.filter fun p => active selected p.owner
  owned.mapM fun p => lookup p.name (roleStore env p.owner)

def bindPorts (typeOf : Value → Ty) (selected : Option Name) (env : RoleEnvironments Value) (names : List Name)
    (ports : List (Name × Ty)) (values : List Value) : Result (RoleEnvironments Value) := do
  ensure (names.length == ports.length) "runtime-port-arity"
  let retained := (names.zip ports).filter fun (_, owner, _) => active selected owner
  ensure (retained.length == values.length) "runtime-owned-arity"
  let mut env := env
  for ((name, owner, ty), value) in retained.zip values do
    ensure (typeOf value == ty) "runtime-port-type"
    let store ← bindValues (roleStore env owner) [name] [value]
    env := replaceStore env owner store
  return env

def executeBody {Value : Type} {m : Type → Type} [Monad m]
    (services : Services Value m) (source : Source) (selected : Option Name) : Nat → Instance → Protocol →
    Scope → Context → RoleEnvironments Value → List Instruction → m (List Value)
  | 0, _, _, origin, _, _, _ => services.fail origin "exhausted" "reference-stack-limit"
  | fuel + 1, binding, definition, origin, initialContext, initialEnv, body => do
    services.enterRegion origin initialEnv
    let mut context := initialContext
    let mut env := initialEnv
    for instruction in body do
      services.charge origin
      match instruction with
      | .localCall site owner callee inputs outputs =>
          let owner ← services.checked origin (binding.role owner)
          let location := { origin with site := site, role := owner }
          let function ← services.checked location (source.function callee)
          let resultPorts := function.results.map fun ty => (owner, ty)
          if active selected owner then
            let values ← services.checked location (readValues (roleStore env owner) inputs)
            let values ← services.executeLocal { location with path := location.path ++ [.localCall site callee] } function values
            env ← services.checked location (bindPorts services.typeOf selected env outputs resultPorts values)
          context ← services.checked location (context.bind outputs resultPorts)
      | .message site schema sender receiver input output =>
          let sender ← services.checked origin (binding.role sender)
          let receiver ← services.checked origin (binding.role receiver)
          let location := { origin with site := site, role := sender }
          let receiving := { location with role := receiver }
          let port ← services.checked location (context.get input)
          if active selected sender then
            let value ← services.checked location (lookup input (roleStore env sender))
            services.send location schema receiver value
            if active selected receiver then
              env ← services.checked receiving (bindPorts services.typeOf selected env [output] [(receiver, port.ty)] [value])
              services.received receiving schema sender value
          else if active selected receiver then
            let value ← services.receive receiving schema sender port.ty
            env ← services.checked receiving (bindPorts services.typeOf selected env [output] [(receiver, port.ty)] [value])
          context ← services.checked location (context.bind [output] [(receiver, port.ty)])
      | .call site dependency inputs outputs =>
          let location := { origin with site := site }
          let child ← services.checked location (source.binding (← services.checked location (lookup dependency binding.dependencies)))
          let childDefinition ← services.checked location (source.protocol child.protocol)
          let (arguments, returns) ← services.checked location (callSignature source definition (some binding) dependency)
          if child.roles.any (fun p => active selected p.2) then
            let some childBody := childDefinition.body | services.fail location "refused" "external-protocol"
            let values ← services.checked location (readPorts selected context env inputs)
            let childContext ← services.checked location (Context.bind [] (childDefinition.arguments.map Port.name) arguments)
            let childEnv ← services.checked location (bindPorts services.typeOf selected [] (childDefinition.arguments.map Port.name) arguments values)
            let values ← executeBody services source selected fuel child childDefinition
              { location with binding := child.name, path := location.path ++ [.call site] }
              childContext childEnv childBody
            env ← services.checked location (bindPorts services.typeOf selected env outputs returns values)
          context ← services.checked location (context.bind outputs returns)
      | .loop site count carried captures nested outputs =>
          let location := { origin with site := site }
          let count ← services.checked location (binding.count count)
          let initial ← services.checked location (context.read (carried.map Prod.snd))
          let ports := initial.map fun p => (p.owner, p.ty)
          let captured ← services.checked location (context.read captures)
          let capturedPorts := captured.map fun p => (p.owner, p.ty)
          let inner ← services.checked location (Context.bind [] (carried.map Prod.fst) ports)
          let inner ← services.checked location (inner.bind captures capturedPorts)
          let captureValues ← services.checked location (readPorts selected context env captures)
          let mut values ← services.checked location (readPorts selected context env (carried.map Prod.snd))
          for iteration in [:count] do
            let step := { location with path := location.path ++ [.iteration site iteration] }
            services.iteration step
            services.charge step
            let innerEnv ← services.checked step (bindPorts services.typeOf selected [] (carried.map Prod.fst) ports values)
            let innerEnv ← services.checked step (bindPorts services.typeOf selected innerEnv captures capturedPorts captureValues)
            values ← executeBody services source selected fuel binding definition step inner innerEnv nested
          env ← services.checked location (bindPorts services.typeOf selected env outputs ports values)
          context ← services.checked location (context.bind outputs ports)
      | .yield names | .ret names =>
          let values ← services.checked origin (readPorts selected context env names)
          let ports ← services.checked origin (context.read names)
          let owners := (ports.filter (fun p => active selected p.owner)).map Port.owner
          services.exitRegion { origin with site := "" } (owners.zip values)
          return values
      | .stop site owner reason =>
          let owner ← services.checked origin (binding.role owner)
          let location := { origin with site := site, role := owner }
          if active selected owner then services.fail location reason "source-stop"
          else
            services.fail { location with site := "", role := selected.getD owner } "incomplete" "foreign-stop-leaf"
      | _ => services.fail origin "refused" "invalid-common-body"
    services.fail origin "refused" "missing-terminal"

end Tools.Interactive.Control
