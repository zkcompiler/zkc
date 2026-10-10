import Tools.Interactive.Bindings

/-! Independent portable source admission. Owner equality is checked again for
each resolved binding, after both parent and child role maps are installed. -/

set_option autoImplicit false

namespace Tools.Interactive

structure KernelSignature where
  inputs : List Ty
  outputs : List Ty
  matchSafe : Bool := true
  deriving BEq, Repr

abbrev Context := List Port

def Context.get (env : Context) (name : Name) : Result Port :=
  lookup name (env.map fun port => (port.name, port))

def Context.read (env : Context) (names : List Name) : Result (List Port) := names.mapM env.get

def Context.bind (env : Context) (names : List Name) (ports : List (Name × Ty)) : Result Context := do
  ensure (names.length ≤ limits.ports) "port-limit"
  ensure (names.length == ports.length) "result-arity"
  ensure (unique names && names.all (fun n => !(env.any fun p => p.name == n))) "ssa-rebinding"
  return (names.zip ports).map (fun (name, owner, ty) => ⟨name, owner, ty⟩) ++ env

def portsMatch (actual : List Port) (expected : List (Name × Ty)) : Bool :=
  actual.length == expected.length && (actual.zip expected).all fun (port, owner, ty) =>
    port.ty == ty && port.owner == owner

def consumeOperands (env : Context) (names used : List Name) : Result (List Port × List Name) := do
  let ports ← env.read names
  let mut used := used
  for port in ports do
    ensure (!(used.contains port.name)) "interactive-resource-reuse"
    if !duplicable port.ty then
      used := port.name :: used
  return (ports, used)

def sites : Nat → List Instruction → Result (List Name)
  | 0, _ => .error "body-depth-limit"
  | depth + 1, body => do
    let mut result := []
    for instruction in body do
      match instruction with
      | .op site .. | .localCall site .. | .message site .. | .send site .. | .receive site ..
      | .call site .. | .variant site .. | .stop site .. | .incomplete site => result := result ++ [site]
      | .localMatch site _ _ arms _ =>
          result := result ++ [site] ++ (← arms.mapM fun arm => sites depth arm.2.2).flatten
      | .loop site _ _ _ nested _ => result := result ++ [site] ++ (← sites depth nested)
      | .conditional site _ _ yes no _ => result := result ++ [site] ++ (← sites depth yes) ++ (← sites depth no)
      | .forLoop site _ _ _ _ _ nested _ => result := result ++ [site] ++ (← sites depth nested)
      | .ret _ | .yield _ | .release _ => pure ()
    return result

def bodyLimits (body : List Instruction) : Result Unit := do
  let all ← sites limits.depth body
  ensure (unique all) "duplicate-site"
  ensure (all.length ≤ limits.instructions) "instruction-limit"

def hasLocalControl (body : List Instruction) : Bool :=
  body.any fun instruction => match instruction with | .conditional .. | .forLoop .. | .localMatch .. | .variant .. | .stop .. => true | _ => false

def instructionCount : Nat → List Instruction → Nat
  | 0, _ => limits.instructions + 1
  | fuel + 1, body => body.length + (body.map fun i => match i with
      | .loop _ _ _ _ nested _ | .forLoop _ _ _ _ _ _ nested _ => instructionCount fuel nested
      | .localMatch _ _ _ arms _ => (arms.map fun arm => instructionCount fuel arm.2.2).sum
      | .conditional _ _ _ yes no _ => instructionCount fuel yes + instructionCount fuel no
      | _ => 0).sum

/-- A local tag must not become a challenge schedule. Calls are checked through
retained bodies, even when the selected arm will not execute. -/
def admitMatchEffects (signature : String → List String → Result KernelSignature)
    (locals : List Function) : Nat → List Instruction → Result Unit
  | 0, _ => throw "body-depth-limit"
  | depth + 1, code => code.forM fun instruction => do
      match instruction with
      | .op _ kernel attrs _ _ => ensure (← signature kernel attrs).matchSafe "variant-challenge"
      | .call _ callee _ _ =>
          let function ← lookup callee (locals.map fun f => (f.name, f))
          let some body := function.body | throw "algorithm-call-symbol"
          admitMatchEffects signature locals depth body
      | .localMatch _ _ _ arms _ => for arm in arms do admitMatchEffects signature locals depth arm.2.2
      | .conditional _ _ _ yes no _ => admitMatchEffects signature locals depth yes; admitMatchEffects signature locals depth no
      | .forLoop _ _ _ _ _ _ nested _ => admitMatchEffects signature locals depth nested
      | _ => pure ()

def usesVariant (locals : List Function) : Nat → List Instruction → Bool
  | 0, _ => true
  | depth + 1, code => code.any fun instruction => match instruction with
      | .variant .. | .localMatch .. => true
      | .call _ callee _ _ => match locals.find? (·.name == callee) with
          | some function => usesVariant locals depth (function.body.getD [])
          | none => true
      | .conditional _ _ _ yes no _ => usesVariant locals depth yes || usesVariant locals depth no
      | .forLoop _ _ _ _ _ _ nested _ => usesVariant locals depth nested
      | _ => false

def admitLocalFlow (signature : String → List String → Result KernelSignature)
    (allowRelease : Bool) (locals : List Function) : Nat → Bool → Context → Option (List Ty) → List Instruction → Result (Option (List Ty))
  | 0, _, _, _, _ => .error "body-depth-limit"
  | depth + 1, region, initial, expected, body => do
      let mut env := initial
      let mut terminal := false
      let mut consumed : List Name := []
      let mut returned : Option (List Ty) := none
      for instruction in body do
        ensure (!terminal) "instruction-after-terminal"
        match instruction with
        | .release names =>
            ensure allowRelease "release-context"
            ensure (!names.isEmpty) "release-empty"
            for name in names do
              let port ← env.get name
              ensure (discardable port.ty) "release-resource"
              ensure (!(consumed.contains name)) "release-unavailable"
              consumed := name :: consumed
        | .op _ kernel attrs inputs outputs =>
            let signature ← signature kernel attrs
            ensure (!((signature.inputs ++ signature.outputs).any fun ty => typeKind ty == "variant")) "variant-operation-boundary"
            let (actual, nextConsumed) ← consumeOperands env inputs consumed
            consumed := nextConsumed
            ensure (actual.map Port.ty == signature.inputs) "binding-operation-signature"
            env ← env.bind outputs (signature.outputs.map fun ty => ("", ty))
        | .call _ callee inputs outputs =>
            ensure (!allowRelease) "algorithm-call-context"
            let callee ← lookup callee (locals.map fun f => (f.name, f))
            ensure callee.body.isSome "algorithm-call-symbol"
            let (actual, nextConsumed) ← consumeOperands env inputs consumed
            consumed := nextConsumed
            ensure (actual.map Port.ty == callee.arguments.map Prod.snd) "algorithm-call-signature"
            env ← env.bind outputs (callee.results.map fun ty => ("", ty))
        | .variant _ ty alternative payload output =>
            let types ← Bindings.variantPayload ty alternative
            let (actual, nextConsumed) ← consumeOperands env payload consumed
            consumed := nextConsumed
            ensure (actual.map Port.ty == types) "variant-payload-types"
            env ← env.bind [output] [("", ty)]
        | .localMatch _ input captures arms outputs =>
            let (scrutinees, nextConsumed) ← consumeOperands env [input] consumed
            consumed := nextConsumed
            let [scrutinee] := scrutinees | throw "variant-type"
            let parsed ← Bindings.valueType (scrutinee.ty.contains '@') scrutinee.ty
            ensure (parsed.kind == "variant") "variant-type"
            let descriptor ← Variant.parse ("variant:" ++ parsed.identity)
            ensure (arms.map Prod.fst == descriptor.alternatives.map Prod.fst) "variant-arms"
            let (captured, nextConsumed) ← consumeOperands env captures consumed
            consumed := nextConsumed
            let mut joined : Option (List Ty) := none
            for (alternative, payload, nested) in arms do
              admitMatchEffects signature locals limits.depth nested
              let types ← Bindings.variantPayload scrutinee.ty alternative
              let inner ← Context.bind [] payload (types.map fun ty => ("", ty))
              let inner ← inner.bind captures (captured.map fun p => ("", p.ty))
              let result ← admitLocalFlow signature allowRelease locals depth true inner none nested
              if let some types := result then
                if let some expected := joined then ensure (types == expected) "local-match-yield"
                joined := some types
            if let some types := joined then env ← env.bind outputs (types.map fun ty => ("", ty))
            else
              ensure outputs.isEmpty "local-terminal-outputs"
        | .stop _ owner reason =>
            ensure (owner.isEmpty && ["reject", "abort", "exhausted", "incomplete", "refused"].contains reason) "unknown-stop"
            terminal := true
        | .conditional _ condition captures yes no outputs =>
            let (guard, _) ← consumeOperands env [condition] consumed
            ensure (guard.map (fun p => typeKind p.ty) == ["bool"]) "local-condition-type"
            let (captured, nextConsumed) ← consumeOperands env captures consumed
            consumed := nextConsumed
            let inner ← Context.bind [] captures (captured.map fun p => ("", p.ty))
            let yesTypes ← admitLocalFlow signature allowRelease locals depth true inner none yes
            let noTypes ← admitLocalFlow signature allowRelease locals depth true inner none no
            if let some yes := yesTypes then
              if let some no := noTypes then ensure (yes == no) "local-if-yield"
            let joined := yesTypes.or noTypes
            if let some types := joined then env ← env.bind outputs (types.map fun ty => ("", ty))
            else
              ensure outputs.isEmpty "local-terminal-outputs"
        | .forLoop _ induction lower upper carried captures nested outputs =>
            let (bounds, _) ← consumeOperands env [lower, upper] consumed
            ensure (bounds.all fun p => typeKind p.ty == "index") "local-bound-type"
            let (initial, nextConsumed) ← consumeOperands env (carried.map Prod.snd) consumed
            consumed := nextConsumed
            let (captured, _) ← consumeOperands env captures consumed
            ensure (captured.all fun p => duplicable p.ty) "affine-capture"
            let ports := initial.map fun p => ("", p.ty)
            let inner ← Context.bind [] [induction] [("", bounds.head!.ty)]
            let inner ← inner.bind (carried.map Prod.fst) ports
            let inner ← inner.bind captures (captured.map fun p => ("", p.ty))
            let _ ← admitLocalFlow signature allowRelease locals depth true inner (some (initial.map Port.ty)) nested
            env ← env.bind outputs ports
        | .yield values | .ret values =>
            ensure (match instruction with | .yield _ => region | _ => !region) "local-terminal-context"
            let (actual, nextConsumed) ← consumeOperands env values consumed
            consumed := nextConsumed
            if let some expected := expected then
              ensure (actual.map Port.ty == expected) (if region then "local-yield-types" else "function-return-types")
            returned := some (actual.map Port.ty)
            terminal := true
        | _ => throw "invalid-function-body"
      ensure terminal "missing-return"
      return returned

def admitLocalBody (signature : String → List String → Result KernelSignature)
    (allowRelease : Bool) (locals : List Function) (depth : Nat) (region : Bool)
    (initial : Context) (expected : Option (List Ty)) (body : List Instruction) : Result (List Ty) := do
  return (← admitLocalFlow signature allowRelease locals depth region initial expected body).getD (expected.getD [])

def admitFunctionWith (signature : String → List String → Result KernelSignature)
    (function : Function) (executable : Bool := true)
    (allowRelease : Bool := false) (locals : List Function := []) : Result Unit := do
  ensure (unique (function.arguments.map Prod.fst)) "duplicate-argument"
  ensure (function.arguments.length ≤ limits.ports && function.results.length ≤ limits.ports) "port-limit"
  let some body := function.body | do
    ensure (!executable) "external-function"
    return
  bodyLimits body
  let _ ← admitLocalBody signature allowRelease locals limits.depth false
    (function.arguments.map fun (name, ty) => Port.mk name "" ty) (some function.results) body

/-- Storage bookkeeping erasure, used only after physical release admission. -/
def eraseReleases : Nat → List Instruction → List Instruction
  | 0, body => body
  | depth + 1, body => body.filterMap fun instruction => match instruction with
    | .release _ => none
    | .localMatch site input captures arms outputs => some (.localMatch site input captures
        (arms.map fun (label, payload, nested) => (label, payload, eraseReleases depth nested)) outputs)
    | .conditional site condition captures yes no outputs => some (.conditional site condition captures
        (eraseReleases depth yes) (eraseReleases depth no) outputs)
    | .forLoop site induction lower upper carried captures nested outputs => some (.forLoop site induction lower upper carried captures
        (eraseReleases depth nested) outputs)
    | other => some other

def eraseStorageReleases (function : Function) : Function :=
  { function with body := function.body.map (eraseReleases limits.depth) }

def localDependencies : Nat → List Instruction → List Name
  | 0, _ => []
  | depth + 1, body => body.flatMap fun instruction => match instruction with
    | .call _ callee _ _ => [callee]
    | .localMatch _ _ _ arms _ => arms.flatMap fun arm => localDependencies depth arm.2.2
    | .conditional _ _ _ yes no _ => localDependencies depth yes ++ localDependencies depth no
    | .forLoop _ _ _ _ _ _ nested _ => localDependencies depth nested
    | _ => []

def environmentSignature (environment : Environment) (stage kernel : String)
    (attrs : List String) : Result KernelSignature := do
  match environment with
  | .explicit bindings =>
      let binding ← lookup kernel (bindings.map fun b => (b.name, b))
      let signature ← Bindings.resolve (stage == "physical") binding
      (Bindings.attributes false binding.contract attrs (binding.arguments.headD Bindings.fr)).mapError
        fun reason =>
          if reason == "noncanonical-field" then "interactive-constant"
          else if reason == "kernel-attributes" then
            if binding.contract == "curve.at" && attrs.length == 1 then "interactive-index"
            else "interactive-kernel-parameters"
          else reason
      return ⟨signature.inputs.map Bindings.ValueType.spelling, signature.outputs.map Bindings.ValueType.spelling,
        !Bindings.historyContract binding.contract⟩

def mapped (binding : Option Instance) (role : Name) : Result Name :=
  match binding with
  | none => .ok role
  | some binding => binding.role role

def callSignature (source : Source) (definition : Protocol) (binding : Option Instance)
    (dependency : Name) : Result (List (Name × Ty) × List (Name × Ty)) := do
  let childName := (← definition.dependency dependency).protocol
  let child ← source.protocol childName
  match binding with
  | none => return (child.arguments.map (fun p => (p.owner, p.ty)), child.results)
  | some binding =>
      let binding ← source.binding (← lookup dependency binding.dependencies)
      ensure (binding.protocol == childName) "dependency-protocol"
      let args ← child.arguments.mapM fun port => return (← binding.role port.owner, port.ty)
      let results ← child.results.mapM fun (owner, ty) => return (← binding.role owner, ty)
      return (args, results)

abbrev Schemas := List (Name × Ty)

/-- Schema state is shared by the entire protocol definition, including closed
nested bodies and zero-iteration loops. Child definitions have separate scopes. -/
def admitBody (source : Source) (definition : Protocol) (binding : Option Instance) (executable : Bool) :
    Nat → Bool → Context → List (Name × Ty) → Schemas → List Instruction → Result Schemas
  | 0, _, _, _, _, _ => .error "body-depth-limit"
  | depth + 1, loopBody, initial, expected, initialSchemas, body => do
    let mut env := initial
    let mut schemas := initialSchemas
    let mut terminal := false
    let mut consumed : List Name := []
    for instruction in body do
      ensure (!terminal) "instruction-after-terminal"
      match instruction with
      | .localCall _ owner callee inputs outputs =>
          ensure (definition.roles.contains owner) "unknown-role"
          let owner ← mapped binding owner
          let function ← source.function callee
          let (actual, nextConsumed) ← consumeOperands env inputs consumed
          consumed := nextConsumed
          ensure (portsMatch actual (function.arguments.map fun p => (owner, p.2)))
            "local-input-ownership-or-types"
          env ← env.bind outputs (function.results.map fun ty => (owner, ty))
      | .message _ schema sender receiver input output =>
          ensure (definition.roles.contains sender && definition.roles.contains receiver) "unknown-role"
          let sender ← mapped binding sender
          let receiver ← mapped binding receiver
          let value ← env.get input
          ensure (sender != receiver) "self-message"
          ensure (value.owner == sender) "message-input-ownership"
          ensure (serializable value.ty || (!executable && value.ty.startsWith "opaque:")) "nonserializable-message"
          if let some previous := schemas.find? (fun p => p.1 == schema) then
            ensure (previous.2 == value.ty) "schema-payload-type"
          else schemas := (schema, value.ty) :: schemas
          env ← env.bind [output] [(receiver, value.ty)]
      | .call _ dependency inputs outputs =>
          let (arguments, results) ← callSignature source definition binding dependency
          let (actual, nextConsumed) ← consumeOperands env inputs consumed
          consumed := nextConsumed
          ensure (portsMatch actual arguments) "call-input-ownership-or-types"
          env ← env.bind outputs results
      | .loop _ iterations carried captures nested outputs =>
          match iterations with
          | .parameter name => ensure (definition.parameters.contains name) "interactive-loop-parameter"
          | .constant value => ensure (value ≤ limits.iterations) "loop-limit"
          if let some binding := binding then
            ensure ((← binding.countBound iterations) ≤ limits.iterations) "loop-limit"
          let (initial, nextConsumed) ← consumeOperands env (carried.map Prod.snd) consumed
          consumed := nextConsumed
          let ports := initial.map fun p => (p.owner, p.ty)
          let inner ← Context.bind [] (carried.map Prod.fst) ports
          let captured ← env.read captures
          ensure (captured.all fun p => duplicable p.ty) "affine-capture"
          let inner ← inner.bind captures (captured.map fun p => (p.owner, p.ty))
          schemas ← admitBody source definition binding executable depth true inner ports schemas nested
          env ← env.bind outputs ports
      | .yield values =>
          ensure loopBody "yield-outside-loop"
          let (actual, nextConsumed) ← consumeOperands env values consumed
          consumed := nextConsumed
          ensure (portsMatch actual expected) "yield-ownership-or-types"
          terminal := true
      | .ret values =>
          ensure (!loopBody) "return-inside-loop"
          let (actual, nextConsumed) ← consumeOperands env values consumed
          consumed := nextConsumed
          ensure (portsMatch actual expected) "return-ownership-or-types"
          terminal := true
      | .stop _ owner _ =>
          ensure (definition.roles.contains owner) "unknown-role"
          terminal := true
      | _ => throw "invalid-common-body"
    ensure terminal "missing-terminal"
    return schemas

def admitCallGraph (source : Source) : Result Unit := do
  let mut localRemaining := source.functions
  let mut localHeights : List (Name × Nat) := []
  for _ in List.range source.functions.length do
    if localRemaining.isEmpty then break
    let dependencies := fun (f : Function) => localDependencies limits.depth (f.body.getD [])
    let ready := localRemaining.filter fun f => (dependencies f).all fun d => localHeights.any fun h => h.1 == d
    ensure (!ready.isEmpty) "algorithm-call-cycle-or-symbol"
    for f in ready do
      let depths ← (dependencies f).mapM fun d => lookup d localHeights
      let height := 1 + (depths.foldl max 0)
      ensure (height ≤ limits.callDepth + 1) "algorithm-call-depth"
      localHeights := (f.name, height) :: localHeights
    localRemaining := localRemaining.filter fun f => !(ready.any fun r => r.name == f.name)
  for definition in source.protocols do
    for dependency in definition.dependencies do
      let _ ← source.protocol dependency.protocol
  let mut remaining := source.protocols
  let mut heights : List (Name × Nat) := []
  for _ in List.range source.protocols.length do
    if remaining.isEmpty then break
    let ready := remaining.filter fun p => p.dependencies.all fun d => heights.any fun h => h.1 == d.protocol
    ensure (!ready.isEmpty) "recursive-protocol"
    for definition in ready do
      let depths ← definition.dependencies.mapM fun d => lookup d.protocol heights
      let height := 1 + depths.foldl max 0
      ensure (height ≤ limits.callDepth) "call-depth-limit"
      heights := (definition.name, height) :: heights
    remaining := remaining.filter fun p => !(ready.any fun q => q.name == p.name)
  ensure remaining.isEmpty "recursive-protocol"

/-- Compute the entry-reachable binding closure with bounded depth. -/
def reachableFrom (source : Source) (name : Name) : Result (List Name) := do
  let mut pending := [name]
  let mut visited : List Name := []
  for _ in List.range (source.instances.length + 1) do
    let fresh := pending.filter fun n => !(visited.contains n)
    if fresh.isEmpty then return visited
    pending := []
    for current in fresh.eraseDups do
      let binding ← source.binding current
      visited := visited ++ [current]
      pending := pending ++ binding.dependencies.map Prod.snd
    pending := pending.eraseDups
  throw "instance-graph-limit"

def Source.reachable (source : Source) : Result (List Name) := do
  let closures ← source.entries.mapM fun (_, name) => reachableFrom source name
  return closures.flatten.eraseDups

def admitSource (source : Source) (executable : Bool := true) : Result Unit := do
  let checkType ← match source.environment with
    | .explicit bindings => do
        ensure (bindings.length ≤ limits.definitions && unique (bindings.map OperationBinding.name)) "binding-declarations"
        for binding in bindings do
          let _ ← Bindings.resolve false binding
        pure (fun ty => (Bindings.valueType false ty).isOk)
  ensure (source.functions.length + source.protocols.length ≤ limits.definitions &&
    source.instances.length ≤ limits.definitions)
    "definition-limit"
  ensure (unique (source.functions.map Function.name)) "duplicate-function"
  ensure (unique (source.protocols.map Protocol.name)) "duplicate-protocol"
  ensure (unique (source.instances.map Instance.name)) "duplicate-instance"
  ensure (unique (source.entries.map Prod.fst)) "duplicate-entry"
  let functionCount := (source.functions.map fun f => instructionCount limits.depth (f.body.getD [])).sum
  let protocolCount := (source.protocols.map fun p => instructionCount limits.depth (p.body.getD [])).sum
  ensure (functionCount + protocolCount ≤ limits.instructions) "module-instruction-limit"
  admitCallGraph source
  for function in source.functions do
    ensure ((function.results ++ function.arguments.map Prod.snd).all checkType) "type-profile"
    if executable then
      ensure (!((function.results ++ function.arguments.map Prod.snd).any abstractType)) "abstract-executable-type"
    admitFunctionWith (environmentSignature source.environment "logical") function executable false source.functions
  for definition in source.protocols do
    ensure (!((definition.arguments.map Port.ty ++ definition.results.map Prod.snd).any fun ty => typeKind ty == "variant")) "variant-protocol-boundary"
    if executable then ensure definition.body.isSome "external-protocol"
    ensure (!definition.roles.isEmpty && unique definition.roles) "protocol-roles"
    ensure (unique definition.parameters) "duplicate-parameter"
    ensure (unique (definition.arguments.map Port.name)) "duplicate-argument"
    ensure (definition.arguments.length ≤ limits.ports && definition.results.length ≤ limits.ports) "port-limit"
    ensure (unique (definition.dependencies.map Dependency.name)) "duplicate-dependency"
    for dependency in definition.dependencies do
      let child ← source.protocol dependency.protocol
      ensure (unique (dependency.agreements.map Prod.fst)) "duplicate-dependency-parameter"
      for (childParameter, parentParameter) in dependency.agreements do
        ensure (child.parameters.contains childParameter) "unknown-child-parameter"
        ensure (definition.parameters.contains parentParameter) "unknown-parent-parameter"
    ensure (definition.arguments.all (fun p => definition.roles.contains p.owner) &&
      definition.results.all (fun p => definition.roles.contains p.1)) "signature-owner"
    ensure ((definition.arguments.map Port.ty ++ definition.results.map Prod.snd).all
      checkType) "type-profile"
    if executable then
      ensure (!((definition.arguments.map Port.ty ++ definition.results.map Prod.snd).any abstractType)) "abstract-executable-type"
    if let some body := definition.body then
      bodyLimits body
      let _ ← admitBody source definition none executable limits.depth false definition.arguments definition.results [] body
  for binding in source.instances do
    let definition ← source.protocol binding.protocol
    ensure (exactKeys binding.parameters (definition.parameters.map fun p => (p, ()))) "instance-parameters"
    ensure (binding.parameters.all (fun p => p.2.bound ≤ limits.iterations)) "parameter-limit"
    ensure (exactKeys binding.dependencies (definition.dependencies.map fun d => (d.name, ()))) "instance-dependencies"
    ensure (exactKeys binding.roles (definition.roles.map fun p => (p, ())) &&
      unique (binding.roles.map Prod.snd)) "instance-role-map"
  for binding in source.instances do
    let definition ← source.protocol binding.protocol
    for (_, parameter) in binding.parameters do
      if let .ingress _ selectors := parameter then
        ensure binding.dependencies.isEmpty "interactive-family-dependency"
        ensure (exactKeys (selectors.map fun s => (s.role, ())) ((binding.roles.map Prod.snd).map fun r => (r, ()))) "interactive-family-roles"
        for (formal, actual) in binding.roles do
          let selector ← lookup actual (selectors.map fun s => (s.role, s))
          let some function := source.functions.find? (·.name == selector.function)
            | throw "interactive-family-selector"
          ensure function.body.isSome "interactive-family-selector"
          ensure (!(usesVariant source.functions limits.depth (function.body.getD []))) "variant-family-selector"
          let inputs ← selector.arguments.mapM fun name => do
            let some port := definition.arguments.find? (·.name == name)
              | throw "interactive-family-argument"
            ensure (port.owner == formal && serializable port.ty) "interactive-family-input"
            return port.ty
          ensure (function.arguments.map Prod.snd == inputs && function.results == ["index"])
            "interactive-family-signature"
    for (dependency, childName) in binding.dependencies do
      let child ← source.binding childName
      ensure (!(child.parameters.any (fun p => p.2.dynamic))) "interactive-family-dependency"
      let declared ← definition.dependency dependency
      ensure (child.protocol == declared.protocol) "dependency-protocol"
      for (childParameter, parentParameter) in declared.agreements do
        ensure ((← lookup childParameter child.parameters) == (← lookup parentParameter binding.parameters))
          "dependency-parameter-agreement"
      ensure (child.roles.all (fun p => (binding.roles.map Prod.snd).contains p.2)) "dependency-role-scope"
      for (formal, actual) in child.roles do
        ensure ((← binding.role formal) == actual) "dependency-role-map-agreement"
  -- Validate all binding interfaces before a caller consumes a child's ports.
  for binding in source.instances do
    let definition ← source.protocol binding.protocol
    if let some body := definition.body then
      let arguments ← definition.arguments.mapM fun p => return { p with owner := ← binding.role p.owner }
      let results ← definition.results.mapM fun (owner, ty) => return (← binding.role owner, ty)
      let _ ← admitBody source definition (some binding) executable limits.depth false arguments results [] body
  let selected ← source.reachable
  if executable then
    ensure (!source.entries.isEmpty) "no-entry"
    for name in selected do
      let binding ← source.binding name
      let definition ← source.protocol binding.protocol
      ensure definition.body.isSome "external-protocol"
      ensure (!(definition.arguments.any fun p => p.ty.startsWith "opaque:") &&
        !(definition.results.any fun p => p.2.startsWith "opaque:")) "opaque-executable-port"

end Tools.Interactive
