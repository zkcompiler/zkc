import Tools.Interactive.Admission

/-! Structural translation validation against actual common source. SSA binder
names and participant symbols are alpha-normalized. Public entry, instance,
function and action-site identities remain part of the interface. -/

set_option autoImplicit false

namespace Tools.Interactive

def participantKey (binding role : Name) : Name := binding ++ ":" ++ role

def participantSymbol (source : Source) (binding role : Name) : Result Name := do
  let selected ← source.binding binding
  let roles := selected.roles.map Prod.snd
  ensure (roles.contains role) "missing-child-role"
  return s!"p{(source.instances.map Instance.name).idxOf binding}_{roles.idxOf role}"

def ownedNames (env : Context) (self : Name) (names : List Name) : Result (List Name) := do
  let ports ← env.read names
  return (names.zip ports).filterMap fun (name, port) => if port.owner == self then some name else none

def projectBody (source : Source) (definition : Protocol) (binding : Instance) (self : Name) :
    Nat → Context → List Instruction → Result (List Instruction)
  | 0, _, _ => .error "body-depth-limit"
  | depth + 1, initial, body => do
    let mut env := initial
    let mut result := []
    for instruction in body do
      match instruction with
      | .localCall site owner callee inputs outputs =>
          let owner ← binding.role owner
          let function ← source.function callee
          if owner == self then result := result ++ [.localCall site "" callee inputs outputs]
          env ← env.bind outputs (function.results.map fun ty => (owner, ty))
      | .message site schema sender receiver input output =>
          let sender ← binding.role sender
          let receiver ← binding.role receiver
          let value ← env.get input
          if sender == self then result := result ++ [.send site schema receiver input]
          if receiver == self then result := result ++ [.receive site schema sender output value.ty]
          env ← env.bind [output] [(receiver, value.ty)]
      | .call site dependency inputs outputs =>
          let (_, returns) ← callSignature source definition (some binding) dependency
          let child ← source.binding (← lookup dependency binding.dependencies)
          let after ← env.bind outputs returns
          if (child.roles.map Prod.snd).contains self then
            result := result ++ [.call site (← participantSymbol source child.name self)
              (← ownedNames env self inputs) (← ownedNames after self outputs)]
          env := after
      | .loop site count carried captures nested outputs =>
          let initial ← env.read (carried.map Prod.snd)
          let ports := initial.map fun p => (p.owner, p.ty)
          let inner ← Context.bind [] (carried.map Prod.fst) ports
          let captured ← env.read captures
          let inner ← inner.bind captures (captured.map fun p => (p.owner, p.ty))
          let projected ← projectBody source definition binding self depth inner nested
          let after ← env.bind outputs ports
          let carried := (carried.zip initial).filterMap fun (pair, p) => if p.owner == self then some pair else none
          result := result ++ [.loop site (← binding.projectCount count) carried
            (← ownedNames env self captures) projected (← ownedNames after self outputs)]
          env := after
      | .ret values => result := result ++ [.ret (← ownedNames env self values)]
      | .yield values => result := result ++ [.yield (← ownedNames env self values)]
      | .stop site owner reason =>
          let owner ← binding.role owner
          result := result ++ [if owner == self then .stop site "" reason else .incomplete site]
      | _ => throw "invalid-common-body"
    return result

def projectControl (source : Source) : Result (List Participant × List (Name × List (Name × Name))) := do
  admitSource source
  let selected ← source.reachable
  let mut participants := []
  for name in selected do
    let binding ← source.binding name
    let definition ← source.protocol binding.protocol
    let some body := definition.body | throw "external-protocol"
    let ports ← definition.arguments.mapM fun p => return { p with owner := ← binding.role p.owner }
    let returns ← definition.results.mapM fun (role, ty) => return (← binding.role role, ty)
    for (_, role) in binding.roles do
      participants := participants ++ [Participant.mk (← participantSymbol source name role) name role
        binding.parameters ((ports.filter fun p => p.owner == role).map fun p => (p.name, p.ty))
        ((returns.filter fun p => p.1 == role).map Prod.snd)
        (← projectBody source definition binding role limits.depth ports body)]
  let entries ← source.entries.mapM fun (name, selected) => do
    let binding ← source.binding selected
    let roles ← binding.roles.mapM fun (_, role) => return (role, ← participantSymbol source selected role)
    return (name, roles)
  return (participants, entries)

abbrev Renaming := List (Name × Name)

def renameRead (env : Renaming) (names : List Name) : Result (List Name) := names.mapM fun n => lookup n env

def renameBind (env : Renaming) (names : List Name) : Result (List Name × Renaming) := do
  ensure (unique names && names.all (fun n => !(env.any fun pair => pair.1 == n))) "ssa-rebinding"
  let canonical := (List.range names.length).map fun i => s!"v{env.length + i}"
  return (canonical, env ++ names.zip canonical)

def normalizeBody (symbols : Renaming) : Nat → Renaming → List Instruction → Result (List Instruction)
  | 0, _, _ => .error "body-depth-limit"
  | depth + 1, initial, body => do
    let mut env := initial
    let mut result := []
    for instruction in body do
      match instruction with
      | .op site kernel attrs inputs outputs =>
          let inputs ← renameRead env inputs
          let (outputs, next) ← renameBind env outputs
          result := result ++ [.op site kernel attrs inputs outputs]
          env := next
      | .localCall site owner callee inputs outputs =>
          let inputs ← renameRead env inputs
          let (outputs, next) ← renameBind env outputs
          result := result ++ [.localCall site owner callee inputs outputs]
          env := next
      | .send site schema peer input => result := result ++ [.send site schema peer (← lookup input env)]
      | .receive site schema peer output ty =>
          let (outputs, next) ← renameBind env [output]
          let [output] := outputs | throw "internal-binding-arity"
          result := result ++ [.receive site schema peer output ty]
          env := next
      | .call site callee inputs outputs =>
          let inputs ← renameRead env inputs
          let (outputs, next) ← renameBind env outputs
          result := result ++ [.call site (← lookup callee symbols) inputs outputs]
          env := next
      | .variant site ty alternative payload output =>
          let payload ← renameRead env payload
          let (outputs, next) ← renameBind env [output]
          let [output] := outputs | throw "internal-binding-arity"
          result := result ++ [.variant site ty alternative payload output]
          env := next
      | .localMatch site input captures arms outputs =>
          let input ← lookup input env
          let outerCaptures ← renameRead env captures
          let arms ← arms.mapM fun (label, payload, nested) => do
            let (payload, inner) ← renameBind [] payload
            -- Capture names in the instruction also name the isolated ports.
            let inner := inner ++ captures.zip outerCaptures
            return (label, payload, ← normalizeBody symbols depth inner nested)
          let (outputs, next) ← renameBind env outputs
          result := result ++ [.localMatch site input outerCaptures arms outputs]
          env := next
      | .conditional site condition captures yes no outputs =>
          let condition ← lookup condition env
          let outerCaptures ← renameRead env captures
          let (_, inner) ← renameBind [] captures
          let yes ← normalizeBody symbols depth inner yes
          let no ← normalizeBody symbols depth inner no
          let (outputs, next) ← renameBind env outputs
          result := result ++ [.conditional site condition outerCaptures yes no outputs]
          env := next
      | .forLoop site induction lower upper carried captures nested outputs =>
          let lower ← lookup lower env
          let upper ← lookup upper env
          let initials ← renameRead env (carried.map Prod.snd)
          let outerCaptures ← renameRead env captures
          let (index, inner) ← renameBind [] [induction]
          let [index] := index | throw "internal-binding-arity"
          let (args, inner) ← renameBind inner (carried.map Prod.fst)
          let (_, inner) ← renameBind inner captures
          let nested ← normalizeBody symbols depth inner nested
          let (outputs, next) ← renameBind env outputs
          result := result ++ [.forLoop site index lower upper (args.zip initials) outerCaptures nested outputs]
          env := next
      | .loop site count carried captures nested outputs =>
          let initials ← renameRead env (carried.map Prod.snd)
          let outerCaptures ← renameRead env captures
          let (args, inner) ← renameBind [] (carried.map Prod.fst)
          let (_, inner) ← renameBind inner captures
          let nested ← normalizeBody symbols depth inner nested
          let (outputs, next) ← renameBind env outputs
          result := result ++ [.loop site count (args.zip initials) outerCaptures nested outputs]
          env := next
      | .ret values => result := result ++ [.ret (← renameRead env values)]
      | .yield values => result := result ++ [.yield (← renameRead env values)]
      | .stop site owner reason => result := result ++ [.stop site owner reason]
      | .incomplete site => result := result ++ [.incomplete site]
      | _ => throw "invalid-role-body"
    return result

def normalizeFunction (function : Function) : Result Function := do
  let (args, env) ← renameBind [] (function.arguments.map Prod.fst)
  return { function with
    arguments := args.zip (function.arguments.map Prod.snd)
    body := ← function.body.mapM (normalizeBody [] limits.depth env) }

def normalizeParticipant (symbols : Renaming) (participant : Participant) : Result Participant := do
  let (args, env) ← renameBind [] (participant.arguments.map Prod.fst)
  let parameters ← participant.parameters.mapM fun (name, parameter) => do
    match parameter with
    | .constant n => pure (name, Parameter.constant n)
    | .ingress bound selectors => do
        let selectors ← selectors.mapM fun s => do
          -- Each role's own selector is checked against its actual port names;
          -- redundant peer argument spellings are checked at that peer.
          let arguments ← if s.role == participant.role then renameRead env s.arguments else pure []
          return { s with arguments }
        pure (name, Parameter.ingress bound (selectors.mergeSort (fun a b => a.role ≤ b.role)))
  return { participant with
    name := participantKey participant.binding participant.role
    arguments := args.zip (participant.arguments.map Prod.snd)
    parameters := parameters.mergeSort (fun a b => a.1 ≤ b.1)
    body := ← normalizeBody symbols limits.depth env participant.body }


end Tools.Interactive
