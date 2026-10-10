import Tools.Interactive.Admission

/-! Independent canonical local expansion. This is a bounded executable adapter
for the stored-body model in `Zkc.Source.Definitions`, not an adequacy theorem
for the raw decoder or native pass. Calls introduce no executable charge/frame;
primitive order, guards, affine admission and occurrence paths are retained. -/

set_option autoImplicit false
namespace Tools.Interactive.Algorithms

def site (path : List (Name × Name)) (leaf : Name) : Result Name := do
  let components := (path.flatMap fun (call, callee) => [call, callee]) ++ [leaf]
  let name := components.foldl (fun acc part => acc ++ s!"_{part.utf8ByteSize}_{part}") "lc"
  ensure (Decode.validName name) "algorithm-origin-limit"
  return name

structure Origin where
  function : Name
  site : Name
  definition : Name
  originalSite : Name
  deriving BEq, Repr

structure State where
  work : Nat := 0
  next : Nat := 0
  code : List Instruction := []
  reserved : List Name := []
  origins : List (Name × Name × Name) := []

private def tick : StateT State Result Unit := do
  let state ← get
  ensure (state.work < limits.instructions) "algorithm-expansion-limit"
  set { state with work := state.work + 1 }

private def fresh : StateT State Result Name := do
  let state ← get
  let choices := (List.range (state.reserved.length + 1)).map fun i => s!"alg{state.next + i}"
  let some name := choices.find? fun name => !(state.reserved.contains name)
    | throw "algorithm-value-limit"
  set { state with next := state.next + state.reserved.length + 1 }
  return name

private def emit (instruction : Instruction) : StateT State Result Unit :=
  modify fun state => { state with code := instruction :: state.code }

private def terminate (body : List Instruction) (terminal : Option Instruction) : List Instruction :=
  body ++ terminal.toList

private def body (functions : List Function) (definitions : List (Name × Name)) : Nat → Function → List (Name × Name) →
    List (Name × Name) → Bool → StateT State Result (Option (List Name))
  | 0, _, _, _, _ => throw "algorithm-call-depth"
  | depth + 1, function, arguments, path, encode => do
      let some instructions := function.body | throw "algorithm-call-symbol"
      let mut env := arguments
      for instruction in instructions do
        tick
        match instruction with
        | .op label kernel attrs inputs outputs =>
            let inputs ← inputs.mapM fun n => lookup n env
            let renamed ← outputs.mapM fun _ => fresh
            let expandedSite ← if encode then site path label else pure label
            emit (.op expandedSite kernel attrs inputs renamed)
            modify fun state => { state with origins := (expandedSite, (definitions.lookup function.name).getD function.name, label) ::
                (if (definitions.lookup function.name).getD function.name != function.name then
                  [(expandedSite, function.name, label)] else []) ++ state.origins }
            env := outputs.zip renamed ++ env
        | .call label callee inputs outputs =>
            let callee ← lookup callee (functions.map fun f => (f.name, f))
            let inputs ← inputs.mapM fun n => lookup n env
            let some values ← body functions definitions depth callee ((callee.arguments.map Prod.fst).zip inputs)
              (path ++ [(label, (definitions.lookup callee.name).getD callee.name)]) true | return none
            ensure (values.length == outputs.length) "algorithm-call-signature"
            env := outputs.zip values ++ env
        | .variant label ty alternative payload output =>
            let payload ← payload.mapM fun n => lookup n env
            let renamed ← fresh
            emit (.variant (← if encode then site path label else pure label) ty alternative payload renamed)
            env := (output, renamed) :: env
        | .localMatch label input captures arms outputs =>
            let input ← lookup input env
            let captured ← captures.mapM fun n => lookup n env
            let outer := (← get).code
            let mut expanded := []
            for (alternative, payload, nested) in arms do
              modify fun state => { state with code := [] }
              let args ← payload.mapM fun _ => fresh
              let values ← body functions definitions depth { function with body := some nested }
                (payload.zip args ++ captures.zip captured) path encode
              let code := (← get).code.reverse
              let code := terminate code (values.map Instruction.yield)
              expanded := expanded ++ [(alternative, args, code)]
            modify fun state => { state with code := outer }
            let renamed ← outputs.mapM fun _ => fresh
            emit (.localMatch (← if encode then site path label else pure label) input captured.eraseDups expanded renamed)
            env := outputs.zip renamed ++ env
        | .stop label owner reason =>
            emit (.stop (← if encode then site path label else pure label) owner reason)
            return none
        | .conditional label condition captures yes no outputs =>
            let condition ← lookup condition env
            let captured ← captures.mapM fun n => lookup n env
            let outer := (← get).code
            modify fun state => { state with code := [] }
            let yesValues ← body functions definitions depth { function with body := some yes }
              (captures.zip captured) path encode
            let yes := terminate (← get).code.reverse (yesValues.map Instruction.yield)
            modify fun state => { state with code := [] }
            let noValues ← body functions definitions depth { function with body := some no }
              (captures.zip captured) path encode
            let no := terminate (← get).code.reverse (noValues.map Instruction.yield)
            modify fun state => { state with code := outer }
            let renamed ← outputs.mapM fun _ => fresh
            emit (.conditional (← if encode then site path label else pure label) condition captured.eraseDups yes no renamed)
            env := outputs.zip renamed ++ env
        | .forLoop label induction lower upper carried captures nested outputs =>
            let lower ← lookup lower env
            let upper ← lookup upper env
            let initial ← (carried.map Prod.snd).mapM fun n => lookup n env
            let captured ← captures.mapM fun n => lookup n env
            let index ← fresh
            let args ← carried.mapM fun _ => fresh
            let outer := (← get).code
            modify fun state => { state with code := [] }
            let values ← body functions definitions depth { function with body := some nested }
              ([(induction, index)] ++ (carried.map Prod.fst).zip args ++ captures.zip captured) path encode
            let nested := terminate (← get).code.reverse (values.map Instruction.yield)
            modify fun state => { state with code := outer }
            let renamed ← outputs.mapM fun _ => fresh
            emit (.forLoop (← if encode then site path label else pure label) index lower upper
              (args.zip initial) captured.eraseDups nested renamed)
            env := outputs.zip renamed ++ env
        | .ret values | .yield values => return some (← values.mapM fun n => lookup n env)
        | _ => throw "algorithm-call-context"
      throw "missing-return"

private def operationSites : Nat → List Instruction → List Name
  | 0, _ => []
  | depth + 1, code => code.flatMap fun i => match i with
    | .op site .. => [site]
    | .localMatch _ _ _ arms _ => arms.flatMap fun arm => operationSites depth arm.2.2
    | .conditional _ _ _ yes no _ => operationSites depth yes ++ operationSites depth no
    | .forLoop _ _ _ _ _ _ body _ => operationSites depth body
    | _ => []

def expandWithOrigins (source : Source) (executable : Bool := true)
    (definitions : List (Name × Name) := []) : Result (Source × List Origin) := do
  admitSource source executable
  let mut work := 0
  let mut functions := []
  let mut origins := []
  for function in source.functions do
    if function.body.isNone then
      functions := functions ++ [function]
    else
      let encode := !(localDependencies limits.depth (function.body.getD [])).isEmpty
      if !encode then
        let instructions := function.body.getD []
        work := work + instructionCount limits.depth instructions
        ensure (work ≤ limits.instructions) "algorithm-expansion-limit"
        functions := functions ++ [function]
        if (definitions.lookup function.name).getD function.name != function.name then
          origins := origins ++ (operationSites limits.depth instructions).map fun label => Origin.mk function.name label function.name label
        origins := origins ++ (operationSites limits.depth instructions).map fun label => Origin.mk function.name label ((definitions.lookup function.name).getD function.name) label
      else
        let args := function.arguments.map Prod.fst
        let (returns, state) ← (body source.functions definitions (limits.callDepth + 1) function (args.zip args) [] encode).run
          { work := work, reserved := args }
        work := state.work
        origins := origins ++ state.origins.reverse.map fun (site, definition, originalSite) =>
          Origin.mk function.name site definition originalSite
        functions := functions ++ [{ function with body := some (terminate state.code.reverse (returns.map Instruction.ret)) }]
  let result := { source with functions := functions }
  if source.functions.any (fun f => !(localDependencies limits.depth (f.body.getD [])).isEmpty) then
    admitSource result executable
  return (result, origins)

def expand (source : Source) (executable : Bool := true) : Result Source := do
  return (← expandWithOrigins source executable).1

end Tools.Interactive.Algorithms
