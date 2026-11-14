module

public import Zkc.Frontend.Static.Evaluate

@[expose] public section

set_option autoImplicit false

/-!
# Inference of static arguments (SP6)

The steps of SP6 that match a parameter type of a callee, with unknowns, against a closed type:
step 3 for types, 3a for modules, 4 for the equations of sizes, 5 for the retry, 7 for the check.
Which equations a call gives (steps 2 and 6) needs the types of its arguments: typing starts a
`Problem` with the callee's unknowns, calls `matchType` per argument in the order of the
parameters and on the result type, then `retry` and `finish`.

Parameter types and terms are read in their lowered form. A term is read in its context: its
file, and for the definition of an alias the lowered terms that the alias's parameters stand for
(`Context`). A size term is solved when it is one unknown, a sum or a difference with one known
side, or a power of a known base of at least 2; any other equation with an unknown is set aside
and tried again after each solution.
-/

namespace Zkc.Frontend.Static.Infer

open Syntax

/-- Where a term is read: its file, and the terms that the parameters of the aliases being
expanded stand for, each in its own context. -/
inductive Context where
  | context (file : FileId) (substitution : List (ParameterRef × Lowered.Expr × Context))
  deriving Inhabited

def Context.file (context : Context) : FileId :=
  match context with
  | .context file _ => file

def Context.lookup (context : Context) (reference : ParameterRef) : Option (Lowered.Expr × Context) :=
  match context with
  | .context _ substitution =>
    (substitution.find? (·.1 == reference)).map fun (_, term, inner) => (term, inner)

/-- An inference problem: the unknown parameters of a callee, the values found or fixed, the
equations set aside, and the values found twice that disagree. -/
structure Problem where
  /-- The callee, for messages. -/
  callee : DeclarationId
  unknowns : Array ParameterRef
  /-- The values of the parameters fixed by the place or written, and those found. -/
  known : StaticEnvironment := {}
  /-- Equations `term = n` that no step solves yet. -/
  setAside : Array (Context × Lowered.Expr × Nat) := #[]
  /-- A parameter found twice with different values: typing reports it at the argument. -/
  conflicts : Array (ParameterRef × StaticValue × StaticValue) := #[]
  /-- The module instance that `Self` is in the callee's types: for a member of an interface,
  the module it is called at. A type member of it is its definition (SP8, TY3). -/
  self? : Option InstanceId := none
  deriving Inhabited

namespace Problem

def isUnknown (problem : Problem) (reference : ParameterRef) : Bool :=
  problem.unknowns.contains reference && !problem.known.contains reference

def remaining (problem : Problem) : Array ParameterRef :=
  problem.unknowns.filter (!problem.known.contains ·)

/-- Records a value found for a parameter; a second, different value is a conflict. -/
def solve (problem : Problem) (reference : ParameterRef) (value : StaticValue) : Problem :=
  match problem.known[reference]? with
  | some earlier =>
    if earlier == value then problem
    else { problem with conflicts := problem.conflicts.push (reference, earlier, value) }
  | none => { problem with known := problem.known.insert reference value }

end Problem

/-- The exponent `k` with `base ^ k = value`, when there is one; a base below 2 determines no
exponent (`1 ^ k = 1` for every `k`). -/
def logarithm (base value : Nat) : Option Nat := Id.run do
  if base < 2 then return none
  if value == 0 then return none
  let mut current := value
  let mut exponent := 0
  while current % base == 0 do
    current := current / base
    exponent := exponent + 1
  return if current == 1 then some exponent else none

/-- The single parameter a term names, when it is one. -/
def parameterOf : Lowered.Expr → Option ParameterRef
  | .reference reference => reference.parameter?
  | _ => none

/-- The parameters that a term names alone, anywhere in it. -/
def exprParameters (term : Lowered.Expr) : Array ParameterRef :=
  term.references.filterMap (·.parameter?)

/-- The parameters that a type names alone, anywhere in it. -/
def typeParameters (type : Lowered.TypeTerm) : Array ParameterRef :=
  type.references.filterMap (·.parameter?)

/-- The written terms of a reference, by the parameters of the declaration they give: the
parameters that the reference's own segment covers, positionally then by name. -/
def writtenTerms (declarationId : DeclarationId) (args : Option (Array Lowered.StaticArgument))
    (shared : ParameterRef → Bool) : CompileM (Array (ParameterRef × Lowered.Expr)) := do
  let program ← program
  let found ← declaration declarationId
  let candidates := (deployedParameters program found).filter fun (reference, _) => !shared reference
  let some list := args | return #[]
  let mut result := #[]
  let mut position := 0
  for arg in list do
    match arg with
    | .term _ none term =>
      if let some (reference, _) := candidates[position]? then result := result.push (reference, term)
      position := position + 1
    | .term _ (some name) term =>
      if let some (reference, _) := candidates.find? (·.2.name.text == name) then
        result := result.push (reference, term)
    | .inferred _ none => position := position + 1
    | _ => pure ()
  return result

/-- The terms of static arguments, in the order written. -/
def argumentTerms (arguments : Array Lowered.StaticArgument) : Array Lowered.Expr :=
  arguments.filterMap fun
    | .term _ _ term => some term
    | _ => none

mutual
  /-- The value of a size term when it has no unknown. -/
  partial def termValue (problem : Problem) (context : Context) (term : Lowered.Expr) :
      CompileM (Option Nat) := do
    match term with
    | .number _ value => return some value
    | .operator span operator #[left, right] =>
      match operator with
      | .add | .subtract | .multiply | .divide | .power =>
        let some a ← termValue problem context left | return none
        let some b ← termValue problem context right | return none
        -- a product and a power are within the budget of static evaluation, as in a size
        match operator with
        | .add => return some (a + b)
        | .subtract => return if b <= a then some (a - b) else none
        | .multiply => return some (← withStaticEvaluation (staticProduct span (textAt span) a b))
        | .divide => return if 1 <= b && a % b == 0 then some (a / b) else none
        | _ => return some (← withStaticEvaluation (staticPower span (textAt span) a b))
      | _ => return none
    | .reference _ | .local .. =>
      if let some reference := parameterOf term then
        if let some (substituted, inner) := context.lookup reference then
          return ← termValue problem inner substituted
        if problem.isUnknown reference then return none
        match problem.known[reference]? with
        | some (.natural value) => return some value
        | _ => return none
      -- a static name or a member: evaluated where no unknown occurs in it
      let env : Env := { file := context.file, values := problem.known }
      recover (some <$> evalSize env term) (pure none) (waits := true)
    | .call .. =>
      let env : Env := { file := context.file, values := problem.known }
      recover (some <$> evalSize env term) (pure none) (waits := true)
    | _ => return none

  /-- Step 4: an equation `term = n`. A parameter that is one of the unknowns is solved, or,
  found already, checked against the value found (step 7). -/
  partial def solveSize (problem : Problem) (context : Context) (term : Lowered.Expr) (n : Nat) :
      CompileM Problem := do
    if let some reference := parameterOf term then
      if let some (substituted, inner) := context.lookup reference then
        return ← solveSize problem inner substituted n
      if problem.unknowns.contains reference then return problem.solve reference (.natural n)
    if (← termValue problem context term).isSome then return problem
    match term with
    | .operator _ .add #[left, right] =>
      if let some a ← termValue problem context left then
        if a <= n then return ← solveSize problem context right (n - a)
        return problem
      if let some b ← termValue problem context right then
        if b <= n then return ← solveSize problem context left (n - b)
        return problem
      return { problem with setAside := problem.setAside.push (context, term, n) }
    | .operator _ .subtract #[left, right] =>
      if let some a ← termValue problem context left then
        if n <= a then return ← solveSize problem context right (a - n)
        return problem
      if let some b ← termValue problem context right then
        return ← solveSize problem context left (n + b)
      return { problem with setAside := problem.setAside.push (context, term, n) }
    | .operator _ .power #[base, exponent] =>
      -- the exponent is solved only for a base of at least 2, where it is unique; otherwise the
      -- equation is set aside (SP6)
      if let some a ← termValue problem context base then
        if a ≥ 2 then
          if let some k := logarithm a n then return ← solveSize problem context exponent k
          return problem
      return { problem with setAside := problem.setAside.push (context, term, n) }
    | _ => return { problem with setAside := problem.setAside.push (context, term, n) }

  /-- Step 3: a parameter type against a closed type. -/
  partial def matchType (problem : Problem) (context : Context) (parameter : Lowered.TypeTerm)
      (actual : ClosedType) : CompileM Problem := do
    match parameter, actual with
    | .nonzero _ inner, .nonzero other => matchType problem context inner other
    | .nonzero _ inner, other => matchType problem context inner other
    | .sequence _ element (some size), .seq other (some n) => do
      let problem ← matchType problem context element other
      solveSize problem context size n
    | .sequence _ element none, .seq other _ => matchType problem context element other
    | .index _ size, .index n => solveSize problem context size n
    | .tuple _ fields _, .tuple components _ =>
      if fields.size != components.size then return problem
      let mut problem := problem
      for (field, component) in fields.zip components do
        problem ← matchType problem context field component
      return problem
    | .reference reference, _ => matchReference problem context reference (.type actual)
    | _, _ => return problem

  /-- Steps 3 and 3a for a reference: an unknown parameter is solved; an alias is its definition
  with its parameters standing for the written terms; two applications of one record, variant,
  type of the vocabulary, `spec type` or module are matched argument by argument. -/
  partial def matchReference (problem : Problem) (context : Context) (reference : Lowered.Reference)
      (actual : StaticValue) : CompileM Problem := do
    let state ← get
    let .reference _ segments := reference
    let steps : List Step := segments.toList.map fun (.segment step _ _) => step
    let lastArguments : Option (Array Lowered.StaticArgument) :=
      segments.back?.bind fun (.segment _ arguments _) => arguments
    -- a type member of the module that `Self` or a known module parameter stands for: its
    -- definition, an alias or a record with the member's parameters (SP8, TY3)
    let memberDefinition (inst : InstanceId) (name : String) : Option DeclarationId :=
      match state.table.content? inst with
      | some (.«module» _ members) =>
        match (members.find? (·.1 == name)).map (·.2) with
        | some (MemberValue.definition id) => some id
        | _ => none
      | _ => none
    let target : Option (DeclarationId × Option (Array Lowered.StaticArgument)) := match steps with
      | [.self _, .member name _] =>
        (problem.self?.bind (memberDefinition · name)).map fun id => (id, lastArguments)
      | [.parameter reference, .member name _] =>
        match problem.known[reference]? with
        | some (.«module» inst) => (memberDefinition inst name).map fun id => (id, lastArguments)
        | _ => none
      | _ => match segments.back? with
        | some (.segment (.declaration id) arguments _) => some (id, arguments)
        | _ => none
    -- two applications of one fresh type member are matched argument by argument (SP12)
    let moduleOf : Option InstanceId := match steps with
      | [.self _, .member ..] => problem.self?
      | [.parameter reference, .member ..] =>
        match problem.known[reference]? with
        | some (.«module» inst) => some inst
        | _ => none
      | _ => none
    if let (some inst, .type (.«opaque» other member arguments _)) := (moduleOf, actual) then
      let lastName : Option String := match steps.getLast? with
        | some (Step.member name _) => some name
        | _ => none
      if inst == other && lastName == some member then
        let mut problem := problem
        for (term, value) in (argumentTerms (lastArguments.getD #[])).zip arguments do
          problem ← matchTerm problem context term value
        return problem
    match steps with
    | [.parameter reference] =>
      if let some (substituted, inner) := context.lookup reference then
        return ← matchTerm problem inner substituted actual
      if problem.unknowns.contains reference then return problem.solve reference actual
      return problem
    | _ =>
      let some (id, args) := target | return problem
      let found ← declaration id
      -- the written arguments of a type member give the member's own parameters (SP8)
      let ofMember := match steps with
        | [.self _, .member ..] | [.parameter _, .member ..] => true
        | _ => false
      let shared (reference : ParameterRef) : Bool :=
        problem.unknowns.contains reference || problem.known.contains reference ||
          (ofMember && some reference.scope != found.ownScope)
      let written ← writtenTerms id args shared
      let substitution : List (ParameterRef × Lowered.Expr × Context) :=
        written.toList.map fun (reference, term) => (reference, term, context)
      let inner : Context := .context found.file substitution
      let content := ((← getModules).lowered? id).map (·.content)
      match content, actual with
      | some (Lowered.Content.alias definition), .type closed => matchType problem inner definition closed
      | some (Lowered.Content.vocabularyType row arguments), .type (.nominal other values) =>
        if row != other then return problem
        let mut problem := problem
        for (term, value) in (argumentTerms arguments).zip values do
          problem ← matchTerm problem inner term value
        return problem
      | _, .type (.record inst) | _, .type (.«variant» inst) | _, .type (.specification inst)
      | _, .«module» inst =>
        let some entry := state.table.entries[inst]? | return problem
        if entry.key.declaration != id then return problem
        let parameters := deployedParameters state.program found
        let mut problem := problem
        for ((reference, _), value) in parameters.zip entry.key.arguments do
          match written.find? (·.1 == reference) with
          | some (_, term) => problem ← matchTerm problem context term value
          | none =>
            if problem.isUnknown reference then problem := problem.solve reference value
        return problem
      | _, _ => return problem

  /-- A static term against a value, by the value's class. -/
  partial def matchTerm (problem : Problem) (context : Context) (term : Lowered.Expr)
      (actual : StaticValue) : CompileM Problem := do
    match actual with
    | .natural n => solveSize problem context term n
    | .type closed =>
      match asType term with
      | some type => matchType problem context type closed
      | none => return problem
    | .«module» _ =>
      match term with
      | .reference reference => matchReference problem context reference actual
      | _ => return problem
end

/-- Step 5: the equations set aside are tried again, in order, until a pass solves nothing. -/
partial def retry (problem : Problem) : CompileM Problem := do
  let before := problem.remaining.size
  let pending := problem.setAside
  let mut current := { problem with setAside := #[] }
  for (context, term, n) in pending do
    current ← solveSize current context term n
  if current.remaining.size < before then retry current else return current

/-- Step 7: every unknown has a value, or the reference is refused. -/
def finish (problem : Problem) (place : Span) : CompileM StaticEnvironment := do
  let program ← program
  let name := program.nameOf problem.callee
  for reference in problem.remaining do
    let parameter := ((program.scopes[reference.scope]?).bind (·.parameters[reference.index]?))
    let parameterName := (parameter.map (·.name.text)).getD "?"
    refuse "SP6" place s!"cannot infer `{parameterName}` of `{name}`; write `{name}<{parameterName} = …>`"
  return problem.known

/-- A problem for a callee: its parameters that the given values do not fix are unknown. -/
def startProblem (callee : DeclarationId) (fixed : StaticEnvironment) : CompileM Problem := do
  let program ← program
  let found ← declaration callee
  let unknowns := (deployedParameters program found).filterMap fun (reference, _) =>
    if fixed.contains reference then none else some reference
  return { callee, unknowns, known := fixed }

end Zkc.Frontend.Static.Infer
