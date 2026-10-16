module

public import Zkc.Source.Structured.RepeatAdmission

@[expose] public section

namespace Zkc.Source.Structured

/-- Computational footprints over formal input positions. Requirements remain
individual: distinct calculations need not execute at the same participant.
For partial folds and Local helpers the footprints are conservative. -/
structure DependencySummary where
  helper : Helper
  results : List (List Nat)
  requirements : List (List Nat)
  «partial» : Bool
  depth : Nat := 0
  deriving Repr

namespace Availability

abbrev Footprint := List Nat

/-- SSA footprints are stored oldest first. Extending a context appends the
result tuple in reverse order, so de Bruijn index zero still names its head.
Persistent environments keep bind-local intermediates out of the continuation. -/
abbrev Environment := Array Footprint

/-- Representation-aware admission policy, not an exact runtime complexity
bound. Operations count stored traversal nodes, excluding marks; dependencies
charge indexed SSA access and incremental summary allocation/substitution/union;
replay charges participant scope processing. Dynamic execution has separate
bounds. In particular, reusing a summary does not expand its operation count. -/
structure Budget where
  operations : Nat := 100000
  dependencies : Nat := 1000000
  replay : Nat := 1000000

abbrev Analysis := StateT Budget (Except String)

def chargeOperations (work : Nat) : Analysis Unit := do
  let budget ← get
  if work > budget.operations then throw "structured-availability-operation-limit"
  set { budget with operations := budget.operations - work }

def chargeDependencies (work : Nat) : Analysis Unit := do
  let budget ← get
  if work > budget.dependencies then throw "structured-availability-dependency-limit"
  set { budget with dependencies := budget.dependencies - work }

def chargeReplay (work : Nat) : Analysis Unit := do
  let budget ← get
  if work > budget.replay then throw "structured-availability-replay-limit"
  set { budget with replay := budget.replay - work }

def noServices (types : List Ty) : Analysis Unit := do
  if types.any (fun ty => match ty with | .service _ => true | _ => false) then
    throw "structured-availability-service"

/-- Charge each membership search and copied prefix before constructing a union.
Repeated operands preserve set semantics, without identifying unknown values. -/
def union (left right : Footprint) : Analysis Footprint :=
  right.foldlM (fun acc index => do
    chargeDependencies (2 * acc.length + 1)
    if acc.contains index then pure acc else pure (acc ++ [index])) left

def lookup (values : Environment) (index : Nat) : Analysis Footprint := do
  chargeDependencies 1
  if h : index < values.size then
    return values[values.size - 1 - index]'(by omega)
  else
    throw "structured-availability-operand"

/-- The caller charges for the result cells before extension. Array persistence
may copy storage; the budget does not assert an exact allocation bound. -/
def extendEnvironment (environment : Environment) (results : List Footprint) : Environment :=
  results.foldr (fun result values => values.push result) environment

/-- Initialize formal input footprints using exposed structural recursion, so
admission remains reducible in downstream public module proofs. -/
def inputEnvironment (count : Nat) : Environment :=
  fill count #[]
where
  fill : Nat → Environment → Environment
    | 0, environment => environment
    | remaining + 1, environment => fill remaining (environment.push [remaining])

def operands {context : List Ty} (values : Environment) :
    {types : List Ty} → Operands context types → Analysis (List Footprint)
  | _, .nil => pure []
  | _, .cons valueRef rest => do
    chargeDependencies 1
    let value ← lookup values valueRef.index
    return value :: (← operands values rest)

/-- Helper argument tuples retain formal-position order and list lookup costs;
unlike the SSA environment, they do not grow with the instruction sequence. -/
def argument (arguments : List Footprint) (index : Nat) : Analysis Footprint := do
  chargeDependencies (index + 1)
  match arguments[index]? with
  | some value => pure value
  | none => throw "structured-availability-operand"

/-- Both results and every intermediate requirement pass through this same
substitution. Work is charged before each new union or collection cell. -/
def substitute (arguments : List Footprint) (footprint : Footprint) : Analysis Footprint :=
  footprint.foldlM (fun result index => do union result (← argument arguments index)) []

def substitutions (arguments : List Footprint) (footprints : List Footprint) :
    Analysis (List Footprint) :=
  footprints.mapM fun footprint => do
    chargeDependencies 1
    substitute arguments footprint

def findSummary (summaries : List DependencySummary) (helper : Helper) :
    Analysis DependencySummary := do
  chargeDependencies (summaries.length + 1)
  let some summary := summaries.find? (·.helper.name == helper.name)
    | throw "structured-availability-helper-order"
  if summary.helper != helper then throw "structured-availability-helper-signature"
  if summary.results.length != helper.outputs.length then
    throw "structured-availability-helper-results"
  return summary

structure HelperWork where
  requirements : List Footprint := []
  «partial» : Bool := false
  depth : Nat := 0

abbrev Summarizing := StateT HelperWork Analysis

def visit : Summarizing Unit :=
  chargeOperations 1

def reference (summary : DependencySummary) : Summarizing Unit := do
  if summary.depth + 1 > 64 then throw "structured-availability-depth-limit"
  modify fun state => { state with
    depth := max state.depth (summary.depth + 1)
    «partial» := state.partial || summary.partial }

def require (footprint : Footprint) : Summarizing Unit := do
  chargeDependencies 1
  modify fun state => { state with requirements := footprint :: state.requirements }

def calculation (summaries : List DependencySummary) (op : Op)
    (arguments : List Footprint) : Summarizing (List Footprint) := do
  noServices op.arguments
  noServices op.results
  if !op.isCalculation then throw "structured-availability-math-operation"
  match op with
  | .invoke helper =>
    let summary ← findSummary summaries helper
    reference summary
    -- An empty result list must not skip intermediate requirements.
    for footprint in summary.requirements do
      require (← substitute arguments footprint)
    substitutions arguments summary.results
  | _ =>
    for helper in op.helpers do
      reference (← findSummary summaries helper)
    match op with
    | .fold _ | .boundedAt _ => modify fun state => { state with «partial» := true }
    | _ => pure ()
    let footprint ← (arguments.foldlM union [] : Analysis Footprint)
    require footprint
    chargeDependencies op.results.length
    return List.replicate op.results.length footprint

/-- Traverse the formed carrier directly, including lexical binds. There is no
source-level identity approximation or re-elaboration of an erased body. -/
def mathRegion (summaries : List DependencySummary) {context outputs : List Ty} :
    Region dialect context outputs → Environment → Summarizing (List Footprint)
  | .ret values, environment => do
    visit
    operands environment values
  | .stop _, _ => throw "structured-availability-math-stop"
  | .letOp (.mark _) _ _ next, environment =>
    mathRegion summaries next environment
  | .letOp op arguments _ next, environment => do
    visit
    let results ← calculation summaries op (← operands environment arguments)
    chargeDependencies results.length
    mathRegion summaries next (extendEnvironment environment results)
  | .bind body next, environment => do
    visit
    let results ← mathRegion summaries body environment
    chargeDependencies results.length
    mathRegion summaries next (extendEnvironment environment results)

mutual
  /-- Local semantics is checked elsewhere. Inspect every stored callback for
  capacity and exact references without expanding its result dependencies. -/
  def localRegion (summaries : List DependencySummary) {context outputs : List Ty} :
      Region dialect context outputs → Summarizing Unit
    | .ret _ | .stop _ => visit
    | .letOp (.mark _) _ _ next => localRegion summaries next
    | .letOp op _ bodies next => do
      visit
      noServices op.arguments
      noServices op.results
      for helper in op.helpers do
        reference (← findSummary summaries helper)
      localRegions summaries bodies
      localRegion summaries next
    | .bind body next => do
      visit
      localRegion summaries body
      localRegion summaries next

  def localRegions (summaries : List DependencySummary) {signatures} :
      Regions dialect signatures → Summarizing Unit
    | .nil => pure ()
    | .cons body rest => do
      localRegion summaries body
      localRegions summaries rest
end

def summarize (summaries : List DependencySummary) (definition : CheckedDefinition) :
    Analysis DependencySummary := do
  noServices definition.inputs
  noServices definition.outputs
  if summaries.any (·.helper.name == definition.name) then
    throw "structured-availability-helper-duplicate"
  chargeDependencies (2 * definition.inputs.length)
  let initial := inputEnvironment definition.inputs.length
  let computation : Summarizing (List Footprint) := match definition.kind with
    | .math => mathRegion summaries definition.body initial
    | .local => do
      -- Realization/map bodies retain Local strictness even when their Math
      -- helper projects an input or ignores a broadcast operand.
      localRegion summaries definition.body
      chargeDependencies (definition.inputs.length + definition.outputs.length + 1)
      let footprint := List.range definition.inputs.length
      require footprint
      modify fun state => { state with «partial» := true }
      pure (List.replicate definition.outputs.length footprint)
  let (results, state) ← computation.run {}
  chargeDependencies state.requirements.length
  return ⟨definition.helper, results, state.requirements.reverse, state.partial,
    state.depth⟩

/-- The caller supplies the checked order. A forward or mismatched reference
refuses instead of introducing another ordering authority. -/
def analyzeHelpers (definitions : List CheckedDefinition) : Analysis (List DependencySummary) := do
  let reversed ← definitions.foldlM (fun summaries definition => do
    let summary ← summarize summaries definition
    chargeDependencies 1
    pure (summary :: summaries)) []
  chargeDependencies reversed.length
  return reversed.reverse

def validScope (roles : Nat) (scope : List Nat) : Analysis Unit := do
  chargeReplay (1 + scope.length * (scope.length + 1))
  if scope.isEmpty || !scope.all (· < roles) || scope.eraseDups.length != scope.length then
    throw "structured-availability-scope"

def subset (requested available : List Nat) : Analysis Bool := do
  chargeReplay (1 + requested.length * (available.length + 1))
  return requested.all available.contains

def owned (roles owner : Nat) (arguments : List Footprint) : Analysis Unit := do
  if owner >= roles then throw "structured-availability-owner"
  for scope in arguments do
    if !(← subset [owner] scope) then throw "structured-availability-owned-operand"

/-- Empty dependencies denote the full roster. Each requirement is intersected
independently; unrelated requirements are never intersected with one another. -/
def available (roles : Nat) (arguments : List Footprint) (footprint : Footprint) :
    Analysis Footprint := do
  chargeReplay (roles + 1)
  footprint.foldlM (fun scope index => do
    chargeReplay (index + 1)
    let some operand := arguments[index]? | throw "structured-availability-operand"
    chargeReplay (1 + scope.length * (operand.length + 1))
    pure (scope.filter operand.contains)) (List.range roles)

def availableCalculation (summaries : List DependencySummary) (roles : Nat)
    (op : Op) (arguments : List Footprint) (active : List Nat := List.range roles) :
    Analysis (List Footprint) := do
  noServices op.arguments
  noServices op.results
  match op with
  | .invoke helper =>
    let summary ← findSummary summaries helper
    if roles > 1 && summary.partial then throw "structured-availability-partial-math"
    if summary.depth + 1 > 64 then throw "structured-availability-depth-limit"
    for footprint in summary.requirements do
      if ((← available roles arguments footprint).filter active.contains).isEmpty then
        throw "structured-availability-requirement"
    summary.results.mapM fun footprint => do
      chargeReplay 1
      return (← available roles arguments footprint).filter active.contains
  | _ =>
    match op with
    | .fold _ | .boundedAt _ =>
      if roles > 1 then throw "structured-availability-partial-math"
    | _ => pure ()
    for helper in op.helpers do
      let summary ← findSummary summaries helper
      if summary.depth + 1 > 64 then throw "structured-availability-depth-limit"
    chargeReplay arguments.length
    let scope := (← available roles arguments (List.range arguments.length)).filter active.contains
    if scope.isEmpty then throw "structured-availability-requirement"
    chargeReplay op.results.length
    return List.replicate op.results.length scope

/-- Callback footprints include the roster index, declared state scopes and
incoming capture footprints intersected with that roster, in exact ABI order. -/
def repeatInputs (roles : Nat) (spec : RepeatSpec) (arguments : List Footprint) :
    Analysis (List Footprint) := do
  validScope roles spec.roles
  if arguments.length != 1 + spec.state.length + spec.captures.length ||
      spec.stateScopes.length != spec.state.length then
    throw "structured-availability-port-scopes"
  noServices spec.state
  let count :: remaining := arguments | throw "structured-availability-operand"
  if !(← subset spec.roles count) then throw "structured-repeat-count-scope"
  for (scope, supplied) in spec.stateScopes.zip (remaining.take spec.state.length) do
    validScope roles scope
    if !(← subset scope spec.roles) || !(← subset scope supplied) then
      throw "structured-repeat-state-scope"
  let captures ← (remaining.drop spec.state.length).mapM fun supplied => do
    chargeReplay (1 + supplied.length * (spec.roles.length + 1))
    let scope := supplied.filter spec.roles.contains
    if scope.isEmpty then throw "structured-repeat-capture-scope"
    return scope
  chargeReplay (1 + spec.state.length + captures.length)
  return spec.roles :: (spec.stateScopes ++ captures)

def operation (summaries : List DependencySummary) (roster : List String)
    (op : ProtocolOp) (arguments : List Footprint)
    (active : List Nat := List.range roster.length) : Analysis (List Footprint) := do
  let roles := roster.length
  -- Full-roster transfer retains the original operation-specific diagnostics.
  if active != List.range roles then checkProtocolRoles active op
  match op with
  | .mark _ => pure ()
  | _ => chargeOperations 1
  match op with
  | .calculate op _ => availableCalculation summaries roles op arguments active
  | .repeat .. =>
    -- The region traversal must inspect the callback before exporting scopes.
    throw "structured-protocol-region"
  | .protocolApply signature indices _ =>
    if indices.length != signature.roles.length ||
        indices.eraseDups.length != indices.length || !indices.all (· < roles) then
      throw "structured-availability-substitution"
    if arguments.length != signature.inputs.length ||
        signature.inputScopes.length != signature.inputs.length ||
        signature.outputScopes.length != signature.outputs.length then
      throw "structured-availability-port-scopes"
    for scope in signature.inputScopes ++ signature.outputScopes do
      validScope signature.roles.length scope
    let mappedInputs := signature.inputScopes.map (List.map (fun role => indices[role]?.getD 0))
    for (requested, supplied) in mappedInputs.zip arguments do
      if !(← subset requested supplied) then throw "structured-availability-application-input"
    chargeReplay (signature.outputs.length + 1)
    return signature.outputScopes.map (List.map (fun role => indices[role]?.getD 0))
  | .localCall helper _ owner _ =>
    noServices helper.inputs
    noServices helper.outputs
    let summary ← findSummary summaries helper
    if summary.depth + 1 > 64 then throw "structured-availability-depth-limit"
    owned roles owner arguments
    chargeReplay (helper.outputs.length + 1)
    return List.replicate helper.outputs.length [owner]
  | .guard owner _ =>
    owned roles owner arguments
    return []
  | .exchange ty sender receiver _ =>
    noServices [ty]
    owned roles sender arguments
    if sender == receiver || receiver >= roles then throw "structured-availability-exchange"
    chargeReplay 3
    return [[sender, receiver]]
  | .restrict ty selected =>
    noServices [ty]
    validScope roles selected
    let [scope] := arguments | throw "structured-availability-operand"
    if !(← subset selected scope) then throw "structured-availability-restriction"
    chargeReplay 1
    return [selected]
  | .draw owner _ _ =>
    owned roles owner arguments
    chargeReplay 2
    return [[owner]]
  | .statement _ types selectors _ =>
    noServices types
    if selectors.length != arguments.length then throw "structured-availability-statement"
    chargeReplay (selectors.length * (roles + 1))
    for (scope, selector) in arguments.zip selectors do
      owned roles (roster.findIdx (· == selector)) [scope]
    return []
  | .mark _ => return []

def protocolRegionWith (summaries : List DependencySummary) (roster : List String)
    (active : List Nat) {context outputs : List Ty} :
    Region protocolDialect context outputs → Environment → Analysis (List Footprint)
  | .ret values, environment => do
    chargeOperations 1
    operands environment values
  | .stop _, _ => throw "structured-availability-protocol-stop"
  | .letOp (.repeat spec _) arguments (.cons body .nil) next, environment => do
    chargeOperations 1
    checkActiveRoles active spec.roles
    let inputs ← repeatInputs roster.length spec (← operands environment arguments)
    let yielded ← protocolRegionWith summaries roster spec.roles body (extendEnvironment #[] inputs)
    if yielded.length != spec.stateScopes.length then throw "structured-availability-port-scopes"
    for (requested, supplied) in spec.stateScopes.zip yielded do
      if !(← subset requested supplied) then throw "structured-repeat-yield-scope"
    chargeReplay spec.stateScopes.length
    protocolRegionWith summaries roster active next (extendEnvironment environment spec.stateScopes)
  | .letOp op arguments _ next, environment => do
    let results ← operation summaries roster op (← operands environment arguments) active
    chargeReplay results.length
    protocolRegionWith summaries roster active next (extendEnvironment environment results)
  | .bind body next, environment => do
    chargeOperations 1
    let results ← protocolRegionWith summaries roster active body environment
    chargeReplay results.length
    protocolRegionWith summaries roster active next (extendEnvironment environment results)

def protocolRegion (summaries : List DependencySummary) (roster : List String)
    {context outputs : List Ty} (body : Region protocolDialect context outputs)
    (environment : Environment) : Analysis (List Footprint) :=
  protocolRegionWith summaries roster (List.range roster.length) body environment

def checkRoot (summaries : List DependencySummary) (root : CheckedProtocol) : Analysis Unit := do
  if root.roles.isEmpty then throw "structured-availability-scope"
  if root.inputScopes.length != root.inputs.length ||
      root.outputScopes.length != root.outputs.length then
    throw "structured-availability-port-scopes"
  for scope in root.inputScopes do validScope root.roles.length scope
  for scope in root.outputScopes do validScope root.roles.length scope
  noServices root.outputs
  chargeReplay root.inputScopes.length
  let results ← protocolRegion summaries root.roles root.body (extendEnvironment #[] root.inputScopes)
  if results.length != root.outputScopes.length then throw "structured-availability-port-scopes"
  chargeReplay root.outputScopes.length
  for (requested, available) in root.outputScopes.zip results do
    if !(← subset requested available) then throw "structured-availability-output"

end Availability

/-- Analyze every helper, including unused Math/group declarations, in the
supplied checked order. This is independent of identity/bounds summaries. -/
def summarizeHelpers (definitions : List CheckedDefinition) : Except String (List DependencySummary) :=
  (Availability.analyzeHelpers definitions).run' {}

/-- Replay a previously computed helper table against one formed protocol. -/
def checkAvailability (summaries : List DependencySummary) (root : CheckedProtocol) : Except String Unit :=
  (Availability.checkRoot summaries root).run' {}

/-- The admission entry point shares budgets across all helpers and roots.
Equality with `.ok ()` records this computation, not a presence-soundness theorem. -/
def checkUnitAvailability (definitions : List CheckedDefinition) (roots : List CheckedProtocol) :
    Except String Unit :=
  (do
    let summaries ← Availability.analyzeHelpers definitions
    for root in roots do Availability.checkRoot summaries root).run' {}

/-- A Boolean success certificate suffices because availability returns no data.
Concrete clients can check this certificate directly in the kernel. -/
theorem checkUnitAvailability_ok_of_isOk {definitions : List CheckedDefinition}
    {roots : List CheckedProtocol}
    (accepted : (checkUnitAvailability definitions roots).isOk = true) :
    checkUnitAvailability definitions roots = .ok () := by
  cases result : checkUnitAvailability definitions roots with
  | error code => simp [result, Except.isOk, Except.toBool] at accepted
  | ok value => cases value; rfl

end Zkc.Source.Structured
