module

public import Zkc.Executable.Execution
public import Zkc.Source.Structured.Admission

@[expose] public section

/-! Structural admission of a whole `zkc.program/0` artifact.

`ProgramArtifact.admit` admits or refuses a decoded program for the profile
this reader claims, and names each refusal with its class from the program byte
language (`docs/spec/formats/program-bytes.md`, "Refusal classes"). It reads
the declarations, every body, including unused functions and untaken arms, and
the entries:

* declarations: distinct binding symbols, one namespace of function,
  participant and entry names, distinct formals, participant service ports that
  name distinct inputs and no formal, distinct participant identities, and entry
  role maps that select declared participants of one instance at their roles;
* participant bodies, typed by their physical types: every loop body and arm is
  a nested lexical environment that sees only its formals; a body binds each
  name once and never binds a service port; sites are unique in the participant
  and a message schema has one type in its instance; operands are visible and an
  affine value is used once; a loop counts with an index and captures copyable
  values only; a branch condition is Boolean, its capture rows move affine
  parents and may share a copyable parent, its formals are distinct, and its arms
  yield the same types; calls match the callee's signature; a receive is
  addressed to a peer at a wire type; a loop body or arm ends with its yield and
  the participant body with its return of the declared results;
* local bodies, by name and by the types the body knows (formals, Boolean
  literals and what they are carried, captured or yielded as): operands and
  captures are visible, an affine value is used once and is never captured by
  an iteration, a body binds each name once, bindings are declared, a known
  condition is Boolean, known yields and returns have the expected types,
  explicit stops name a known reason, and a body ends with its sole
  terminator.

It does not check the types of operation results in local bodies (they need the
installed signature of every binding), operation attributes, the installed
catalog or any carrier bound: the native decoder that produced the decoded program checks those, and
this reader claims none of them. Programs that use an instruction or type
outside its vocabulary refuse with `outside` and the instruction's name.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction

/-- The refusal classes of the program byte language, and `outside` for a
well-formed program this reader does not claim. -/
inductive AdmissionClass where
  | syntax
  | namesAndSsa
  | types
  | affineUse
  | unsupportedProfile
  | outside
  deriving DecidableEq, Repr

/-- A refusal: its class and a reader-specific reason. -/
structure AdmissionRefusal where
  kind : AdmissionClass
  reason : String
  deriving DecidableEq, Repr

abbrev Admitting := Except AdmissionRefusal

def refuse {α : Type} (kind : AdmissionClass) (reason : String) : Admitting α :=
  .error ⟨kind, reason⟩

/-- Whether a value of the type may be read more than once: data other than a
custody permission, and coordinates. The transcript is affine. -/
def PhysicalType.copyable (type : PhysicalType) : Bool :=
  match type.sort with
  | .data ty => !ty.isCustody
  | .indices => true
  | .transcript _ => false

/-- Whether a message may carry a value of the type: data other than a custody
permission. -/
def PhysicalType.wire (type : PhysicalType) : Bool :=
  match type.sort with
  | .data ty => !ty.isCustody
  | _ => false

/-- The names one participant body sees, with their types, and its affine names
already used. A nested body starts with its formals only. -/
structure BodyScope where
  names : List (String × PhysicalType) := []
  used : List String := []

/-- What admission threads through a participant: the sites it has used, and,
for the whole program, the type of every message schema of an instance. -/
structure AdmissionState where
  sites : List String := []
  schemas : List ((String × String) × PhysicalType) := []

def AdmissionState.site (state : AdmissionState) (site : String) : Admitting AdmissionState :=
  if state.sites.contains site then refuse .namesAndSsa "interactive-site"
  else pure { state with sites := site :: state.sites }

def AdmissionState.schema (state : AdmissionState) (entry schema : String) (type : PhysicalType) :
    Admitting AdmissionState :=
  match state.schemas.lookup (entry, schema) with
  | some known => if known = type then pure state else refuse .types "interactive-schema-type"
  | none => pure { state with schemas := ((entry, schema), type) :: state.schemas }

/-- Use an operand: it must be visible, and an affine one is used once. -/
def BodyScope.use (scope : BodyScope) (name : String) : Admitting (PhysicalType × BodyScope) :=
  match scope.names.lookup name with
  | none => refuse .namesAndSsa "interactive-unavailable"
  | some type =>
    if scope.used.contains name then refuse .affineUse "interactive-resource-reuse"
    else if type.copyable then pure (type, scope)
    else pure (type, { scope with used := name :: scope.used })

def BodyScope.useAll (scope : BodyScope) : List String → Admitting (List PhysicalType × BodyScope)
  | [] => pure ([], scope)
  | name :: rest => do
    let (type, scope) ← scope.use name
    let (types, scope) ← scope.useAll rest
    pure (type :: types, scope)

/-- Bind a name in a body: once, and never a service port. -/
def BodyScope.bind (services : List String) (scope : BodyScope) (name : String) (type : PhysicalType)
    (reason : String := "interactive-ssa") : Admitting BodyScope :=
  if services.contains name then refuse .namesAndSsa "service-port-interface"
  else if (scope.names.lookup name).isSome then refuse .namesAndSsa reason
  else pure { scope with names := (name, type) :: scope.names }

def BodyScope.bindAll (services : List String) (scope : BodyScope) :
    List String → List PhysicalType → Admitting BodyScope
  | [], [] => pure scope
  | name :: names, type :: types => do
    let scope ← scope.bind services name type
    scope.bindAll services names types
  | _, _ => refuse .types "interactive-shape"

/-- The participant instructions of the byte language outside this reader's
vocabulary. Any other unknown instruction belongs to no participant grammar. -/
def participantOutside : List String := ["send", "query", "return_if"]

/-- The local instructions of the byte language outside this reader's
vocabulary. -/
def localOutside : List String := ["variant", "match", "for_while", "release"]

section Participants
variable (program : ProgramArtifact) (definition : ParticipantDefinition)

/-- The participant's service port names. -/
def ParticipantDefinition.serviceNames (definition : ParticipantDefinition) : List String :=
  definition.services.map (·.name)

mutual
/-- Admit a participant body: `nested` for a loop body or an arm, which ends with
its yield, as opposed to the participant's body, which ends with its return.
The result is the types the terminator hands back. -/
def admitActions (nested : Bool) :
    List Action → BodyScope → AdmissionState → Admitting (List PhysicalType × AdmissionState)
  | [], _, _ => refuse .syntax "interactive-body"
  | [.yield values], scope, state =>
    if nested then do
      let (types, _) ← scope.useAll values
      pure (types, state)
    else refuse .syntax "interactive-return"
  | [.ret values], scope, state =>
    if nested then refuse .syntax "interactive-return"
    else do
      let (types, _) ← scope.useAll values
      if types = definition.results then pure (types, state) else refuse .types "interactive-return"
  | .yield _ :: _ :: _, _, _ | .ret _ :: _ :: _, _, _ => refuse .syntax "interactive-terminator"
  | action :: rest, scope, state => do
    let (scope, state) ← admitAction action scope state
    admitActions nested rest scope state

/-- Admit one participant instruction that does not end its body. -/
def admitAction :
    Action → BodyScope → AdmissionState → Admitting (BodyScope × AdmissionState)
  | .receive site schema peer output type, scope, state => do
    let state ← state.site site
    if peer = definition.role then refuse .namesAndSsa "interactive-peer"
    else if !type.wire then refuse .types "interactive-receive"
    else do
      let scope ← scope.bind definition.serviceNames output type
      let state ← state.schema definition.entry schema type
      pure (scope, state)
  | .call site function inputs outputs, scope, state => do
    let state ← state.site site
    match program.functions.find? (·.symbol = function) with
    | none => refuse .namesAndSsa "interactive-local-symbol"
    | some callee =>
      let (types, scope) ← scope.useAll inputs
      if types = callee.inputs.map (·.2) then do
        let scope ← scope.bindAll definition.serviceNames outputs callee.results
        pure (scope, state)
      else refuse .types "interactive-local-signature"
  | .loop site count _ induction carried captures body outputs, scope, state => do
    let state ← state.site site
    let (counter, scope) ← scope.use count
    if counter.sort ≠ .data .index then refuse .types "interactive-loop-count"
    else do
      let inner ← ({} : BodyScope).bind definition.serviceNames induction counter "interactive-loop-count"
      let (types, scope) ← scope.useAll (carried.map (·.2))
      let inner ← (carried.map (·.1)).zip types |>.foldlM
        (fun inner (formal, type) => inner.bind definition.serviceNames formal type "interactive-loop-input") inner
      let inner ← captures.foldlM (fun inner row => do
          match scope.names.lookup row.parent with
          | none => refuse .namesAndSsa "interactive-loop-capture"
          | some type =>
            if type.copyable then inner.bind definition.serviceNames row.formal type "interactive-loop-capture"
            else refuse .affineUse "interactive-loop-capture") inner
      let (yielded, state) ← admitActions true body inner state
      if yielded = types then do
        let scope ← scope.bindAll definition.serviceNames outputs types
        pure (scope, state)
      else refuse .types "interactive-return"
  | .cond site condition captures yes no outputs, scope, state => do
    let state ← state.site site
    let (selector, scope) ← scope.use condition
    if selector.sort ≠ .data .boolean then refuse .types "local-if-condition"
    else do
      let (types, scope) ← scope.useAll (captures.map (·.parent))
      let inner ← (captures.map (·.formal)).zip types |>.foldlM
        (fun inner (formal, type) => inner.bind definition.serviceNames formal type "interactive-branch-capture")
        ({} : BodyScope)
      let (left, state) ← admitActions true yes inner state
      let (right, state) ← admitActions true no inner state
      if left = right then do
        let scope ← scope.bindAll definition.serviceNames outputs left
        pure (scope, state)
      else refuse .types "local-if-yield"
  | .select site input _ _ _, scope, state => do
    let _ ← state.site site
    let _ ← scope.use input
    -- No physical type of this vocabulary is a variant.
    refuse .types "variant-type"
  | .yield _, _, _ | .ret _, _, _ => refuse .syntax "interactive-terminator"
  | .unsupported name, _, _ =>
    if participantOutside.contains name then refuse .outside name
    else refuse .syntax "interactive-instruction"
end

end Participants

section Locals
variable (program : ProgramArtifact)

/-- The names one local body sees, with their types where the body knows them
(formals, Boolean literals, induction variables, and what a known value is
carried or captured as), and its affine names already used. An operation's
results have its installed binding's types, which this reader does not
resolve. -/
structure LocalScope where
  names : List (String × Option PhysicalType) := []
  used : List String := []

/-- Use a local operand: it must be visible, and an affine one is used once. -/
def LocalScope.use (scope : LocalScope) (name : String) : Admitting (Option PhysicalType × LocalScope) :=
  match scope.names.lookup name with
  | none => refuse .namesAndSsa "interactive-unavailable"
  | some type =>
    if scope.used.contains name then refuse .affineUse "interactive-resource-reuse"
    else if type.all PhysicalType.copyable then pure (type, scope)
    else pure (type, { scope with used := name :: scope.used })

def LocalScope.useAll (scope : LocalScope) : List String → Admitting (List (Option PhysicalType) × LocalScope)
  | [] => pure ([], scope)
  | name :: rest => do
    let (type, scope) ← scope.use name
    let (types, scope) ← scope.useAll rest
    pure (type :: types, scope)

/-- Bind a local name once. -/
def LocalScope.bind (scope : LocalScope) (name : String) (type : Option PhysicalType)
    (reason : String := "interactive-ssa") : Admitting LocalScope :=
  if (scope.names.lookup name).isSome then refuse .namesAndSsa reason
  else pure { scope with names := (name, type) :: scope.names }

def LocalScope.bindAll (scope : LocalScope) (bound : List (String × Option PhysicalType))
    (reason : String := "interactive-ssa") : Admitting LocalScope :=
  bound.foldlM (fun scope (name, type) => scope.bind name type reason) scope

def siteOf (sites : List String) (site : String) : Admitting (List String) :=
  if sites.contains site then refuse .namesAndSsa "interactive-site" else pure (site :: sites)

/-- The Boolean literal's physical type. -/
def nativeBoolean : PhysicalType := ⟨.data .boolean, "native.bool/0"⟩

/-- Types two value lists may both have: equal lengths, and equal types where
both are known. -/
def compatibleTypes : List (Option PhysicalType) → List (Option PhysicalType) → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
    (match left, right with | some left, some right => left = right | _, _ => true) &&
      compatibleTypes lefts rights
  | _, _ => false

mutual
/-- Admit a local body: `top` for a function body, which ends with its return,
as opposed to a region, which ends with its yield; either may end with an
explicit stop. The result is the types of the returned or yielded values, or
`none` after a stop, and the sites used so far in the function. -/
def admitSteps (top : Bool) : List Step → LocalScope → List String →
    Admitting (Option (List (Option PhysicalType)) × List String)
  | [], _, _ => refuse .syntax "interactive-body"
  | [.ret values], scope, sites =>
    if top then do let (types, _) ← scope.useAll values; pure (some types, sites)
    else refuse .syntax "local-terminal-context"
  | [.yield values], scope, sites =>
    if top then refuse .syntax "local-terminal-context"
    else do let (types, _) ← scope.useAll values; pure (some types, sites)
  | [.stop site reason], _, sites => do
    let sites ← siteOf sites site
    match stopReason? reason with
    | some _ => pure (none, sites)
    | none => refuse .syntax "interactive-stop-reason"
  | .yield _ :: _ :: _, _, _ | .ret _ :: _ :: _, _, _ | .stop .. :: _ :: _, _, _ =>
    refuse .syntax "interactive-terminator"
  | step :: rest, scope, sites => do
    let (scope, sites) ← admitStep step scope sites
    admitSteps top rest scope sites

/-- Admit one local instruction that does not end its body. -/
def admitStep : Step → LocalScope → List String → Admitting (LocalScope × List String)
  | .operation site binding _ inputs outputs, scope, sites => do
    let sites ← siteOf sites site
    if (program.bindings.map (·.symbol)).contains binding then do
      let (_, scope) ← scope.useAll inputs
      pure (← scope.bindAll (outputs.map (·, none)), sites)
    else refuse .namesAndSsa "binding-reference"
  | .constant site output _, scope, sites => do
    let sites ← siteOf sites site
    pure (← scope.bind output (some nativeBoolean), sites)
  | .cond site condition captures yes no outputs, scope, sites => do
    let sites ← siteOf sites site
    let (selector, scope) ← scope.use condition
    if selector.any (·.sort ≠ .data .boolean) then refuse .types "local-if-condition" else
    -- Captures move affine values into the regions.
    let (types, scope) ← scope.useAll captures
    let inner ← ({} : LocalScope).bindAll (captures.zip types) "local-control-capture"
    let (left, sites) ← admitSteps false yes inner sites
    let (right, sites) ← admitSteps false no inner sites
    match left, right with
    | some left, some right =>
      if compatibleTypes left right then pure (← scope.bindAll (outputs.zip left), sites)
      else refuse .types "local-if-yield"
    | some yielded, none | none, some yielded => pure (← scope.bindAll (outputs.zip yielded), sites)
    | none, none =>
      if outputs.isEmpty then pure (scope, sites) else refuse .types "local-terminal-outputs"
  | .iterate site induction lower upper carried captures body outputs, scope, sites => do
    let sites ← siteOf sites site
    let (bounds, scope) ← scope.useAll [lower, upper]
    let (types, scope) ← scope.useAll (carried.map (·.2))
    let inner ← ({} : LocalScope).bind induction bounds.head?.join "local-for-induction"
    let inner ← inner.bindAll ((carried.map (·.1)).zip types) "local-for-input"
    -- An iteration reads its captures in every iteration: copyable values only.
    let inner ← captures.foldlM (fun inner name => do
        match scope.names.lookup name with
        | none => refuse .namesAndSsa "local-control-capture"
        | some type =>
          if scope.used.contains name || !type.all PhysicalType.copyable then
            refuse .affineUse "local-control-capture"
          else inner.bind name type "local-control-capture") inner
    let (yielded, sites) ← admitSteps false body inner sites
    if yielded.all (compatibleTypes types) then pure (← scope.bindAll (outputs.zip types), sites)
    else refuse .types "local-yield-types"
  | .stop .., _, _ | .yield _, _, _ | .ret _, _, _ => refuse .syntax "interactive-terminator"
  | .unsupported name, _, _ =>
    if localOutside.contains name then refuse .outside name
    else refuse .syntax "interactive-instruction"
end

end Locals

/-- Check every element, in order. -/
def admitEach {α : Type} (check : α → Admitting Unit) : List α → Admitting Unit
  | [] => pure ()
  | value :: rest => do check value; admitEach check rest

/-- A participant's interface: distinct formals; service ports with distinct
names that are not formals, naming distinct inputs of the complete interface. -/
def ParticipantDefinition.admitInterface (definition : ParticipantDefinition) : Admitting Unit := do
  let formals := definition.inputs.map (·.1)
  if !formals.Nodup then refuse .namesAndSsa "interactive-argument"
  else if !(formals ++ definition.serviceNames).Nodup then refuse .namesAndSsa "service-port-interface"
  else if !(definition.services.map (·.input)).Nodup ||
      !definition.services.all (·.input < definition.inputs.length + definition.services.length) then
    refuse .namesAndSsa "service-port-interface"
  else pure ()

/-- An entry: a nonempty role map with distinct roles, whose participants are
declared at those roles and serve one instance. -/
def ProgramEntry.admit (program : ProgramArtifact) (entry : ProgramEntry) : Admitting Unit := do
  if entry.roles.isEmpty then refuse .syntax "interactive-entry-targets"
  else if !(entry.roles.map (·.1)).Nodup then refuse .namesAndSsa "interactive-binding"
  else
    let selected := entry.roles.map fun (role, symbol) =>
      (program.participants.find? (·.symbol = symbol)).filter (·.role = role)
    if !selected.all Option.isSome then refuse .namesAndSsa "interactive-entry-role"
    else if !((selected.filterMap id).map (·.entry)).eraseDups.length ≤ 1 then
      refuse .namesAndSsa "interactive-entry-instance"
    else pure ()

/-- Admit a decoded program for the profile this reader claims. -/
def ProgramArtifact.admit (program : ProgramArtifact) : Admitting Unit := do
  if !(program.bindings.map (·.symbol)).Nodup then refuse .namesAndSsa "interactive-binding"
  else if !(program.functions.map (·.symbol) ++ program.participants.map (·.symbol)).Nodup then
    refuse .namesAndSsa "interactive-duplicate-symbol"
  else if !program.functions.all (fun function => (function.inputs.map (·.1)).Nodup) then
    refuse .namesAndSsa "interactive-argument"
  else do
    admitEach (·.admitInterface) program.participants
    if !(program.participants.map fun definition => (definition.entry, definition.role)).Nodup then
      refuse .namesAndSsa "interactive-participant-identity"
    else do
      admitEach (fun function => do
        let (returned, _) ← admitSteps program true function.body
          { names := function.inputs.map fun (name, type) => (name, some type) } []
        if returned.all (compatibleTypes · (function.results.map some)) then pure ()
        else refuse .types "function-return-types") program.functions
      let _ ← program.participants.foldlM (fun (schemas : List ((String × String) × PhysicalType)) definition => do
          let scope ← ({} : BodyScope).bindAll definition.serviceNames (definition.inputs.map (·.1))
            (definition.inputs.map (·.2))
          let (_, state) ← admitActions program definition false definition.body scope { schemas }
          pure state.schemas) []
      if program.entries.isEmpty && (!program.participants.isEmpty || program.functions.isEmpty) then
        refuse .syntax "interactive-entry"
      else if program.participants.isEmpty && !program.entries.isEmpty then refuse .syntax "interactive-entry"
      else if !(program.functions.map (·.symbol) ++ program.participants.map (·.symbol) ++
          program.entries.map (·.name)).Nodup then
        refuse .namesAndSsa "interactive-entry-name"
      else admitEach (ProgramEntry.admit program) program.entries

end Zkc.Executable
