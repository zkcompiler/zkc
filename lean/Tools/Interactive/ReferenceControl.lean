import Tools.Interactive.ReferenceRuntime

/-! Resumable original-source traversal. Source cuts select which role advances;
transparent calls/loops advance only when that role is polled. Completing a cut
never polls its continuation. Root returns are observed only in the final lexical
role drain. No projected or compiled participant is read. -/

set_option autoImplicit false

namespace Tools.Interactive.Reference.SourceControl
open Control

structure RoleState where
  iterations : Nat := 0
  frames : List (State × List Value) := []

abbrev RoleM := StateT RoleState RunM

inductive Cut where
  | local (scope : Scope) (function : Function) (inputs : List Value)
  | send (scope : Scope) (schema receiver : Name) (value : Value)
  | receive (scope : Scope) (schema sender : Name) (ty : Ty)

inductive Script (α : Type) where
  | done (value : α)
  | effect (action : RoleM Unit) (resume : Unit → Script α)
  | failed (scope : Scope) (reason detail : String)
  | cut (request : Cut) (resume : List Value → Script α)

private def bind {α β : Type} (p : Script α) (k : α → Script β) : Script β :=
  match p with
  | .done value => k value
  | .effect action resume => .effect action (fun u => bind (resume u) k)
  | .cut request resume => .cut request (fun values => bind (resume values) k)
  | .failed scope reason detail => .failed scope reason detail

instance : Monad Script where
  pure := .done
  bind := bind

private def lift (action : RunM Unit) : Script Unit :=
  .effect (do action) .done

/-- Region disposal is role-owned even if another role creates units between
entry and exit. Nested source returns close only their own region. -/
def services (base : Location) (underlying : Services Value RunM) : Services Value Script where
  typeOf := underlying.typeOf
  fail scope reason detail := .failed scope reason detail
  charge scope := lift (underlying.charge scope)
  iteration scope := .effect (do
    let state ← get
    if state.iterations ≥ 100000 then
      throw ⟨"exhausted", "local-iteration-limit", { base with scope }⟩
    set { state with iterations := state.iterations + 1 }
    pure ()) .done
  executeLocal scope function inputs := .cut (.local scope function inputs) .done
  send scope schema receiver value := .cut (.send scope schema receiver value) (fun _ => .done ())
  received scope schema sender value := lift (underlying.received scope schema sender value)
  receive scope schema sender ty := .cut (.receive scope schema sender ty) fun values =>
    match values with
    | [value] => .done value
    | _ => .failed scope "refused" "reference-receive-arity"
  enterRegion scope environments := .effect (do
    underlying.enterRegion scope environments
    activateRole scope.role
    let before ← getThe State
    let inputs := (roleStore environments scope.role).map Prod.snd
    modify fun s => { s with frames := (before, inputs) :: s.frames }
    pure ()) .done
  exitRegion scope values := .effect (do
    underlying.exitRegion scope values
    activateRole scope.role
    let (before, inputs) :: rest := (← get).frames
      | throw ⟨"refused", "reference-frame-stack", { base with scope }⟩
    let after ← getThe State
    let closed := closeLocalFrame before after inputs (.ok (values.map Prod.snd))
    modifyThe State fun s => { s with resources := s.resources.filter fun r =>
      r.owner != scope.role || closed.resources.any (·.identity == r.identity) }
    modify fun s => { s with frames := rest }
    pure ()) .done

structure Participant where
  role : Name
  script : Script (List Value)
  state : RoleState := {}
  returned : Option (List Value) := none

/-- Termination fuel for scripts produced by `Control.executeBody` with one
selected role. Every effect is a charge, or belongs to one: loop iteration and
entry share a step charge; child entry follows a call charge; exit follows a
return/yield charge. There are at most three effects per charge, plus root
entry. Allow one failing charge beyond `limits.steps` (including its preceding
iteration effect), and one inspection of the terminal script. Cuts cannot
increase this whole-execution bound. This is not an additional work allowance:
the underlying charge and iteration checks still enforce their original limits.
The `received` service is run by the driver, not a selected-role script. -/
def resumeFuel : Nat := 3 * (limits.steps + 1) + 2

def poll (base : Location) : Nat → Participant → RunM Participant
  | 0, p => failAt { base with scope := { base.scope with role := p.role } } "exhausted" "reference-resume-limit"
  | fuel + 1, p => do
      match p.script with
      | .effect action resume =>
          let ((), state) ← action.run p.state
          poll base fuel { p with script := resume (), state }
      | .failed scope reason detail => failAt ({ base with scope }) reason detail
      | _ => return p

inductive Action where
  | local (scope : Scope) (function : Name)
  | message (scope : Scope) (schema receiver : Name)
  | stop (scope : Scope) (reason : String)

structure Cursor where
  binding : Instance
  scope : Scope
  body : List Instruction
  repeatBody : List Instruction := []
  remaining : Nat := 0
  iteration : Nat := 0

/-- Source-only structural cut policy, with its own bounded cursor work. Empty
loops consume scheduling work but do not execute any participant's iterations. -/
def next (base : Location) (source : Source) : Nat → List Cursor →
    RunM (Option Action × List Cursor × Nat)
  | fuel, [] => pure (none, [], fuel)
  | 0, _ :: _ => failAt base "exhausted" "source-schedule-work-limit"
  | fuel + 1, cursor :: outer => do
      let location := { base with scope := cursor.scope }
      match cursor.body with
      | [] =>
          if cursor.remaining == 0 then next base source fuel outer
          else
            let index := cursor.iteration + 1
            let path := cursor.scope.path.dropLast ++ [.iteration cursor.scope.site index]
            next base source fuel ({ cursor with
              body := cursor.repeatBody, remaining := cursor.remaining - 1, iteration := index,
              scope := { cursor.scope with path } } :: outer)
      | instruction :: tail =>
          let rest := { cursor with body := tail } :: outer
          match instruction with
          | .localCall site owner function _ _ =>
              let role ← checked location (cursor.binding.role owner)
              return (some (.local { cursor.scope with site := site, role := role } function), rest, fuel)
          | .message site schema sender receiver _ _ =>
              let role ← checked location (cursor.binding.role sender)
              let receiver ← checked location (cursor.binding.role receiver)
              return (some (.message { cursor.scope with site := site, role := role } schema receiver), rest, fuel)
          | .stop site owner reason =>
              let role ← checked location (cursor.binding.role owner)
              return (some (.stop { cursor.scope with site := site, role := role } reason), [], fuel)
          | .call site dependency _ _ =>
              let child ← checked location (source.binding (← checked location (lookup dependency cursor.binding.dependencies)))
              let definition ← checked location (source.protocol child.protocol)
              let some body := definition.body | failAt location "refused" "external-protocol"
              require location (rest.length < limits.callDepth) "source-schedule-depth-limit"
              next base source fuel ({
                binding := child, body := body,
                scope := { cursor.scope with
                  binding := child.name, site := site,
                  path := cursor.scope.path ++ [.call site] } } :: rest)
          | .loop site count _ _ body _ =>
              let count ← checked location (cursor.binding.count count)
              if count == 0 then next base source fuel rest
              else
                require location (rest.length < limits.callDepth) "source-schedule-depth-limit"
                next base source fuel ({
                  binding := cursor.binding, body := body,
                  repeatBody := body, remaining := count - 1,
                  scope := { cursor.scope with
                    site := site,
                    path := cursor.scope.path ++ [.iteration site 0] } } :: rest)
          | .yield _ | .ret _ => next base source fuel ({ cursor with body := [] } :: outer)
          | _ => failAt location "refused" "invalid-common-body"

private def matching (actual expected : Scope) : Bool :=
  actual.binding == expected.binding && actual.path == expected.path &&
    actual.site == expected.site && actual.role == expected.role

private def getRole (base : Location) (participants : List Participant) (role : Name) : RunM Participant := do
  let some p := participants.find? (·.role == role) | failAt base "refused" "reference-schedule-role"
  poll base resumeFuel p

private def replace (participants : List Participant) (p : Participant) : List Participant :=
  participants.map fun old => if old.role == p.role then p else old

private def runAction (base : Location) (underlying : Services Value RunM)
    (participants : List Participant) (action : Action) : RunM (List Participant) := do
  match action with
  | .local scope function =>
      let p ← getRole base participants scope.role
      let .cut (.local actual f inputs) resume := p.script
        | failAt { base with scope } "refused" "reference-schedule-local"
      let expected := { scope with path := scope.path ++ [.localCall scope.site function] }
      require base (matching actual expected && f.name == function) "reference-schedule-local"
      -- Local and protocol loops debit the same participant budget.
      modify fun state => { state with iterations := p.state.iterations }
      let values ← underlying.executeLocal actual f inputs
      let iterations := (← get).iterations
      return replace participants { p with
        script := resume values,
        state := { p.state with iterations } }
  | .message scope schema receiver =>
      let p ← getRole base participants scope.role
      let .cut (.send actual s r value) resume := p.script
        | failAt { base with scope } "refused" "reference-schedule-send"
      require base (matching actual scope && s == schema && r == receiver) "reference-schedule-send"
      underlying.send actual s r value
      let participants := replace participants { p with script := resume [] }
      let p ← getRole base participants receiver
      let .cut (.receive actual s sender _) resume := p.script
        | failAt { base with scope } "refused" "reference-schedule-receive"
      require base (matching actual { scope with role := receiver } && s == schema && sender == scope.role)
        "reference-schedule-receive"
      underlying.received actual s sender value
      return replace participants { p with script := resume [value] }
  | .stop scope _ =>
      let _ ← getRole base participants scope.role
      failAt { base with scope } "refused" "reference-schedule-stop"

private def cancel (state : State) (participants : List Participant) : State :=
  { state with resources := state.resources.filter fun r =>
    r.payload.kind != "resource_unit" ||
      participants.any (fun p => p.role == r.owner && p.returned.isSome) }

set_option maxRecDepth 4096 in
private def driveLoop (base : Location) (source : Source) (underlying : Services Value RunM) :
    Nat → Nat → List Cursor → List Participant → RunM (List (Name × List Value))
  | 0, _, _, participants => do
      modify (fun state => cancel state participants)
      failAt base "exhausted" "source-schedule-work-limit"
  | fuel + 1, budget, cursors, participants => do
      let attempt : RunM _ := do
        let (action, cursors, remaining) ← next base source budget cursors
        match action with
        | some action => return Sum.inl (cursors, remaining, ← runAction base underlying participants action)
        | none => return Sum.inr ()
      let (result, state) := attempt.run (← get)
      set state
      match result with
      | .error fault =>
          modify (fun state => cancel state participants)
          throw fault
      | .ok (.inl (cursors, remaining, participants)) =>
          driveLoop base source underlying fuel remaining cursors participants
      | .ok (.inr _) =>
          let mut completed := participants
          let mut outputs := []
          for p in participants do
            let action : RunM (List Value) := do
              let p ← poll base resumeFuel p
              let .done values := p.script | failAt base "refused" "reference-unfinished-role"
              activateRole p.role
              modify fun state => closeParticipantFrame state p.role (.ok values)
              return values
            let (result, state) := action.run (← get)
            set state
            match result with
            | .ok values =>
                completed := replace completed { p with returned := some values }
                outputs := outputs ++ [(p.role, values)]
            | .error fault =>
                modify (fun state => cancel state completed)
                throw fault
          return outputs

/-- A joint stop cancels only roots that have not returned. Each scheduled cut
spends at least one unit in `next`, so at most `budget` recursive advances are
possible. The extra structural step permits the final cursor inspection/drain,
including an initially empty stack at zero budget. Only `next` spends source
work; inspecting an empty stack does not. -/
def drive (base : Location) (source : Source) (underlying : Services Value RunM)
    (budget : Nat) (cursors : List Cursor) (participants : List Participant) :
    RunM (List (Name × List Value)) :=
  driveLoop base source underlying (budget + 1) budget cursors participants

end Tools.Interactive.Reference.SourceControl
