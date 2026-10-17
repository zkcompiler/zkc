module

public import Zkc.Construction.Structured
public import Zkc.Source.Structured.OpenMeaning

@[expose] public section

/-! The participant projection rule.

`project` checks that an exported role-local program, read interactively, is the
projection of the admitted original entry to the validator role. It walks the
original typed body in lockstep with the exported instructions, tracking for
every original component what the validator holds (`Slot`): nothing, the value
at an exported reference, a present value the exported program does not keep, or
the replaced service. Every operation the validator executes must be implemented
by the next exported instruction: a calculation by the same calculation on the
references holding its operands, a validator-owned helper call by a call of the
same checked helper, a guard by a guard on the condition's reference, a received
message by a receive at the same qualified site from the producer, a selected
draw by a challenge at the same qualified query site, and the delivery of its
answer by the observation of a message the validator sends at the delivery site.
Calculations whose operands are all present but which the exported program does
not keep are admitted only when they cannot stop. Transcript plumbing
(coordinates and observations of received messages) is skipped. Every exported
instruction must be accounted for, and the returned references must hold the
validator's outputs.

`Zkc.Construction.project_sound` proves that the exported program's interactive
reading equals the original validator's participant process, read through its
outputs, for every handle, input and reply.
-/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source Zkc.Source.Structured

/-- What the projected role holds for one original component: nothing (the
component is absent at the role), the value at an exported reference, a present
value the exported program does not keep, or the replaced service. -/
inductive Slot where
  | absent
  | held (reference : Nat)
  | free
  | service
  deriving DecidableEq, Repr

namespace Slot

def at_ (slots : List Slot) (index : Nat) : Slot := slots.getD index .absent

/-- Hide the components outside the role's scopes, as `maskValues` does. -/
def mask (self : Nat) : List (List Nat) → List Slot → List Slot
  | _, [] => []
  | scopes, slot :: rest =>
      (if (scopes.headD []).contains self then slot else .absent) :: mask self scopes.tail rest

/-- The references of slots that are all held. -/
def references : List Slot → Option (List Nat)
  | [] => some []
  | .held reference :: rest => (references rest).map (reference :: ·)
  | _ :: _ => none

def isAbsent : Slot → Bool
  | .absent => true
  | _ => false

end Slot

/-- Leading instructions that the interactive reading runs without any action:
coordinate constructions and observations of messages the validator does not
send. Returns the rest and the number of values they append. -/
def skip (context : Context) : List Instruction → List Instruction × Nat
  | ⟨.indicesEmpty, [], _, _⟩ :: rest =>
      let (remaining, count) := skip context rest
      (remaining, count + 1)
  | ⟨.indicesAppend, [_, _], _, _⟩ :: rest =>
      let (remaining, count) := skip context rest
      (remaining, count + 1)
  | ⟨.observe suite template, [state, value, coordinates], results, body⟩ :: rest =>
      if template.sentBy (context.role context.validator) then
        (⟨.observe suite template, [state, value, coordinates], results, body⟩ :: rest, 0)
      else
        let (remaining, count) := skip context rest
        (remaining, count + 1)
  | instructions => (instructions, 0)

section Walk
variable (program : Structured.Program) (context : Context)

/-- The next action-bearing instruction after skipped transcript plumbing. -/
def next? (instructions : List Instruction) : Option (Instruction × List Instruction × Nat) :=
  match skip context instructions with
  | (instruction :: rest, count) => some (instruction, rest, count)
  | ([], _) => none

/-- The next instruction receives a scalar of type `ty` at `site`. -/
def expectReceive (site : String) (ty : Ty) (instructions : List Instruction) :
    Option (List Instruction × Nat) :=
  match next? context instructions with
  | some (⟨.receive site' _ _ ty', [], _, []⟩, rest, count) =>
      if site' = site ∧ ty' = ty then some (rest, count) else none
  | _ => none

/-- The next instruction observes `reference` as a message the validator sends
at `site`: the delivery of a challenge. -/
def expectDelivery (site : String) (reference : Nat) (instructions : List Instruction) :
    Option (List Instruction × Nat) :=
  match next? context instructions with
  | some (⟨.observe _ template, [_, value, _], _, []⟩, rest, count) =>
      if value = reference ∧ template.sentBy (context.role context.validator) = true ∧
          template.messageSite? = some site ∧ (template.origin context).isSome then some (rest, count)
      else none
  | _ => none

/-- The next instruction is a challenge of `field` at the query `site`. -/
def expectChallenge (site field : String) (instructions : List Instruction) :
    Option (List Instruction × Nat) :=
  match next? context instructions with
  | some (⟨.challenge _ field' template, [_, _], _, []⟩, rest, count) =>
      if field' = field ∧ template.querySite? = some site ∧ (template.origin context).isSome then
        some (rest, count)
      else none
  | _ => none

/-- The next instruction guards on `reference`. -/
def expectGuard (reference : Nat) (instructions : List Instruction) :
    Option (List Instruction × Nat) :=
  match next? context instructions with
  | some (⟨.guard _, [condition], [], []⟩, rest, count) =>
      if condition = reference then some (rest, count) else none
  | _ => none

/-- The next instruction calls `helper` on `references`. -/
def expectCall (helper : Helper) (references : List Nat) (instructions : List Instruction) :
    Option (List Instruction × Nat) :=
  match next? context instructions with
  | some (⟨.call name, operands, results, []⟩, rest, count) =>
      if name = helper.name ∧ operands = references ∧ results = helper.outputs.map .data then
        some (rest, count)
      else none
  | _ => none

/-- The next instruction is `calculation` on `references`. -/
def expectCalculation (calculation : Calculation) (references : List Nat)
    (instructions : List Instruction) : Option (List Instruction × Nat) :=
  match next? context instructions with
  | some (⟨.calculate calculation', operands, results, []⟩, rest, count) =>
      if calculation' = calculation ∧ operands = references ∧
          results = calculation.op.results.map .data then some (rest, count)
      else none
  | _ => none

/-- One original operation without nested regions, at the validator role.
Returns the remaining instructions, the slots of the operation's results and the
extended reference count. -/
def walkOperation (ctx : ProtocolContext) (n : Nat) (op : ProtocolOp) (arguments : List Slot)
    (instructions : List Instruction) : Except String (List Instruction × List Slot × Nat) :=
  let self := context.validator
  match op with
  | .mark _ => .ok (instructions, [], n)
  | .statement .. => .ok (instructions, [], n)
  | .restrict _ roles =>
      .ok (instructions,
        [if (roles.map ctx.roles).contains self then arguments.headD .absent else .absent], n)
  | .calculate operation _ =>
      match Calculation.ofOp? operation with
      | some calculation =>
          if arguments.any Slot.isAbsent then
            .ok (instructions, operation.results.map fun _ => .absent, n)
          else
            match (if calculation.op.results.all dataType then Slot.references arguments else none).bind
                (fun references => expectCalculation context calculation references instructions) with
            | some (rest, count) => .ok (rest, [.held (n + count)], n + count + 1)
            | none =>
                if calculation.total then .ok (instructions, [.free], n)
                else .error "projection-calculation"
      | none => .error "projection-operation"
  | .localCall helper _ owner _ =>
      if ctx.roles owner = self then
        match Slot.references arguments with
        | some references =>
            match expectCall context helper references instructions with
            | some (rest, count) =>
                if helper ∈ program.payload.definitions.map CheckedDefinition.helper ∧
                    helper.outputs.all dataType = true then
                  .ok (rest, (List.range helper.outputs.length).map fun index => .held (n + count + index),
                    n + count + helper.outputs.length)
                else .error "projection-helper"
            | none => .error "projection-call"
        | none => .error "projection-call-operands"
      else .ok (instructions, helper.outputs.map fun _ => .absent, n)
  | .guard owner _ =>
      if ctx.roles owner = self then
        match arguments with
        | [.held reference] =>
            match expectGuard context reference instructions with
            | some (rest, count) => .ok (rest, [], n + count)
            | none => .error "projection-guard"
        | _ => .error "projection-guard-operand"
      else .ok (instructions, [], n)
  | .exchange ty sender receiver site =>
      let qualified := qualifyProtocolSite ctx.applicationPrefix site
      if ctx.roles sender = ctx.roles receiver then .error "projection-exchange-roles"
      else if scalarType ty = none then .error "projection-message-type"
      else if ctx.roles sender = self then
        match arguments with
        | [.held reference] =>
            if ctx.roles receiver = context.producer then
              match expectDelivery context qualified reference instructions with
              | some (rest, count) => .ok (rest, [.held reference], n + count + 1)
              | none => .error "projection-delivery"
            else .error "projection-delivery-receiver"
        | _ => .error "projection-send-operand"
      else if ctx.roles receiver = self then
        if ctx.roles sender = context.producer then
          match expectReceive context qualified ty instructions with
          | some (rest, count) => .ok (rest, [.held (n + count)], n + count + 1)
          | none => .error "projection-receive"
        else .error "projection-receive-sender"
      else .ok (instructions, [.absent], n)
  | .draw owner field site =>
      if ctx.roles owner = self then
        match arguments with
        | [.service] =>
            match expectChallenge context (qualifyProtocolSite ctx.applicationPrefix site) field
                instructions with
            | some (rest, count) => .ok (rest, [.held (n + count)], n + count + 2)
            | none => .error "projection-challenge"
        | _ => .error "projection-draw-service"
      else .ok (instructions, [.absent], n)
  | .protocolApply .. => .error "projection-application"
  | .repeat .. => .error "projection-repeat"

/-- The projection walk of one region at the validator role. -/
def walk : Nat → {Γ out : List Ty} → ProtocolContext → List Slot → Nat →
    Region protocolDialect Γ out → List Instruction →
      Except String (List Instruction × List Slot × Nat)
  | 0, _, _, _, _, _, _, _ => .error "projection-depth"
  | fuel + 1, _, _, ctx, slots, n, region, instructions =>
      match region with
      | .ret values => .ok (instructions, (Operands.indices values).map (Slot.at_ slots), n)
      | .stop _ => .error "projection-stop"
      | .bind _ _ => .error "projection-bind"
      | .letOp op arguments _ next =>
          match walkOperation program context ctx n op
              ((Operands.indices arguments).map (Slot.at_ slots)) instructions with
          | .ok (remaining, results, n') => walk fuel ctx (results ++ slots) n' next remaining
          | .error error => .error error

end Walk

/-- Region nesting and instruction counts are bounded by the admitted program;
this fuel only makes the walk structurally recursive. -/
def projectionFuel : Nat := 1048576

section Root
variable (program : Structured.Program) (context : Context)

/-- The validator's input slots before masking: each published data input is held
at its exported position, the replaced service is the handle, and every other
input is absent. -/
def inputSlots (policy : Policy) (inputs : List Ty) : List Slot :=
  (List.range inputs.length).map fun index =>
    match policy.publicInputs.idxOf? index with
    | some position => .held position
    | none => if index = context.service then .service else .absent

/-- The references the validator returns for its outputs, in original order. -/
def outputReferences (self : Nat) : List (List Nat) → List Slot → Option (List Nat)
  | _, [] => some []
  | scopes, slot :: rest =>
      if (scopes.headD []).contains self then
        match slot with
        | .held reference => (outputReferences self scopes.tail rest).map (reference :: ·)
        | _ => none
      else outputReferences self scopes.tail rest

/-- The participant projection rule: the exported validator, read interactively,
is the validator's projection of the original entry. The walk matches every
original operation the validator executes with the exported instruction that
implements it, at the same qualified site and with operands holding the same
values; the returned references hold the validator's outputs, followed by one
more value. -/
def project (participant : Participant) : Except String Unit :=
  let root := program.payload.entry
  let self := context.validator
  let slots := Slot.mask self root.inputScopes (inputSlots context participant.policy root.inputs)
  match walk program context projectionFuel {} slots (participant.policy.publicInputs.length + 1) root.body
      participant.instructions with
  | .error error => .error error
  | .ok (rest, outputs, count) =>
      match skip context rest with
      | ([], skipped) =>
          match outputReferences self root.outputScopes outputs with
          | some references =>
              if participant.returned.dropLast = references ∧ participant.returned ≠ [] ∧
                  participant.returned.all (· < count + skipped) then .ok ()
              else .error "projection-outputs"
          | none => .error "projection-outputs"
      | _ => .error "projection-unexplained"

end Root

end Zkc.Construction
