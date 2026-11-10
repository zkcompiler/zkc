module

public import Zkc.IR.Core.Laws
public import Zkc.Protocol.Construction.Region

/-! Steps of core regions for the source proof constructor.

Each equation rewrites the meaning of a region whose first operation is known into the
operation's process followed by the rest of the region in the extended environment. It is the
root step of `Zkc.IR.Core.Laws` applied to the equation of one operation, stated for a symbolic
rest so that the constructor applies it by matching the operation alone. The premises are the
memberships of the roles that the operation names. For a literal side they are decided by
evaluation, and the equations of one operation select one another by them.

The right sides keep the transports of `Zkc.IR.Core.Laws` (`Held.of`, `presentValues`,
`remapValues`, …). For a literal side they are evaluated by the constructor; for a symbolic side
they remain.

- A pure row, a role outside the side and an exchange inside or outside the side cost one step:
  the rest of the region on the results.
- An effect is a `call` followed by the rest of the region.
- A `call` and an `apply` are the callee's entry in the table followed by the rest of the
  region. The entry equations that the importer generates turn the entry into the callee's own
  meaning, to which a law about the callee applies.
- A `repeat` and a `loop` are the bounded iteration of their region, a `branch` and an `if` the
  selected region, and a `guard` a choice between the rest of the region and a stop.
-/

@[expose] public section

set_option autoImplicit false

namespace Zkc.Core.Step

open Zkc.Source PIR

/-- The row number of a definition typed over the headers of the earlier ones. -/
def definitionRow (headers : List Header) : Nat := headers.length

/-- A guarded return followed by a continuation is a choice between the continuation and the
stop. -/
theorem guarded_bind {I : Signature} {A B : Type} (condition : Bool) (value : A) (reason : Stop)
    (next : A → Process I B) :
    (cond condition (Process.done value) (Process.halt reason)).bind next =
      if condition = true then next value else .halt reason := by
  cases condition <;> rfl

/-- The operands of a local operation of a role in the side, as the role's own values. -/
abbrev roleValues {model : Model} {side : Side} {role : Nat} (member : side role = true)
    {types : List Ty} (values : Values (SideValue model side) (Located.atRole role types)) :
    Values model.Value types :=
  presentValues (side role) member
    (unmapValues (F := SideValue model side) (fun type => ⟨type, role⟩) types values)

/-- The values read at the positions of a list, as values indexed by a mapped list. Each value
is named by its position in the source, so that the results of a callee are read by position
whatever their form. -/
def collect {α β : Type} {F : β → Type} (f : α → β) :
    (items : List α) → ({item : α} → Var items item → F (f item)) → Values F (items.map f)
  | [], _ => .nil
  | _ :: rest, read => .cons (read .here) (collect f rest fun position => read (.there position))

/-- Re-indexing a value list reads each of its positions. -/
theorem remapValues_eq_collect {α β : Type} {F : β → Type} (f : α → β) :
    (items : List α) → (values : Values (fun item => F (f item)) items) →
      remapValues f items values = collect f items values.get
  | [], _ => rfl
  | _ :: rest, .cons value values =>
    congrArg (Values.cons value) (remapValues_eq_collect f rest values)

/-- The results of a local operation of a role, as values that the side holds. -/
abbrev heldValues {model : Model} (side : Side) (role : Nat) {types : List Ty}
    (values : Values model.Value types) :
    Values (SideValue model side) (Located.atRole role types) :=
  collect (F := SideValue model side) (fun type => ⟨type, role⟩) types
    (holdValues (side role) values).get

/-- The results of a local operation of a role in the transported form of the laws. -/
theorem remapValues_holdValues {model : Model} (side : Side) (role : Nat) {types : List Ty}
    (values : Values model.Value types) :
    remapValues (F := SideValue model side) (fun type => ⟨type, role⟩) types
        (holdValues (side role) values) = heldValues side role values :=
  remapValues_eq_collect _ _ _

/-! ## Protocol regions for a side -/

section Protocol

variable {model : Model} {operations : List OperationSignature} {headers : List Header}
  {deployed : Bool} {table : Table model headers} {side : Side}
  {Γ out : List Located} {env : Environment (SideValue model side) Γ}

/-- A pure row of a role in the side: the rest of the region on the model's results. -/
@[spec high] theorem pure_row {role : Nat} {inputs outputs : List Ty}
    {row : Var operations ⟨inputs, outputs, .pure⟩} {computes : OperationKind.pure.computes = true}
    {localBodies : Regions (LocalDialect operations headers deployed) []}
    (member : side role = true)
    {arguments : Operands Γ (Located.atRole role inputs)}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed)
      (Located.atRole role outputs ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.at role (.op row computes) localBodies) arguments bodies next).denote
        (sideMeaning model table side) env =
      next.denote (sideMeaning model table side) (env.prepend (heldValues side role
        (model.pure (.of row) (roleValues member (Operands.eval env arguments))))) :=
  remapValues_holdValues side role _ ▸ sideMeaning_step_done (at_pure member)

/-- A partial row of a role in the side: the model's result, or a stop, then the rest of the
region. -/
@[spec high] theorem partial_row {role : Nat} {inputs outputs : List Ty}
    {row : Var operations ⟨inputs, outputs, .partial⟩}
    {computes : OperationKind.partial.computes = true}
    {localBodies : Regions (LocalDialect operations headers deployed) []}
    (member : side role = true)
    {arguments : Operands Γ (Located.atRole role inputs)}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed)
      (Located.atRole role outputs ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.at role (.op row computes) localBodies) arguments bodies next).denote
        (sideMeaning model table side) env =
      (partialProcess model (model.partial (.of row)
          (roleValues member (Operands.eval env arguments)))).bind fun values =>
        next.denote (sideMeaning model table side) (env.prepend (heldValues side role values)) :=
  ((sideMeaning_step (at_partial member)).trans (Process.bind_assoc _ _ _)).trans
    (congrArg (Process.bind _) (funext fun values => remapValues_holdValues side role values ▸ rfl))

/-- A function called by a role in the side: its entry in the table, then the rest of the
region. -/
@[spec high] theorem function_call {role : Nat} {inputs outputs : List Ty}
    {specificationOnly : Bool}
    {callee : Var headers (.function inputs outputs specificationOnly)}
    {permitted : (deployed && specificationOnly) = false}
    {localBodies : Regions (LocalDialect operations headers deployed) []}
    (member : side role = true)
    {arguments : Operands Γ (Located.atRole role inputs)}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed)
      (Located.atRole role outputs ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.at role (.call callee permitted) localBodies) arguments bodies next).denote
        (sideMeaning model table side) env =
      (table.get callee (roleValues member (Operands.eval env arguments))).bind fun values =>
        next.denote (sideMeaning model table side) (env.prepend (heldValues side role values)) :=
  ((sideMeaning_step (at_call member)).trans (Process.bind_assoc _ _ _)).trans
    (congrArg (Process.bind _) (funext fun values => remapValues_holdValues side role values ▸ rfl))

/-- A guard of a role in the side: the rest of the region when the condition holds, a stop
with the authored reason otherwise. -/
@[spec high] theorem guard {role : Nat} {reason : Reason}
    {localBodies : Regions (LocalDialect operations headers deployed) []}
    (member : side role = true)
    {arguments : Operands Γ (Located.atRole role [.bool])}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed) (([] : List Located) ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.at role (.guard reason) localBodies) arguments bodies next).denote
        (sideMeaning model table side) env =
      if Held.value (side role) member ((Operands.eval env arguments).get .here) = true then
        next.denote (sideMeaning model table side) (env.prepend .nil)
      else .halt reason.stop :=
  (sideMeaning_step_guarded (at_guard member)).trans (Bool.cond_eq_ite _ _ _)

/-- An `if` of a role in the side: the selected local region on the captures, then the rest of
the region. -/
@[spec high] theorem conditional {role : Nat} {captures outputs : List Ty}
    {onTrue onFalse : Region (LocalDialect operations headers deployed) captures outputs}
    (member : side role = true)
    {arguments : Operands Γ (Located.atRole role (.bool :: captures))}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed)
      (Located.atRole role outputs ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.at role (.conditional captures outputs)
          (Regions.cons onTrue (Regions.cons onFalse Regions.nil))) arguments bodies next).denote
        (sideMeaning model table side) env =
      (if (roleValues member (Operands.eval env arguments)).get .here = true then
          onTrue.denote (localMeaning model table)
            (roleValues member (Operands.eval env arguments)).tail.get
        else onFalse.denote (localMeaning model table)
            (roleValues member (Operands.eval env arguments)).tail.get).bind fun values =>
        next.denote (sideMeaning model table side) (env.prepend (heldValues side role values)) :=
  (sideMeaning_step (at_present (op := .conditional captures outputs) member)).trans
    ((Process.bind_assoc _ _ _).trans ((congrArg (fun process => Process.bind process _)
      (localOperation_conditional.trans (Bool.cond_eq_ite _ _ _))).trans
        (congrArg (Process.bind _)
          (funext fun values => remapValues_holdValues side role values ▸ rfl))))

/-- A `loop` of a role in the side: the bounded iteration of its local region, then the rest of
the region. -/
@[spec high] theorem loop {role maximum : Nat} {carried captures : List Ty}
    {body : Region (LocalDialect operations headers deployed) (.index :: (carried ++ captures))
      carried}
    (member : side role = true)
    {arguments : Operands Γ (Located.atRole role (.index :: (carried ++ captures)))}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed)
      (Located.atRole role carried ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.at role (.loop maximum carried captures) (Regions.cons body Regions.nil)) arguments
          bodies next).denote (sideMeaning model table side) env =
      (loopProcess model maximum carried captures (loopBody (table := table) body)
          ((roleValues member (Operands.eval env arguments)).get .here)
          ((roleValues member (Operands.eval env arguments)).tail.split carried).1
          ((roleValues member (Operands.eval env arguments)).tail.split carried).2).bind
        fun values =>
          next.denote (sideMeaning model table side) (env.prepend (heldValues side role values)) :=
  (sideMeaning_step (at_present (op := .loop maximum carried captures) member)).trans
    ((Process.bind_assoc _ _ _).trans ((congrArg (fun process => Process.bind process _)
      localOperation_loop).trans (congrArg (Process.bind _)
        (funext fun values => remapValues_holdValues side role values ▸ rfl))))

/-- A local operation of a role outside the side: the rest of the region on absent results. -/
@[spec high] theorem outside {role : Nat} {op : LocalOp operations headers deployed}
    {localBodies : Regions (LocalDialect operations headers deployed) op.regions}
    (absent : side role = false)
    {arguments : Operands Γ (Located.atRole role op.arguments)}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed)
      (Located.atRole role op.results ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.at role op localBodies) arguments bodies next).denote
        (sideMeaning model table side) env =
      next.denote (sideMeaning model table side) (env.prepend
        (remapValues (F := SideValue model side) (fun type => ⟨type, role⟩) op.results
          (absentHeldValues (side role) absent op.results))) :=
  sideMeaning_step_done (at_absent absent)

/-- An exchange between two roles of the side: the receiver's copy is the sender's value. -/
@[spec high] theorem exchange_internal {sender receiver site : Nat} {type : Ty}
    (senderMember : side sender = true) (receiverMember : side receiver = true)
    {arguments : Operands Γ [⟨type, sender⟩]}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed) ([⟨type, receiver⟩] ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.exchange sender receiver site type) arguments bodies next).denote
        (sideMeaning model table side) env =
      next.denote (sideMeaning model table side) (env.prepend (.cons (Held.of (side receiver)
        (Held.value (side sender) senderMember ((Operands.eval env arguments).get .here))) .nil)) :=
  sideMeaning_step_done (Zkc.Core.exchange_internal senderMember receiverMember)

/-- An exchange that leaves the side: a `send` of the sender's value. -/
@[spec high] theorem exchange_send {sender receiver site : Nat} {type : Ty}
    (senderMember : side sender = true) (receiverAbsent : side receiver = false)
    {arguments : Operands Γ [⟨type, sender⟩]}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed) ([⟨type, receiver⟩] ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.exchange sender receiver site type) arguments bodies next).denote
        (sideMeaning model table side) env =
      .call (.send ⟨definitionRow headers, site⟩ type
          (Held.value (side sender) senderMember ((Operands.eval env arguments).get .here)))
        fun _ => next.denote (sideMeaning model table side)
          (env.prepend (.cons (Held.absent (side receiver) receiverAbsent) .nil)) :=
  sideMeaning_step_call (Zkc.Core.exchange_send senderMember receiverAbsent)

/-- An exchange that enters the side: a `receive`; the receiver's copy is the reply. -/
@[spec high] theorem exchange_receive {sender receiver site : Nat} {type : Ty}
    (senderAbsent : side sender = false) (receiverMember : side receiver = true)
    {arguments : Operands Γ [⟨type, sender⟩]}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed) ([⟨type, receiver⟩] ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.exchange sender receiver site type) arguments bodies next).denote
        (sideMeaning model table side) env =
      .call (.receive ⟨definitionRow headers, site⟩ type) fun reply =>
        next.denote (sideMeaning model table side)
          (env.prepend (.cons (Held.of (side receiver) reply) .nil)) :=
  sideMeaning_step_call (Zkc.Core.exchange_receive senderAbsent receiverMember)

/-- An exchange between two roles outside the side: nothing. -/
@[spec high] theorem exchange_outside {sender receiver site : Nat} {type : Ty}
    (senderAbsent : side sender = false) (receiverAbsent : side receiver = false)
    {arguments : Operands Γ [⟨type, sender⟩]}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed) ([⟨type, receiver⟩] ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.exchange sender receiver site type) arguments bodies next).denote
        (sideMeaning model table side) env =
      next.denote (sideMeaning model table side)
        (env.prepend (.cons (Held.absent (side receiver) receiverAbsent) .nil)) :=
  sideMeaning_step_done (Zkc.Core.exchange_outside senderAbsent receiverAbsent)

/-- A draw whose owner is in the side: a `draw`; every copy held in the side is the coin. -/
@[spec high] theorem draw_owner {owner site : Nat} {receivers : List Nat} {inputs : List Ty}
    {output : Ty} {law : Var operations ⟨inputs, [output], .sampling⟩} (member : side owner = true)
    {arguments : Operands Γ (Located.atRole owner inputs)}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed)
      ((⟨output, owner⟩ :: Located.ofRoles output receivers) ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.draw owner receivers site law) arguments bodies next).denote
        (sideMeaning model table side) env =
      .call (.draw ⟨definitionRow headers, site⟩ (.of law)
          (roleValues member (Operands.eval env arguments)))
        fun reply => next.denote (sideMeaning model table side)
          (env.prepend (broadcast model side owner receivers output reply)) :=
  sideMeaning_step_call (Zkc.Core.draw_owner member)

/-- A draw whose owner is outside the side: each receiver in the side receives its own copy,
then the rest of the region. -/
@[spec high] theorem draw_outside {owner site : Nat} {receivers : List Nat} {inputs : List Ty}
    {output : Ty} {law : Var operations ⟨inputs, [output], .sampling⟩} (absent : side owner = false)
    {arguments : Operands Γ (Located.atRole owner inputs)}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed)
      ((⟨output, owner⟩ :: Located.ofRoles output receivers) ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.draw owner receivers site law) arguments bodies next).denote
        (sideMeaning model table side) env =
      (receiverReplies model side ⟨definitionRow headers, site⟩ output receivers).bind
        fun replies => next.denote (sideMeaning model table side)
          (env.prepend (.cons (Held.absent (side owner) absent) replies)) :=
  (sideMeaning_step (Zkc.Core.draw_outside absent)).trans (Process.bind_assoc _ _ _)

/-- A sample whose owner is in the side: a `sample`; the owner holds the reply. -/
@[spec high] theorem sample_owner {owner site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} (member : side owner = true)
    {arguments : Operands Γ (Located.atRole owner inputs)}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed) ([⟨output, owner⟩] ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.sample owner site law) arguments bodies next).denote
        (sideMeaning model table side) env =
      .call (.sample ⟨definitionRow headers, site⟩ (.of law)
          (roleValues member (Operands.eval env arguments)))
        fun reply => next.denote (sideMeaning model table side)
          (env.prepend (.cons (Held.of (side owner) reply) .nil)) :=
  sideMeaning_step_call (Zkc.Core.sample_owner member)

/-- A sample whose owner is outside the side: nothing. -/
@[spec high] theorem sample_outside {owner site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} (absent : side owner = false)
    {arguments : Operands Γ (Located.atRole owner inputs)}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed) ([⟨output, owner⟩] ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.sample owner site law) arguments bodies next).denote
        (sideMeaning model table side) env =
      next.denote (sideMeaning model table side)
        (env.prepend (.cons (Held.absent (side owner) absent) .nil)) :=
  sideMeaning_step_done (Zkc.Core.sample_outside absent)

/-- A `repeat`: the bounded iteration of its region for the count that the participants in the
side agree on, then the rest of the region. -/
@[spec high] theorem «repeat» {participants : List Nat} {maximum : Nat}
    {carried captures : List Located}
    {body : Region (ProtocolDialect operations headers deployed) (carried ++ captures) carried}
    {arguments : Operands Γ (Located.ofRoles .index participants ++ (carried ++ captures))}
    {next : Region (ProtocolDialect operations headers deployed) (carried ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.repeat participants maximum carried captures) arguments
        (Regions.cons body Regions.nil) next).denote (sideMeaning model table side) env =
      (agreed Nat.beq side
          (fun count => repeatProcess model maximum
            (repeatBody (table := table) (Operands.eval env arguments) body) count
            (repeatInitial (Operands.eval env arguments)))
          (.halt .incomplete) participants (repeatCounts (Operands.eval env arguments))
          fun _ => .done (repeatInitial (Operands.eval env arguments))).bind fun values =>
        next.denote (sideMeaning model table side) (env.prepend values) :=
  sideMeaning_step repeat_meaning

/-- The region of a `branch` that a condition selects, on the captures, as a conditional. -/
abbrev branchRegion {participants : List Nat} {captures outputs : List Located}
    (arguments : Values (SideValue model side) (Located.ofRoles .bool participants ++ captures))
    (onTrue onFalse : Region (ProtocolDialect operations headers deployed) captures outputs)
    (condition : Bool) : Process (Effects model) (Values (SideValue model side) outputs) :=
  if condition = true then
    onTrue.denote (sideMeaning model table side)
      (arguments.split (Located.ofRoles .bool participants)).2.get
  else
    onFalse.denote (sideMeaning model table side)
      (arguments.split (Located.ofRoles .bool participants)).2.get

/-- A `branch`: the region that the participants in the side agree on, then the rest of the
region. -/
@[spec high] theorem branch {participants : List Nat} {captures outputs : List Located}
    {covered : Located.heldBy participants outputs = true}
    {onTrue onFalse : Region (ProtocolDialect operations headers deployed) captures outputs}
    {arguments : Operands Γ (Located.ofRoles .bool participants ++ captures)}
    {next : Region (ProtocolDialect operations headers deployed) (outputs ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.branch participants captures outputs covered) arguments
        (Regions.cons onTrue (Regions.cons onFalse Regions.nil)) next).denote
        (sideMeaning model table side) env =
      (agreed agreeBool side
          (branchRegion (table := table) (Operands.eval env arguments) onTrue onFalse)
          (.halt .incomplete) participants (branchConditions (Operands.eval env arguments))
          fun none => .done (absentOutputs model side outputs fun _ member =>
            not_held_of_heldBy covered none member)).bind fun values =>
        next.denote (sideMeaning model table side) (env.prepend values) :=
  (sideMeaning_step branch_meaning).trans
    (congrArg (fun selected => Process.bind
        (agreed agreeBool side selected (.halt .incomplete) participants
          (branchConditions (Operands.eval env arguments)) fun none =>
            .done (absentOutputs model side outputs fun _ member =>
              not_held_of_heldBy covered none member)) _)
      (funext fun condition => Bool.cond_eq_ite condition _ _))

/-- An `apply`: the callee's entry in the table for the preimage side, then the rest of the
region. -/
@[spec high] theorem apply {roles : Nat} {inputs outputs : List Located}
    {agreements : Agreements inputs outputs} {specificationOnly : Bool}
    {callee : Var headers (.protocol roles inputs outputs agreements specificationOnly)}
    {roleMap : RoleMap} {site : Nat} {permitted : (deployed && specificationOnly) = false}
    {arguments : Operands Γ (inputs.map (Located.rename roleMap))}
    {bodies : Regions (ProtocolDialect operations headers deployed) []}
    {next : Region (ProtocolDialect operations headers deployed)
      (outputs.map (Located.rename roleMap) ++ Γ) out} :
    (Region.letOp (dialect := ProtocolDialect operations headers deployed)
        (.apply callee roleMap site permitted) arguments bodies next).denote
        (sideMeaning model table side) env =
      ((table.get callee) (Side.preimage roleMap side)
          (unmapValues (F := SideValue model side) (Located.rename roleMap) _
            (Operands.eval env arguments))).bind fun values =>
        next.denote (sideMeaning model table side) (env.prepend
          (collect (F := SideValue model side) (Located.rename roleMap) outputs values.get)) :=
  ((sideMeaning_step apply_meaning).trans (Process.bind_assoc _ _ _)).trans
    (congrArg (Process.bind _) (funext fun values =>
      remapValues_eq_collect (F := SideValue model side) (Located.rename roleMap) outputs values ▸
        rfl))

end Protocol

/-! ## Local regions -/

section Local

variable {model : Model} {operations : List OperationSignature} {headers : List Header}
  {deployed : Bool} {table : Table model headers}
  {Γ out : List Ty} {env : Environment model.Value Γ}

/-- A pure row: the rest of the region on the model's results. -/
@[spec high] theorem local_pure_row {inputs outputs : List Ty}
    {row : Var operations ⟨inputs, outputs, .pure⟩} {computes : OperationKind.pure.computes = true}
    {arguments : Operands Γ inputs}
    {bodies : Regions (LocalDialect operations headers deployed) []}
    {next : Region (LocalDialect operations headers deployed) (outputs ++ Γ) out} :
    (Region.letOp (dialect := LocalDialect operations headers deployed) (.op row computes)
        arguments bodies next).denote (localMeaning model table) env =
      next.denote (localMeaning model table)
        (env.prepend (model.pure (.of row) (Operands.eval env arguments))) :=
  localMeaning_step_done localOperation_pure

/-- A partial row: the model's result, or a stop, then the rest of the region. -/
@[spec high] theorem local_partial_row {inputs outputs : List Ty}
    {row : Var operations ⟨inputs, outputs, .partial⟩}
    {computes : OperationKind.partial.computes = true}
    {arguments : Operands Γ inputs}
    {bodies : Regions (LocalDialect operations headers deployed) []}
    {next : Region (LocalDialect operations headers deployed) (outputs ++ Γ) out} :
    (Region.letOp (dialect := LocalDialect operations headers deployed) (.op row computes)
        arguments bodies next).denote (localMeaning model table) env =
      (partialProcess model (model.partial (.of row) (Operands.eval env arguments))).bind
        fun values => next.denote (localMeaning model table) (env.prepend values) :=
  localMeaning_step localOperation_partial

/-- A call: the callee's entry in the table, then the rest of the region. -/
@[spec high] theorem local_function_call {inputs outputs : List Ty} {specificationOnly : Bool}
    {callee : Var headers (.function inputs outputs specificationOnly)}
    {permitted : (deployed && specificationOnly) = false}
    {arguments : Operands Γ inputs}
    {bodies : Regions (LocalDialect operations headers deployed) []}
    {next : Region (LocalDialect operations headers deployed) (outputs ++ Γ) out} :
    (Region.letOp (dialect := LocalDialect operations headers deployed)
        (.call callee permitted) arguments bodies next).denote (localMeaning model table) env =
      (table.get callee (Operands.eval env arguments)).bind fun values =>
        next.denote (localMeaning model table) (env.prepend values) :=
  localMeaning_step localOperation_call

/-- A guard: the rest of the region when the condition holds, a stop with the authored reason
otherwise. -/
@[spec high] theorem local_guard {reason : Reason}
    {arguments : Operands Γ [.bool]}
    {bodies : Regions (LocalDialect operations headers deployed) []}
    {next : Region (LocalDialect operations headers deployed) (([] : List Ty) ++ Γ) out} :
    (Region.letOp (dialect := LocalDialect operations headers deployed) (.guard reason)
        arguments bodies next).denote (localMeaning model table) env =
      if (Operands.eval env arguments).get .here = true then
        next.denote (localMeaning model table) (env.prepend .nil)
      else .halt reason.stop :=
  (localMeaning_step localOperation_guard).trans (guarded_bind _ _ _ _)

/-- An `if`: the selected region on the captures, then the rest of the region. -/
@[spec high] theorem local_conditional {captures outputs : List Ty}
    {onTrue onFalse : Region (LocalDialect operations headers deployed) captures outputs}
    {arguments : Operands Γ (.bool :: captures)}
    {next : Region (LocalDialect operations headers deployed) (outputs ++ Γ) out} :
    (Region.letOp (dialect := LocalDialect operations headers deployed)
        (.conditional captures outputs) arguments
        (Regions.cons onTrue (Regions.cons onFalse Regions.nil)) next).denote
        (localMeaning model table) env =
      (if (Operands.eval env arguments).get .here = true then
          onTrue.denote (localMeaning model table) (Operands.eval env arguments).tail.get
        else onFalse.denote (localMeaning model table)
          (Operands.eval env arguments).tail.get).bind fun values =>
        next.denote (localMeaning model table) (env.prepend values) :=
  (localMeaning_step localOperation_conditional).trans
    (congrArg (fun process => Process.bind process _) (Bool.cond_eq_ite _ _ _))

/-- A `loop`: the bounded iteration of its region, then the rest of the region. -/
@[spec high] theorem local_loop {maximum : Nat} {carried captures : List Ty}
    {body : Region (LocalDialect operations headers deployed) (.index :: (carried ++ captures))
      carried}
    {arguments : Operands Γ (.index :: (carried ++ captures))}
    {next : Region (LocalDialect operations headers deployed) (carried ++ Γ) out} :
    (Region.letOp (dialect := LocalDialect operations headers deployed)
        (.loop maximum carried captures) arguments (Regions.cons body Regions.nil) next).denote
        (localMeaning model table) env =
      (loopProcess model maximum carried captures (loopBody (table := table) body)
          ((Operands.eval env arguments).get .here)
          ((Operands.eval env arguments).tail.split carried).1
          ((Operands.eval env arguments).tail.split carried).2).bind fun values =>
        next.denote (localMeaning model table) (env.prepend values) :=
  localMeaning_step localOperation_loop

end Local

/-! ## Announcements from outside the side

The receivers of a draw whose owner is outside the side are walked one at a time, by the
membership of each. -/

attribute [spec] receiverReplies_nil receiverReplies_present receiverReplies_absent

end Zkc.Core.Step
