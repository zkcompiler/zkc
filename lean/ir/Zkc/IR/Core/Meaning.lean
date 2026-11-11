module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.IR.Core.WellFormed

@[expose] public section

/-! The meaning of core programs.

A function denotes a process that returns its outputs or stops; it performs no
effect. A protocol denotes, for every side, the process of the side's roles acting
together over the one effect signature `Effects model`. Every presence decision is a
match on a `Bool` membership: the step functions below take the membership of the
roles involved as explicit `Bool` arguments, so a literal side reduces each of them
to one case.

Nothing assumes a broadcast channel: a `draw` announced from outside the side is one
`receive` per receiver in the side. At a `repeat` or a `branch`, the participants in
the side must hold equal copies of the count or condition; otherwise the side stops
with the reserved reason `incomplete`, before the count is compared with the maximum.
A stop by any role of the side ends the side's process.

No other construct names `incomplete`: a `guard` and a partial row stop with a
`Reason`, and a `stop` of a well-formed definition names an authored reason.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

variable (model : Model)

/-- The meaning of a function with the given signature. -/
abbrev FunctionMeaning (inputs outputs : List Ty) : Type :=
  Values model.Value inputs → PIR.Process (Effects model) (Values model.Value outputs)

/-- The meaning of a protocol: for every side, the side's process. -/
abbrev ProtocolMeaning (inputs outputs : List Located) : Type :=
  (side : Side) → Values (SideValue model side) inputs →
    PIR.Process (Effects model) (Values (SideValue model side) outputs)

def Header.Meaning : Header → Type
  | .function inputs outputs _ => FunctionMeaning model inputs outputs
  | .protocol _ inputs outputs _ _ => ProtocolMeaning model inputs outputs

/-- The meanings of the earlier definitions, most recent first. -/
abbrev Table (headers : List Header) : Type := Values (Header.Meaning model) headers

/-- The result of a partial row as a process: its outputs, or a stop with its
authored reason. -/
def partialProcess {A : Type} : Except Reason A → PIR.Process (Effects model) A
  | .ok value => .done value
  | .error reason => .halt reason.stop

/-- A pure or partial row applied to its inputs. -/
def rowProcess (row : OperationRow) :
    (kind : OperationKind) → kind.computes = true → Values model.Value row.inputs →
      PIR.Process (Effects model) (Values model.Value row.outputs)
  | .pure, _, arguments => .done (model.pure row arguments)
  | .partial, _, arguments => partialProcess model (model.partial row arguments)
  | .sampling, computes, _ => absurd computes Bool.false_ne_true

/-- `loop(m)`: run the region `count` times with the iteration number, threading the
carried values; stop `refused` when the count exceeds the maximum. -/
def loopProcess (maximum : Nat) (carried captures : List Ty)
    (body : RegionFunction model.Value (Effects model) (.index :: (carried ++ captures), carried))
    (count : Nat) (initial : Values model.Value carried) (captured : Values model.Value captures) :
    PIR.Process (Effects model) (Values model.Value carried) :=
  if count ≤ maximum then
    (PIR.repeatN count
      (fun (state : Nat × Values model.Value carried) =>
        (body (.cons state.1 (state.2.append captured))).bind fun next => .done (state.1 + 1, next))
      (0, initial)).bind fun final => .done final.2
  else .halt .refused

section Local

variable {operations : List OperationSignature} {headers : List Header} {deployed : Bool}

/-- The meaning of a local operation, given the meanings of earlier definitions. -/
def localOperation (table : Table model headers) :
    (op : LocalOp operations headers deployed) → Values model.Value op.arguments →
      Values (RegionFunction model.Value (Effects model)) op.regions →
        PIR.Process (Effects model) (Values model.Value op.results)
  | .op (kind := kind) row computes => fun arguments _ =>
      rowProcess model (.of row) kind computes arguments
  | .call callee _ => fun arguments _ => table.get callee arguments
  | .conditional .. => fun arguments regions =>
      cond (arguments.get .here) ((regions.get .here) arguments.tail)
        ((regions.get (.there .here)) arguments.tail)
  | .loop maximum carried captures => fun arguments regions =>
      loopProcess model maximum carried captures (regions.get .here) (arguments.get .here)
        (arguments.tail.split carried).1 (arguments.tail.split carried).2
  | .guard reason => fun arguments _ => cond (arguments.get .here) (.done .nil) (.halt reason.stop)

def localMeaning (table : Table model headers) :
    RegionMeaning (LocalDialect operations headers deployed) (Effects model) :=
  ⟨model.Value, localOperation model table⟩

end Local

/-! ## Presence steps

Each step takes the membership of the roles it concerns as `Bool` arguments. -/

/-- `at(r, ℓ)`: the local operation when `r` is present; otherwise nothing. -/
def performStep {inputs outputs : List Ty}
    (run : Values model.Value inputs → PIR.Process (Effects model) (Values model.Value outputs)) :
    (present : Bool) → Values (fun type => Held (model.Value type) present) inputs →
      PIR.Process (Effects model) (Values (fun type => Held (model.Value type) present) outputs)
  | true, arguments => run arguments
  | false, _ => .done (absentValues outputs)

/-- `exchange(s, r, site)` for the memberships of `s` and of `r`. -/
def exchangeStep (site : Site) (type : Ty) :
    (sender receiver : Bool) → Held (model.Value type) sender →
      PIR.Process (Effects model) (Held (model.Value type) receiver)
  | true, true, value => .done value
  | true, false, value => .call (.send site type value) fun _ => .done PUnit.unit
  | false, true, _ => .call (.receive site type) fun reply => .done reply
  | false, false, _ => .done PUnit.unit

/-- The owner's part of `draw(o, R, site, law)`: draw when the owner is present,
otherwise continue without a coin. -/
def drawStep {α : Type} (site : Site) (law : SamplingRow)
    (onDraw : model.Value law.output → PIR.Process (Effects model) α) :
    (owner : Bool) → Values (fun type => Held (model.Value type) owner) law.inputs →
      (owner = false → PIR.Process (Effects model) α) → PIR.Process (Effects model) α
  | true, inputs, _ => .call (.draw site law inputs) onDraw
  | false, _, onOutside => onOutside rfl

/-- One receiver's announcement from outside the side: its own `receive`. -/
def receiveStep (site : Site) (type : Ty) :
    (receiver : Bool) → PIR.Process (Effects model) (Held (model.Value type) receiver)
  | true => .call (.receive site type) fun reply => .done reply
  | false => .done PUnit.unit

/-- `sample(o, site, law)` for the membership of the owner. -/
def sampleStep (site : Site) (law : SamplingRow) :
    (owner : Bool) → Values (fun type => Held (model.Value type) owner) law.inputs →
      PIR.Process (Effects model) (Held (model.Value law.output) owner)
  | true, inputs => .call (.sample site law inputs) fun reply => .done reply
  | false, _ => .done PUnit.unit

/-- One public coin held by every role of a list that is in the side. -/
def heldCopies (side : Side) (type : Ty) (reply : model.Value type) :
    (roles : List Nat) → Values (SideValue model side) (Located.ofRoles type roles)
  | [] => .nil
  | role :: rest => .cons (Held.of (side role) reply) (heldCopies side type reply rest)

/-- The results of a draw whose owner is in the side: every copy held in the side is
the coin. -/
def broadcast (side : Side) (owner : Nat) (receivers : List Nat) (type : Ty)
    (reply : model.Value type) :
    Values (SideValue model side) (⟨type, owner⟩ :: Located.ofRoles type receivers) :=
  .cons (Held.of (side owner) reply) (heldCopies model side type reply receivers)

/-- The announcements of a draw whose owner is outside the side: each receiver in the
side, in order, performs its own `receive` and holds its own reply. -/
def receiverReplies (side : Side) (site : Site) (type : Ty) :
    (receivers : List Nat) →
      PIR.Process (Effects model) (Values (SideValue model side) (Located.ofRoles type receivers))
  | [] => .done .nil
  | role :: rest =>
      (receiveStep model site type (side role)).bind fun reply =>
        (receiverReplies side site type rest).bind fun replies => .done (.cons reply replies)

/-- No role of a list is in the side when its first role and the later ones are not. -/
theorem Side.absent_cons {side : Side} {role : Nat} {rest : List Nat}
    (absent : side role = false) (restAbsent : rest.any side = false) :
    (role :: rest).any side = false := by
  simp only [List.any_cons, absent, restAbsent, Bool.or_self]

/-- Two copies of a Boolean control value agree. -/
def agreeBool : Bool → Bool → Bool
  | true, true | false, false => true
  | true, false | false, true => false

/-- Continue with `value` when every later copy held in the side equals it. -/
def agreeWith {X α : Type} (same : X → X → Bool) (side : Side) (onValue : X → α)
    (onDisagree : α) (value : X) :
    (roles : List Nat) → Values (fun role => Held X (side role)) roles → α
  | [], _ => onValue value
  | role :: rest, values =>
      Held.elim (side role) (values.get .here)
        (fun other => cond (same value other)
          (agreeWith same side onValue onDisagree value rest values.tail) onDisagree)
        fun _ => agreeWith same side onValue onDisagree value rest values.tail

/-- The control value the participants in the side hold: continue with it when all
their copies agree, with `onDisagree` when two differ, and with `onNone` when no
participant is in the side. -/
def agreed {X α : Type} (same : X → X → Bool) (side : Side) (onValue : X → α) (onDisagree : α) :
    (roles : List Nat) → Values (fun role => Held X (side role)) roles →
      (roles.any side = false → α) → α
  | [], _, onNone => onNone rfl
  | role :: rest, values, onNone =>
      Held.elim (side role) (values.get .here)
        (fun value => agreeWith same side onValue onDisagree value rest values.tail)
        fun absent => agreed same side onValue onDisagree rest values.tail fun restAbsent =>
          onNone (Side.absent_cons absent restAbsent)

theorem not_held_of_heldBy {side : Side} {participants : List Nat} {located : Located}
    {outputs : List Located} (covered : Located.heldBy participants outputs = true)
    (none : participants.any side = false) (member : located ∈ outputs) :
    side located.holder = false := by
  simp only [Located.heldBy, occursIn, List.all_eq_true, List.any_eq_true] at covered
  obtain ⟨role, inside, same⟩ := covered located member
  simp only [List.any_eq_false] at none
  rw [Nat.eq_of_beq_eq_true same]
  simpa using none _ inside

/-- The unit values of outputs held by roles none of which is in the side. -/
def absentOutputs (side : Side) :
    (outputs : List Located) → (∀ located ∈ outputs, side located.holder = false) →
      Values (SideValue model side) outputs
  | [], _ => .nil
  | located :: rest, absent =>
      .cons (Held.absent _ (absent located (List.mem_cons_self ..)))
        (absentOutputs side rest fun other member => absent other (List.mem_cons_of_mem _ member))

/-- `repeat(P, m)` once its count is agreed. -/
def repeatProcess {carried : Type} (maximum : Nat)
    (step : carried → PIR.Process (Effects model) carried) (count : Nat) (initial : carried) :
    PIR.Process (Effects model) carried :=
  if count ≤ maximum then PIR.repeatN count step initial else .halt .refused

section Protocol

variable {operations : List OperationSignature} {headers : List Header} {deployed : Bool}

/-- The meaning of a protocol operation for a side. The site of an effect is the
current definition, whose row number is the number of earlier definitions. -/
def protocolOperation (table : Table model headers) (side : Side) :
    (op : ProtocolOp operations headers deployed) → Values (SideValue model side) op.arguments →
      Values (RegionFunction (SideValue model side) (Effects model)) op.regions →
        PIR.Process (Effects model) (Values (SideValue model side) op.results)
  | .at role op bodies => fun arguments _ =>
      (performStep model
        (fun values => localOperation model table op values (bodies.denote (localMeaning model table)))
        (side role) (unmapValues _ _ arguments)).bind fun values =>
          .done (remapValues _ _ values)
  | .exchange sender receiver site type => fun arguments _ =>
      (exchangeStep model ⟨headers.length, site⟩ type (side sender) (side receiver)
        (arguments.get .here)).bind fun result => .done (.cons result .nil)
  | .draw owner receivers site (output := output) law => fun arguments _ =>
      drawStep model ⟨headers.length, site⟩ (.of law)
        (fun reply => .done (broadcast model side owner receivers output reply))
        (side owner) (unmapValues _ _ arguments) fun absent =>
          (receiverReplies model side ⟨headers.length, site⟩ output receivers).bind fun replies =>
            .done (.cons (Held.absent _ absent) replies)
  | .sample owner site law => fun arguments _ =>
      (sampleStep model ⟨headers.length, site⟩ (.of law) (side owner)
        (unmapValues _ _ arguments)).bind fun reply => .done (.cons reply .nil)
  | .repeat participants maximum carried _ => fun arguments regions =>
      let parts := arguments.split (Located.ofRoles .index participants)
      let state := parts.2.split carried
      agreed Nat.beq side
        (fun count => repeatProcess model maximum
          (fun values => (regions.get .here) (values.append state.2)) count state.1)
        (.halt .incomplete) participants
        (unmapValues (F := SideValue model side) (fun role => ⟨.index, role⟩) _ parts.1)
        fun _ => .done state.1
  | .branch participants _ outputs covered => fun arguments regions =>
      let parts := arguments.split (Located.ofRoles .bool participants)
      agreed agreeBool side
        (fun condition => cond condition ((regions.get .here) parts.2)
          ((regions.get (.there .here)) parts.2))
        (.halt .incomplete) participants
        (unmapValues (F := SideValue model side) (fun role => ⟨.bool, role⟩) _ parts.1) fun none =>
          .done (absentOutputs model side outputs fun _ member =>
            not_held_of_heldBy covered none member)
  | .apply callee roleMap _ _ => fun arguments _ =>
      ((table.get callee) (Side.preimage roleMap side)
        (unmapValues (F := SideValue model side) (Located.rename roleMap) _ arguments)).bind
        fun values => .done (remapValues (F := SideValue model side) (Located.rename roleMap) _ values)

def sideMeaning (table : Table model headers) (side : Side) :
    RegionMeaning (ProtocolDialect operations headers deployed) (Effects model) :=
  ⟨SideValue model side, protocolOperation model table side⟩

end Protocol

/-- The meaning of a definition, given the meanings of the earlier ones. -/
def Definition.meaning {operations : List OperationSignature} {headers : List Header}
    (table : Table model headers) :
    {header : Header} → Definition operations headers header → header.Meaning model
  | _, .function _ body => fun arguments => body.denote (localMeaning model table) arguments.get
  | _, .protocol _ _ _ body => fun side arguments =>
      body.denote (sideMeaning model table side) arguments.get

/-- The meanings of all definitions of a program, most recent first. -/
def Program.table {operations : List OperationSignature} :
    {headers : List Header} → Program operations headers → Table model headers
  | _, .nil => .nil
  | _, .snoc earlier definition _ =>
      .cons (definition.meaning model (earlier.table)) earlier.table

/-- The meaning of a program's last definition. -/
def Program.meaning {operations : List OperationSignature} {headers : List Header}
    {header : Header} : Program operations (header :: headers) → header.Meaning model
  | .snoc earlier definition _ => definition.meaning model (earlier.table model)

/-- The table of a program is the meaning of its last definition followed by the
table of the earlier definitions. The hypothesis holds by unfolding an imported
program's constant. -/
theorem Program.table_unfold {operations : List OperationSignature} {headers : List Header}
    {header : Header} {program : Program operations (header :: headers)}
    {earlier : Program operations headers} {definition : Definition operations headers header}
    {wellFormed : definition.violation = none}
    (unfolded : program = .snoc earlier definition wellFormed) :
    program.table model = .cons (program.meaning model) (earlier.table model) := by
  subst unfolded; rfl

/-- The entry of a table for its most recent definition. -/
theorem Program.entry_here {headers : List Header} {header : Header}
    {table : Table model (header :: headers)} {meaning : header.Meaning model}
    {rest : Table model headers} (unfolded : table = .cons meaning rest) :
    table.get .here = meaning := by
  subst unfolded; rfl

/-- The entry of a table for an earlier definition is its entry in the earlier table. -/
theorem Program.entry_there {headers : List Header} {header callee : Header}
    {table : Table model (header :: headers)} {meaning : header.Meaning model}
    {rest : Table model headers} {position : Var headers callee} {entry : callee.Meaning model}
    (unfolded : table = .cons meaning rest) (earlier : rest.get position = entry) :
    table.get (.there position) = entry := by
  subst unfolded; exact earlier

/-! ## Agreements

An agreement of a protocol's signature names copies of one source value. An honest
execution starts with equal copies; a contract assumes the proposition below of the
inputs of the side it speaks of. -/

/-- The copies of an agreement that the side holds are equal. -/
def Agreement.Holds (side : Side) {ports : List Located} (agreement : Agreement ports)
    (values : Values (SideValue model side) ports) : Prop :=
  ∀ first ∈ agreement.copies, ∀ second ∈ agreement.copies,
    ∀ (firstMember : side first.holder = true) (secondMember : side second.holder = true),
      Held.value (side first.holder) firstMember (values.get first.port) =
        Held.value (side second.holder) secondMember (values.get second.port)

/-- For every agreement over a protocol's inputs, the copies that the side holds are
equal. -/
def Agreements.InputsHold (side : Side) {inputs outputs : List Located}
    (agreements : Agreements inputs outputs) (values : Values (SideValue model side) inputs) : Prop :=
  ∀ agreement ∈ agreements.inputs, agreement.Holds model side values

end Zkc.Core

-- Materialize shared unfolding equations in their defining module. Otherwise
-- separate clients can generate the same public equation name with different
-- private proof helpers, leaving its stored provider ambiguous to an audit.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.partialProcess
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.rowProcess
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.localOperation
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.performStep
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.exchangeStep
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.drawStep
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.receiveStep
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.sampleStep
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.heldCopies
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.broadcast
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.receiverReplies
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.agreeBool
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.agreeWith
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.agreed
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.absentOutputs
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.repeatProcess
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.protocolOperation
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Definition.meaning
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Program.table
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Program.meaning
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Header.Meaning
