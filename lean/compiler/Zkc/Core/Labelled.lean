module

public import Zkc.Core.Laws

public section

/-! The meaning of a protocol region for a side, with the sites of its effects read
through a labelling.

`protocolOperation` reports an effect of the operation with site number `s` at the site
`⟨d, s⟩`, where `d` is the number of the definition. Expansion renumbers sites: an
operation of the expanded definition stands for an operation of some definition that
the entry reaches, and its effect has to be reported at that operation's site. The
labelled meaning is `protocolOperation` with the site of every effect given by a
function of the site number; with the labelling `ownSites d` it is `protocolOperation`
itself (`labelledMeaning_own`).

The operation equations below are those of `Core/Laws.lean` for the labelled meaning.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-! ## Operands and value lists -/

theorem eval_append {Ty : Type} {Value : Ty → Type} {Γ first second : List Ty}
    (env : Environment Value Γ) (left : Operands Γ first) (right : Operands Γ second) :
    Operands.eval env (left.append right) = (Operands.eval env left).append (Operands.eval env right) := by
  induction left with
  | nil => rfl
  | cons reference rest ih => simp only [Values.cons_append, Operands.eval, ih]

theorem eval_split {Ty : Type} {Value : Ty → Type} {Γ : List Ty} (env : Environment Value Γ) :
    ∀ (added : List Ty) {rest : List Ty} (operands : Operands Γ (added ++ rest)),
      Values.split added (Operands.eval env operands) =
        (Operands.eval env (Values.split added operands).1,
          Operands.eval env (Values.split added operands).2)
  | [], _, _ => rfl
  | _ :: added, _, .cons reference operands => by
      simp only [Operands.eval, Values.split, eval_split env added operands]

/-! ## Processes and agreement -/

theorem call_bind {I : PIR.Signature} {A B : Type} (effect : I.Op)
    (next : I.Reply effect → PIR.Process I A) (last : A → PIR.Process I B) :
    (PIR.Process.call effect next).bind last = .call effect fun reply => (next reply).bind last :=
  rfl

/-- Two iterations are related step by step: when the restricted step on the restricted
state is the step, restricted, and what it produces carries and collects as the restriction
of what the step produces, the restricted iterations of the restricted state are the
iterations, restricted. -/
theorem iterations_restrict {I : PIR.Signature} {A P B Q : Type} {C D : Nat → Type}
    (restrict : A → B) (restrictCollected : (done : Nat) → C done → D done) (image : P → Q)
    {step : Nat → A → PIR.Process I P} {carry : P → A}
    {push : (done : Nat) → P → C done → C (done + 1)}
    {restricted : Nat → B → PIR.Process I Q} {carryRestricted : Q → B}
    {pushRestricted : (done : Nat) → Q → D done → D (done + 1)}
    (related : ∀ iteration state, restricted iteration (restrict state) =
      (step iteration state).bind fun produced => .done (image produced))
    (carries : ∀ produced, carryRestricted (image produced) = restrict (carry produced))
    (pushes : ∀ done produced earlier,
      pushRestricted done (image produced) (restrictCollected done earlier) =
        restrictCollected (done + 1) (push done produced earlier)) :
    ∀ (remaining done : Nat) (state : A) (earlier : C done),
      iterations restricted carryRestricted pushRestricted remaining done (restrict state)
          (restrictCollected done earlier) =
        (iterations step carry push remaining done state earlier).bind fun final =>
          .done (restrict final.1, restrictCollected _ final.2)
  | 0, _, _, _ => rfl
  | remaining + 1, done, state, earlier => by
      show (restricted done (restrict state)).bind _ = ((step done state).bind _).bind _
      rw [related, PIR.Process.bind_assoc, PIR.Process.bind_assoc]
      congr 1
      funext produced
      show iterations restricted carryRestricted pushRestricted remaining (done + 1)
        (carryRestricted (image produced))
        (pushRestricted done (image produced) (restrictCollected done earlier)) = _
      rw [carries, pushes]
      exact iterations_restrict restrict restrictCollected image related carries pushes remaining
        (done + 1) (carry produced) (push done produced earlier)

/-- No role of a list is in the side when each of them is not. -/
theorem any_absent {side : Side} {roles : List Nat} (absent : ∀ role ∈ roles, side role = false) :
    roles.any side = false := by
  simp only [List.any_eq_false]
  intro role member
  simp [absent role member]

/-- No participant is in the side. -/
theorem agreed_none {X α : Type} (same : X → X → Bool) (side : Side) (onValue : X → α)
    (onDisagree : α) :
    ∀ (roles : List Nat) (values : Values (fun role => Held X (side role)) roles)
      (onNone : roles.any side = false → α) (absent : ∀ role ∈ roles, side role = false),
        agreed same side onValue onDisagree roles values onNone = onNone (any_absent absent)
  | [], _, _, _ => rfl
  | role :: rest, values, onNone, absent => by
      rw [agreed_absent (absent role List.mem_cons_self)]
      exact agreed_none same side onValue onDisagree rest values.tail _
        (fun other member => absent other (List.mem_cons_of_mem _ member))

section Laws

variable {model : Model} {operations : List OperationSignature}
  {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
  {label : Nat → Site} {functionTable : FunctionTable model functions}
  {table : ProtocolTable model protocols} {side : Side}

/-- A step of a protocol region for a side. -/
theorem labelled_step {Γ out : List Located}
    {op : ProtocolOp operations functions protocols deployed} {arguments : Operands Γ op.arguments}
    {bodies : Regions (ProtocolDialect operations functions protocols deployed) op.regions}
    {next : Region (ProtocolDialect operations functions protocols deployed) (bindAll Γ op.results) out}
    {env : Environment (SideValue model side) Γ}
    {process : PIR.Process (Effects model) (Values (SideValue model side) op.results)}
    (step : labelledOperation model label functionTable table side op (Operands.eval env arguments)
      (bodies.denote (labelledMeaning model label functionTable table side)) = process) :
    (Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op arguments
        bodies next).denote (labelledMeaning model label functionTable table side) env =
      process.bind fun values =>
        next.denote (labelledMeaning model label functionTable table side)
          (Environment.bindAll env values) := by
  rw [← step]; rfl

/-- A step whose operation returns without an effect. -/
theorem labelled_step_done {Γ out : List Located}
    {op : ProtocolOp operations functions protocols deployed} {arguments : Operands Γ op.arguments}
    {bodies : Regions (ProtocolDialect operations functions protocols deployed) op.regions}
    {next : Region (ProtocolDialect operations functions protocols deployed) (bindAll Γ op.results) out}
    {env : Environment (SideValue model side) Γ}
    {results : Values (SideValue model side) op.results}
    (step : labelledOperation model label functionTable table side op (Operands.eval env arguments)
      (bodies.denote (labelledMeaning model label functionTable table side)) = .done results) :
    (Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op arguments
        bodies next).denote (labelledMeaning model label functionTable table side) env =
      next.denote (labelledMeaning model label functionTable table side)
        (Environment.bindAll env results) := by
  rw [labelled_step step]; rfl

/-- A step whose operation performs one effect. -/
theorem labelled_step_call {Γ out : List Located}
    {op : ProtocolOp operations functions protocols deployed} {arguments : Operands Γ op.arguments}
    {bodies : Regions (ProtocolDialect operations functions protocols deployed) op.regions}
    {next : Region (ProtocolDialect operations functions protocols deployed) (bindAll Γ op.results) out}
    {env : Environment (SideValue model side) Γ} {effect : Effect model.Value}
    {results : Effect.Reply effect → Values (SideValue model side) op.results}
    (step : labelledOperation model label functionTable table side op (Operands.eval env arguments)
      (bodies.denote (labelledMeaning model label functionTable table side)) =
        .call effect fun reply => .done (results reply)) :
    (Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op arguments
        bodies next).denote (labelledMeaning model label functionTable table side) env =
      .call effect fun reply =>
        next.denote (labelledMeaning model label functionTable table side)
          (Environment.bindAll env (results reply)) := by
  rw [labelled_step step]; rfl

theorem labelled_at_present {role : Nat} {op : LocalOp operations functions deployed}
    {bodies : Regions (LocalDialect operations functions deployed) op.regions}
    (member : side role = true)
    {arguments : Values (SideValue model side) (Located.atRole role op.arguments)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (.at role op bodies) arguments regions =
      (localOperation model functionTable op (presentValues (side role) member (unmapValues _ _ arguments))
          (bodies.denote (localMeaning model functionTable))).bind fun values =>
        .done (remapValues (F := SideValue model side) (fun type => ⟨type, role⟩) _
          (holdValues (side role) values)) := by
  show (performStep model _ (side role) _).bind _ = _
  rw [performStep_present model _ _ member, PIR.Process.bind_assoc]
  rfl

theorem labelled_at_absent {role : Nat} {op : LocalOp operations functions deployed}
    {bodies : Regions (LocalDialect operations functions deployed) op.regions}
    (absent : side role = false)
    {arguments : Values (SideValue model side) (Located.atRole role op.arguments)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (.at role op bodies) arguments regions =
      .done (remapValues (F := SideValue model side) (fun type => ⟨type, role⟩) _
        (absentHeldValues (side role) absent op.results)) := by
  show (performStep model _ (side role) _).bind _ = _
  rw [performStep_absent model _ _ absent]
  rfl

theorem labelled_exchange_internal {sender receiver site : Nat} {type : Ty}
    (senderMember : side sender = true) (receiverMember : side receiver = true)
    {arguments : Values (SideValue model side) [⟨type, sender⟩]}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (operations := operations)
        (deployed := deployed) (.exchange sender receiver site type) arguments regions =
      .done (.cons (Held.of (side receiver)
        (Held.value (side sender) senderMember (arguments.get .here))) .nil) := by
  show (exchangeStep model _ type (side sender) (side receiver) _).bind _ = _
  rw [exchangeStep_internal model type _ _ senderMember receiverMember]
  rfl

theorem labelled_exchange_send {sender receiver site : Nat} {type : Ty}
    (senderMember : side sender = true) (receiverAbsent : side receiver = false)
    {arguments : Values (SideValue model side) [⟨type, sender⟩]}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (operations := operations)
        (deployed := deployed) (.exchange sender receiver site type) arguments regions =
      .call (.send (label site) type
          (Held.value (side sender) senderMember (arguments.get .here))) fun _ =>
        .done (.cons (Held.absent (side receiver) receiverAbsent) .nil) := by
  show (exchangeStep model _ type (side sender) (side receiver) _).bind _ = _
  rw [exchangeStep_send model type _ _ senderMember receiverAbsent]
  rfl

theorem labelled_exchange_receive {sender receiver site : Nat} {type : Ty}
    (senderAbsent : side sender = false) (receiverMember : side receiver = true)
    {arguments : Values (SideValue model side) [⟨type, sender⟩]}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (operations := operations)
        (deployed := deployed) (.exchange sender receiver site type) arguments regions =
      .call (.receive (label site) type) fun reply =>
        .done (.cons (Held.of (side receiver) reply) .nil) := by
  show (exchangeStep model _ type (side sender) (side receiver) _).bind _ = _
  rw [exchangeStep_receive model type _ _ senderAbsent receiverMember]
  rfl

theorem labelled_exchange_outside {sender receiver site : Nat} {type : Ty}
    (senderAbsent : side sender = false) (receiverAbsent : side receiver = false)
    {arguments : Values (SideValue model side) [⟨type, sender⟩]}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (operations := operations)
        (deployed := deployed) (.exchange sender receiver site type) arguments regions =
      .done (.cons (Held.absent (side receiver) receiverAbsent) .nil) := by
  show (exchangeStep model _ type (side sender) (side receiver) _).bind _ = _
  rw [exchangeStep_outside model type _ _ senderAbsent receiverAbsent]
  rfl

theorem labelled_draw_owner {owner site : Nat} {receivers : List Nat} {inputs : List Ty}
    {output : Ty} {law : Var operations ⟨inputs, [output], .sampling⟩}
    {populated : output.populated = true} (member : side owner = true)
    {arguments : Values (SideValue model side) (Located.atRole owner inputs)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (deployed := deployed)
        (.draw owner receivers site law populated) arguments regions =
      .call (.draw (label site) (.of law populated)
          (presentValues (side owner) member (unmapValues _ _ arguments))) fun reply =>
        .done (broadcast model side owner receivers output reply) :=
  drawStep_owner model _ _ _ member _ _

theorem labelled_draw_outside {owner site : Nat} {receivers : List Nat} {inputs : List Ty}
    {output : Ty} {law : Var operations ⟨inputs, [output], .sampling⟩}
    {populated : output.populated = true} (absent : side owner = false)
    {arguments : Values (SideValue model side) (Located.atRole owner inputs)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (deployed := deployed)
        (.draw owner receivers site law populated) arguments regions =
      (receiverReplies model side (label site) output receivers).bind fun replies =>
        .done (.cons (Held.absent (side owner) absent) replies) :=
  drawStep_outside model _ _ _ absent _ _

theorem labelled_sample_owner {owner site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩}
    {populated : output.populated = true} (member : side owner = true)
    {arguments : Values (SideValue model side) (Located.atRole owner inputs)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (deployed := deployed)
        (.sample owner site law populated) arguments regions =
      .call (.sample (label site) (.of law populated)
          (presentValues (side owner) member (unmapValues _ _ arguments))) fun reply =>
        .done (.cons (Held.of (side owner) reply) .nil) := by
  show (sampleStep model _ _ (side owner) _).bind _ = _
  rw [sampleStep_owner model _ _ member]
  rfl

theorem labelled_sample_outside {owner site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩}
    {populated : output.populated = true} (absent : side owner = false)
    {arguments : Values (SideValue model side) (Located.atRole owner inputs)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (deployed := deployed)
        (.sample owner site law populated) arguments regions =
      .done (.cons (Held.absent (side owner) absent) .nil) := by
  show (sampleStep model _ _ (side owner) _).bind _ = _
  rw [sampleStep_outside model _ _ absent]
  rfl

/-- `repeat` for a side, with its region named. -/
theorem labelled_repeat_meaning {participants : List Nat} {count : RepeatCount}
    {carried collected captures : List Located}
    {covered : Located.heldBy participants collected = true}
    {arguments : Values (SideValue model side)
      (count.operands participants ++ (carried ++ captures))}
    {body : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll [] (Located.ofRoles .nat participants ++ (carried ++ captures)))
      (collected ++ carried)} :
    labelledOperation model label functionTable table side (operations := operations)
        (deployed := deployed) (.repeat participants count carried collected captures covered)
        arguments
        (Regions.denote (labelledMeaning model label functionTable table side)
          (Regions.cons body Regions.nil)) =
      agreed Nat.beq side
        (fun agreed => repeatProcess model side count carried collected
          (fun iteration values =>
            body.denote (labelledMeaning model label functionTable table side)
              (Environment.ofValues ((heldCopies model side .nat iteration participants).append
                (values.append (repeatCaptured arguments)))))
          agreed (repeatInitial arguments))
        (.halt .incomplete) participants (repeatCounts arguments)
        fun none => .done (repeatOutside covered arguments none) := rfl

/-- `choose` for a side. -/
theorem labelled_choose_meaning {participants : List Nat} {tag : ChoiceTag}
    {captures outputs : List Located} {covered : Located.heldBy participants outputs = true}
    {arguments : Values (SideValue model side) (Located.ofRoles tag.type participants ++ captures)}
    {arms : Regions (ProtocolDialect operations functions protocols deployed)
      (tag.regions participants captures outputs)} :
    labelledOperation model label functionTable table side (operations := operations)
        (deployed := deployed) (.choose participants tag captures outputs covered) arguments
        (Regions.denote (labelledMeaning model label functionTable table side) arms) =
      agreed (tag.same model.Carrier) side
        (chosenRegion model side participants captures outputs tag
          (Regions.denote (labelledMeaning model label functionTable table side) arms)
          (chooseTags arguments) (arguments.split (Located.ofRoles tag.type participants)).2)
        (.halt .incomplete) participants (chooseTags arguments)
        fun none => .done (absentOutputs model side outputs fun _ member =>
          not_held_of_heldBy covered none member) := rfl

/-- `apply` for a side: the callee's entry in the table for the preimage side. -/
theorem labelled_apply_meaning {header : ProtocolHeader} {callee : Var protocols header}
    {roleMap : RoleMap} {site : Nat} {permitted : (deployed && header.specificationOnly) = false}
    {arguments : Values (SideValue model side) (header.inputs.map (Located.rename roleMap))}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (operations := operations)
        (.apply callee roleMap site permitted) arguments regions =
      ((table.get callee) (label site).below (Side.preimage roleMap side)
          (unmapValues (F := SideValue model side) (Located.rename roleMap) _ arguments)).bind
        fun values => .done (remapValues (F := SideValue model side) (Located.rename roleMap) _ values) :=
  rfl

end Laws

end Zkc.Core
