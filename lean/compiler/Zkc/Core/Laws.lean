module

public import Zkc.Core.Meaning

public section

/-! Equations of the meaning, one operation at a time.

A proof about a side walks a body operation by operation with three kinds of
equations.

- A root equation rewrites the meaning of a region whose first operation is known:
  `sideMeaning_step` and `localMeaning_step` turn an equation for the operation into
  one for the region, the operation's process followed by the rest of the region in
  the extended environment. `ProtocolDefinition.meaning_eq` and
  `FunctionDefinition.meaning_eq` open a definition at its body.
- An operation equation gives the process of one operation. Its left side is the
  operation applied to arbitrary arguments and regions, so it matches whatever a
  body passes; its right side names their components by `get`, `tail` and `split`,
  which reduce on the literal lists of a body. Its side conditions are memberships
  `side role = true` or `side role = false` of the roles the operation names. For a
  literal side, or the preimage of one under a literal role map, they hold by
  evaluation.
- An entry equation replaces the table entry that a `call` or `apply` names by the
  callee's own meaning: `Values.get_here` and `Values.get_there` walk a table whose
  constructor is known.

The agreement of a `repeat` or `choose` is walked one participant at a time by
`agreed_present`, `agreed_absent`, `agreeWith_present`, `agreeWith_absent` and
`agreeWith_nil`. For a symbolic side the transports `Held.value`, `Held.of`,
`Held.absent` and `presentValues` remain in the equations; for a literal side they
reduce away.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-! ## Processes

The shapes that a step leaves are a `call`, a `bind` and a guarded process. A proof
continues under each with `congrArg (PIR.Process.call _) (funext _)`,
`congrArg (PIR.Process.bind _) (funext _)` and `guarded_congr`; `bind_cond` moves the
rest of a region into the two regions of an `if`. -/

/-- Binding after a choice is the choice of the bound processes. -/
theorem bind_cond {I : PIR.Signature} {A B : Type} (condition : Bool)
    (onTrue onFalse : PIR.Process I A) (next : A → PIR.Process I B) :
    (cond condition onTrue onFalse).bind next =
      cond condition (onTrue.bind next) (onFalse.bind next) := by
  cases condition <;> rfl

/-- Two processes guarded by one condition and one reason are equal when the guarded
processes are. -/
theorem guarded_congr {I : PIR.Signature} {A : Type} {condition : Bool} {reason : PIR.Stop}
    {process other : PIR.Process I A} (same : process = other) :
    cond condition process (.halt reason) = cond condition other (.halt reason) := by
  rw [same]

/-! ## Held values -/

namespace Held

variable {X : Type}

theorem elim_present {α : Sort _} (present : Bool) (member : present = true) (held : Held X present)
    (onPresent : X → α) (onAbsent : present = false → α) :
    Held.elim present held onPresent onAbsent = onPresent (Held.value present member held) := by
  subst member; rfl

theorem elim_absent {α : Sort _} (present : Bool) (absent : present = false) (held : Held X present)
    (onPresent : X → α) (onAbsent : present = false → α) :
    Held.elim present held onPresent onAbsent = onAbsent absent := by
  subst absent; rfl

theorem value_of (present : Bool) (member : present = true) (value : X) :
    Held.value present member (Held.of present value) = value := by
  subst member; rfl

theorem value_map {Y : Type} (f : X → Y) (present : Bool) (member : present = true)
    (held : Held X present) :
    Held.value present member (Held.map f present held) = f (Held.value present member held) := by
  subst member; rfl

theorem value_map₂ {Y Z : Type} (f : X → Y → Z) (present : Bool) (member : present = true)
    (first : Held X present) (second : Held Y present) :
    Held.value present member (Held.map₂ f present first second) =
      f (Held.value present member first) (Held.value present member second) := by
  subst member; rfl

end Held

/-! ## Value lists -/

/-- Two value lists are equal when their first values and their rests are. -/
theorem cons_congr {Ty : Type} {Value : Ty → Type} {ty : Ty} {Γ : List Ty} {first other : Value ty}
    {rest others : Values Value Γ} (head : first = other) (tail : rest = others) :
    Values.cons first rest = Values.cons other others := by
  rw [head, tail]

@[simp] theorem unmapValues_cons {α β : Type} {F : β → Type} (f : α → β) (item : α)
    (items : List α) (value : F (f item)) (values : Values F (items.map f)) :
    unmapValues f (item :: items) (.cons value values) = .cons value (unmapValues f items values) :=
  rfl

@[simp] theorem presentValues_cons {X : Ty → Type} (present : Bool) (member : present = true)
    {type : Ty} {types : List Ty} (value : Held (X type) present)
    (values : Values (fun type => Held (X type) present) types) :
    presentValues present member (.cons value values) =
      .cons (Held.value present member value) (presentValues present member values) := by
  subst member; rfl

/-- A position of the tail of a value list is the next position of the list. -/
theorem tail_get {Ty : Type} {Value : Ty → Type} {Γ : List Ty} {head ty : Ty}
    (values : Values Value (head :: Γ)) (position : Var Γ ty) :
    values.tail.get position = values.get position.there := by
  cases values; rfl

/-! ## Presence steps -/

section Steps

variable (model : Model) {site : Site}

theorem performStep_present {inputs outputs : List Ty}
    (run : Values model.Value inputs → PIR.Process (Effects model) (Values model.Value outputs))
    (present : Bool) (member : present = true)
    (arguments : Values (fun type => Held (model.Value type) present) inputs) :
    performStep model run present arguments =
      (run (presentValues present member arguments)).bind fun values =>
        .done (holdValues present values) := by
  subst member
  exact (PIR.Process.bind_done _).symm

theorem performStep_absent {inputs outputs : List Ty}
    (run : Values model.Value inputs → PIR.Process (Effects model) (Values model.Value outputs))
    (present : Bool) (absent : present = false)
    (arguments : Values (fun type => Held (model.Value type) present) inputs) :
    performStep model run present arguments = .done (absentHeldValues present absent outputs) := by
  subst absent; rfl

theorem exchangeStep_internal (type : Ty) (sender receiver : Bool)
    (senderMember : sender = true) (receiverMember : receiver = true)
    (value : Held (model.Value type) sender) :
    exchangeStep model site type sender receiver value =
      .done (Held.of receiver (Held.value sender senderMember value)) := by
  subst senderMember; subst receiverMember; rfl

theorem exchangeStep_send (type : Ty) (sender receiver : Bool)
    (senderMember : sender = true) (receiverAbsent : receiver = false)
    (value : Held (model.Value type) sender) :
    exchangeStep model site type sender receiver value =
      .call (.send site type (Held.value sender senderMember value)) fun _ =>
        .done (Held.absent receiver receiverAbsent) := by
  subst senderMember; subst receiverAbsent; rfl

theorem exchangeStep_receive (type : Ty) (sender receiver : Bool)
    (senderAbsent : sender = false) (receiverMember : receiver = true)
    (value : Held (model.Value type) sender) :
    exchangeStep model site type sender receiver value =
      .call (.receive site type) fun reply => .done (Held.of receiver reply) := by
  subst senderAbsent; subst receiverMember; rfl

theorem exchangeStep_outside (type : Ty) (sender receiver : Bool)
    (senderAbsent : sender = false) (receiverAbsent : receiver = false)
    (value : Held (model.Value type) sender) :
    exchangeStep model site type sender receiver value =
      .done (Held.absent receiver receiverAbsent) := by
  subst senderAbsent; subst receiverAbsent; rfl

theorem drawStep_owner {α : Type} (law : SamplingRow)
    (onDraw : model.Value law.output → PIR.Process (Effects model) α) (owner : Bool)
    (member : owner = true) (inputs : Values (fun type => Held (model.Value type) owner) law.inputs)
    (onOutside : owner = false → PIR.Process (Effects model) α) :
    drawStep model site law onDraw owner inputs onOutside =
      .call (.draw site law (presentValues owner member inputs)) onDraw := by
  subst member; rfl

theorem drawStep_outside {α : Type} (law : SamplingRow)
    (onDraw : model.Value law.output → PIR.Process (Effects model) α) (owner : Bool)
    (absent : owner = false) (inputs : Values (fun type => Held (model.Value type) owner) law.inputs)
    (onOutside : owner = false → PIR.Process (Effects model) α) :
    drawStep model site law onDraw owner inputs onOutside = onOutside absent := by
  subst absent; rfl

theorem sampleStep_owner (law : SamplingRow) (owner : Bool) (member : owner = true)
    (inputs : Values (fun type => Held (model.Value type) owner) law.inputs) :
    sampleStep model site law owner inputs =
      .call (.sample site law (presentValues owner member inputs)) fun reply =>
        .done (Held.of owner reply) := by
  subst member; rfl

theorem sampleStep_outside (law : SamplingRow) (owner : Bool) (absent : owner = false)
    (inputs : Values (fun type => Held (model.Value type) owner) law.inputs) :
    sampleStep model site law owner inputs = .done (Held.absent owner absent) := by
  subst absent; rfl

end Steps

/-! ## Announcements from outside the side -/

section Announcements

variable (model : Model)

theorem receiveStep_present (site : Site) (type : Ty) (receiver : Bool) (member : receiver = true) :
    receiveStep model site type receiver =
      .call (.receive site type) fun reply => .done (Held.of receiver reply) := by
  subst member; rfl

theorem receiveStep_absent (site : Site) (type : Ty) (receiver : Bool) (absent : receiver = false) :
    receiveStep model site type receiver = .done (Held.absent receiver absent) := by
  subst absent; rfl

theorem receiverReplies_nil (side : Side) (site : Site) (type : Ty) :
    receiverReplies model side site type [] = .done .nil := rfl

/-- A receiver in the side performs its own `receive`; its copy is its own reply. -/
theorem receiverReplies_present (side : Side) (site : Site) (type : Ty) (role : Nat)
    (rest : List Nat) (member : side role = true) :
    receiverReplies model side site type (role :: rest) =
      .call (.receive site type) fun reply =>
        (receiverReplies model side site type rest).bind fun replies =>
          .done (.cons (Held.of (side role) reply) replies) := by
  show (receiveStep model site type (side role)).bind _ = _
  rw [receiveStep_present model site type _ member]
  rfl

theorem receiverReplies_absent (side : Side) (site : Site) (type : Ty) (role : Nat)
    (rest : List Nat) (absent : side role = false) :
    receiverReplies model side site type (role :: rest) =
      (receiverReplies model side site type rest).bind fun replies =>
        .done (.cons (Held.absent (side role) absent) replies) := by
  show (receiveStep model site type (side role)).bind _ = _
  rw [receiveStep_absent model site type _ absent]
  rfl

end Announcements

/-! ## Agreement of the participants' copies

The first group walks the participants one at a time, with the membership of each
as the side condition. The second group states what the walk amounts to. -/

section Agreement

variable {X α : Type} {same : X → X → Bool} {side : Side} {onValue : X → α} {onDisagree : α}

theorem agreeWith_nil {value : X} {values : Values (fun role => Held X (side role)) []} :
    agreeWith same side onValue onDisagree value [] values = onValue value := rfl

/-- A later participant in the side: its copy is compared with the first one. -/
theorem agreeWith_present {role : Nat} {rest : List Nat} (member : side role = true) {value : X}
    {values : Values (fun role => Held X (side role)) (role :: rest)} :
    agreeWith same side onValue onDisagree value (role :: rest) values =
      cond (same value (Held.value (side role) member (values.get .here)))
        (agreeWith same side onValue onDisagree value rest values.tail) onDisagree := by
  rw [agreeWith, Held.elim_present _ member]

theorem agreeWith_absent {role : Nat} {rest : List Nat} (absent : side role = false) {value : X}
    {values : Values (fun role => Held X (side role)) (role :: rest)} :
    agreeWith same side onValue onDisagree value (role :: rest) values =
      agreeWith same side onValue onDisagree value rest values.tail := by
  rw [agreeWith, Held.elim_absent _ absent]

/-- No participant in the side: the operation does nothing. -/
theorem agreed_nil {values : Values (fun role => Held X (side role)) []}
    {onNone : ([] : List Nat).any side = false → α} :
    agreed same side onValue onDisagree [] values onNone = onNone rfl := rfl

/-- The first participant in the side: its copy is the one the later copies are
compared with. -/
theorem agreed_present {role : Nat} {rest : List Nat} (member : side role = true)
    {values : Values (fun role => Held X (side role)) (role :: rest)}
    {onNone : (role :: rest).any side = false → α} :
    agreed same side onValue onDisagree (role :: rest) values onNone =
      agreeWith same side onValue onDisagree (Held.value (side role) member (values.get .here)) rest
        values.tail := by
  rw [agreed, Held.elim_present _ member]

theorem agreed_absent {role : Nat} {rest : List Nat} (absent : side role = false)
    {values : Values (fun role => Held X (side role)) (role :: rest)}
    {onNone : (role :: rest).any side = false → α} :
    agreed same side onValue onDisagree (role :: rest) values onNone =
      agreed same side onValue onDisagree rest values.tail fun restAbsent =>
        onNone (Side.absent_cons absent restAbsent) := by
  rw [agreed, Held.elim_absent _ absent]

variable (same side onValue onDisagree)

/-- Every later copy in the side equals the first one. -/
theorem agreeWith_equal (value : X) :
    (roles : List Nat) → (values : Values (fun role => Held X (side role)) roles) →
      (∀ {role : Nat} (position : Var roles role) (member : side role = true),
        same value (Held.value (side role) member (values.get position)) = true) →
      agreeWith same side onValue onDisagree value roles values = onValue value
  | [], _, _ => rfl
  | role :: rest, values, equal => by
    have rest_equal : ∀ {other : Nat} (position : Var rest other) (member : side other = true),
        same value (Held.value (side other) member (values.tail.get position)) = true :=
      fun position member => tail_get values position ▸ equal position.there member
    cases present : side role with
    | true =>
      rw [agreeWith_present present, equal .here present]
      exact agreeWith_equal value rest values.tail rest_equal
    | false =>
      rw [agreeWith_absent present]
      exact agreeWith_equal value rest values.tail rest_equal

/-- A later copy in the side differs from the first one. -/
theorem agreeWith_unequal (value : X) :
    (roles : List Nat) → (values : Values (fun role => Held X (side role)) roles) →
      {role : Nat} → (position : Var roles role) → (member : side role = true) →
      same value (Held.value (side role) member (values.get position)) = false →
      agreeWith same side onValue onDisagree value roles values = onDisagree
  | [], _, _, position, _, _ => position.elimNil
  | head :: rest, values, _, position, member, differs => by
    cases position with
    | here => rw [agreeWith_present member, differs]; rfl
    | there position =>
      have later := agreeWith_unequal value rest values.tail position member
        (tail_get values position ▸ differs)
      cases present : side head with
      | true =>
        rw [agreeWith_present present, later]
        cases same value (Held.value (side head) present (values.get .here)) <;> rfl
      | false => rw [agreeWith_absent present, later]

/-- No later participant is in the side: nothing is compared. -/
theorem agreeWith_none (value : X) :
    (roles : List Nat) → (values : Values (fun role => Held X (side role)) roles) →
      (∀ role ∈ roles, side role = false) →
      agreeWith same side onValue onDisagree value roles values = onValue value
  | [], _, _ => rfl
  | role :: rest, values, absent => by
    rw [agreeWith_absent (absent role (List.mem_cons_self ..))]
    exact agreeWith_none value rest values.tail fun other member =>
      absent other (List.mem_cons_of_mem _ member)

/-- Equal copies: the participants in the side agree on `value`. This covers one
participant in the side and several. -/
theorem agreed_equal (reflexive : ∀ value, same value value = true) (value : X) :
    (roles : List Nat) → (values : Values (fun role => Held X (side role)) roles) →
      (onNone : roles.any side = false → α) →
      (∀ {role : Nat} (position : Var roles role) (member : side role = true),
        Held.value (side role) member (values.get position) = value) →
      roles.any side = true →
        agreed same side onValue onDisagree roles values onNone = onValue value
  | [], _, _, _, present => Bool.noConfusion present
  | role :: rest, values, onNone, equal, inside => by
    have rest_equal : ∀ {other : Nat} (position : Var rest other) (member : side other = true),
        Held.value (side other) member (values.tail.get position) = value :=
      fun position member => tail_get values position ▸ equal position.there member
    cases present : side role with
    | true =>
      rw [agreed_present present, equal .here present]
      exact agreeWith_equal same side onValue onDisagree value rest values.tail
        fun position member => by rw [rest_equal position member]; exact reflexive value
    | false =>
      rw [agreed_absent present]
      refine agreed_equal reflexive value rest values.tail _ rest_equal ?_
      simpa only [List.any_cons, present, Bool.false_or] using inside

/-- Unequal copies: two participants in the side hold different values. -/
theorem agreed_unequal (decides : ∀ left right, same left right = true ↔ left = right) :
    (roles : List Nat) → (values : Values (fun role => Held X (side role)) roles) →
      (onNone : roles.any side = false → α) →
      {first second : Nat} → (firstPosition : Var roles first) → (secondPosition : Var roles second) →
      (firstMember : side first = true) → (secondMember : side second = true) →
      Held.value (side first) firstMember (values.get firstPosition) ≠
        Held.value (side second) secondMember (values.get secondPosition) →
        agreed same side onValue onDisagree roles values onNone = onDisagree
  | [], _, _, _, _, firstPosition, _, _, _, _ => firstPosition.elimNil
  | role :: rest, values, onNone, first, second, firstPosition, secondPosition, firstMember,
      secondMember, differ => by
    have unequal : ∀ {left right : X}, left ≠ right → same left right = false := by
      intro left right distinct
      cases result : same left right with
      | false => rfl
      | true => exact absurd ((decides _ _).mp result) distinct
    cases present : side role with
    | false =>
      rw [agreed_absent present]
      cases firstPosition with
      | here => rw [present] at firstMember; exact Bool.noConfusion firstMember
      | there firstPosition =>
        cases secondPosition with
        | here => rw [present] at secondMember; exact Bool.noConfusion secondMember
        | there secondPosition =>
          exact agreed_unequal decides rest values.tail _ firstPosition secondPosition firstMember
            secondMember (by rwa [tail_get, tail_get])
    | true =>
      rw [agreed_present present]
      cases firstPosition with
      | here =>
        cases secondPosition with
        | here => exact absurd rfl differ
        | there secondPosition =>
          exact agreeWith_unequal same side onValue onDisagree _ rest values.tail secondPosition
            secondMember (tail_get values secondPosition ▸ unequal differ)
      | there firstPosition =>
        cases result : same (Held.value (side role) present (values.get .here))
            (Held.value (side first) firstMember (values.get firstPosition.there)) with
        | true =>
          have same_first := (decides _ _).mp result
          cases secondPosition with
          | here => exact absurd same_first.symm differ
          | there secondPosition =>
            exact agreeWith_unequal same side onValue onDisagree _ rest values.tail secondPosition
              secondMember (tail_get values secondPosition ▸ unequal (same_first ▸ differ))
        | false =>
          exact agreeWith_unequal same side onValue onDisagree _ rest values.tail firstPosition
            firstMember (tail_get values firstPosition ▸ result)

theorem occursIn_iff (numbers : List Nat) (number : Nat) :
    occursIn numbers number = true ↔ number ∈ numbers := by
  simp only [occursIn, List.any_eq_true]
  exact ⟨fun ⟨_, member, same⟩ => Nat.eq_of_beq_eq_true same ▸ member,
    fun member => ⟨number, member, Nat.beq_refl number⟩⟩

/-- A position of a context names a member of it. -/
theorem position_mem {Ty : Type} {Γ : List Ty} {ty : Ty} (position : Var Γ ty) : ty ∈ Γ :=
  List.mem_of_getElem? position.valid

/-- Distinct participants of which one is in the side: its own copy decides and
nothing is compared. With distinct participants, a side with one role never stops
`incomplete` at a `repeat` or a `choose`. -/
theorem agreed_single :
    (roles : List Nat) → distinctNumbers roles = true →
      (values : Values (fun role => Held X (side role)) roles) →
      (onNone : roles.any side = false → α) →
      {role : Nat} → (position : Var roles role) → (member : side role = true) →
      (∀ other ∈ roles, side other = true → other = role) →
        agreed same side onValue onDisagree roles values onNone =
          onValue (Held.value (side role) member (values.get position))
  | [], _, _, _, _, position, _, _ => position.elimNil
  | head :: rest, distinct, values, onNone, role, position, member, alone => by
    have parts : occursIn rest head = false ∧ distinctNumbers rest = true := by
      simpa only [distinctNumbers, Bool.and_eq_true, Bool.not_eq_true'] using distinct
    have outside : head ∉ rest := fun inside =>
      Bool.noConfusion (parts.1.symm.trans ((occursIn_iff rest head).mpr inside))
    cases position with
    | here =>
      rw [agreed_present member]
      refine agreeWith_none same side onValue onDisagree _ rest values.tail fun other inside => ?_
      cases present : side other with
      | false => rfl
      | true => exact absurd (alone other (List.mem_cons_of_mem _ inside) present ▸ inside) outside
    | there position =>
      have absent : side head = false := by
        cases present : side head with
        | false => rfl
        | true =>
          exact absurd (alone head (List.mem_cons_self ..) present ▸ position_mem position) outside
      rw [agreed_absent absent,
        agreed_single rest parts.2 values.tail _ position member fun other inside =>
          alone other (List.mem_cons_of_mem _ inside)]
      rw [tail_get]

/-- The key of a copy that a participant in the side holds, among the keys of the copies. -/
theorem keys_get {K : Type} (key : X → K) :
    (roles : List Nat) → (values : Values (fun role => Held X (side role)) roles) →
      {role : Nat} → (position : Var roles role) → (member : side role = true) →
      Held.value (side role) member
          ((values.map fun {role} copy => Held.map key (side role) copy).get position) =
        key (Held.value (side role) member (values.get position))
  | [], _, _, position, _ => position.elimNil
  | _ :: rest, .cons copy copies, _, position, member => by
    cases position with
    | here => exact Held.value_map key _ member copy
    | there position => exact keys_get key rest copies position member

/-- A test that compares a key of two copies, with a continuation that reads the key only:
the later copies agree with the first one as their keys do. -/
theorem agreeWith_key {K : Type} (key : X → K) (sameKey : K → K → Bool) (onKey : K → α)
    (value : X) :
    (roles : List Nat) → (values : Values (fun role => Held X (side role)) roles) →
      agreeWith (fun left right => sameKey (key left) (key right)) side
          (fun copy => onKey (key copy)) onDisagree value roles values =
        agreeWith sameKey side onKey onDisagree (key value) roles
          (values.map fun {role} copy => Held.map key (side role) copy)
  | [], _ => rfl
  | role :: rest, .cons copy copies => by
    have tail := agreeWith_key key sameKey onKey value rest copies
    cases present : side role with
    | true =>
      rw [agreeWith_present present, agreeWith_present present]
      show cond (sameKey (key value) (key (Held.value (side role) present copy))) _ _ =
        cond (sameKey (key value)
          (Held.value (side role) present (Held.map key (side role) copy))) _ _
      rw [Held.value_map]
      exact congrArg (fun agrees => cond _ agrees onDisagree) tail
    | false =>
      rw [agreeWith_absent present, agreeWith_absent present]
      exact tail

/-- A test that compares a key of two copies, with a continuation that reads the key only:
the participants in the side agree on their copies as they agree on the keys of their
copies. -/
theorem agreed_key {K : Type} (key : X → K) (sameKey : K → K → Bool) (onKey : K → α) :
    (roles : List Nat) → (values : Values (fun role => Held X (side role)) roles) →
      (onNone : roles.any side = false → α) →
      agreed (fun left right => sameKey (key left) (key right)) side
          (fun copy => onKey (key copy)) onDisagree roles values onNone =
        agreed sameKey side onKey onDisagree roles
          (values.map fun {role} copy => Held.map key (side role) copy) onNone
  | [], _, _ => rfl
  | role :: rest, .cons copy copies, onNone => by
    cases present : side role with
    | true =>
      rw [agreed_present present, agreed_present present]
      show agreeWith _ side _ onDisagree (Held.value (side role) present copy) rest copies =
        agreeWith sameKey side onKey onDisagree
          (Held.value (side role) present (Held.map key (side role) copy)) rest _
      rw [Held.value_map]
      exact agreeWith_key side onDisagree key sameKey onKey _ rest copies
    | false =>
      rw [agreed_absent present, agreed_absent present]
      exact agreed_key key sameKey onKey rest copies _

end Agreement

theorem nat_beq_decides (left right : Nat) : Nat.beq left right = true ↔ left = right :=
  ⟨Nat.eq_of_beq_eq_true, fun equal => equal ▸ Nat.beq_refl left⟩

theorem agreeBool_decides (left right : Bool) : agreeBool left right = true ↔ left = right := by
  cases left <;> cases right <;> decide

/-! ## Local regions and operations

The equations of the regions take a literal region apart; those of the operations
give one operation's process. Both are stated for symbolic regions, so that applying
one to a body is a syntactic match and never unfolds the denotation of the body. -/

section Local

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool} {table : FunctionTable model functions}

/-- A step of a local region: when the first operation's process is `process`, the
region is `process` followed by the rest in the extended environment. -/
theorem localMeaning_step {Γ out : List Ty} {op : LocalOp operations functions deployed}
    {arguments : Operands Γ op.arguments}
    {bodies : Regions (LocalDialect operations functions deployed) op.regions}
    {next : Region (LocalDialect operations functions deployed) (bindAll Γ op.results) out}
    {env : Environment model.Value Γ}
    {process : PIR.Process (Effects model) (Values model.Value op.results)}
    (step : localOperation model table op (Operands.eval env arguments)
      (bodies.denote (localMeaning model table)) = process) :
    (Region.letOp (dialect := LocalDialect operations functions deployed) op arguments bodies
        next).denote (localMeaning model table) env =
      process.bind fun values => next.denote (localMeaning model table) (Environment.bindAll env values) := by
  rw [← step]; rfl

/-- A step whose operation returns without stopping: the rest of the region in the
environment extended by its results. -/
theorem localMeaning_step_done {Γ out : List Ty} {op : LocalOp operations functions deployed}
    {arguments : Operands Γ op.arguments}
    {bodies : Regions (LocalDialect operations functions deployed) op.regions}
    {next : Region (LocalDialect operations functions deployed) (bindAll Γ op.results) out}
    {env : Environment model.Value Γ} {results : Values model.Value op.results}
    (step : localOperation model table op (Operands.eval env arguments)
      (bodies.denote (localMeaning model table)) = .done results) :
    (Region.letOp (dialect := LocalDialect operations functions deployed) op arguments bodies
        next).denote (localMeaning model table) env =
      next.denote (localMeaning model table) (Environment.bindAll env results) := by
  rw [localMeaning_step step]; rfl

theorem localMeaning_ret {Γ out : List Ty} {values : Operands Γ out}
    {env : Environment model.Value Γ} :
    (Region.ret (dialect := LocalDialect operations functions deployed) values).denote
        (localMeaning model table) env = .done (Operands.eval env values) := rfl

theorem localMeaning_stop {Γ out : List Ty} {reason : PIR.Stop} {env : Environment model.Value Γ} :
    (Region.stop (dialect := LocalDialect operations functions deployed) (Γ := Γ) (out := out)
        reason).denote (localMeaning model table) env = .halt reason := rfl

theorem localOperation_pure {inputs outputs : List Ty}
    {row : Var operations ⟨inputs, outputs, .pure⟩}
    {applies : OperationSignature.applies ⟨inputs, outputs, .pure⟩ = true}
    {arguments : Values model.Value inputs}
    {regions : Values (RegionFunction model.Value (Effects model)) []} :
    localOperation model table (functions := functions) (deployed := deployed) (.op row applies)
        arguments regions =
      .done (model.pure (.of row) applies arguments) := rfl

/-- A restricted row: the model's value where it is defined, and the stop `undefined`
outside its domain. -/
theorem localOperation_restricted {inputs outputs : List Ty} {domain : Option Nat}
    {row : Var operations ⟨inputs, outputs, .restricted domain⟩}
    {applies : OperationSignature.applies ⟨inputs, outputs, .restricted domain⟩ = true}
    {arguments : Values model.Value inputs}
    {regions : Values (RegionFunction model.Value (Effects model)) []} :
    localOperation model table (functions := functions) (deployed := deployed) (.op row applies)
        arguments regions =
      definedProcess model (model.restricted (.of row) arguments) := rfl

/-- An operation the core owns: its value where it is defined, and the stop `undefined`
outside its domain. The model has no part in it. -/
theorem localOperation_builtin {operation : Builtin}
    {arguments : Values model.Value operation.arguments}
    {regions : Values (RegionFunction model.Value (Effects model)) []} :
    localOperation model table (operations := operations) (functions := functions)
        (deployed := deployed) (.builtin operation) arguments regions =
      definedProcess model (operation.eval arguments) := rfl

theorem localOperation_call {header : FunctionHeader} {callee : Var functions header}
    {permitted : (deployed && header.specificationOnly) = false}
    {arguments : Values model.Value header.inputs}
    {regions : Values (RegionFunction model.Value (Effects model)) []} :
    localOperation model table (operations := operations) (.call callee permitted) arguments
        regions =
      table.get callee arguments :=
  rfl

/-- `if`: the selected region on the captures. -/
theorem localOperation_conditional {captures outputs : List Ty}
    {arguments : Values model.Value (.bool :: captures)}
    {onTrue onFalse : Region (LocalDialect operations functions deployed) (bindAll [] captures)
      outputs} :
    localOperation model table (operations := operations) (deployed := deployed)
        (.conditional captures outputs) arguments
        (Regions.denote (localMeaning model table)
          (Regions.cons onTrue (Regions.cons onFalse Regions.nil))) =
      cond (arguments.get .here)
        (onTrue.denote (localMeaning model table) (Environment.ofValues arguments.tail))
        (onFalse.denote (localMeaning model table) (Environment.ofValues arguments.tail)) := rfl

/-- `match`: the region of the alternative that the value is, on its payload and the
captures. -/
theorem localOperation_match {declaration : Nat} {alternatives captures outputs : List Ty}
    {arguments : Values model.Value (.variant declaration alternatives :: captures)}
    {bodies : Regions (LocalDialect operations functions deployed)
      (alternatives.map fun payload => (payload :: captures, outputs))} :
    localOperation model table (operations := operations) (deployed := deployed)
        (.match declaration alternatives captures outputs) arguments
        (bodies.denote (localMeaning model table)) =
      matchProcess model captures outputs alternatives (bodies.denote (localMeaning model table))
        (arguments.get .here) arguments.tail := rfl

/-- One iteration of a `loop`: its region on the iteration number, the carried values
and the captures. -/
abbrev loopBody {carried collected captures : List Ty}
    (body : Region (LocalDialect operations functions deployed)
      (bindAll [] (.nat :: (carried ++ captures))) (collected ++ carried)) :
    RegionFunction model.Value (Effects model)
      (.nat :: (carried ++ captures), collected ++ carried) :=
  fun values => body.denote (localMeaning model table) (Environment.ofValues values)

/-- `loop` over a count that is a value: the iteration of its region, within the maximum
if there is one. -/
theorem localOperation_loop {maximum : Option Nat} {carried collected captures : List Ty}
    {arguments : Values model.Value (.nat :: (carried ++ captures))}
    {body : Region (LocalDialect operations functions deployed)
      (bindAll [] (.nat :: (carried ++ captures))) (collected ++ carried)} :
    localOperation model table (operations := operations) (deployed := deployed)
        (.loop (.runtime maximum) carried collected captures) arguments
        (Regions.denote (localMeaning model table) (Regions.cons body Regions.nil)) =
      loopProcess model maximum carried collected captures (loopBody (table := table) body)
        (arguments.get .here) (arguments.tail.split carried).1 (arguments.tail.split carried).2 :=
  rfl

/-- `loop` over a count of the operation: the iteration of its region that many times. -/
theorem localOperation_staticLoop {count : Nat} {carried collected captures : List Ty}
    {arguments : Values model.Value (carried ++ captures)}
    {body : Region (LocalDialect operations functions deployed)
      (bindAll [] (.nat :: (carried ++ captures))) (collected ++ carried)} :
    localOperation model table (operations := operations) (deployed := deployed)
        (.loop (.static count) carried collected captures) arguments
        (Regions.denote (localMeaning model table) (Regions.cons body Regions.nil)) =
      staticLoopProcess model count carried collected captures (loopBody (table := table) body)
        (arguments.split carried).1 (arguments.split carried).2 :=
  rfl

theorem localOperation_guard {reason : Reason} {arguments : Values model.Value [.bool]}
    {regions : Values (RegionFunction model.Value (Effects model)) []} :
    localOperation model table (operations := operations) (deployed := deployed) (.guard reason)
        arguments regions =
      cond (arguments.get .here) (.done .nil) (.halt reason.stop) := rfl

variable (model)

/-- A value of the first alternative runs the first region on its payload and the
captures. -/
theorem matchProcess_first {payload : Ty} {rest captures outputs : List Ty}
    {first : RegionFunction model.Value (Effects model) (payload :: captures, outputs)}
    {others : Values (RegionFunction model.Value (Effects model))
      (rest.map fun payload => (payload :: captures, outputs))}
    (value : model.Value payload) (captured : Values model.Value captures) :
    matchProcess model captures outputs (payload :: rest) (.cons first others) (.inl value)
        captured =
      first (.cons value captured) := rfl

/-- A value of a later alternative runs the match over the other alternatives. -/
theorem matchProcess_later {payload : Ty} {rest captures outputs : List Ty}
    {first : RegionFunction model.Value (Effects model) (payload :: captures, outputs)}
    {others : Values (RegionFunction model.Value (Effects model))
      (rest.map fun payload => (payload :: captures, outputs))}
    (later : Ty.Variant model.Carrier rest) (captured : Values model.Value captures) :
    matchProcess model captures outputs (payload :: rest) (.cons first others) (.inr later)
        captured =
      matchProcess model captures outputs rest others later captured := rfl

/-- No iteration left: the carried values and what the iterations collected. -/
theorem loopIterations_zero (carried collected : List Ty)
    (step : Nat → Values model.Value carried →
      PIR.Process (Effects model) (Values model.Value (collected ++ carried)))
    (done : Nat) (state : Values model.Value carried)
    (earlier : Values model.Value (collectedSequences (some done) collected)) :
    loopIterations model carried collected step 0 done state earlier = .done (state, earlier) :=
  rfl

/-- One more iteration: the step on the iteration number and the carried values, then the
remaining iterations on the carried values it returns, with the values it collects put
before the earlier ones. -/
theorem loopIterations_succ (carried collected : List Ty)
    (step : Nat → Values model.Value carried →
      PIR.Process (Effects model) (Values model.Value (collected ++ carried)))
    (remaining done : Nat) (state : Values model.Value carried)
    (earlier : Values model.Value (collectedSequences (some done) collected)) :
    loopIterations model carried collected step (remaining + 1) done state earlier =
      (step done state).bind fun produced =>
        loopIterations model carried collected step remaining (done + 1)
          (produced.split collected).2
          (collectedPush model collected (produced.split collected).1 earlier) :=
  rfl

/-- The carried values of the iterations are those of the bounded iteration of the step
over the iteration number and the carried values. -/
theorem loopIterations_carried (carried collected : List Ty)
    (step : Nat → Values model.Value carried →
      PIR.Process (Effects model) (Values model.Value (collected ++ carried))) :
    ∀ (remaining done : Nat) (state : Values model.Value carried)
      (earlier : Values model.Value (collectedSequences (some done) collected)),
      ((loopIterations model carried collected step remaining done state earlier).bind
          fun final => .done final.1) =
        (PIR.repeatN remaining
          (fun (state : Nat × Values model.Value carried) =>
            (step state.1 state.2).bind fun produced =>
              .done (state.1 + 1, (produced.split collected).2))
          (done, state)).bind fun final => .done final.2
  | 0, _, _, _ => rfl
  | remaining + 1, done, state, earlier => by
      rw [loopIterations_succ, PIR.Process.bind_assoc]
      show _ = ((PIR.Process.bind _ _).bind _).bind _
      rw [PIR.Process.bind_assoc, PIR.Process.bind_assoc]
      congr 1
      funext produced
      exact loopIterations_carried carried collected step remaining (done + 1) _ _

/-- A loop over a count of the operation is the iteration of its region from the iteration
number 0: what the iterations collected, in their order, at the size that is the count,
then the carried values. -/
theorem staticLoopProcess_iterations (count : Nat) (carried collected captures : List Ty)
    (body : RegionFunction model.Value (Effects model)
      (.nat :: (carried ++ captures), collected ++ carried))
    (initial : Values model.Value carried) (captured : Values model.Value captures) :
    staticLoopProcess model count carried collected captures body initial captured =
      (loopIterations model carried collected
          (loopStep model carried collected captures body captured) count 0 initial
          (collectedNone model collected)).bind
        fun final => .done
          ((collectedSized model (iterationsAfter_eq count 0) collected final.2).append
            final.1) :=
  rfl

/-- A loop within its maximum is the iteration of its region from the iteration number 0:
what the iterations collected, in their order, then the carried values. -/
theorem loopProcess_within {maximum count : Nat} (within : count ≤ maximum)
    (carried collected captures : List Ty)
    (body : RegionFunction model.Value (Effects model)
      (.nat :: (carried ++ captures), collected ++ carried))
    (initial : Values model.Value carried) (captured : Values model.Value captures) :
    loopProcess model (some maximum) carried collected captures body count initial captured =
      (loopIterations model carried collected
          (loopStep model carried collected captures body captured) count 0 initial
          (collectedNone model collected)).bind
        fun final => .done ((collectedLists model collected final.2).append final.1) := by
  simp only [loopProcess, withinMaximum, Nat.ble_eq_true_of_le within, Bool.cond_true]

/-- A loop without a maximum is the iteration of its region whatever the count. -/
theorem loopProcess_unbounded (count : Nat) (carried collected captures : List Ty)
    (body : RegionFunction model.Value (Effects model)
      (.nat :: (carried ++ captures), collected ++ carried))
    (initial : Values model.Value carried) (captured : Values model.Value captures) :
    loopProcess model none carried collected captures body count initial captured =
      (loopIterations model carried collected
          (loopStep model carried collected captures body captured) count 0 initial
          (collectedNone model collected)).bind
        fun final => .done ((collectedLists model collected final.2).append final.1) :=
  rfl

theorem loopProcess_beyond {maximum count : Nat} (beyond : maximum < count)
    (carried collected captures : List Ty)
    (body : RegionFunction model.Value (Effects model)
      (.nat :: (carried ++ captures), collected ++ carried))
    (initial : Values model.Value carried) (captured : Values model.Value captures) :
    loopProcess model (some maximum) carried collected captures body count initial captured =
      .halt .undefined := by
  have above : Nat.ble count maximum = false := by
    cases within : Nat.ble count maximum with
    | false => rfl
    | true => exact absurd (Nat.le_of_ble_eq_true within) (Nat.not_le.mpr beyond)
  simp only [loopProcess, withinMaximum, above, Bool.cond_false]

end Local

/-! ## Protocol regions and operations for a side -/

section Iteration

variable (model : Model)

/-- No iteration left: the state and what the iterations collected. -/
theorem iterations_zero {I : PIR.Signature} {State Produced : Type} {Collected : Nat → Type}
    (step : Nat → State → PIR.Process I Produced) (carry : Produced → State)
    (push : (done : Nat) → Produced → Collected done → Collected (done + 1))
    (done : Nat) (state : State) (earlier : Collected done) :
    iterations step carry push 0 done state earlier = .done (state, earlier) := rfl

/-- One more iteration: the step on its number and the state, then the remaining
iterations from the next number on the state that follows, with what the step produced
pushed onto what was collected. -/
theorem iterations_succ {I : PIR.Signature} {State Produced : Type} {Collected : Nat → Type}
    (step : Nat → State → PIR.Process I Produced) (carry : Produced → State)
    (push : (done : Nat) → Produced → Collected done → Collected (done + 1))
    (remaining done : Nat) (state : State) (earlier : Collected done) :
    iterations step carry push (remaining + 1) done state earlier =
      (step done state).bind fun produced =>
        iterations step carry push remaining (done + 1) (carry produced)
          (push done produced earlier) := rfl

variable (side : Side)

/-- No iteration of a `repeat` left for a side: the carried values and what the holders in
the side collected. -/
theorem repeatIterations_zero (carried collected : List Located)
    (step : Nat → Values (SideValue model side) carried →
      PIR.Process (Effects model) (Values (SideValue model side) (collected ++ carried)))
    (done : Nat) (state : Values (SideValue model side) carried)
    (earlier : Values (SideValue model side) (collectedSequencesAt (some done) collected)) :
    repeatIterations model side carried collected step 0 done state earlier =
      .done (state, earlier) := rfl

/-- One more iteration of a `repeat` for a side: the step on the iteration number and the
carried values, then the remaining iterations on the carried values it returns, with the
values it collects put before the earlier ones at their holders. -/
theorem repeatIterations_succ (carried collected : List Located)
    (step : Nat → Values (SideValue model side) carried →
      PIR.Process (Effects model) (Values (SideValue model side) (collected ++ carried)))
    (remaining done : Nat) (state : Values (SideValue model side) carried)
    (earlier : Values (SideValue model side) (collectedSequencesAt (some done) collected)) :
    repeatIterations model side carried collected step (remaining + 1) done state earlier =
      (step done state).bind fun produced =>
        repeatIterations model side carried collected step remaining (done + 1)
          (produced.split collected).2
          (sideCollectedPush model side collected (produced.split collected).1 earlier) := rfl

/-- A count of the operation runs that many iterations from the iteration number 0,
whatever the participants hold: the sequences of the collected values at the size that is
the count, then the carried values. -/
theorem repeatProcess_static (number agreed : Nat) (carried collected : List Located)
    (step : Nat → Values (SideValue model side) carried →
      PIR.Process (Effects model) (Values (SideValue model side) (collected ++ carried)))
    (initial : Values (SideValue model side) carried) :
    repeatProcess model side (.static number) carried collected step agreed initial =
      (repeatIterations model side carried collected step number 0 initial
          (sideCollectedNone model side collected)).bind fun final =>
        .done ((sideCollectedSized model side (iterationsAfter_eq number 0) collected
          final.2).append final.1) := rfl

/-- A count that is a value, within its maximum, runs that many iterations: the unsized
sequences of the collected values, then the carried values. -/
theorem repeatProcess_within {maximum count : Nat} (within : count ≤ maximum)
    (carried collected : List Located)
    (step : Nat → Values (SideValue model side) carried →
      PIR.Process (Effects model) (Values (SideValue model side) (collected ++ carried)))
    (initial : Values (SideValue model side) carried) :
    repeatProcess model side (.runtime maximum) carried collected step count initial =
      (repeatIterations model side carried collected step count 0 initial
          (sideCollectedNone model side collected)).bind fun final =>
        .done ((sideCollectedLists model side collected final.2).append final.1) := by
  simp only [repeatProcess, within, ite_true]

/-- The iterations of a loop that collects nothing: the step run once per iteration number
below the count, from 0, within the maximum when the count is a value. -/
@[expose] def countedIterations {carried : Type} (count : RepeatCount)
    (step : Nat → carried → PIR.Process (Effects model) carried) (agreed : Nat)
    (initial : carried) : PIR.Process (Effects model) carried :=
  match count with
  | .static number => PIR.iterateN number step 0 initial
  | .runtime maximum =>
      if agreed ≤ maximum then PIR.iterateN agreed step 0 initial else .halt .undefined

/-- Iterations that collect nothing return the state of the bounded iteration of the
step. -/
theorem iterations_nothing {I : PIR.Signature} {State : Type} {Collected : Nat → Type}
    (step : Nat → State → PIR.Process I State)
    (push : (done : Nat) → State → Collected done → Collected (done + 1)) :
    ∀ (remaining done : Nat) (state : State) (earlier : Collected done),
      (iterations step (fun produced => produced) push remaining done state earlier).bind
          (fun final => .done final.1) =
        PIR.iterateN remaining step done state
  | 0, _, _, _ => rfl
  | remaining + 1, done, state, earlier => by
      show ((step done state).bind _).bind _ = (step done state).bind _
      rw [PIR.Process.bind_assoc]
      congr 1
      funext produced
      exact iterations_nothing step push remaining (done + 1) produced (push done produced earlier)

/-- A `repeat` that collects nothing is, for a side, the bounded iteration of its region on
the carried values. -/
theorem repeatProcess_nothing (count : RepeatCount) (carried : List Located)
    (step : Nat → Values (SideValue model side) carried →
      PIR.Process (Effects model) (Values (SideValue model side) carried))
    (agreed : Nat) (initial : Values (SideValue model side) carried) :
    repeatProcess model side count carried [] step agreed initial =
      countedIterations model count step agreed initial := by
  cases count with
  | static number => exact iterations_nothing step _ number 0 initial _
  | runtime maximum =>
      show (if agreed ≤ maximum then PIR.Process.bind _ _ else .halt .undefined) =
        (if agreed ≤ maximum then PIR.iterateN agreed step 0 initial else .halt .undefined)
      split
      · exact iterations_nothing step _ agreed 0 initial _
      · rfl

theorem repeatProcess_beyond {maximum count : Nat} (beyond : maximum < count)
    (carried collected : List Located)
    (step : Nat → Values (SideValue model side) carried →
      PIR.Process (Effects model) (Values (SideValue model side) (collected ++ carried)))
    (initial : Values (SideValue model side) carried) :
    repeatProcess model side (.runtime maximum) carried collected step count initial =
      .halt .undefined := by
  simp only [repeatProcess, Nat.not_le.mpr beyond, ite_false]

end Iteration

section Protocol

variable {model : Model} {operations : List OperationSignature}
  {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {side : Side} {label : Nat → Site}

/-- A step of a protocol region for a side: when the first operation's process is
`process`, the region is `process` followed by the rest in the extended
environment. -/
theorem sideMeaning_step {Γ out : List Located} {op : ProtocolOp operations functions protocols deployed}
    {arguments : Operands Γ op.arguments}
    {bodies : Regions (ProtocolDialect operations functions protocols deployed) op.regions}
    {next : Region (ProtocolDialect operations functions protocols deployed) (bindAll Γ op.results) out}
    {env : Environment (SideValue model side) Γ}
    {process : PIR.Process (Effects model) (Values (SideValue model side) op.results)}
    (step : labelledOperation model label functionTable table side op (Operands.eval env arguments)
      (bodies.denote (labelledMeaning model label functionTable table side)) = process) :
    (Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op arguments bodies
        next).denote (labelledMeaning model label functionTable table side) env =
      process.bind fun values => next.denote (labelledMeaning model label functionTable table side) (Environment.bindAll env values) := by
  rw [← step]; rfl

/-- A step whose operation returns without an effect: the rest of the region in the
environment extended by its results. -/
theorem sideMeaning_step_done {Γ out : List Located} {op : ProtocolOp operations functions protocols deployed}
    {arguments : Operands Γ op.arguments}
    {bodies : Regions (ProtocolDialect operations functions protocols deployed) op.regions}
    {next : Region (ProtocolDialect operations functions protocols deployed) (bindAll Γ op.results) out}
    {env : Environment (SideValue model side) Γ}
    {results : Values (SideValue model side) op.results}
    (step : labelledOperation model label functionTable table side op (Operands.eval env arguments)
      (bodies.denote (labelledMeaning model label functionTable table side)) = .done results) :
    (Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op arguments bodies
        next).denote (labelledMeaning model label functionTable table side) env =
      next.denote (labelledMeaning model label functionTable table side) (Environment.bindAll env results) := by
  rw [sideMeaning_step step]; rfl

/-- A step whose operation performs one effect: the effect, then the rest of the
region in the environment extended by the results for its reply. -/
theorem sideMeaning_step_call {Γ out : List Located} {op : ProtocolOp operations functions protocols deployed}
    {arguments : Operands Γ op.arguments}
    {bodies : Regions (ProtocolDialect operations functions protocols deployed) op.regions}
    {next : Region (ProtocolDialect operations functions protocols deployed) (bindAll Γ op.results) out}
    {env : Environment (SideValue model side) Γ} {effect : Effect model.Value}
    {results : Effect.Reply effect → Values (SideValue model side) op.results}
    (step : labelledOperation model label functionTable table side op (Operands.eval env arguments)
      (bodies.denote (labelledMeaning model label functionTable table side)) =
        .call effect fun reply => .done (results reply)) :
    (Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op arguments bodies
        next).denote (labelledMeaning model label functionTable table side) env =
      .call effect fun reply =>
        next.denote (labelledMeaning model label functionTable table side) (Environment.bindAll env (results reply)) := by
  rw [sideMeaning_step step]; rfl

/-- A step whose operation continues or stops on a condition, as a guard does. -/
theorem sideMeaning_step_guarded {Γ out : List Located}
    {op : ProtocolOp operations functions protocols deployed} {arguments : Operands Γ op.arguments}
    {bodies : Regions (ProtocolDialect operations functions protocols deployed) op.regions}
    {next : Region (ProtocolDialect operations functions protocols deployed) (bindAll Γ op.results) out}
    {env : Environment (SideValue model side) Γ} {condition : Bool}
    {results : Values (SideValue model side) op.results} {reason : PIR.Stop}
    (step : labelledOperation model label functionTable table side op (Operands.eval env arguments)
      (bodies.denote (labelledMeaning model label functionTable table side)) =
        cond condition (.done results) (.halt reason)) :
    (Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op arguments bodies
        next).denote (labelledMeaning model label functionTable table side) env =
      cond condition (next.denote (labelledMeaning model label functionTable table side) (Environment.bindAll env results))
        (.halt reason) := by
  rw [sideMeaning_step step]; cases condition <;> rfl

theorem sideMeaning_ret {Γ out : List Located} {values : Operands Γ out}
    {env : Environment (SideValue model side) Γ} :
    (Region.ret (dialect := ProtocolDialect operations functions protocols deployed) values).denote
        (labelledMeaning model label functionTable table side) env = .done (Operands.eval env values) := rfl

/-- `at(r, ℓ)` with `r` in the side: the local operation on `r`'s values. -/
theorem at_present {role : Nat} {op : LocalOp operations functions deployed}
    {bodies : Regions (LocalDialect operations functions deployed) op.regions} (member : side role = true)
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

/-- `at(r, ℓ)` with `r` outside the side: nothing. -/
theorem at_absent {role : Nat} {op : LocalOp operations functions deployed}
    {bodies : Regions (LocalDialect operations functions deployed) op.regions} (absent : side role = false)
    {arguments : Values (SideValue model side) (Located.atRole role op.arguments)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (.at role op bodies) arguments regions =
      .done (remapValues (F := SideValue model side) (fun type => ⟨type, role⟩) _
        (absentHeldValues (side role) absent op.results)) := by
  show (performStep model _ (side role) _).bind _ = _
  rw [performStep_absent model _ _ absent]
  rfl

/-- A pure row performed by a role in the side: the model's function. -/
theorem at_pure {role : Nat} {inputs outputs : List Ty}
    {row : Var operations ⟨inputs, outputs, .pure⟩}
    {applies : OperationSignature.applies ⟨inputs, outputs, .pure⟩ = true}
    {bodies : Regions (LocalDialect operations functions deployed) []}
    (member : side role = true)
    {arguments : Values (SideValue model side) (Located.atRole role inputs)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (.at role (.op row applies) bodies) arguments regions =
      .done (remapValues (F := SideValue model side) (fun type => ⟨type, role⟩) _
        (holdValues (side role)
          (model.pure (.of row) applies
            (presentValues (side role) member (unmapValues _ _ arguments))))) :=
  at_present (op := .op row applies) member

/-- A restricted row performed by a role in the side: the model's value where it is
defined, or the stop `undefined` outside its domain. -/
theorem at_restricted {role : Nat} {inputs outputs : List Ty} {domain : Option Nat}
    {row : Var operations ⟨inputs, outputs, .restricted domain⟩}
    {applies : OperationSignature.applies ⟨inputs, outputs, .restricted domain⟩ = true}
    {bodies : Regions (LocalDialect operations functions deployed) []}
    (member : side role = true)
    {arguments : Values (SideValue model side) (Located.atRole role inputs)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (.at role (.op row applies) bodies) arguments regions =
      (definedProcess model (model.restricted (.of row)
          (presentValues (side role) member (unmapValues _ _ arguments)))).bind fun values =>
        .done (remapValues (F := SideValue model side) (fun type => ⟨type, role⟩) _
          (holdValues (side role) values)) :=
  at_present (op := .op row applies) member

/-- An operation the core owns, performed by a role in the side: its value where it is
defined, or the stop `undefined` outside its domain. -/
theorem at_builtin {role : Nat} {operation : Builtin}
    {bodies : Regions (LocalDialect operations functions deployed) []}
    (member : side role = true)
    {arguments : Values (SideValue model side) (Located.atRole role operation.arguments)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (.at role (.builtin operation) bodies)
        arguments regions =
      (definedProcess model (operation.eval
          (presentValues (side role) member (unmapValues _ _ arguments)))).bind fun values =>
        .done (remapValues (F := SideValue model side) (fun type => ⟨type, role⟩) _
          (holdValues (side role) values)) :=
  at_present (op := .builtin operation) member

/-- A function called by a role in the side: its entry in the table. -/
theorem at_call {role : Nat} {header : FunctionHeader} {callee : Var functions header}
    {permitted : (deployed && header.specificationOnly) = false}
    {bodies : Regions (LocalDialect operations functions deployed) []}
    (member : side role = true)
    {arguments : Values (SideValue model side) (Located.atRole role header.inputs)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (operations := operations) (.at role (.call callee permitted) bodies)
        arguments regions =
      (functionTable.get callee (presentValues (side role) member (unmapValues _ _ arguments))).bind
        fun values => .done (remapValues (F := SideValue model side) (fun type => ⟨type, role⟩) _
          (holdValues (side role) values)) :=
  at_present (op := .call callee permitted) member

/-- A `match` of a role in the side: the region of the alternative that the role's value
is, on its payload and the role's captures. -/
theorem at_match {role declaration : Nat} {alternatives captures outputs : List Ty}
    {bodies : Regions (LocalDialect operations functions deployed)
      (alternatives.map fun payload => (payload :: captures, outputs))}
    (member : side role = true)
    {arguments : Values (SideValue model side)
      (Located.atRole role (.variant declaration alternatives :: captures))}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side
        (.at role (.match declaration alternatives captures outputs) bodies) arguments regions =
      (matchProcess model captures outputs alternatives
          (bodies.denote (localMeaning model functionTable))
          ((presentValues (X := model.Value) (side role) member
            (unmapValues (F := SideValue model side) (fun type => ⟨type, role⟩)
              (.variant declaration alternatives :: captures) arguments)).get .here)
          (presentValues (X := model.Value) (side role) member
            (unmapValues (F := SideValue model side) (fun type => ⟨type, role⟩)
              (.variant declaration alternatives :: captures) arguments)).tail).bind fun values =>
        .done (remapValues (F := SideValue model side) (fun type => ⟨type, role⟩) _
          (holdValues (side role) values)) :=
  at_present (op := .match declaration alternatives captures outputs) member

/-- A guard of a role in the side: continue when the condition holds, stop with the
authored reason otherwise. -/
theorem at_guard {role : Nat} {reason : Reason}
    {bodies : Regions (LocalDialect operations functions deployed) []}
    (member : side role = true)
    {arguments : Values (SideValue model side) (Located.atRole role [.bool])}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (operations := operations) (deployed := deployed)
        (.at role (.guard reason) bodies) arguments regions =
      cond (Held.value (side role) member (arguments.get .here)) (.done .nil) (.halt reason.stop) := by
  refine (at_present (op := .guard reason) member).trans ?_
  match arguments with
  | .cons condition .nil =>
    simp only [unmapValues_cons, presentValues_cons, Values.get_here]
    cases Held.value (side role) member condition <;> rfl

theorem exchange_internal {sender receiver site : Nat} {type : Ty}
    (senderMember : side sender = true) (receiverMember : side receiver = true)
    {arguments : Values (SideValue model side) [⟨type, sender⟩]}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (operations := operations) (deployed := deployed)
        (.exchange sender receiver site type) arguments regions =
      .done (.cons (Held.of (side receiver)
        (Held.value (side sender) senderMember (arguments.get .here))) .nil) := by
  show (exchangeStep model _ type (side sender) (side receiver) _).bind _ = _
  rw [exchangeStep_internal model type _ _ senderMember receiverMember]
  rfl

theorem exchange_send {sender receiver site : Nat} {type : Ty}
    (senderMember : side sender = true) (receiverAbsent : side receiver = false)
    {arguments : Values (SideValue model side) [⟨type, sender⟩]}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (operations := operations) (deployed := deployed)
        (.exchange sender receiver site type) arguments regions =
      .call (.send (label site) type
          (Held.value (side sender) senderMember (arguments.get .here))) fun _ =>
        .done (.cons (Held.absent (side receiver) receiverAbsent) .nil) := by
  show (exchangeStep model _ type (side sender) (side receiver) _).bind _ = _
  rw [exchangeStep_send model type _ _ senderMember receiverAbsent]
  rfl

theorem exchange_receive {sender receiver site : Nat} {type : Ty}
    (senderAbsent : side sender = false) (receiverMember : side receiver = true)
    {arguments : Values (SideValue model side) [⟨type, sender⟩]}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (operations := operations) (deployed := deployed)
        (.exchange sender receiver site type) arguments regions =
      .call (.receive (label site) type) fun reply =>
        .done (.cons (Held.of (side receiver) reply) .nil) := by
  show (exchangeStep model _ type (side sender) (side receiver) _).bind _ = _
  rw [exchangeStep_receive model type _ _ senderAbsent receiverMember]
  rfl

theorem exchange_outside {sender receiver site : Nat} {type : Ty}
    (senderAbsent : side sender = false) (receiverAbsent : side receiver = false)
    {arguments : Values (SideValue model side) [⟨type, sender⟩]}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (operations := operations) (deployed := deployed)
        (.exchange sender receiver site type) arguments regions =
      .done (.cons (Held.absent (side receiver) receiverAbsent) .nil) := by
  show (exchangeStep model _ type (side sender) (side receiver) _).bind _ = _
  rw [exchangeStep_outside model type _ _ senderAbsent receiverAbsent]
  rfl

/-- The owner is in the side: it draws, and every copy in the side is the coin. -/
theorem draw_owner {owner site : Nat} {receivers : List Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩}
    {populated : output.populated = true} (member : side owner = true)
    {arguments : Values (SideValue model side) (Located.atRole owner inputs)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (deployed := deployed) (.draw owner receivers site law populated)
        arguments regions =
      .call (.draw (label site) (.of law populated)
          (presentValues (side owner) member (unmapValues _ _ arguments))) fun reply =>
        .done (broadcast model side owner receivers output reply) :=
  drawStep_owner model _ _ _ member _ _

/-- The owner is outside the side: each receiver in the side receives its own copy. -/
theorem draw_outside {owner site : Nat} {receivers : List Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩}
    {populated : output.populated = true} (absent : side owner = false)
    {arguments : Values (SideValue model side) (Located.atRole owner inputs)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (deployed := deployed) (.draw owner receivers site law populated)
        arguments regions =
      (receiverReplies model side (label site) output receivers).bind fun replies =>
        .done (.cons (Held.absent (side owner) absent) replies) :=
  drawStep_outside model _ _ _ absent _ _

/-- The owner is outside the side and its one receiver is inside: the receiver's own
`receive`. -/
theorem draw_received {owner receiver site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩}
    {populated : output.populated = true} (absent : side owner = false)
    (member : side receiver = true)
    {arguments : Values (SideValue model side) (Located.atRole owner inputs)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (deployed := deployed) (.draw owner [receiver] site law populated)
        arguments regions =
      .call (.receive (label site) output) fun reply =>
        .done (.cons (Held.absent (side owner) absent)
          (.cons (Held.of (side receiver) reply) .nil)) := by
  rw [draw_outside absent, receiverReplies_present model side _ output receiver [] member]
  rfl

theorem sample_owner {owner site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩}
    {populated : output.populated = true} (member : side owner = true)
    {arguments : Values (SideValue model side) (Located.atRole owner inputs)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (deployed := deployed) (.sample owner site law populated) arguments
        regions =
      .call (.sample (label site) (.of law populated)
          (presentValues (side owner) member (unmapValues _ _ arguments))) fun reply =>
        .done (.cons (Held.of (side owner) reply) .nil) := by
  show (sampleStep model _ _ (side owner) _).bind _ = _
  rw [sampleStep_owner model _ _ member]
  rfl

theorem sample_outside {owner site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩}
    {populated : output.populated = true} (absent : side owner = false)
    {arguments : Values (SideValue model side) (Located.atRole owner inputs)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (deployed := deployed) (.sample owner site law populated) arguments
        regions =
      .done (.cons (Held.absent (side owner) absent) .nil) := by
  show (sampleStep model _ _ (side owner) _).bind _ = _
  rw [sampleStep_outside model _ _ absent]
  rfl

/-- The copies of the count that the participants of a `repeat` hold: its count operands,
or the count of the operation. -/
abbrev repeatCounts {participants : List Nat} {count : RepeatCount}
    {carried captures : List Located}
    (arguments : Values (SideValue model side)
      (count.operands participants ++ (carried ++ captures))) :
    Values (fun role => Held Nat (side role)) participants :=
  repeatCopies model side participants count (arguments.split (count.operands participants)).1

/-- The carried values that enter a `repeat`. -/
abbrev repeatInitial {participants : List Nat} {count : RepeatCount}
    {carried captures : List Located}
    (arguments : Values (SideValue model side)
      (count.operands participants ++ (carried ++ captures))) :
    Values (SideValue model side) carried :=
  ((arguments.split (count.operands participants)).2.split carried).1

/-- The captures of a `repeat`. -/
abbrev repeatCaptured {participants : List Nat} {count : RepeatCount}
    {carried captures : List Located}
    (arguments : Values (SideValue model side)
      (count.operands participants ++ (carried ++ captures))) :
    Values (SideValue model side) captures :=
  ((arguments.split (count.operands participants)).2.split carried).2

/-- One iteration of a `repeat`: its region on the iteration number, which each
participant in the side holds, the carried values and the captures. -/
abbrev repeatBody {participants : List Nat} {carried collected captures : List Located}
    (captured : Values (SideValue model side) captures)
    (body : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll [] (Located.ofRoles .nat participants ++ (carried ++ captures)))
      (collected ++ carried))
    (iteration : Nat) (values : Values (SideValue model side) carried) :
    PIR.Process (Effects model) (Values (SideValue model side) (collected ++ carried)) :=
  body.denote (labelledMeaning model label functionTable table side) (Environment.ofValues
    ((heldCopies model side .nat iteration participants).append (values.append captured)))

/-- The results of a `repeat` for a side without a participant: no collected sequence is
held in the side, and the carried values are the operands. -/
abbrev repeatOutside {participants : List Nat} {count : RepeatCount}
    {carried collected captures : List Located}
    (covered : Located.heldBy participants collected = true)
    (arguments : Values (SideValue model side)
      (count.operands participants ++ (carried ++ captures)))
    (none : participants.any side = false) :
    Values (SideValue model side) (collectedSequencesAt count.size collected ++ carried) :=
  (absentSequences model side count.size collected fun _ member =>
    not_held_of_heldBy covered none member).append (repeatInitial arguments)

/-- `repeat` selects the count its participants in the side agree on and runs the
iterations; disagreement stops `incomplete`, before the count is compared with the
maximum; with no participant in the side it returns the carried values, and no collected
sequence is held in the side. -/
theorem repeat_meaning {participants : List Nat} {count : RepeatCount}
    {carried collected captures : List Located}
    {covered : Located.heldBy participants collected = true}
    {arguments : Values (SideValue model side)
      (count.operands participants ++ (carried ++ captures))}
    {body : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll [] (Located.ofRoles .nat participants ++ (carried ++ captures)))
      (collected ++ carried)} :
    labelledOperation model label functionTable table side (operations := operations) (deployed := deployed)
        (.repeat participants count carried collected captures covered) arguments
        (Regions.denote (labelledMeaning model label functionTable table side) (Regions.cons body Regions.nil)) =
      agreed Nat.beq side
        (fun agreed => repeatProcess model side count carried collected
          (repeatBody (label := label) (functionTable := functionTable) (table := table)
            (repeatCaptured arguments) body) agreed (repeatInitial arguments))
        (.halt .incomplete) participants (repeatCounts arguments)
        fun none => .done (repeatOutside covered arguments none) := rfl

/-- Equal counts held by the participants in the side (one or several): the iterations of
the region. -/
theorem repeat_agreed {participants : List Nat} {count : RepeatCount}
    {carried collected captures : List Located}
    {covered : Located.heldBy participants collected = true}
    {arguments : Values (SideValue model side)
      (count.operands participants ++ (carried ++ captures))}
    {body : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll [] (Located.ofRoles .nat participants ++ (carried ++ captures)))
      (collected ++ carried)}
    (agreed : Nat)
    (equal : ∀ {role : Nat} (position : Var participants role) (member : side role = true),
      Held.value (side role) member ((repeatCounts arguments).get position) = agreed)
    (inside : participants.any side = true) :
    labelledOperation model label functionTable table side (operations := operations) (deployed := deployed)
        (.repeat participants count carried collected captures covered) arguments
        (Regions.denote (labelledMeaning model label functionTable table side) (Regions.cons body Regions.nil)) =
      repeatProcess model side count carried collected
        (repeatBody (label := label) (functionTable := functionTable) (table := table)
          (repeatCaptured arguments) body) agreed (repeatInitial arguments) := by
  rw [repeat_meaning]
  exact agreed_equal Nat.beq side _ _ Nat.beq_refl agreed participants _ _ equal inside

/-- Two participants in the side hold different counts: the side stops `incomplete`. -/
theorem repeat_disagree {participants : List Nat} {count : RepeatCount}
    {carried collected captures : List Located}
    {covered : Located.heldBy participants collected = true}
    {arguments : Values (SideValue model side)
      (count.operands participants ++ (carried ++ captures))}
    {body : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll [] (Located.ofRoles .nat participants ++ (carried ++ captures)))
      (collected ++ carried)}
    {first second : Nat} (firstPosition : Var participants first)
    (secondPosition : Var participants second) (firstMember : side first = true)
    (secondMember : side second = true)
    (differ : Held.value (side first) firstMember ((repeatCounts arguments).get firstPosition) ≠
      Held.value (side second) secondMember ((repeatCounts arguments).get secondPosition)) :
    labelledOperation model label functionTable table side (operations := operations) (deployed := deployed)
        (.repeat participants count carried collected captures covered) arguments
        (Regions.denote (labelledMeaning model label functionTable table side) (Regions.cons body Regions.nil)) =
      .halt .incomplete := by
  rw [repeat_meaning]
  exact agreed_unequal Nat.beq side _ _ nat_beq_decides participants _ _ firstPosition
    secondPosition firstMember secondMember differ

/-- Every copy of a count of the operation that a participant in the side holds is the
count. -/
theorem staticCopies_get (model : Model) (side : Side) (number : Nat) :
    ∀ (participants : List Nat) {role : Nat} (position : Var participants role)
      (member : side role = true),
      Held.value (side role) member
          ((repeatCopies model side participants (.static number) .nil).get position) =
        number
  | _ :: rest, _, position, member => by
      cases position with
      | here => exact Held.value_of _ member number
      | there position => exact staticCopies_get model side number rest position member

/-- A count of the operation, with a participant in the side: that many iterations of the
region, whatever the roles hold. -/
theorem repeat_static {participants : List Nat} {number : Nat}
    {carried collected captures : List Located}
    {covered : Located.heldBy participants collected = true}
    {arguments : Values (SideValue model side) (carried ++ captures)}
    {body : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll [] (Located.ofRoles .nat participants ++ (carried ++ captures)))
      (collected ++ carried)}
    (inside : participants.any side = true) :
    labelledOperation model label functionTable table side (operations := operations) (deployed := deployed)
        (.repeat participants (.static number) carried collected captures covered) arguments
        (Regions.denote (labelledMeaning model label functionTable table side) (Regions.cons body Regions.nil)) =
      repeatProcess model side (.static number) carried collected
        (repeatBody (label := label) (functionTable := functionTable) (table := table)
          (arguments.split carried).2 body) number (arguments.split carried).1 :=
  repeat_agreed (count := .static number) number
    (staticCopies_get model side number participants) inside

/-- The copies of the tag that the participants of a `choose` hold: its first
operands. -/
abbrev chooseTags {participants : List Nat} {tag : ChoiceTag} {captures : List Located}
    (arguments : Values (SideValue model side) (Located.ofRoles tag.type participants ++ captures)) :
    Values (fun role => Held (model.Value tag.type) (side role)) participants :=
  unmapValues (F := SideValue model side) (fun role => ⟨tag.type, role⟩) participants
    (arguments.split (Located.ofRoles tag.type participants)).1

/-- The region of a `choose` that a tag selects: on the captures, and for an alternative of
a variant on the payloads of the participants in the side before them. -/
abbrev chooseSelected {participants : List Nat} {tag : ChoiceTag} {captures outputs : List Located}
    (arguments : Values (SideValue model side) (Located.ofRoles tag.type participants ++ captures))
    (arms : Regions (ProtocolDialect operations functions protocols deployed)
      (tag.regions participants captures outputs))
    (value : model.Value tag.type) :
    PIR.Process (Effects model) (Values (SideValue model side) outputs) :=
  chosenRegion model side participants captures outputs tag
    (Regions.denote (labelledMeaning model label functionTable table side) arms)
    (chooseTags arguments) (arguments.split (Located.ofRoles tag.type participants)).2 value

/-- `choose` runs the region its participants in the side agree on; disagreement
stops `incomplete`; with no participant in the side its results are absent. -/
theorem choose_meaning {participants : List Nat} {tag : ChoiceTag} {captures outputs : List Located}
    {covered : Located.heldBy participants outputs = true}
    {arguments : Values (SideValue model side) (Located.ofRoles tag.type participants ++ captures)}
    {arms : Regions (ProtocolDialect operations functions protocols deployed)
      (tag.regions participants captures outputs)} :
    labelledOperation model label functionTable table side (operations := operations) (deployed := deployed)
        (.choose participants tag captures outputs covered) arguments
        (Regions.denote (labelledMeaning model label functionTable table side) arms) =
      agreed (tag.same model.Carrier) side
        (chooseSelected (label := label) (functionTable := functionTable) (table := table) arguments arms)
        (.halt .incomplete) participants (chooseTags arguments)
        fun none => .done (absentOutputs model side outputs fun _ member =>
          not_held_of_heldBy covered none member) := rfl

/-- The test of two tags decides whether they are the same: equal conditions, equal arm
numbers, the same alternative of a variant. -/
theorem ChoiceTag.same_decides (Carrier : Nat → Type) :
    ∀ (tag : ChoiceTag) (left right : Ty.Value Carrier tag.type),
      tag.same Carrier left right = true ↔ tag.Same Carrier left right
  | .condition, left, right => agreeBool_decides left right
  | .arm _, left, right => (nat_beq_decides left.val right.val).trans Fin.val_inj
  | .alternative _ alternatives, left, right =>
      nat_beq_decides (alternativeNumber alternatives left) (alternativeNumber alternatives right)

/-- The same tags held by the participants in the side: the selected region. Copies of a
condition or of an arm number are the same when they are equal, and copies of a variant
when they are the same alternative. -/
theorem choose_agreed {participants : List Nat} {tag : ChoiceTag} {captures outputs : List Located}
    {covered : Located.heldBy participants outputs = true}
    {arguments : Values (SideValue model side) (Located.ofRoles tag.type participants ++ captures)}
    {arms : Regions (ProtocolDialect operations functions protocols deployed)
      (tag.regions participants captures outputs)}
    (value : model.Value tag.type)
    (equal : ∀ {role : Nat} (position : Var participants role) (member : side role = true),
      tag.Same model.Carrier
        (Held.value (side role) member ((chooseTags arguments).get position)) value)
    (inside : participants.any side = true) :
    labelledOperation model label functionTable table side (operations := operations) (deployed := deployed)
        (.choose participants tag captures outputs covered) arguments
        (Regions.denote (labelledMeaning model label functionTable table side) arms) =
      chooseSelected (label := label) (functionTable := functionTable) (table := table) arguments arms value := by
  rw [choose_meaning]
  cases tag with
  | condition =>
    exact agreed_equal agreeBool side _ _ (fun value => (agreeBool_decides value value).mpr rfl)
      value participants _ _ equal inside
  | arm count =>
    exact agreed_equal _ side _ _
      (fun value => (ChoiceTag.same_decides model.Carrier (.arm count) value value).mpr rfl)
      value participants _ _ equal inside
  | alternative declaration alternatives =>
    refine (agreed_key side _ (alternativeNumber alternatives) Nat.beq
      (fun number => alternativeProcess model side participants captures outputs alternatives
        _ number (chooseTags arguments) _) participants (chooseTags arguments) _).trans ?_
    exact agreed_equal Nat.beq side _ _ Nat.beq_refl (alternativeNumber alternatives value)
      participants _ _
      (fun position member => (keys_get side _ participants _ position member).trans
        (equal position member))
      inside

/-- Two participants in the side hold tags that are not the same: the side stops
`incomplete`. Two copies of a condition or of an arm number are not the same when they
differ, and two copies of a variant when they are different alternatives. -/
theorem choose_disagree {participants : List Nat} {tag : ChoiceTag} {captures outputs : List Located}
    {covered : Located.heldBy participants outputs = true}
    {arguments : Values (SideValue model side) (Located.ofRoles tag.type participants ++ captures)}
    {arms : Regions (ProtocolDialect operations functions protocols deployed)
      (tag.regions participants captures outputs)}
    {first second : Nat} (firstPosition : Var participants first)
    (secondPosition : Var participants second) (firstMember : side first = true)
    (secondMember : side second = true)
    (differ : ¬ tag.Same model.Carrier
      (Held.value (side first) firstMember ((chooseTags arguments).get firstPosition))
      (Held.value (side second) secondMember ((chooseTags arguments).get secondPosition))) :
    labelledOperation model label functionTable table side (operations := operations) (deployed := deployed)
        (.choose participants tag captures outputs covered) arguments
        (Regions.denote (labelledMeaning model label functionTable table side) arms) =
      .halt .incomplete := by
  rw [choose_meaning]
  cases tag with
  | condition =>
    exact agreed_unequal agreeBool side _ _ agreeBool_decides participants _ _ firstPosition
      secondPosition firstMember secondMember differ
  | arm count =>
    exact agreed_unequal _ side _ _ (ChoiceTag.same_decides model.Carrier (.arm count))
      participants _ _ firstPosition secondPosition firstMember secondMember differ
  | alternative declaration alternatives =>
    refine (agreed_key side _ (alternativeNumber alternatives) Nat.beq
      (fun number => alternativeProcess model side participants captures outputs alternatives
        _ number (chooseTags arguments) _) participants (chooseTags arguments) _).trans ?_
    refine agreed_unequal Nat.beq side _ _ nat_beq_decides participants _ _ firstPosition
      secondPosition firstMember secondMember ?_
    rw [keys_get side _ participants _ firstPosition firstMember,
      keys_get side _ participants _ secondPosition secondMember]
    exact differ

/-- Copies that are found, with one more before them: the first one and the later ones
are found. -/
theorem consFound_some {F : Nat → Type} {role : Nat} {rest : List Nat} :
    ∀ (head : Option (F role)) (tail : Option (Values F rest)) (values : Values F (role :: rest)),
      consFound head tail = some values →
        ∃ first later, head = some first ∧ tail = some later ∧ values = .cons first later
  | some first, some later, _, found => ⟨first, later, rfl, rfl, (Option.some.inj found).symm⟩
  | none, _, _, found => nomatch found
  | some _, none, _, found => nomatch found

/-- The region of the first alternative of a variant runs on the payloads of the
participants in the side and the captures, when every copy held in the side is that
alternative. -/
theorem alternativeProcess_first {participants : List Nat} {captures outputs : List Located}
    {payload : Ty} {rest : List Ty}
    {regions : Values (RegionFunction (SideValue model side) (Effects model))
      ((payload :: rest).map fun payload =>
        (Located.ofRoles payload participants ++ captures, outputs))}
    {copies : Values (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (side role))
      participants}
    {captured : Values (SideValue model side) captures}
    {payloads : Values (fun role => Held (model.Value payload) (side role)) participants}
    (found : firstPayloads model side payload rest participants copies = some payloads) :
    alternativeProcess model side participants captures outputs (payload :: rest) regions 0
        copies captured =
      (regions.get .here)
        ((remapValues (F := SideValue model side) (fun role => ⟨payload, role⟩) participants
          payloads).append captured) := by
  simp only [alternativeProcess, found]

/-- A copy held in the side that is a later alternative stops the region of the first
alternative `incomplete`. -/
theorem alternativeProcess_first_other {participants : List Nat}
    {captures outputs : List Located} {payload : Ty} {rest : List Ty}
    {regions : Values (RegionFunction (SideValue model side) (Effects model))
      ((payload :: rest).map fun payload =>
        (Located.ofRoles payload participants ++ captures, outputs))}
    {copies : Values (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (side role))
      participants}
    {captured : Values (SideValue model side) captures}
    (missing : firstPayloads model side payload rest participants copies = none) :
    alternativeProcess model side participants captures outputs (payload :: rest) regions 0
        copies captured =
      .halt .incomplete := by
  simp only [alternativeProcess, missing]

/-- The region of a later alternative is the region of that alternative among the later
ones, on the copies as copies of the variant of the later alternatives, when no copy held
in the side is the first alternative. -/
theorem alternativeProcess_later {participants : List Nat} {captures outputs : List Located}
    {payload : Ty} {rest : List Ty}
    {regions : Values (RegionFunction (SideValue model side) (Effects model))
      ((payload :: rest).map fun payload =>
        (Located.ofRoles payload participants ++ captures, outputs))}
    {copies : Values (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (side role))
      participants}
    {captured : Values (SideValue model side) captures} (number : Nat)
    {later : Values (fun role => Held (Ty.Variant model.Carrier rest) (side role)) participants}
    (found : laterCopies model side payload rest participants copies = some later) :
    alternativeProcess model side participants captures outputs (payload :: rest) regions
        (number + 1) copies captured =
      alternativeProcess model side participants captures outputs rest regions.tail number later
        captured := by
  simp only [alternativeProcess, found]

/-- A copy held in the side that is the first alternative stops the region of a later
alternative `incomplete`. -/
theorem alternativeProcess_later_other {participants : List Nat}
    {captures outputs : List Located} {payload : Ty} {rest : List Ty}
    {regions : Values (RegionFunction (SideValue model side) (Effects model))
      ((payload :: rest).map fun payload =>
        (Located.ofRoles payload participants ++ captures, outputs))}
    {copies : Values (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (side role))
      participants}
    {captured : Values (SideValue model side) captures} (number : Nat)
    (missing : laterCopies model side payload rest participants copies = none) :
    alternativeProcess model side participants captures outputs (payload :: rest) regions
        (number + 1) copies captured =
      .halt .incomplete := by
  simp only [alternativeProcess, missing]

/-- The region of a `choose` that a condition selects, as a conditional: the second of the
two regions when the condition holds, the first otherwise. -/
theorem selectArm_ite {I : PIR.Signature} {Ty : Type} {Value : Ty → Type}
    {signature : List Ty × List Ty}
    (regions : Values (RegionFunction Value I) (List.replicate 2 signature)) (condition : Bool) :
    selectArm signature 2 regions (if condition = true then 1 else 0) =
      if condition = true then regions.get (Var.there .here) else regions.get .here := by
  cases condition
  · rfl
  · cases regions with
    | cons first rest => rfl

/-- A condition that does not hold selects the first of the two regions of a branch, and
one that holds selects the second. -/
theorem selectArm_condition {I : PIR.Signature} {Ty : Type} {Value : Ty → Type}
    {signature : List Ty × List Ty}
    (regions : Values (RegionFunction Value I) (List.replicate 2 signature)) (condition : Bool) :
    selectArm signature 2 regions (cond condition 1 0) =
      cond condition (regions.get (Var.there .here)) (regions.get .here) := by
  cases condition
  · rfl
  · cases regions with
    | cons first rest => rfl

/-- `apply` runs the callee's entry in the table for the preimage side. -/
theorem apply_meaning {header : ProtocolHeader} {callee : Var protocols header}
    {roleMap : RoleMap} {site : Nat} {permitted : (deployed && header.specificationOnly) = false}
    {arguments : Values (SideValue model side) (header.inputs.map (Located.rename roleMap))}
    {regions : Values (RegionFunction (SideValue model side) (Effects model)) []} :
    labelledOperation model label functionTable table side (operations := operations)
        (.apply callee roleMap site permitted) arguments regions =
      ((table.get callee) (label site).below (Side.preimage roleMap side)
          (unmapValues (F := SideValue model side) (Located.rename roleMap) _ arguments)).bind
        fun values => .done (remapValues (F := SideValue model side) (Located.rename roleMap) _ values) :=
  rfl

end Protocol

/-! ## Programs -/

section Programs

variable (model : Model) {typeTable : TypeTable} {operations : List OperationSignature}

/-- The meaning of a function is its body over the table of the earlier functions. -/
theorem FunctionDefinition.meaning_eq {functions : List FunctionHeader} {header : FunctionHeader}
    (table : FunctionTable model functions)
    (definition : FunctionDefinition operations functions header)
    (arguments : Values model.Value header.inputs) :
    definition.meaning model table arguments =
      definition.body.denote (localMeaning model table) (Environment.ofValues arguments) := rfl

/-- The meaning of a protocol for a side is its body over the tables of the functions
and of the earlier protocols. -/
theorem ProtocolDefinition.meaning_eq {functions : List FunctionHeader}
    {protocols : List ProtocolHeader} {header : ProtocolHeader}
    (functionTable : FunctionTable model functions) (table : ProtocolTable model protocols)
    (definition : ProtocolDefinition operations functions protocols header) (identity : Nat)
    (path : List Nat) (side : Side) (arguments : Values (SideValue model side) header.inputs) :
    definition.meaning model functionTable table identity path side arguments =
      definition.body.denote (sideMeaning model functionTable table identity path side)
        (Environment.ofValues arguments) := rfl

/-- The table of the functions is the meaning of the last one followed by the table of
the earlier ones. -/
theorem Functions.table_snoc {functions : List FunctionHeader} {header : FunctionHeader}
    (earlier : Functions typeTable operations functions)
    (definition : FunctionDefinition operations functions header)
    (wellFormed : definition.violation typeTable = none) :
    (Functions.snoc earlier definition wellFormed).table model =
      .cons (definition.meaning model (earlier.table model)) (earlier.table model) := rfl

theorem Protocols.table_snoc {functions : List FunctionHeader} {protocols : List ProtocolHeader}
    {header : ProtocolHeader} (functionTable : FunctionTable model functions)
    (earlier : Protocols typeTable operations functions protocols)
    (definition : ProtocolDefinition operations functions protocols header)
    (wellFormed : definition.violation typeTable = none) (identities : Identities) :
    (Protocols.snoc earlier definition wellFormed).table model functionTable identities =
      .cons (definition.meaning model functionTable (earlier.table model functionTable identities)
          (identities protocols.length))
        (earlier.table model functionTable identities) := rfl

end Programs

end Zkc.Core
