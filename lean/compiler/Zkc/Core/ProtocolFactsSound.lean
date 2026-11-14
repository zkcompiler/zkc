module

public import Zkc.Core.ProtocolFactsHold

public section

/-! A protocol that passes the check of facts never stops `undefined`, for any side.

For every model that satisfies the domain laws of its restricted rows and every side, the
meaning for that side of a protocol whose body passes the check, over functions and
protocols that never stop `undefined`, never stops `undefined`, on any values and through
every reply of every effect: what the roles outside the side do reaches the side as
replies, and the statement holds for all of them.

The proof follows the check. What the roles know holds of the side's environment at each
instruction (`RoleFacts.Sound`): the facts of every role of the side hold of the values
that the side holds. A local operation that a role of the side performs is the local
operation on the role's values, so the theorem of the local check applies to it. A role
outside the side performs nothing in the side's process, and nothing is required of what
it knows. A stop `incomplete`, where two roles of the side disagree on a control value,
and a stop `refused` are not `undefined`.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

variable {model : Model}

/-! ## Presence steps -/

theorem exchangeStep_yields (site : Site) (type : Ty) : ∀ (sender receiver : Bool)
    (value : Held (model.Value type) sender),
    Yields (fun _ => True) (exchangeStep model site type sender receiver value)
  | true, true, _ => Yields.done trivial
  | true, false, _ => Yields.call fun _ => Yields.done trivial
  | false, true, _ => Yields.call fun _ => Yields.done trivial
  | false, false, _ => Yields.done trivial

theorem receiveStep_yields (site : Site) (type : Ty) : ∀ (receiver : Bool),
    Yields (fun _ => True) (receiveStep model site type receiver)
  | true => Yields.call fun _ => Yields.done trivial
  | false => Yields.done trivial

theorem receiverReplies_yields (side : Side) (site : Site) (type : Ty) : ∀ (receivers : List Nat),
    Yields (fun _ => True) (receiverReplies model side site type receivers)
  | [] => Yields.done trivial
  | role :: rest =>
      (receiveStep_yields site type (side role)).bind fun _ _ =>
        (receiverReplies_yields side site type rest).bind fun _ _ => Yields.done trivial

theorem sampleStep_yields (site : Site) (law : SamplingRow) : ∀ (owner : Bool)
    (inputs : Values (fun type => Held (model.Value type) owner) law.inputs),
    Yields (fun _ => True) (sampleStep model site law owner inputs)
  | true, _ => Yields.call fun _ => Yields.done trivial
  | false, _ => Yields.done trivial

theorem drawStep_yields {α : Type} {post : α → Prop} (site : Site) (law : SamplingRow)
    {onDraw : model.Value law.output → PIR.Process (Effects model) α}
    (drawn : ∀ reply, Yields post (onDraw reply)) : ∀ (owner : Bool)
    (inputs : Values (fun type => Held (model.Value type) owner) law.inputs)
    (onOutside : owner = false → PIR.Process (Effects model) α),
    (∀ absent, Yields post (onOutside absent)) →
      Yields post (drawStep model site law onDraw owner inputs onOutside)
  | true, _, _, _ => Yields.call drawn
  | false, _, _, outside => outside rfl

/-! ## Agreement -/

section Agreement

variable {X α : Type} {same : X → X → Bool} {side : Side} {onValue : X → α} {onDisagree : α}

/-- What holds of both outcomes of comparing the later copies with a first one holds of the
comparison: of the stop when two differ, and of the continuation when every later copy in
the side is the same as the first. -/
theorem agreeWith_copies (motive : α → Prop) (disagree : motive onDisagree) (value : X) :
    ∀ (roles : List Nat) (values : Values (fun role => Held X (side role)) roles),
      ((∀ {role : Nat} (position : Var roles role) (member : side role = true),
          same value (Held.value (side role) member (values.get position)) = true) →
        motive (onValue value)) →
      motive (agreeWith same side onValue onDisagree value roles values)
  | [], _, agree => agree fun position _ => position.elimNil
  | role :: rest, values, agree => by
      cases present : side role with
      | true =>
          rw [agreeWith_present present]
          cases equal : same value (Held.value (side role) present (values.get .here)) with
          | false => exact disagree
          | true =>
              refine agreeWith_copies motive disagree value rest values.tail fun later => agree ?_
              intro other position member
              cases position with
              | here => exact equal
              | there position => exact tail_get values position ▸ later position member
      | false =>
          rw [agreeWith_absent present]
          refine agreeWith_copies motive disagree value rest values.tail fun later => agree ?_
          intro other position member
          cases position with
          | here => rw [present] at member; cases member
          | there position => exact tail_get values position ▸ later position member

/-- As `agreed_copies`, with a copy in the side that the agreed value is. -/
theorem agreed_copies_held (motive : α → Prop) (disagree : motive onDisagree) :
    ∀ (roles : List Nat) (values : Values (fun role => Held X (side role)) roles)
      (onNone : roles.any side = false → α),
      (∀ none, motive (onNone none)) →
      (∀ value : X,
        (∀ {role : Nat} (position : Var roles role) (member : side role = true),
          value = Held.value (side role) member (values.get position) ∨
            same value (Held.value (side role) member (values.get position)) = true) →
        (∃ (role : Nat) (position : Var roles role) (member : side role = true),
          value = Held.value (side role) member (values.get position)) →
          motive (onValue value)) →
      motive (agreed same side onValue onDisagree roles values onNone)
  | [], _, _, outside, _ => outside rfl
  | role :: rest, values, onNone, outside, agree => by
      cases present : side role with
      | true =>
          rw [agreed_present present]
          refine agreeWith_copies motive disagree _ rest values.tail fun later =>
            agree _ ?_ ⟨role, .here, present, rfl⟩
          intro other position member
          cases position with
          | here => exact Or.inl rfl
          | there position => exact Or.inr (tail_get values position ▸ later position member)
      | false =>
          rw [agreed_absent present]
          refine agreed_copies_held motive disagree rest values.tail _ (fun none => outside _)
            fun value later held => agree value ?_ ?_
          · intro other position member
            cases position with
            | here => rw [present] at member; cases member
            | there position => exact tail_get values position ▸ later position member
          · obtain ⟨other, position, member, equal⟩ := held
            exact ⟨other, position.there, member, tail_get values position ▸ equal⟩

/-- What holds of every outcome of an agreement holds of the agreement: of the stop when two
copies differ, of the continuation without a participant in the side, and of the
continuation with a value that every copy in the side is, or is the same as. -/
theorem agreed_copies (motive : α → Prop) (disagree : motive onDisagree) :
    ∀ (roles : List Nat) (values : Values (fun role => Held X (side role)) roles)
      (onNone : roles.any side = false → α),
      (∀ none, motive (onNone none)) →
      (∀ value : X,
        (∀ {role : Nat} (position : Var roles role) (member : side role = true),
          value = Held.value (side role) member (values.get position) ∨
            same value (Held.value (side role) member (values.get position)) = true) →
          motive (onValue value)) →
      motive (agreed same side onValue onDisagree roles values onNone)
  | [], _, _, outside, _ => outside rfl
  | role :: rest, values, onNone, outside, agree => by
      cases present : side role with
      | true =>
          rw [agreed_present present]
          refine agreeWith_copies motive disagree _ rest values.tail fun later => agree _ ?_
          intro other position member
          cases position with
          | here => exact Or.inl rfl
          | there position => exact Or.inr (tail_get values position ▸ later position member)
      | false =>
          rw [agreed_absent present]
          refine agreed_copies motive disagree rest values.tail _ (fun none => outside _)
            fun value later => agree value ?_
          intro other position member
          cases position with
          | here => rw [present] at member; cases member
          | there position => exact tail_get values position ▸ later position member

end Agreement

/-! ## The values of the participants -/

theorem plain_entry_present {type : Ty} : ∀ (present : Bool) (member : present = true)
    (held : Held (model.Value type) present),
    (⟨cond present type Ty.unit, plainValue present held⟩ : Sigma model.Value) =
      ⟨type, Held.value present member held⟩
  | true, _, _ => rfl

theorem plain_entry_of {type : Ty} : ∀ (present : Bool), present = true →
    ∀ (value : model.Value type),
    (⟨cond present type Ty.unit, plainValue present (Held.of present value)⟩ : Sigma model.Value) =
      ⟨type, value⟩
  | true, _, _ => rfl

/-- The copy of a control value that a participant of the side holds is the value at its
position among the operands. -/
theorem entryOf_plain_copy (side : Side) (type : Ty) : ∀ (participants : List Nat)
    {rest : List Located}
    (values : Values (SideValue model side) (Located.ofRoles type participants ++ rest))
    {role : Nat} (position : Var participants role) (member : side role = true),
    entryOf (plainValues side values) position.index =
      some ⟨type, Held.value (side role) member
        ((unmapValues (F := SideValue model side) (fun role => (⟨type, role⟩ : Located))
          participants (values.split (Located.ofRoles type participants)).1).get position)⟩
  | [], _, _, _, position, _ => position.elimNil
  | first :: participants, _, .cons value values, _, position, member => by
      cases position with
      | here => exact congrArg some (plain_entry_present (side first) member value)
      | there position => exact entryOf_plain_copy side type participants values position member

/-- A value that every role of a list holds is, for a role of the side, the value at the
role's position. -/
theorem entryOf_plain_heldCopies (side : Side) (type : Ty) (reply : model.Value type) :
    ∀ (participants : List Nat) {rest : List Located}
      (others : Values (SideValue model side) rest) (index role : Nat),
      participants[index]? = some role → side role = true →
        entryOf (plainValues side ((heldCopies model side type reply participants).append others))
            index =
          some ⟨type, reply⟩
  | [], _, _, _, _, found, _ => nomatch found
  | first :: participants, _, others, 0, role, found, member => by
      cases Option.some.inj found
      exact congrArg some (plain_entry_of (side first) member reply)
  | _ :: participants, _, others, index + 1, role, found, member =>
      entryOf_plain_heldCopies side type reply participants others index role found member

/-! ## The inputs of a nested region -/

/-- Inputs of a region that are values read at levels are those values. -/
theorem sourced_reads {store : Store model} : ∀ {levels : List Nat} {types : List Ty}
    {values : Values model.Value types}, Reads store levels values →
      Sourced (levels.map some) store (entryOf values) := by
  intro levels types values reads index level source
  rw [List.getElem?_map] at source
  cases found : levels[index]? with
  | none => rw [found] at source; cases source
  | some other =>
      rw [found] at source
      cases Option.some.inj (Option.some.inj source)
      exact reads.entry _ _ found

/-- Inputs of a region that capture nothing, before the others. -/
theorem sourced_plain_shift (side : Side) {store : Store model} {sources : List (Option Nat)}
    {first rest : List Located} (values : Values (SideValue model side) first)
    {others : Values (SideValue model side) rest}
    (sourced : Sourced sources store (entryOf (plainValues side others))) :
    Sourced (List.replicate first.length none ++ sources) store
      (entryOf (plainValues side (values.append others))) := by
  intro index level source
  by_cases early : index < first.length
  · rw [List.getElem?_append_left (by rw [List.length_replicate]; exact early),
      List.getElem?_replicate] at source
    simp only [early, ↓reduceIte] at source
    cases Option.some.inj source
  · have position : index = first.length + (index - first.length) := by omega
    rw [List.getElem?_append_right (by rw [List.length_replicate]; omega),
      List.length_replicate] at source
    rw [position, entryOf_plain_append]
    exact sourced _ level source

namespace RoleFacts

variable {side : Side} {Γ : List Located} {env : Environment (SideValue model side) Γ}

/-- Each participant of the side knows its own copy of a condition that has the given
truth. -/
theorem Sound.assumeTags (truth : Bool) : ∀ (participants tags : List Nat) {state : RoleFacts},
    state.Sound side env →
    (∀ (index role tag : Nat), participants[index]? = some role → tags[index]? = some tag →
      side role = true → storeOf (plainEnvironment side env) tag = some ⟨.bool, truth⟩) →
    (RoleFacts.assumeTags truth participants tags state).Sound side env
  | [], _, _, sound, _ => sound
  | _ :: _, [], _, sound, _ => sound
  | role :: participants, tag :: tags, state, sound, read => by
      refine Sound.assumeTags truth participants tags
        (sound.set role fun member =>
          (sound.roles role member).assume state.depth (read 0 role tag rfl rfl member))
        fun index other level found at_ member => read (index + 1) other level found at_ member

/-- Each participant of the side knows the interval of its iteration number, in a
`repeat` over a count of the operation. -/
theorem Sound.countStatic {count iteration : Nat} (below : iteration < count) :
    ∀ (level : Nat) (participants : List Nat) {state : RoleFacts}, state.Sound side env →
    (∀ (index role : Nat), participants[index]? = some role → side role = true →
      storeOf (plainEnvironment side env) (level + index) = some ⟨.nat, iteration⟩) →
    (RoleFacts.countStatic count level participants state).Sound side env
  | _, [], _, sound, _ => sound
  | level, role :: participants, state, sound, read => by
      refine Sound.countStatic below (level + 1) participants
        (sound.set role fun member =>
          (sound.roles role member).bound (read 0 role rfl member) (Nat.zero_le _)
            fun end_ at_ => by
              cases Option.some.inj at_
              omega)
        fun index other found member => ?_
      have at_ := read (index + 1) other found member
      have same : level + 1 + index = level + (index + 1) := by omega
      rw [same]
      exact at_

/-- Each participant of the side knows the interval of its iteration number and its order
below the participant's own copy of the count, in a `repeat` over a count that is a value
on which the participants of the side agree. -/
theorem Sound.countRuntime {outer : RoleFacts} (outerSound : outer.Sound side env)
    {Δ : List Located} {inner : Environment (SideValue model side) Δ}
    {sources : List (Option Nat)}
    (sourced : Sourced sources (storeOf (plainEnvironment side env))
      (storeOf (plainEnvironment side inner)))
    {iteration agreed : Nat} (below : iteration < agreed) :
    ∀ (level : Nat) (participants counts : List Nat) {state : RoleFacts},
    state.Sound side inner →
    (∀ (index role : Nat), participants[index]? = some role → side role = true →
      storeOf (plainEnvironment side inner) (level + index) = some ⟨.nat, iteration⟩) →
    (∀ (index role count : Nat), participants[index]? = some role →
      counts[index]? = some count → side role = true →
        storeOf (plainEnvironment side env) count = some ⟨.nat, agreed⟩) →
    (RoleFacts.countRuntime outer sources level participants counts state).Sound side inner
  | _, [], _, _, sound, _, _ => sound
  | _, _ :: _, [], _, sound, _, _ => sound
  | level, role :: participants, count :: counts, state, sound, read, counted => by
      refine Sound.countRuntime outerSound sourced below (level + 1) participants counts
        (sound.set role fun member => ?_)
        (fun index other found member => ?_)
        fun index other number found at_ member =>
          counted (index + 1) other number found at_ member
      · have first := read 0 role rfl member
        have held := counted 0 role count rfl rfl member
        have bounded := (sound.roles role member).bound first (Nat.zero_le _)
          (before_le below fun _ at_ => (outerSound.roles role member).2.le_hi held at_)
        show (Facts.iteration _ level _ (Facts.sourceOf count sources 0)).Sound _
        cases captured : Facts.sourceOf count sources 0 with
        | none => exact bounded
        | some source =>
            exact bounded.order first (sourced.maps _ _ _ captured held) (Nat.le_of_lt below)
              fun _ => below
      · have at_ := read (index + 1) other found member
        have same : level + 1 + index = level + (index + 1) := by omega
        rw [same]
        exact at_

end RoleFacts

/-! ## Operations and regions -/

/-- Every protocol of a table never stops `undefined`, under any path, for any side, on
any values. -/
@[expose] def DefinedProtocols {protocols : List ProtocolHeader} (table : ProtocolTable model protocols) :
    Prop :=
  ∀ {header : ProtocolHeader} (callee : Var protocols header) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) header.inputs),
    NeverStops .undefined (table.get callee path side arguments)

/-- Each nested region of a protocol instruction, on inputs of which what the roles know at
its start holds, never stops `undefined` and returns values in the intervals that the check
says it returns. -/
def RegionsYield (side : Side) (stateOf : Nat → RoleFacts) : (number : Nat) → List Outcome →
    {signatures : List (List Located × List Located)} →
      Values (RegionFunction (SideValue model side) (Effects model)) signatures → Prop
  | _, outcomes, _, .nil => outcomes = []
  | number, outcomes, _, .cons (ty := signature) body rest =>
      ∃ outcome others, outcomes = outcome :: others ∧
        (∀ arguments : Values (SideValue model side) signature.1,
          (stateOf number).Sound side (Environment.ofValues arguments) →
            Yields (fun results => outcome.Bounds (plainValues side results)) (body arguments)) ∧
        RegionsYield side stateOf (number + 1) others rest

/-- Nested regions that never stop `undefined` from what the roles know at their numbers
with their inputs in scope never do from what the roles know at their numbers: inputs on
which a region runs for the side exist. -/
theorem RegionsYield.entered {side : Side} {stateOf : Nat → RoleFacts}
    {inputsOf : Nat → List Located} :
    ∀ {signatures : List (List Located × List Located)} (number : Nat) (outcomes : List Outcome)
      (regions : Values (RegionFunction (SideValue model side) (Effects model)) signatures),
      (∀ (index : Nat) (signature : List Located × List Located),
        signatures[index]? = some signature → inputsOf (number + index) = signature.1) →
      RegionsYield side (fun number => (stateOf number).inScope (inputsOf number)) number outcomes
        regions →
      RegionsYield side stateOf number outcomes regions
  | _, _, _, .nil, _, sound => sound
  | _, number, _, .cons (ty := signature) body rest, inputs, sound => by
      obtain ⟨outcome, others, same, here, there⟩ := sound
      refine ⟨outcome, others, same, fun arguments holds => ?_, ?_⟩
      · have first := inputs 0 signature rfl
        rw [Nat.add_zero] at first
        have entered : ((stateOf number).inScope (inputsOf number)).Sound side
            (Environment.ofValues arguments) := by
          rw [first]
          exact holds.inScope arguments
        exact here arguments entered
      · refine RegionsYield.entered (number + 1) others rest (fun index found at_ => ?_) there
        have later := inputs (index + 1) found at_
        rw [← Nat.add_assoc, Nat.add_right_comm] at later
        exact later

/-- The region with a number among equal regions never stops `undefined`, on inputs of
which what the roles know at its start holds, and returns what one of the regions
returns. -/
theorem selectArm_yields (side : Side) (stateOf : Nat → RoleFacts)
    (signature : List Located × List Located) : ∀ (count base : Nat)
    (regions : Values (RegionFunction (SideValue model side) (Effects model))
      (List.replicate count signature)) (number : Fin count) (outcomes : List Outcome),
    RegionsYield side stateOf base outcomes regions →
    ∀ arguments : Values (SideValue model side) signature.1,
      (stateOf (base + number.val)).Sound side (Environment.ofValues arguments) →
        Yields (fun results => (Outcome.joinAll outcomes).Bounds (plainValues side results))
          (selectArm signature count regions number arguments)
  | 0, _, _, number, _, _ => number.elim0
  | count + 1, base, regions, ⟨0, _⟩, outcomes, sound => by
      cases regions with
      | cons body rest =>
          obtain ⟨outcome, others, rfl, here, _⟩ := sound
          exact fun arguments holds =>
            (here arguments holds).weaken fun _ bounds => bounds.join_left _
  | count + 1, base, regions, ⟨number + 1, below⟩, outcomes, sound => by
      cases regions with
      | cons body rest =>
          obtain ⟨outcome, others, rfl, _, there⟩ := sound
          intro arguments holds
          refine (selectArm_yields side stateOf signature count (base + 1) rest
            ⟨number, Nat.lt_of_succ_lt_succ below⟩ others there arguments ?_).weaken
              fun _ bounds => bounds.join_right _
          have same : base + 1 + number = base + (number + 1) := by omega
          show (stateOf (base + 1 + number)).Sound side _
          rw [same]
          exact holds

/-- The region of an alternative never stops `undefined`, on whatever payloads the
participants of the side hold, and returns what one of the regions returns. -/
theorem alternativeProcess_yields (side : Side) (participants : List Nat)
    (captures outputs : List Located) (captured : Values (SideValue model side) captures)
    (stateOf : Nat → RoleFacts)
    (enters : ∀ (number : Nat) {payload : Ty}
      (payloads : Values (SideValue model side) (Located.ofRoles payload participants)),
      (stateOf number).Sound side (Environment.ofValues (payloads.append captured))) :
    ∀ (alternatives : List Ty)
      (regions : Values (RegionFunction (SideValue model side) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs)))
      (number base : Nat)
      (copies : Values (fun role => Held (Ty.Variant model.Carrier alternatives) (side role))
        participants) (outcomes : List Outcome),
      RegionsYield side stateOf base outcomes regions →
        Yields (fun results => (Outcome.joinAll outcomes).Bounds (plainValues side results))
          (alternativeProcess model side participants captures outputs alternatives regions number
            copies captured)
  | [], _, _, _, _, _, _ => Yields.halt PIR.Stop.noConfusion
  | payload :: rest, regions, 0, base, copies, outcomes, sound => by
      cases regions with
      | cons body others =>
          obtain ⟨outcome, later, rfl, here, _⟩ := sound
          unfold alternativeProcess
          split
          · exact (here _ (enters base _)).weaken fun _ bounds => bounds.join_left _
          · exact Yields.halt PIR.Stop.noConfusion
  | payload :: rest, regions, number + 1, base, copies, outcomes, sound => by
      cases regions with
      | cons body others =>
          obtain ⟨outcome, later, rfl, _, there⟩ := sound
          unfold alternativeProcess
          split
          · exact (alternativeProcess_yields side participants captures outputs captured stateOf
              enters rest others number (base + 1) _ later there).weaken
                fun _ bounds => bounds.join_right _
          · exact Yields.halt PIR.Stop.noConfusion

/-- The iterations of a step that never stops `undefined` below the count never do. -/
theorem iterations_yields {I : PIR.Signature} {State Produced : Type} {Collected : Nat → Type}
    {step : Nat → State → PIR.Process I Produced} {carry : Produced → State}
    {push : (done : Nat) → Produced → Collected done → Collected (done + 1)} {count : Nat}
    (steps : ∀ iteration state, iteration < count →
      Yields (fun _ => True) (step iteration state)) :
    ∀ (remaining done : Nat) (state : State) (earlier : Collected done),
      done + remaining ≤ count →
        Yields (fun _ => True) (iterations step carry push remaining done state earlier)
  | 0, _, _, _, _ => Yields.done trivial
  | remaining + 1, done, state, earlier, within =>
      (steps done state (by omega)).bind fun produced _ =>
        iterations_yields steps remaining (done + 1) (carry produced)
          (push done produced earlier) (by omega)

/-- The levels of operands are as many as the operands. -/
theorem numbers_length {Γ : List Located} (depth : Nat) :
    ∀ {types : List Located} (operands : Operands Γ types),
      (Scope.numbers depth operands).length = types.length
  | _, .nil => rfl
  | _, .cons _ rest => congrArg (· + 1) (numbers_length depth rest)

/-- Each participant's copy of a count, at its level, is known to be within the maximum. -/
theorem RoleFacts.countsWithin_at {state : RoleFacts} {maximum : Nat} :
    ∀ {participants counts : List Nat}, state.countsWithin maximum participants counts = true →
      ∀ (index role level : Nat), participants[index]? = some role → counts[index]? = some level →
        ((state.view role).dead || within ((state.view role).hi level) maximum) = true
  | [], _, _, _, _, _, found, _ => nomatch found
  | _ :: _, [], _, _, _, _, _, at_ => nomatch at_
  | _ :: _, _ :: _, holds, 0, _, _, found, at_ => by
      cases Option.some.inj found
      cases Option.some.inj at_
      exact (Bool.and_eq_true_iff.mp holds).1
  | _ :: _, _ :: _, holds, index + 1, role, level, found, at_ =>
      RoleFacts.countsWithin_at (Bool.and_eq_true_iff.mp holds).2 index role level found at_

/-- The number of iterations of a `repeat` on whose count the participants of the side
agree: the count of the operation, or the agreed value. -/
@[expose] def RepeatCount.iterations (agreed : Nat) : RepeatCount → Nat
  | .static number => number
  | .runtime _ => agreed

/-- A `repeat` never stops `undefined` when no iteration below the count does, for a count
that every participant of the side holds. -/
theorem repeatOperation_yields (side : Side) (participants : List Nat) (count : RepeatCount)
    (carried collected captures : List Located)
    (covered : Located.heldBy participants collected = true)
    (region : RegionFunction (SideValue model side) (Effects model)
      (Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried))
    (counts : Values (fun role => Held Nat (side role)) participants)
    (initial : Values (SideValue model side) carried)
    (captured : Values (SideValue model side) captures)
    (steps : ∀ (agreed iteration : Nat) (state : Values (SideValue model side) carried),
      (∀ {role : Nat} (position : Var participants role) (member : side role = true),
        Held.value (side role) member (counts.get position) = agreed) →
      iteration < count.iterations agreed →
        Yields (fun _ => True)
          (region ((heldCopies model side .nat iteration participants).append
            (state.append captured))))
    (bounded : ∀ (agreed maximum : Nat), count = .runtime maximum →
      (∃ (role : Nat) (position : Var participants role) (member : side role = true),
        agreed = Held.value (side role) member (counts.get position)) → agreed ≤ maximum) :
    Yields (fun _ => True)
      (repeatOperation model side participants count carried collected captures covered region
        counts initial captured) := by
  unfold repeatOperation
  refine agreed_copies_held (Yields (fun _ => True)) (Yields.halt PIR.Stop.noConfusion) participants
    counts _ (fun _ => Yields.done trivial) fun agreed agree held => ?_
  have equal : ∀ {role : Nat} (position : Var participants role) (member : side role = true),
      Held.value (side role) member (counts.get position) = agreed := by
    intro role position member
    rcases agree position member with same | same
    · exact same.symm
    · exact (Nat.eq_of_beq_eq_true same).symm
  cases count with
  | «static» number =>
      exact (iterations_yields (fun iteration state below => steps agreed iteration state equal below)
        number 0 _ _ (Nat.le_of_eq (Nat.zero_add _))).bind fun _ _ => Yields.done trivial
  | runtime maximum =>
      show Yields _ (if agreed ≤ maximum then _ else _)
      split
      · exact (iterations_yields
          (fun iteration state below => steps agreed iteration state equal below)
          agreed 0 _ _ (Nat.le_of_eq (Nat.zero_add _))).bind fun _ _ => Yields.done trivial
      · rename_i above
        exact absurd (bounded agreed maximum rfl held) above

section Protocol

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

/-- The inputs of the nested region with a number are the inputs of its signature. -/
theorem ProtocolOp.regionInputs_at (op : ProtocolOp operations functions protocols deployed)
    (index : Nat) (signature : List Located × List Located)
    (found : op.regions[index]? = some signature) :
    op.regionInputs (0 + index) = signature.1 := by
  rw [Nat.zero_add]
  show (match op.regions[index]? with
    | some signature => signature.1
    | none => []) = _
  rw [found]

/-- A justified protocol instruction, over regions, functions and protocols that never stop
`undefined`, never does for a side, and what the roles know after it, with what its regions
return, holds of the environment that binds its results. -/
theorem ProtocolOp.sound (laws : model.DomainLaws operations)
    {functionTable : FunctionTable model functions} (defined : DefinedTable functionTable)
    {table : ProtocolTable model protocols} (earlier : DefinedProtocols table)
    (label : Nat → Site) {side : Side} {Γ : List Located}
    {env : Environment (SideValue model side) Γ} {state : RoleFacts}
    (sound : state.Sound side env) :
    ∀ (op : ProtocolOp operations functions protocols deployed)
      (arguments : Operands Γ op.arguments)
      (regions : Values (RegionFunction (SideValue model side) (Effects model)) op.regions)
      (path : List Nat) (after : RoleFacts) (outcomes : List Outcome),
      op.justify path state (Scope.numbers Γ.length arguments) = .ok after →
      RegionsYield side (op.regionEntry state (Scope.numbers Γ.length arguments)) 0 outcomes
        regions →
        Yields (fun results =>
            (op.joined Γ.length outcomes after).Sound side (Environment.bindAll env results))
          (labelledOperation model label functionTable table side op
            (Operands.eval env arguments) regions)
  | .at role op bodies, arguments, _, path, after, _, passes, _ => by
      rw [ProtocolOp.justify] at passes
      have counted : (Located.atRole role op.results).length = op.results.length :=
        List.length_map _
      cases member : side role with
      | false =>
          -- A role outside the side performs nothing, and nothing is required of its facts.
          have after_ : after = state.afterLocal role op (Scope.numbers Γ.length arguments)
              (match justifyRegions path
                  (state.localRegionFacts role op (Scope.numbers Γ.length arguments)) 0
                  bodies with
                | .ok outcomes => outcomes
                | .error _ => [])
              (LocalOp.branchShape op (Scope.numbers Γ.length arguments) bodies) := by
            split at passes
            · cases passes
            · split at passes
              · cases passes
              · rename_i outcomes nested
                cases passes
                rw [nested]
          subst after_
          show Yields (fun results => RoleFacts.Sound side _ (Environment.bindAll env results)) _
          rw [at_absent member]
          have bound := sound.bind (remapValues (F := SideValue model side)
            (fun type => (⟨type, role⟩ : Located)) _
            (absentHeldValues (side role) member op.results))
          rw [counted] at bound
          exact Yields.done (bound.set role fun present => by
            rw [member] at present
            cases present)
      | true =>
          simp only [RoleFacts.unjustifiedLocal, RoleFacts.afterLocal, sound.alive,
            (sound.roles role member).2.alive, Bool.or_self, Bool.cond_false] at passes
          split at passes
          · cases passes
          · rename_i justified
            split at passes
            · cases passes
            · rename_i outcomes nested
              cases passes
              show Yields
                (fun results => RoleFacts.Sound side _ (Environment.bindAll env results)) _
              have length : (Γ.map (plainType side)).length = Γ.length := List.length_map _
              have levels : Scope.numbers (Γ.map (plainType side)).length
                  (presentOperands side member arguments) = Scope.numbers Γ.length arguments := by
                rw [length]
                exact numbers_presentOperands side member _ arguments
              have depth : state.depth = (Γ.map (plainType side)).length := by
                rw [sound.depth, length]
              rw [← levels] at justified nested ⊢
              rw [depth, at_present member, ← eval_presentOperands side member env arguments]
              refine Yields.bind
                ((LocalOp.sound laws defined (sound.roles role member) op
                  (presentOperands side member arguments) _ outcomes justified
                  (RegionsSound.entered 0 outcomes _ (LocalOp.regionInputs_at op)
                    (justifyRegions_sound laws defined bodies _ _ 0 outcomes nested))).and
                  (LocalOp.branch_returns op (presentOperands side member arguments) bodies))
                fun results holds => Yields.done ?_
              have bound := sound.bind (remapValues (F := SideValue model side)
                (fun type => (⟨type, role⟩ : Located)) _ (holdValues (side role) results))
              rw [counted] at bound
              refine bound.set role fun _ => ?_
              refine Facts.Sound.plain (results := results) ?_ counted.symm
                fun index => (entryOf_plain_held side member results index).symm
              refine (holds.1.inScope results).reshape _ _ ?_
              intro shape found entry at_
              rw [storeOf_bindAll] at at_
              simp only [Nat.lt_irrefl, ↓reduceIte, Nat.sub_self] at at_
              exact (holds.2 shape found entry at_).grow (storeOf_grows _ results)
  | .exchange sender receiver site type, arguments, _, path, after, _, passes, _ => by
      cases passes
      exact (exchangeStep_yields (label site) type (side sender) (side receiver) _).bind
        fun _ _ => Yields.done (sound.bind _)
  | .draw owner receivers site law populated, arguments, _, path, after, _, passes, _ => by
      cases passes
      apply drawStep_yields
      · exact fun _ => Yields.done (sound.bind _)
      · exact fun _ => (receiverReplies_yields side (label site) _ receivers).bind
          fun _ _ => Yields.done (sound.bind _)
  | .sample owner site law populated, arguments, _, path, after, _, passes, _ => by
      cases passes
      exact (sampleStep_yields (label site) (.of law populated) (side owner) _).bind
        fun _ _ => Yields.done (sound.bind _)
  | .apply callee roleMap site permitted, arguments, _, path, after, _, passes, _ => by
      cases passes
      exact (earlier callee _ _ _).yields.bind fun _ _ => Yields.done (sound.bind _)
  | .choose participants .condition captures outputs covered, arguments, regions, path, after,
      outcomes, passes, nested => by
      cases passes
      have reads := plain_reads side env arguments
      have captured := plain_reads_split side (Located.ofRoles .bool participants) reads
      rw [List.length_map] at captured
      rw [← sound.depth]
      refine agreed_copies (Yields _) (Yields.halt PIR.Stop.noConfusion) participants _ _
        (fun outside => Yields.done (sound.outside covered outside _ _)) fun value agree => ?_
      show Yields _ (selectArm (captures, outputs) 2 regions
        (ChoiceTag.select model.Carrier .condition value) _)
      refine (selectArm_yields side _ (captures, outputs) 2 0 regions _ outcomes nested _
        ?_).weaken fun results holds => sound.joined results holds
      have tags : (RoleFacts.assumeTags value participants (Scope.numbers Γ.length arguments)
          state).Sound side env := by
        refine sound.assumeTags value participants _ fun index role tag found at_ member => ?_
        rw [← reads.entry index tag at_,
          entryOf_plain_copy side .bool participants _ ⟨index, found⟩ member]
        rcases agree ⟨index, found⟩ member with same | same
        · rw [same]
        · rw [(agreeBool_decides _ _).mp same]
      have entered := tags.enter _ (by rw [List.length_map, captured.length, List.length_map])
        (sourced_reads captured)
      rw [ChoiceTag.select_condition]
      cases value with
      | false => exact entered
      | true => exact entered
  | .choose participants (.arm count) captures outputs covered, arguments, regions, path, after,
      outcomes, passes, nested => by
      cases passes
      have reads := plain_reads side env arguments
      have captured := plain_reads_split side (Located.ofRoles (.fin count) participants) reads
      rw [List.length_map] at captured
      rw [← sound.depth]
      refine agreed_copies (Yields _) (Yields.halt PIR.Stop.noConfusion) participants _ _
        (fun outside => Yields.done (sound.outside covered outside _ _)) fun value _ => ?_
      show Yields _ (selectArm (captures, outputs) count regions
        (ChoiceTag.select model.Carrier (.arm count) value) _)
      exact (selectArm_yields side _ (captures, outputs) count 0 regions _ outcomes nested _
        (sound.enter _ (by rw [List.length_map, captured.length, List.length_map])
          (sourced_reads captured))).weaken fun results holds => sound.joined results holds
  | .choose participants (.alternative declaration alternatives) captures outputs covered,
      arguments, regions, path, after, outcomes, passes, nested => by
      cases passes
      have reads := plain_reads side env arguments
      have captured := plain_reads_split side
        (Located.ofRoles (.variant declaration alternatives) participants) reads
      rw [List.length_map] at captured
      rw [← sound.depth]
      refine agreed_copies (Yields _) (Yields.halt PIR.Stop.noConfusion) participants _ _
        (fun outside => Yields.done (sound.outside covered outside _ _)) fun value _ => ?_
      refine (alternativeProcess_yields side participants captures outputs _ _
        (fun number payload payloads => ?_) alternatives regions _ 0 _ outcomes nested).weaken
          fun results holds => sound.joined results holds
      have sourced := sourced_plain_shift side payloads (sourced_reads captured)
      rw [List.length_map] at sourced
      exact sound.enter _ (by
        rw [List.length_append, List.length_replicate, List.length_map, captured.length,
          List.length_map, List.length_append, List.length_map]) sourced
  | .repeat participants (.static count) carried collected captures covered, arguments, regions,
      path, after, outcomes, passes, nested => by
      cases passes
      cases regions with
      | cons region rest =>
      obtain ⟨outcome, others, _, inner, _⟩ := nested
      have reads := plain_reads side env arguments
      have captured := plain_reads_split side carried reads
      refine (repeatOperation_yields side participants (.static count) carried collected captures
        covered region _ _ _ (fun agreed iteration values _ below =>
          (inner _ ?_).weaken fun _ _ => trivial)
        (fun _ _ impossible => nomatch impossible)).weaken fun results _ => sound.bind results
      have live : decide (count = 0) = false := decide_eq_false (by
        have : iteration < count := below
        omega)
      show (cond (decide (count = 0)) _ _ : RoleFacts).Sound side _
      rw [live]
      have sourced := sourced_plain_shift side
        (heldCopies model side .nat iteration participants)
        (sourced_plain_shift side values (sourced_reads captured))
      rw [List.length_map, ← List.append_assoc, List.replicate_append_replicate] at sourced
      refine RoleFacts.Sound.countStatic below 0 participants
        (sound.enter _ (by
          rw [List.length_append, List.length_replicate, List.length_map, captured.length,
            List.length_map, List.length_append, List.length_map, List.length_append]
          omega) sourced)
        fun index role found member => ?_
      rw [storeOf_plain_ofValues, Nat.zero_add]
      exact entryOf_plain_heldCopies side .nat iteration participants _ index role found member
  | .repeat participants (.runtime maximum) carried collected captures covered, arguments,
      regions, path, after, outcomes, passes, nested => by
      -- the counts are known to be within the maximum
      have within_ : state.countsWithin maximum participants (Scope.numbers Γ.length arguments) =
          true := by
        have checked : cond
            (state.dead || state.countsWithin maximum participants (Scope.numbers Γ.length arguments))
            (Except.ok (state.bind
              (ProtocolOp.repeat (operations := operations) (functions := functions)
                (protocols := protocols) (deployed := deployed) participants (.runtime maximum)
                carried collected captures covered).results.length))
            (Except.error ({ path := path, requirement := .maximum } : Unjustified)) = .ok after := passes
        cases held : state.countsWithin maximum participants (Scope.numbers Γ.length arguments) with
        | true => rfl
        | false =>
            rw [held, sound.alive] at checked
            cases checked
      have after_ : after = state.bind
          (ProtocolOp.repeat (operations := operations) (functions := functions)
            (protocols := protocols) (deployed := deployed) participants (.runtime maximum)
            carried collected captures covered).results.length := by
        have checked : cond
            (state.dead || state.countsWithin maximum participants (Scope.numbers Γ.length arguments))
            (Except.ok (state.bind
              (ProtocolOp.repeat (operations := operations) (functions := functions)
                (protocols := protocols) (deployed := deployed) participants (.runtime maximum)
                carried collected captures covered).results.length))
            (Except.error ({ path := path, requirement := .maximum } : Unjustified)) = .ok after := passes
        rw [within_, Bool.or_true] at checked
        exact (Except.ok.inj checked).symm
      subst after_
      cases regions with
      | cons region rest =>
      obtain ⟨outcome, others, _, body, _⟩ := nested
      have reads := plain_reads side env arguments
      have counts := plain_reads_split side (Located.ofRoles .nat participants) reads
      rw [List.length_map] at counts
      have captured := plain_reads_split side carried counts
      refine (repeatOperation_yields side participants (.runtime maximum) carried collected
        captures covered region _ _ _ (fun agreed iteration values agree below =>
          (body _ ?_).weaken fun _ _ => trivial) ?_).weaken fun results _ => sound.bind results
      rotate_left
      · intro agreed limit same held
        cases same
        obtain ⟨role, position, member, equal⟩ := held
        have below := position.index_lt
        have counted : (Scope.numbers Γ.length arguments).length =
            (Located.ofRoles .nat participants ++ (carried ++ captures)).length :=
          numbers_length _ arguments
        rw [List.length_append, List.length_map] at counted
        obtain ⟨level, at_⟩ : ∃ level, (Scope.numbers Γ.length arguments)[position.index]? = some level :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have known := RoleFacts.countsWithin_at within_ position.index role level position.valid at_
        have alive := ((sound.roles role member).holds).alive
        rw [alive, Bool.false_or] at known
        obtain ⟨top, hi, fits⟩ := within_le known
        have entry := (reads.entry position.index level at_).symm.trans
          (entryOf_plain_copy side .nat participants _ position member)
        rw [equal]
        exact Nat.le_trans ((sound.roles role member).holds.le_hi entry hi) fits
      have sourced := sourced_plain_shift side
        (heldCopies model side .nat iteration participants)
        (sourced_plain_shift side values (sourced_reads captured))
      rw [List.length_map, ← List.append_assoc, List.replicate_append_replicate] at sourced
      have inner := storeOf_plain_ofValues side
        ((heldCopies model side .nat iteration participants).append
          (values.append
            (((Operands.eval env arguments).split (Located.ofRoles .nat participants)).2.split
              carried).2))
      refine RoleFacts.Sound.countRuntime sound (inner ▸ sourced) below 0 participants _
        (sound.enter _ (by
          rw [List.length_append, List.length_replicate, List.length_map, captured.length,
            List.length_map, List.length_append, List.length_map, List.length_append]
          omega) sourced)
        (fun index role found member => ?_)
        fun index role level found at_ member => ?_
      · rw [inner, Nat.zero_add]
        exact entryOf_plain_heldCopies side .nat iteration participants _ index role found member
      · rw [← reads.entry index level at_,
          entryOf_plain_copy side .nat participants _ ⟨index, found⟩ member]
        exact congrArg (fun number : Nat => some (⟨.nat, number⟩ : Sigma model.Value))
          (agree ⟨index, found⟩ member)

mutual
  /-- A region of a protocol body that passes the check, on an environment of a side of
  which what the roles know at its start holds, never stops `undefined`, and returns values
  in the intervals that the check says it returns. -/
  theorem justifyProtocol_sound (laws : model.DomainLaws operations)
      {functionTable : FunctionTable model functions} (defined : DefinedTable functionTable)
      {table : ProtocolTable model protocols} (earlier : DefinedProtocols table)
      (label : Nat → Site) (side : Side) :
      ∀ {Γ out : List Located}
        (region : Region (ProtocolDialect operations functions protocols deployed) Γ out)
        (path : List Nat) (index : Nat) (state : RoleFacts) (outcome : Outcome),
        justifyProtocol path index state region = .ok outcome →
          ∀ (env : Environment (SideValue model side) Γ), state.Sound side env →
            Yields (fun results => outcome.Bounds (plainValues side results))
              (region.denote (labelledMeaning model label functionTable table side) env)
    | _, _, .ret values, _, _, state, outcome, passes, env, sound => by
        unfold justifyProtocol at passes
        rw [sound.depth] at passes
        cases passes
        exact Yields.done (sound.returned values)
    | _, _, .stop reason, path, index, state, outcome, passes, env, _ => by
        unfold justifyProtocol at passes
        split at passes
        · cases passes
        · rename_i other
          exact Yields.halt other
    | Γ, _, .letOp op arguments bodies next, path, index, state, outcome, passes, env, sound => by
        unfold justifyProtocol at passes
        rw [sound.depth] at passes
        split at passes
        · cases passes
        · rename_i after justified
          split at passes
          · cases passes
          · rename_i outcomes nested
            exact Yields.bind
              (ProtocolOp.sound laws defined earlier label sound op arguments _ _ after outcomes
                justified
                (RegionsYield.entered 0 outcomes _ (ProtocolOp.regionInputs_at op)
                  (justifyProtocols_sound laws defined earlier label side bodies _ _ 0 outcomes
                    nested)))
              fun results holds =>
                justifyProtocol_sound laws defined earlier label side next path (index + 1) _
                  outcome passes _ (holds.inScope results)
    | _, _, .bind body next, path, index, state, outcome, passes, env, sound => by
        unfold justifyProtocol at passes
        split at passes
        · cases passes
        · rename_i middle first
          exact Yields.bind
            (justifyProtocol_sound laws defined earlier label side body _ 0 state middle first env
              sound)
            fun values holds =>
              justifyProtocol_sound laws defined earlier label side next path (index + 1) _
                outcome passes _ ((sound.joined values holds).inScope values)

  /-- Nested regions of a protocol instruction that pass the check, each from what the roles
  know at its start, never stop `undefined` and return what the check says they return. -/
  theorem justifyProtocols_sound (laws : model.DomainLaws operations)
      {functionTable : FunctionTable model functions} (defined : DefinedTable functionTable)
      {table : ProtocolTable model protocols} (earlier : DefinedProtocols table)
      (label : Nat → Site) (side : Side) :
      ∀ {signatures : List (List Located × List Located)}
        (bodies : Regions (ProtocolDialect operations functions protocols deployed) signatures)
        (path : List Nat) (stateOf : Nat → RoleFacts) (number : Nat) (outcomes : List Outcome),
        justifyProtocols path stateOf number bodies = .ok outcomes →
          RegionsYield side stateOf number outcomes
            (bodies.denote (labelledMeaning model label functionTable table side))
    | _, .nil, _, _, _, outcomes, passes => by
        unfold justifyProtocols at passes
        cases passes
        rfl
    | _, .cons body tail, path, stateOf, number, outcomes, passes => by
        unfold justifyProtocols at passes
        split at passes
        · cases passes
        · rename_i outcome first
          split at passes
          · cases passes
          · rename_i others rest
            cases passes
            exact ⟨outcome, others, rfl,
              fun arguments sound =>
                justifyProtocol_sound laws defined earlier label side body _ 0 _ outcome first _
                  sound,
              justifyProtocols_sound laws defined earlier label side tail path stateOf (number + 1)
                others rest⟩
end

end Protocol

/-! ## Protocols and programs -/

section Programs

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader}

/-- A protocol whose body passes the check of facts, over functions and protocols that
never stop `undefined`, never stops `undefined`: with any identity, under any path, for any
side, on any values. -/
theorem ProtocolDefinition.neverUndefined (laws : model.DomainLaws operations)
    {functionTable : FunctionTable model functions} (defined : DefinedTable functionTable)
    {table : ProtocolTable model protocols} (earlier : DefinedProtocols table)
    {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header)
    (passes : definition.justified = true) (identity : Nat) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) header.inputs) :
    NeverStops .undefined
      (definition.meaning model functionTable table identity path side arguments) := by
  unfold ProtocolDefinition.justified ProtocolDefinition.unjustified at passes
  split at passes
  · cases passes
  · rename_i outcome checked
    exact (justifyProtocol_sound laws defined earlier (ownSites identity path) side
      definition.body [] 0 _ outcome checked _
      ((RoleFacts.start_sound arguments).inScope arguments)).neverStops

/-- The protocols of a program that all pass the check of facts, over functions that never
stop `undefined`, never stop `undefined`. -/
theorem Protocols.table_defined (laws : model.DomainLaws operations) {typeTable : TypeTable}
    {functionTable : FunctionTable model functions} (defined : DefinedTable functionTable)
    (identities : Identities) :
    ∀ {protocols : List ProtocolHeader}
      (program : Protocols typeTable operations functions protocols),
      program.justified = true → DefinedProtocols (program.table model functionTable identities)
  | _, .nil, _ => fun callee => callee.elimNil
  | _, .snoc earlier definition wellFormed, passes => by
      have both : earlier.justified = true ∧ definition.justified = true :=
        Bool.and_eq_true_iff.mp passes
      intro callee
      exact Var.cases
        (motive := fun header callee => ∀ (path : List Nat) (side : Side)
          (arguments : Values (SideValue model side) header.inputs),
          NeverStops (I := Effects model) (A := Values (SideValue model side) header.outputs)
            .undefined
            (Values.get ((Protocols.snoc earlier definition wellFormed).table model functionTable
              identities) callee path side arguments))
        (fun path side arguments => definition.neverUndefined laws defined
          (Protocols.table_defined laws defined identities earlier both.1) both.2 _ path side
          arguments)
        (fun callee => Protocols.table_defined laws defined identities earlier both.1 callee)
        callee

/-- For every model that satisfies the domain laws of its restricted rows and every side: a
protocol whose body passes the check of facts, in a program whose functions and earlier
protocols all pass it, never stops `undefined`, under any path and on any values, whatever
the replies of its effects. -/
theorem Protocols.never_undefined (laws : model.DomainLaws operations) {typeTable : TypeTable}
    {header : ProtocolHeader} (functionsOf : Functions typeTable operations functions)
    (earlier : Protocols typeTable operations functions protocols)
    (definition : ProtocolDefinition operations functions protocols header)
    (wellFormed : definition.violation typeTable = none)
    (functionsPass : functionsOf.justified = true) (earlierPass : earlier.justified = true)
    (passes : definition.justified = true) (identities : Identities) (path : List Nat)
    (side : Side) (arguments : Values (SideValue model side) header.inputs) :
    NeverStops .undefined
      (((Protocols.snoc earlier definition wellFormed).table model (functionsOf.table model)
        identities).get .here path side arguments) :=
  definition.neverUndefined laws (Functions.table_defined laws functionsOf functionsPass)
    (Protocols.table_defined laws (Functions.table_defined laws functionsOf functionsPass)
      identities earlier earlierPass)
    passes _ path side arguments

/-- For a program all of whose functions and protocols pass the check of facts and a model
that satisfies the domain laws, the process of every protocol for every side, with any
identities, under any path and on any values, has no `undefined` stop. -/
theorem Program.protocols_never_undefined (laws : model.DomainLaws operations)
    {typeTable : TypeTable} (program : Program typeTable operations functions protocols)
    (passes : program.justified = true) (identities : Identities) {header : ProtocolHeader}
    (callee : Var protocols header) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) header.inputs) :
    NeverStops .undefined
      ((program.protocolTable model identities).get callee path side arguments) :=
  Protocols.table_defined laws
    (Functions.table_defined laws program.functions (Bool.and_eq_true_iff.mp passes).1)
    identities program.protocols (Bool.and_eq_true_iff.mp passes).2 callee path side arguments

end Programs

end Zkc.Core
