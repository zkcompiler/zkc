module

public import Zkc.Core.ProtocolFacts
public import Zkc.Core.FactsSound
public import Zkc.Core.Laws

public section

/-! What the facts of the roles say of the environment of a side.

A side holds the values of its roles. Its environment is read as an environment of the
local dialect, value by value: a value whose holder is in the side is itself, and a value
whose holder is outside the side is the unit value. The levels are unchanged. What the
roles know holds of a side's environment (`RoleFacts.Sound`) when, for every role of the
side, the facts of that role hold of the environment read this way, in the sense of the
local check. Nothing is required of what a role outside the side knows: its values are not
there, and its facts are about them alone.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

variable {model : Model}

/-! ## The values of a side, one by one -/

/-- The type at which a side has a located value: its type when the holder is in the side,
the unit type otherwise. -/
@[expose, reducible] def plainType (side : Side) (located : Located) : Ty :=
  cond (side located.holder) located.type Ty.unit

/-- A held value by itself: the value of a holder that is present, the unit value of one
that is not. -/
@[expose] def plainValue : (present : Bool) → {type : Ty} → Held (model.Value type) present →
    model.Value (cond present type Ty.unit)
  | true, _, value => value
  | false, _, _ => PUnit.unit

/-- The values of a side by themselves. -/
@[expose] def plainValues (side : Side) : {types : List Located} → Values (SideValue model side) types →
    Values model.Value (types.map (plainType side))
  | _, .nil => .nil
  | _, .cons (ty := located) value rest =>
      .cons (plainValue (side located.holder) (type := located.type) value) (plainValues side rest)

/-- The environment of a side by itself: each value at its level. -/
@[expose] def plainEnvironment (side : Side) : {Γ : List Located} → Environment (SideValue model side) Γ →
    Environment model.Value (Γ.map (plainType side))
  | [], _ => Environment.empty
  | located :: _, env =>
      Environment.push (plainEnvironment side fun reference => env reference.there)
        (plainValue (side located.holder) (type := located.type) (env .here))

/-- Binding the values of a side and reading them one by one is reading and then binding. -/
theorem storeOf_plain_bindAll (side : Side) : ∀ {added Γ : List Located}
    (env : Environment (SideValue model side) Γ) (values : Values (SideValue model side) added),
    storeOf (plainEnvironment side (Environment.bindAll env values)) =
      storeOf (Environment.bindAll (plainEnvironment side env) (plainValues side values))
  | _, _, _, .nil => rfl
  | _, _, env, .cons value rest => by
      exact storeOf_plain_bindAll side (env.push value) rest

/-- The store of a region's inputs for a side is the inputs by position. -/
theorem storeOf_plain_ofValues (side : Side) {types : List Located}
    (values : Values (SideValue model side) types) :
    storeOf (plainEnvironment side (Environment.ofValues values)) =
      entryOf (plainValues side values) := by
  funext level
  show storeOf (plainEnvironment side (Environment.bindAll Environment.empty values)) level = _
  rw [storeOf_plain_bindAll]
  exact storeOf_ofValues (plainValues side values) level

theorem plain_get (side : Side) : ∀ {Γ : List Located} {located : Located}
    (reference : Var Γ located) (env : Environment (SideValue model side) Γ),
    entryAt (plainEnvironment side env) reference.index =
      some ⟨plainType side located,
        plainValue (side located.holder) (type := located.type) (env reference)⟩ := by
  intro Γ located reference
  induction reference with
  | here => intro env; rfl
  | there reference ih => intro env; exact ih fun reference => env reference.there

/-- The value at the level of a reference, for a side. -/
theorem plain_number (side : Side) {Γ : List Located} (env : Environment (SideValue model side) Γ)
    {located : Located} (reference : Var Γ located) :
    storeOf (plainEnvironment side env) (Scope.number Γ.length reference) =
      some ⟨plainType side located,
        plainValue (side located.holder) (type := located.type) (env reference)⟩ := by
  have bound := reference.index_lt
  have length : (Γ.map (plainType side)).length = Γ.length := List.length_map _
  have below : Scope.number Γ.length reference < (Γ.map (plainType side)).length := by
    simp only [Scope.number, Scope.position, length]; omega
  have back : (Γ.map (plainType side)).length - 1 - Scope.number Γ.length reference =
      reference.index := by
    simp only [Scope.number, Scope.position, length]; omega
  simp only [storeOf, below, ↓reduceIte, back, plain_get]

/-- The operands of a protocol instruction are read at their levels. -/
theorem plain_reads (side : Side) {Γ : List Located} (env : Environment (SideValue model side) Γ) :
    ∀ {types : List Located} (operands : Operands Γ types),
      Reads (storeOf (plainEnvironment side env)) (Scope.numbers Γ.length operands)
        (plainValues side (Operands.eval env operands))
  | _, .nil => trivial
  | _, .cons reference rest => ⟨plain_number side env reference, plain_reads side env rest⟩

/-- The values after a prefix are read at the levels after it. -/
theorem plain_reads_split (side : Side) {store : Store model} : ∀ (first : List Located)
    {rest : List Located} {levels : List Nat} {values : Values (SideValue model side) (first ++ rest)},
    Reads store levels (plainValues side values) →
      Reads store (levels.drop first.length) (plainValues side (values.split first).2)
  | [], _, _, _, reads => reads
  | _ :: _, _, [], .cons _ _, reads => reads.elim
  | _ :: first, _, _ :: _, .cons _ _, reads => plain_reads_split side first reads.2

theorem entryOf_plain_append (side : Side) : ∀ {first rest : List Located}
    (values : Values (SideValue model side) first) (others : Values (SideValue model side) rest)
    (index : Nat),
    entryOf (plainValues side (values.append others)) (first.length + index) =
      entryOf (plainValues side others) index
  | _, _, .nil, others, index => by
      show entryOf (plainValues side others) (0 + index) = _
      rw [Nat.zero_add]
  | _, _, .cons value values, others, index => by
      rw [Values.cons_append, List.length_cons, Nat.add_right_comm]
      exact entryOf_plain_append side values others index

/-- The facts that hold of the values of a side bound after its environment hold of the
environment that binds them, when they are stated of values that are the same by position. -/
theorem Facts.Sound.plain {side : Side} {facts : Facts} {Γ added : List Located}
    {env : Environment (SideValue model side) Γ} {values : Values (SideValue model side) added}
    {others : List Ty} {results : Values model.Value others}
    (sound : facts.Sound (Environment.bindAll (plainEnvironment side env) results))
    (counted : others.length = added.length)
    (same : ∀ index, entryOf results index = entryOf (plainValues side values) index) :
    facts.Sound (plainEnvironment side (Environment.bindAll env values)) := by
  refine ⟨?_, ?_⟩
  · rw [sound.1, length_bindAll, List.length_map, List.length_map, length_bindAll, counted]
  · have stores : storeOf (plainEnvironment side (Environment.bindAll env values)) =
        storeOf (Environment.bindAll (plainEnvironment side env) results) := by
      funext level
      rw [storeOf_plain_bindAll, storeOf_bindAll, storeOf_bindAll, same]
    rw [stores]
    exact sound.2

/-! ## The values of one role of the side -/

/-- A reference to a value of a role of the side, among the values of the side. -/
@[expose] def presentReference (side : Side) {role : Nat} (member : side role = true) {Γ : List Located}
    {type : Ty} (reference : Var Γ ⟨type, role⟩) : Var (Γ.map (plainType side)) type :=
  ⟨reference.index, by
    rw [List.getElem?_map, reference.valid]
    show some (cond (side role) type Ty.unit) = some type
    rw [member]
    rfl⟩

/-- The operands of a local operation that a role of the side performs. -/
@[expose] def presentOperands (side : Side) {role : Nat} (member : side role = true) {Γ : List Located} :
    {types : List Ty} → Operands Γ (Located.atRole role types) →
      Operands (Γ.map (plainType side)) types
  | [], _ => .nil
  | _ :: _, operands =>
      .cons (presentReference side member (operands.get .here))
        (presentOperands side member operands.tail)

theorem numbers_cons {α : Type} {Γ : List α} {head : α} {rest : List α}
    (operands : Operands Γ (head :: rest)) (depth : Nat) :
    Scope.numbers depth operands =
      Scope.number depth (operands.get .here) :: Scope.numbers depth operands.tail := by
  cases operands with
  | cons reference tail => rfl

/-- The operands of a role of the side keep their levels. -/
theorem numbers_presentOperands (side : Side) {role : Nat} (member : side role = true)
    {Γ : List Located} (depth : Nat) : ∀ {types : List Ty}
    (operands : Operands Γ (Located.atRole role types)),
    Scope.numbers depth (presentOperands side member operands) = Scope.numbers depth operands
  | [], .nil => rfl
  | _ :: _, operands => by
      rw [numbers_cons operands]
      show _ :: Scope.numbers depth (presentOperands side member operands.tail) = _
      rw [numbers_presentOperands side member depth operands.tail]
      rfl

theorem plain_present {type : Ty} : ∀ (present : Bool) (member : present = true)
    (held : Held (model.Value type) present) (value : model.Value type),
    (⟨type, value⟩ : Sigma model.Value) = ⟨cond present type Ty.unit, plainValue present held⟩ →
      value = Held.value present member held
  | true, _, _, _, same => entry_eq same

theorem plain_presentReference (side : Side) {role : Nat} (member : side role = true) {Γ : List Located}
    (env : Environment (SideValue model side) Γ) {type : Ty} (reference : Var Γ ⟨type, role⟩) :
    plainEnvironment side env (presentReference side member reference) =
      Held.value (side role) member (env reference) := by
  have one := entryAt_index (plainEnvironment side env) (presentReference side member reference)
  have two := plain_get side reference env
  exact plain_present (side role) member (env reference) _
    (Option.some.inj (one.symm.trans two))

theorem presentValues_empty {X : Ty → Type} : ∀ (present : Bool) (member : present = true),
    presentValues (X := X) present member (.nil) = .nil
  | true, _ => rfl

/-- The operands of a role of the side have the values that the role holds. -/
theorem eval_presentOperands (side : Side) {role : Nat} (member : side role = true)
    {Γ : List Located} (env : Environment (SideValue model side) Γ) : ∀ {types : List Ty}
    (operands : Operands Γ (Located.atRole role types)),
    Operands.eval (plainEnvironment side env) (presentOperands side member operands) =
      presentValues (side role) member
        (unmapValues (fun type => (⟨type, role⟩ : Located)) types (Operands.eval env operands))
  | [], .nil => (presentValues_empty _ member).symm
  | type :: rest, .cons reference operands => by
      show Values.cons (plainEnvironment side env (presentReference side member reference))
          (Operands.eval (plainEnvironment side env) (presentOperands side member operands)) =
        presentValues (side role) member
          (unmapValues (fun type => (⟨type, role⟩ : Located)) (type :: rest)
            (Values.cons (env reference) (Operands.eval env operands)))
      rw [unmapValues_cons, presentValues_cons, plain_presentReference, eval_presentOperands side member env operands]

/-- Values that one holder holds, by themselves. -/
@[expose] def plainHeld (present : Bool) : {types : List Ty} →
    Values (fun type => Held (model.Value type) present) types →
      Values model.Value (types.map fun type => cond present type Ty.unit)
  | _, .nil => .nil
  | _, .cons value rest => .cons (plainValue present value) (plainHeld present rest)

theorem entryOf_plain_remap (side : Side) (role : Nat) : ∀ (types : List Ty)
    (held : Values (fun type => Held (model.Value type) (side role)) types) (index : Nat),
    entryOf (plainValues side
        (remapValues (F := SideValue model side) (fun type => (⟨type, role⟩ : Located)) types
          held)) index =
      entryOf (plainHeld (side role) held) index
  | [], .nil, _ => rfl
  | _ :: _, .cons _ _, 0 => rfl
  | _ :: types, .cons _ held, index + 1 => entryOf_plain_remap side role types held index

theorem entryOf_plainHeld_hold : ∀ (present : Bool), present = true → ∀ {types : List Ty}
    (results : Values model.Value types) (index : Nat),
    entryOf (plainHeld present (holdValues present results)) index = entryOf results index
  | true, _, _, .nil, _ => rfl
  | true, _, _, .cons _ _, 0 => rfl
  | true, _, _, .cons _ rest, index + 1 => entryOf_plainHeld_hold true rfl rest index

/-- The results of a role of the side, held and read back, are the results. -/
theorem entryOf_plain_held (side : Side) {role : Nat} (member : side role = true)
    {types : List Ty} (results : Values model.Value types) (index : Nat) :
    entryOf (plainValues side
        (remapValues (F := SideValue model side) (fun type => (⟨type, role⟩ : Located)) types
          (holdValues (side role) results))) index =
      entryOf results index := by
  rw [entryOf_plain_remap, entryOf_plainHeld_hold _ member]

/-! ## What the roles know holds of a side's environment -/

/-- Nothing is known of the values of an environment. -/
theorem Facts.start_holds {Γ : List Ty} (env : Environment model.Value Γ) {depth : Nat}
    (counted : depth = Γ.length) : (Facts.start depth).Sound env := by
  refine ⟨counted ▸ ?_, ?_, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim, rfl⟩
  · show (List.replicate _ _).length = _
    rw [List.length_replicate]
  · intro level entry _
    have other : (Facts.start depth).shape level = .other := by
      show (List.replicate _ Shape.other).getD level Shape.other = Shape.other
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    rw [other]
    trivial

namespace RoleFacts

theorem find_put (role : Nat) (facts : Facts) (other : Nat) : ∀ (roles : List (Nat × Facts)),
    find other (put role facts roles) = if other = role then some facts else find other roles
  | [] => by
      show (if role = other then some facts else none) = _
      by_cases same : other = role
      · simp only [same, ↓reduceIte]
      · have differ : ¬ role = other := fun equal => same equal.symm
        simp only [same, differ, ↓reduceIte]
        rfl
  | entry :: rest => by
      unfold put
      by_cases first : entry.1 = role
      · simp only [first, ↓reduceIte]
        by_cases same : other = role
        · have back : role = other := same.symm
          simp only [find, back, ↓reduceIte]
        · have differ : ¬ role = other := fun equal => same equal.symm
          simp only [find, first, same, differ, ↓reduceIte]
      · simp only [first, ↓reduceIte]
        by_cases here : entry.1 = other
        · have differ : ¬ other = role := fun equal => first (here.trans equal)
          simp only [find, here, differ, ↓reduceIte]
        · simp only [find, here, ↓reduceIte]
          exact find_put role facts other rest

theorem find_map (role : Nat) (change : Facts → Facts) : ∀ (roles : List (Nat × Facts)),
    find role (roles.map fun entry => (entry.1, change entry.2)) = (find role roles).map change
  | [] => rfl
  | entry :: rest => by
      show (if entry.1 = role then _ else _) = Option.map change (if entry.1 = role then _ else _)
      by_cases same : entry.1 = role
      · simp only [same, ↓reduceIte, Option.map_some]
      · simp only [same, ↓reduceIte]
        exact find_map role change rest

/-- What the roles know holds of the environment of a side: the context has the tracked
number of values, the region runs, and what each role of the side knows holds of the
values of the side. -/
structure Sound (side : Side) (state : RoleFacts) {Γ : List Located}
    (env : Environment (SideValue model side) Γ) : Prop where
  depth : state.depth = Γ.length
  alive : state.dead = false
  roles : ∀ role, side role = true → (state.view role).Sound (plainEnvironment side env)

variable {side : Side} {state : RoleFacts} {Γ : List Located}
  {env : Environment (SideValue model side) Γ}

/-- Nothing is known of the inputs of a protocol. -/
theorem start_sound {inputs : List Located} (values : Values (SideValue model side) inputs) :
    (RoleFacts.start inputs.length).Sound side (Environment.ofValues values) := by
  refine ⟨?_, rfl, fun role _ => Facts.start_holds _ ?_⟩
  · show inputs.length = (bindAll [] inputs).length
    rw [length_bindAll]
    exact (Nat.zero_add _).symm
  · show inputs.length = ((bindAll [] inputs).map _).length
    rw [List.length_map, length_bindAll]
    exact (Nat.zero_add _).symm

/-- One role of the side knows something that holds. -/
theorem Sound.set (sound : state.Sound side env) (role : Nat) {facts : Facts}
    (holds : side role = true → facts.Sound (plainEnvironment side env)) :
    (state.set role facts).Sound side env := by
  refine ⟨sound.depth, sound.alive, fun other member => ?_⟩
  have found : find other (put role facts state.roles) =
      if other = role then some facts else find other state.roles := find_put role facts other _
  show (match find other (put role facts state.roles) with
    | some known => known
    | none => cond state.dead (Facts.start state.depth).kill (Facts.start state.depth)).Sound _
  rw [found]
  by_cases same : other = role
  · simp only [same, ↓reduceIte]
    exact holds (same ▸ member)
  · simp only [same, ↓reduceIte]
    exact sound.roles other member

/-- What the roles know holds with values that the side holds in scope: a role of the
side that holds one of them holds a value, so its type is populated. -/
theorem Sound.inScope : ∀ {types : List Located} {state : RoleFacts}, state.Sound side env →
    Values (SideValue model side) types → (state.inScope types).Sound side env
  | _, _, sound, .nil => sound
  | _, state, sound, .cons (ty := located) value rest => by
      have first : (cond located.type.populated state
          (state.set located.holder (state.view located.holder).kill)).Sound side env := by
        cases populated : located.type.populated with
        | true => exact sound
        | false =>
            refine sound.set located.holder fun member => ?_
            have held : model.Value located.type :=
              Held.value (side located.holder) member value
            rw [Ty.populated_of_value located.type held] at populated
            cases populated
      exact Sound.inScope (state := cond located.type.populated state
        (state.set located.holder (state.view located.holder).kill)) first rest

/-- Every role's facts changed in a way that keeps them holding, for another environment. -/
theorem Sound.each (sound : state.Sound side env) {Δ : List Located}
    (inner : Environment (SideValue model side) Δ) {depth : Nat} (counted : depth = Δ.length)
    {change : Facts → Facts}
    (changes : ∀ facts : Facts, facts.Sound (plainEnvironment side env) →
      (change facts).Sound (plainEnvironment side inner)) :
    (state.each depth change).Sound side inner := by
  refine ⟨counted, sound.alive, fun role member => ?_⟩
  have before := sound.roles role member
  have found := find_map role change state.roles
  show (match find role (state.roles.map fun (entry : Nat × Facts) => (entry.1, change entry.2)) with
    | some known => known
    | none => cond state.dead (Facts.start depth).kill (Facts.start depth)).Sound _
  rw [found]
  have viewed : state.view role = match find role state.roles with
      | some known => known
      | none => cond state.dead (Facts.start state.depth).kill (Facts.start state.depth) := rfl
  cases listed : find role state.roles with
  | some known =>
      rw [listed] at viewed
      rw [viewed] at before
      exact changes known before
  | none =>
      rw [sound.alive]
      exact Facts.start_holds _ (by rw [counted, List.length_map])

/-- New values of which no role knows anything. -/
theorem Sound.bind (sound : state.Sound side env) {added : List Located}
    (values : Values (SideValue model side) added) :
    (state.bind added.length).Sound side (Environment.bindAll env values) := by
  refine sound.each _ (by rw [sound.depth, length_bindAll]) fun facts holds => ?_
  have after := holds.afterAny (plainValues side values)
  rw [List.map_const', List.length_map] at after
  exact after.plain (List.length_map _) fun _ => rfl

/-- What each role knows at the start of a nested region holds of the inputs of the region,
when each input that captures a value is that value. -/
theorem Sound.enter (sound : state.Sound side env) {inputs : List Located}
    (values : Values (SideValue model side) inputs) {sources : List (Option Nat)}
    (counted : sources.length = inputs.length)
    (sourced : Sourced sources (storeOf (plainEnvironment side env))
      (entryOf (plainValues side values))) :
    (state.enter sources).Sound side (Environment.ofValues values) := by
  have length : sources.length = (bindAll [] inputs).length := by
    rw [length_bindAll, counted]
    exact (Nat.zero_add _).symm
  refine sound.each _ length fun facts holds => ⟨?_, ?_⟩
  · show (List.map _ _).length = _
    rw [List.length_map, List.length_map, length]
  · rw [storeOf_plain_ofValues]
    exact holds.2.enter sourced

/-- A value whose holder is outside the side is not a natural. -/
theorem plain_absent_ne {type : Ty} : ∀ (present : Bool), present = false →
    ∀ (held : Held (model.Value type) present) (value : Nat),
    (⟨cond present type Ty.unit, plainValue present held⟩ : Sigma model.Value) ≠ ⟨.nat, value⟩
  | false, _, _, _ => fun same => by cases same

/-- The intervals that a region returns contain the values that the side holds of the
returned values. -/
theorem Sound.returned (sound : state.Sound side env) : ∀ {out : List Located}
    (values : Operands Γ out),
    IntervalsHold ((state.returned Γ.length values).map (·.interval))
      (plainValues side (Operands.eval env values))
  | _, .nil => fun _ _ _ found _ => nomatch found
  | _, .cons (ty := located) reference rest => by
      intro index interval entry found at_
      cases index with
      | zero =>
          have known : (state.view located.holder).interval (Scope.number Γ.length reference) =
              interval := Option.some.inj found
          have same : (⟨plainType side located,
              plainValue (side located.holder) (type := located.type) (env reference)⟩ :
                Sigma model.Value) = entry := Option.some.inj at_
          subst known same
          intro value natural
          have stored := plain_number side env reference
          cases member : side located.holder with
          | false => exact absurd natural (plain_absent_ne _ member _ value)
          | true =>
              rw [natural] at stored
              have holds := (sound.roles located.holder member).2
              exact ⟨holds.lo_le stored, fun hi top => holds.le_hi stored top⟩
      | succ index => exact Sound.returned sound rest index interval entry found at_

/-- Each holder in the side of a `nat` result knows an interval that contains the
result. -/
theorem Sound.withResults : ∀ (level : Nat) (outputs : List Located) (intervals : List Interval)
    {state : RoleFacts}, state.Sound side env →
    (∀ (index : Nat) (located : Located) (interval : Interval),
      outputs[index]? = some located → intervals[index]? = some interval →
      located.type = .nat → side located.holder = true →
        ∃ value : Nat, storeOf (plainEnvironment side env) (level + index) = some ⟨.nat, value⟩ ∧
          interval.lo ≤ value ∧ ∀ hi, interval.hi = some hi → value ≤ hi) →
    (RoleFacts.withResults level outputs intervals state).Sound side env
  | _, [], _, _, sound, _ => sound
  | _, _ :: _, [], _, sound, _ => sound
  | level, located :: outputs, interval :: intervals, state, sound, read => by
      have later : ∀ (index : Nat) (other : Located) (found : Interval),
          outputs[index]? = some other → intervals[index]? = some found →
          other.type = .nat → side other.holder = true →
            ∃ value : Nat, storeOf (plainEnvironment side env) (level + 1 + index) =
                some ⟨.nat, value⟩ ∧
              found.lo ≤ value ∧ ∀ hi, found.hi = some hi → value ≤ hi := by
        intro index other found at_ known typed member
        have same : level + 1 + index = level + (index + 1) := by omega
        rw [same]
        exact read (index + 1) other found at_ known typed member
      unfold RoleFacts.withResults
      split
      · rename_i typed
        refine Sound.withResults (level + 1) outputs intervals
          (sound.set located.holder fun member => ?_) later
        obtain ⟨value, stored, low, high⟩ := read 0 located interval rfl rfl typed member
        exact (sound.roles located.holder member).bound stored low high
      · exact Sound.withResults (level + 1) outputs intervals sound later

/-- The results of a `choose` or of a block: no role knows anything of them but, for a
`nat` result that a role of the side holds, an interval that contains it. -/
theorem Sound.results (sound : state.Sound side env) {outputs : List Located}
    (results : Values (SideValue model side) outputs) (intervals : List Interval)
    (holds : ∀ (index : Nat) (located : Located) (interval : Interval)
      (entry : Sigma model.Value), outputs[index]? = some located →
      intervals[index]? = some interval → side located.holder = true →
      entryOf (plainValues side results) index = some entry → interval.Holds entry) :
    ((state.bind outputs.length).withResults state.depth outputs intervals).Sound side
      (Environment.bindAll env results) := by
  refine (sound.bind results).withResults _ _ _ fun index located interval found at_ typed
    member => ?_
  have natural : (outputs.map (plainType side))[index]? = some .nat := by
    rw [List.getElem?_map, found]
    show some (cond (side located.holder) located.type Ty.unit) = _
    rw [member, typed]
    rfl
  obtain ⟨value, entry⟩ := entryOf_type (plainValues side results) index .nat natural
  obtain ⟨low, high⟩ := holds index located interval _ found at_ member entry value rfl
  refine ⟨value, ?_, low, high⟩
  rw [storeOf_plain_bindAll, storeOf_bindAll, sound.depth]
  simp only [List.length_map, Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte,
    Nat.add_sub_cancel_left]
  exact entry

/-- The results of a `choose` without a participant in the side: no role of the side holds
one. -/
theorem Sound.outside (sound : state.Sound side env) {participants : List Nat}
    {outputs : List Located} (covered : Located.heldBy participants outputs = true)
    (outside : participants.any side = false)
    (results : Values (SideValue model side) outputs) (intervals : List Interval) :
    ((state.bind outputs.length).withResults state.depth outputs intervals).Sound side
      (Environment.bindAll env results) :=
  sound.results results intervals fun _ located _ _ found _ member _ => by
    have absent := not_held_of_heldBy covered outside (List.mem_of_getElem? found)
    rw [absent] at member
    cases member

/-- The results of regions that return values in the intervals of an outcome. -/
theorem Sound.joined (sound : state.Sound side env) {outputs : List Located}
    (results : Values (SideValue model side) outputs) {outcome : Outcome}
    (holds : outcome.Bounds (plainValues side results)) :
    ((state.bind outputs.length).withResults state.depth outputs outcome.intervals).Sound side
      (Environment.bindAll env results) := by
  cases outcome with
  | none => exact holds.elim
  | some returned =>
      exact sound.results results _ fun index located interval entry _ at_ _ stored =>
        holds index interval entry at_ stored

end RoleFacts

end Zkc.Core
