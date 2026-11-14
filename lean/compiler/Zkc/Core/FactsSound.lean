module

public import Zkc.Core.FactsHold
public import Zkc.Core.ProtocolFacts

public section

/-! A function that passes the check of facts never stops `undefined`.

For every model that satisfies the domain laws of its restricted rows, the meaning of a
function whose body passes the check, over functions that never stop `undefined`, never
stops `undefined`, on any arguments. The proof follows the check: the facts at each
instruction hold of the environment there (`Facts.Sound`), a justified application is
therefore inside its domain, and the facts after it hold of the environment that binds its
results.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-! ## Processes that never stop `undefined` -/

/-- A process never stops `undefined`, and every result it returns satisfies `post`,
through every reply of every effect. -/
def Yields {I : PIR.Signature} {A : Type} (post : A → Prop) : PIR.Process I A → Prop
  | .done value => post value
  | .halt why => why ≠ .undefined
  | .call _ next => ∀ reply, Yields post (next reply)

theorem Yields.done {I : PIR.Signature} {A : Type} {post : A → Prop} {value : A}
    (holds : post value) : Yields post (.done value : PIR.Process I A) := holds

theorem Yields.halt {I : PIR.Signature} {A : Type} {post : A → Prop} {why : PIR.Stop}
    (other : why ≠ .undefined) : Yields post (.halt why : PIR.Process I A) := other

theorem Yields.call {I : PIR.Signature} {A : Type} {post : A → Prop} {op : I.Op}
    {next : I.Reply op → PIR.Process I A} (continues : ∀ reply, Yields post (next reply)) :
    Yields post (.call op next) := continues

theorem Yields.bind {I : PIR.Signature} {A B : Type} {post : A → Prop} {after : B → Prop}
    {source : PIR.Process I A} {next : A → PIR.Process I B} (yields : Yields post source)
    (continues : ∀ value, post value → Yields after (next value)) :
    Yields after (source.bind next) := by
  induction source with
  | done value => exact continues value yields
  | halt why => exact yields
  | call op tail ih => exact fun reply => ih reply (yields reply)

theorem Yields.weaken {I : PIR.Signature} {A : Type} {post wider : A → Prop}
    {source : PIR.Process I A} (yields : Yields post source)
    (implies : ∀ value, post value → wider value) : Yields wider source := by
  induction source with
  | done value => exact implies value yields
  | halt why => exact yields
  | call op tail ih => exact fun reply => ih reply (yields reply)

theorem Yields.neverStops {I : PIR.Signature} {A : Type} {post : A → Prop}
    {source : PIR.Process I A} (yields : Yields post source) :
    NeverStops .undefined source := by
  induction source with
  | done value => exact NeverStops.done _ value
  | halt why => exact NeverStops.halt_iff.mpr yields
  | call op tail ih => exact NeverStops.call_iff.mpr fun reply => ih reply (yields reply)

theorem NeverStops.yields {I : PIR.Signature} {A : Type} {source : PIR.Process I A}
    (never : NeverStops .undefined source) : Yields (fun _ => True) source := by
  induction source with
  | done value => trivial
  | halt why => exact NeverStops.halt_iff.mp never
  | call op tail ih => exact fun reply => ih reply (NeverStops.call_iff.mp never reply)

/-- A process that never stops with a reason, followed by processes that never do, never
does. -/
theorem NeverStops.bind {I : PIR.Signature} {A B : Type} {reason : PIR.Stop}
    {source : PIR.Process I A} {next : A → PIR.Process I B} (never : NeverStops reason source)
    (continues : ∀ value, NeverStops reason (next value)) :
    NeverStops reason (source.bind next) := by
  induction source with
  | done value => exact continues value
  | halt why => exact NeverStops.halt_iff.mpr (NeverStops.halt_iff.mp never)
  | call op tail ih =>
      exact NeverStops.call_iff.mpr fun reply => ih reply (NeverStops.call_iff.mp never reply)

variable {model : Model}

/-- A value that exists is returned; none stops `undefined`. -/
theorem yields_defined {A : Type} {post : A → Prop} {result : Option A}
    (defined : result.isSome = true) (holds : ∀ value, result = some value → post value) :
    Yields post (definedProcess model result) := by
  cases result with
  | none => cases defined
  | some value => exact holds value rfl

/-- A function known by its header stops with an authored reason. -/
theorem partialProcess_neverStops {A : Type} (result : Except Reason A) :
    NeverStops .undefined (partialProcess model result) := by
  cases result with
  | ok value => exact NeverStops.done _ value
  | error reason => exact NeverStops.halt_iff.mpr reason.stop_ne_undefined

/-- A process returns only values that satisfy `post`, through every reply of every
effect. It may stop. -/
def Returns {I : PIR.Signature} {A : Type} (post : A → Prop) : PIR.Process I A → Prop
  | .done value => post value
  | .halt _ => True
  | .call _ next => ∀ reply, Returns post (next reply)

theorem Returns.of_forall {I : PIR.Signature} {A : Type} {post : A → Prop}
    (holds : ∀ value, post value) (source : PIR.Process I A) : Returns post source := by
  induction source with
  | done value => exact holds value
  | halt why => trivial
  | call op tail ih => exact fun reply => ih reply

theorem Yields.and {I : PIR.Signature} {A : Type} {post other : A → Prop}
    {source : PIR.Process I A} (yields : Yields post source) (returns : Returns other source) :
    Yields (fun value => post value ∧ other value) source := by
  induction source with
  | done value => exact ⟨yields, returns⟩
  | halt why => exact yields
  | call op tail ih => exact fun reply => ih reply (yields reply) (returns reply)

/-- The iterations of a loop never stop `undefined` when no iteration below the count
does, and they keep an invariant of the iteration number and the carried values that
every iteration keeps. -/
theorem loopIterations_invariant {carried collected : List Ty}
    {step : Nat → Values model.Value carried →
      PIR.Process (Effects model) (Values model.Value (collected ++ carried))} {count : Nat}
    (invariant : Nat → Values model.Value carried → Prop)
    (steps : ∀ iteration state, iteration < count → invariant iteration state →
      Yields (fun produced => invariant (iteration + 1) (produced.split collected).2)
        (step iteration state)) :
    ∀ (remaining done : Nat) (state : Values model.Value carried)
      (earlier : Values model.Value (collectedSequences (some done) collected)),
      done + remaining ≤ count → invariant done state →
        Yields (fun final => invariant (done + remaining) final.1)
          (loopIterations model carried collected step remaining done state earlier)
  | 0, _, _, _, _, holds => holds
  | remaining + 1, done, state, earlier, within, holds =>
      (steps done state (by omega) holds).bind fun produced next => by
        have rest := loopIterations_invariant invariant steps remaining (done + 1)
          (produced.split collected).2
          (collectedPush model collected (produced.split collected).1 earlier) (by omega) next
        have same : done + 1 + remaining = done + (remaining + 1) := by omega
        rw [same] at rest
        exact rest

/-! ## Results -/

/-- A natural is in an interval; a value of another type is in every interval. -/
@[expose] def Interval.Holds (interval : Interval) (entry : Sigma model.Value) : Prop :=
  ∀ value : Nat, entry = ⟨.nat, value⟩ →
    interval.lo ≤ value ∧ ∀ hi, interval.hi = some hi → value ≤ hi

/-- Each value is in the interval of its position. -/
@[expose] def IntervalsHold (intervals : List Interval) {types : List Ty} (values : Values model.Value types) :
    Prop :=
  ∀ (index : Nat) (interval : Interval) (entry : Sigma model.Value),
    intervals[index]? = some interval → entryOf values index = some entry → interval.Holds entry

/-- The intervals that a region returns hold of returned values: a region that does not
return returns none. -/
@[expose] def Outcome.Bounds {types : List Ty} : Outcome → Values model.Value types → Prop
  | none, _ => False
  | some returned, values => IntervalsHold (returned.map (·.interval)) values

/-- Each returned value that is a sum is, for an addend that is a natural of the store,
that natural plus a term in the interval of the other addend. -/
def StepsHold (store : Store model) (returned : List Returned) {types : List Ty}
    (values : Values model.Value types) : Prop :=
  ∀ (index : Nat) (found : Returned) (entry : Sigma model.Value),
    returned[index]? = some found → entryOf values index = some entry →
      ∀ step ∈ found.steps, ∀ x : Nat, store step.1 = some ⟨.nat, x⟩ →
        ∃ y : Nat, entry = ⟨.nat, (x + y : Nat)⟩ ∧ step.2.lo ≤ y ∧
          ∀ hi, step.2.hi = some hi → y ≤ hi

/-- What a region returns holds of returned values, for the store of the environment the
region started in. -/
def Outcome.Holds (store : Store model) {types : List Ty} (outcome : Outcome)
    (values : Values model.Value types) : Prop :=
  outcome.Bounds values ∧ StepsHold store outcome.returned values

/-- What a region returns holds for a store with fewer values. -/
theorem Outcome.Holds.shrink {store other : Store model} {types : List Ty} {outcome : Outcome}
    {values : Values model.Value types} (holds : outcome.Holds other values)
    (grows : ∀ level entry, store level = some entry → other level = some entry) :
    outcome.Holds store values :=
  ⟨holds.1, fun index found entry at_ value step member x first =>
    holds.2 index found entry at_ value step member x (grows _ _ first)⟩

theorem Interval.Holds.join_left {first second : Interval} {entry : Sigma model.Value}
    (holds : first.Holds entry) : (first.join second).Holds entry := by
  intro value same
  obtain ⟨low, high⟩ := holds value same
  refine ⟨Nat.le_trans (Nat.min_le_left _ _) low, ?_⟩
  intro hi at_
  unfold Interval.join at at_
  dsimp only at at_
  split at at_
  · rename_i one two left right
    cases Option.some.inj at_
    exact Nat.le_trans (high one left) (Nat.le_max_left _ _)
  · cases at_

theorem Interval.Holds.join_right {first second : Interval} {entry : Sigma model.Value}
    (holds : second.Holds entry) : (first.join second).Holds entry := by
  intro value same
  obtain ⟨low, high⟩ := holds value same
  refine ⟨Nat.le_trans (Nat.min_le_right _ _) low, ?_⟩
  intro hi at_
  unfold Interval.join at at_
  dsimp only at at_
  split at at_
  · rename_i one two left right
    cases Option.some.inj at_
    exact Nat.le_trans (high two right) (Nat.le_max_right _ _)
  · cases at_

theorem joinIntervals_at : ∀ (firsts seconds : List Interval) (index : Nat) (interval : Interval),
    (joinIntervals firsts seconds)[index]? = some interval →
      ∃ first second, firsts[index]? = some first ∧ seconds[index]? = some second ∧
        interval = first.join second
  | [], _, _, _, found => nomatch found
  | _ :: _, [], _, _, found => nomatch found
  | first :: _, second :: _, 0, _, found => ⟨first, second, rfl, rfl, (Option.some.inj found).symm⟩
  | _ :: firsts, _ :: seconds, index + 1, interval, found =>
      joinIntervals_at firsts seconds index interval found

/-- The intervals of the values that one of two regions returns. -/
theorem joined_intervals (firsts seconds : List Returned) :
    ((joinIntervals (firsts.map (·.interval)) (seconds.map (·.interval))).map
      fun interval => (⟨interval, []⟩ : Returned)).map (·.interval) =
        joinIntervals (firsts.map (·.interval)) (seconds.map (·.interval)) := by
  rw [List.map_map]
  exact List.map_id _

theorem Outcome.Bounds.join_left {types : List Ty} {values : Values model.Value types}
    {first : Outcome} (holds : first.Bounds values) (second : Outcome) :
    (first.join second).Bounds values := by
  cases first with
  | none => exact holds.elim
  | some firsts =>
      cases second with
      | none => exact holds
      | some seconds =>
          show IntervalsHold (List.map Returned.interval (List.map _ _)) values
          rw [joined_intervals]
          intro index interval entry found at_
          obtain ⟨one, two, left, _, same⟩ := joinIntervals_at _ _ index interval found
          rw [same]
          exact (holds index one entry left at_).join_left

theorem Outcome.Bounds.join_right {types : List Ty} {values : Values model.Value types}
    {second : Outcome} (holds : second.Bounds values) (first : Outcome) :
    (first.join second).Bounds values := by
  cases second with
  | none => exact holds.elim
  | some seconds =>
      cases first with
      | none => exact holds
      | some firsts =>
          show IntervalsHold (List.map Returned.interval (List.map _ _)) values
          rw [joined_intervals]
          intro index interval entry found at_
          obtain ⟨one, two, _, right, same⟩ := joinIntervals_at _ _ index interval found
          rw [same]
          exact (holds index two entry right at_).join_right

theorem Outcome.joinAll_single (outcome : Outcome) : Outcome.joinAll [outcome] = outcome := by
  cases outcome <;> rfl

theorem mem_boundsOf {bound : Bound} : ∀ (level : Nat) (types : List Ty) (intervals : List Interval),
    bound ∈ boundsOf level types intervals →
      ∃ index, bound.level = level + index ∧ types[index]? = some .nat ∧
        intervals[index]? = some ⟨bound.lo, bound.hi⟩
  | _, [], _, member => by
      unfold boundsOf at member
      cases member
  | _, _ :: _, [], member => by
      unfold boundsOf at member
      cases member
  | level, type :: types, interval :: rest, member => by
      have later : bound ∈ boundsOf (level + 1) types rest →
          ∃ index, bound.level = level + index ∧ (type :: types)[index]? = some .nat ∧
            (interval :: rest)[index]? = some ⟨bound.lo, bound.hi⟩ := fun inside => by
        obtain ⟨index, at_, typed, found⟩ := mem_boundsOf (level + 1) types rest inside
        exact ⟨index + 1, by omega, typed, found⟩
      unfold boundsOf at member
      split at member
      · rcases List.mem_cons.mp member with rfl | inside
        · exact ⟨0, rfl, rfl, rfl⟩
        · exact later inside
      · exact later member

/-- The facts after the results of a nested computation hold: nothing is tracked of their
shapes, and a natural is in the interval that the computation returns for it. -/
theorem Facts.Sound.afterOutcome {Γ added : List Ty} {env : Environment model.Value Γ}
    {facts : Facts} (sound : facts.Sound env) (values : Values model.Value added)
    {outcome : Outcome} (holds : outcome.Bounds values) :
    (facts.after (added.map fun _ => Shape.other)
      (boundsOf facts.depth added outcome.intervals)).Sound (Environment.bindAll env values) := by
  refine sound.after values _ _ (List.length_map _) ?_ ?_
  · intro index entry _
    have other : (added.map fun _ => Shape.other).getD index Shape.other = Shape.other := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases added[index]? <;> rfl
    rw [other]
    trivial
  · intro bound member
    cases outcome with
    | none => exact holds.elim
    | some intervals =>
        obtain ⟨index, level, typed, found⟩ := mem_boundsOf _ _ _ member
        obtain ⟨value, at_⟩ := entryOf_type values index .nat typed
        obtain ⟨low, high⟩ := holds index _ _ found at_ value rfl
        exact ⟨index, value, by rw [level, sound.1], at_, low, high⟩

/-! ## Entering a region -/

theorem Reads.length {store : Store model} : ∀ {levels : List Nat} {types : List Ty}
    {values : Values model.Value types}, Reads store levels values → levels.length = types.length
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons _ _, reads => congrArg (· + 1) reads.2.length
  | [], _, .cons _ _, reads => reads.elim
  | _ :: _, _, .nil, reads => reads.elim

/-- The facts that enter a nested region hold of its inputs: inputs that are not captures,
then the captures. -/
theorem Facts.Sound.enter {Γ : List Ty} {env : Environment model.Value Γ} {facts : Facts}
    (sound : facts.Sound env) {fresh captures : List Ty} (values : Values model.Value fresh)
    {levels : List Nat} {captured : Values model.Value captures}
    (reads : Reads (storeOf env) levels captured) :
    (facts.enter (List.replicate fresh.length none ++ levels.map some)).Sound
      (Environment.ofValues (values.append captured)) := by
  refine ⟨?_, ?_⟩
  · show (List.map _ _).length = _
    rw [List.length_map, List.length_append, List.length_replicate, List.length_map,
      length_bindAll, List.length_append, reads.length, List.length_nil, Nat.zero_add]
  · have same : storeOf (Environment.ofValues (values.append captured)) =
        entryOf (values.append captured) := funext fun level => storeOf_ofValues _ level
    rw [same]
    exact sound.2.enter (sourced_append values reads)

theorem Facts.Sound.bound {Γ : List Ty} {env : Environment model.Value Γ} {facts : Facts}
    (sound : facts.Sound env) {level lo value : Nat} {hi : Option Nat}
    (found : storeOf env level = some ⟨.nat, value⟩) (low : lo ≤ value)
    (high : ∀ end_, hi = some end_ → value ≤ end_) : (facts.bound level lo hi).Sound env :=
  ⟨sound.1, sound.2.bound found low high⟩

theorem Facts.Sound.order {Γ : List Ty} {env : Environment model.Value Γ} {facts : Facts}
    (sound : facts.Sound env) {strict : Bool} {left right x y : Nat}
    (first : storeOf env left = some ⟨.nat, x⟩) (second : storeOf env right = some ⟨.nat, y⟩)
    (most : x ≤ y) (less : strict = true → x < y) : (facts.order strict left right).Sound env :=
  ⟨sound.1, sound.2.order first second most less⟩

/-- Facts that hold of an environment hold with values that exist in scope: their types
are populated, and the facts are unchanged. -/
theorem Facts.Sound.inScope {Γ : List Ty} {env : Environment model.Value Γ} {facts : Facts}
    (sound : facts.Sound env) {types : List Ty} (values : Values model.Value types) :
    (facts.inScope types).Sound env := by
  show (cond (Ty.allPopulated types) facts facts.kill).Sound env
  rw [Ty.allPopulated_of_values values]
  exact sound

/-- Nothing is known of the inputs of a function. -/
theorem Facts.start_sound {inputs : List Ty} (values : Values model.Value inputs) :
    (Facts.start inputs.length).Sound (Environment.ofValues values) := by
  refine ⟨?_, ?_, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim, rfl⟩
  · show (List.replicate _ _).length = _
    rw [List.length_replicate, length_bindAll]
    exact (Nat.zero_add _).symm
  · intro level entry _
    have other : (Facts.start inputs.length).shape level = .other := by
      show (List.replicate _ Shape.other).getD level Shape.other = Shape.other
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    rw [other]
    trivial

/-! ## Operations the core owns -/

section Builtin

variable {Γ : List Ty} {env : Environment model.Value Γ} {facts : Facts}

theorem operands_one {type : Ty} (operands : Operands Γ [type]) :
    ∃ first, operands = .cons first .nil := by
  cases operands with
  | cons first rest => cases rest with
    | nil => exact ⟨first, rfl⟩

theorem operands_two {one two : Ty} (operands : Operands Γ [one, two]) :
    ∃ first second, operands = .cons first (.cons second .nil) := by
  cases operands with
  | cons first rest => cases rest with
    | cons second rest => cases rest with
      | nil => exact ⟨first, second, rfl⟩

theorem operands_three {one two three : Ty} (operands : Operands Γ [one, two, three]) :
    ∃ first second third, operands = .cons first (.cons second (.cons third .nil)) := by
  cases operands with
  | cons first rest => cases rest with
    | cons second rest => cases rest with
      | cons third rest => cases rest with
        | nil => exact ⟨first, second, third, rfl⟩

/-- The facts after one new value: its shape, and its interval when it is a natural. -/
theorem Facts.Sound.single (sound : facts.Sound env) {type : Ty} (value : model.Value type)
    (shape : Shape) (interval : Option Interval)
    (shaped : shape.Holds (storeOf env) ⟨type, value⟩)
    (bounded : ∀ found, interval = some found →
      ∃ number : Nat, (⟨type, value⟩ : Sigma model.Value) = ⟨.nat, number⟩ ∧
        found.lo ≤ number ∧ ∀ hi, found.hi = some hi → number ≤ hi) :
    (facts.after [shape] (boundOf facts.depth interval)).Sound
      (Environment.bindAll env (Values.cons value Values.nil)) := by
  refine sound.after _ _ _ rfl ?_ ?_
  · intro index entry found
    cases index with
    | zero =>
        cases Option.some.inj found
        exact shaped
    | succ index => cases found
  · intro bound member
    cases interval with
    | none => cases member
    | some found =>
        obtain ⟨number, same, low, high⟩ := bounded found rfl
        rcases List.mem_cons.mp member with rfl | impossible
        · exact ⟨0, number, sound.1, by rw [← same]; rfl, low, high⟩
        · cases impossible

theorem plus_le {x y : Nat} {first second : Option Nat} (one : ∀ hi, first = some hi → x ≤ hi)
    (two : ∀ hi, second = some hi → y ≤ hi) : ∀ hi, plus first second = some hi → x + y ≤ hi := by
  intro hi at_
  cases first with
  | none => cases at_
  | some a =>
      cases second with
      | none => cases at_
      | some b =>
          cases Option.some.inj at_
          exact Nat.add_le_add (one a rfl) (two b rfl)

theorem times_le {x y : Nat} {first second : Option Nat} (one : ∀ hi, first = some hi → x ≤ hi)
    (two : ∀ hi, second = some hi → y ≤ hi) : ∀ hi, times first second = some hi → x * y ≤ hi := by
  intro hi at_
  cases first with
  | none => cases at_
  | some a =>
      cases second with
      | none => cases at_
      | some b =>
          cases Option.some.inj at_
          exact Nat.mul_le_mul (one a rfl) (two b rfl)

theorem atMost_le {x : Nat} {first second : Option Nat} (one : ∀ hi, first = some hi → x ≤ hi)
    (two : ∀ hi, second = some hi → x ≤ hi) : ∀ hi, atMost first second = some hi → x ≤ hi := by
  intro hi at_
  cases first with
  | none => exact two hi at_
  | some a =>
      cases second with
      | none =>
          cases Option.some.inj at_
          exact one _ rfl
      | some b =>
          cases Option.some.inj at_
          exact Nat.le_min.mpr ⟨one a rfl, two b rfl⟩

theorem before_le {x y : Nat} {end_ : Option Nat} (less : x < y)
    (most : ∀ hi, end_ = some hi → y ≤ hi) : ∀ hi, Facts.before end_ = some hi → x ≤ hi := by
  intro hi at_
  cases end_ with
  | none => cases at_
  | some a =>
      cases Option.some.inj at_
      have := most a rfl
      omega

theorem pow_low {x y lo : Nat} {exponentLo : Nat} {exponentHi : Option Nat} (low : lo ≤ x)
    (least : exponentLo ≤ y) (most : ∀ hi, exponentHi = some hi → y ≤ hi) :
    cond (decide (1 ≤ lo)) (lo ^ exponentLo) (cond (within exponentHi 0) 1 0) ≤ x ^ y := by
  by_cases positive : 1 ≤ lo
  · simp only [positive, decide_true, Bool.cond_true]
    exact Nat.le_trans (Nat.pow_le_pow_left low exponentLo)
      (Nat.pow_le_pow_right (by omega) least)
  · simp only [positive, decide_false, Bool.cond_false]
    cases zero : within exponentHi 0 with
    | false => exact Nat.zero_le _
    | true =>
        obtain ⟨end_, high, none⟩ := within_le zero
        have := most end_ high
        have exponent : y = 0 := by omega
        rw [exponent]
        exact Nat.le_refl _

theorem pow_high {x y base exponent lo : Nat} (first : x ≤ base) (second : y ≤ exponent)
    (least : lo ≤ y) :
    x ^ y ≤ cond (decide (lo = 0)) (max (base ^ exponent) 1) (base ^ exponent) := by
  by_cases positive : 1 ≤ x
  · have power : x ^ y ≤ base ^ exponent :=
      Nat.le_trans (Nat.pow_le_pow_left first y) (Nat.pow_le_pow_right (by omega) second)
    cases decide (lo = 0) with
    | true => exact Nat.le_trans power (Nat.le_max_left _ _)
    | false => exact power
  · have zero : x = 0 := by omega
    subst zero
    cases y with
    | zero =>
        have none : lo = 0 := by omega
        simp only [none, decide_true, Bool.cond_true]
        exact Nat.le_max_right _ _
    | succ y =>
        rw [Nat.zero_pow (Nat.succ_pos y)]
        exact Nat.zero_le _

/-- The value at a level whose shape is the length of a sequence is that length. -/
theorem Facts.Sound.length_at (sound : facts.Sound env) {element : Ty} {size : Option Nat}
    (sequence : Var Γ (.seq element size)) {level : Nat}
    (shaped : facts.shape level = .length (Scope.number Γ.length sequence)) :
    storeOf env level = some ⟨.nat, (Ty.elements size (env sequence)).length⟩ := by
  have inside : level < Γ.length := by
    rw [← sound.1]
    exact Facts.shape_defined (by rw [shaped]; exact Shape.noConfusion)
  obtain ⟨entry, found⟩ := storeOf_defined env inside
  have holds := sound.2.shapes level entry found
  rw [shaped] at holds
  obtain ⟨other, otherSize, values, at_, value⟩ := holds
  rw [found, value, store_length at_ (storeOf_number env sequence)]

theorem Facts.mem_lengthsFrom {sequence level : Nat} : ∀ (shapes : List Shape) (first : Nat),
    level ∈ lengthsFrom sequence shapes first →
      ∃ index, level = first + index ∧ shapes[index]? = some (.length sequence)
  | [], _, member => nomatch member
  | shape :: rest, first, member => by
      have later : level ∈ lengthsFrom sequence rest (first + 1) →
          ∃ index, level = first + index ∧ (shape :: rest)[index]? = some (.length sequence) :=
        fun inside => by
          obtain ⟨index, at_, found⟩ := Facts.mem_lengthsFrom rest (first + 1) inside
          exact ⟨index + 1, by omega, found⟩
      unfold lengthsFrom at member
      split at member
      · split at member
        · rename_i same
          rcases List.mem_cons.mp member with rfl | inside
          · exact ⟨0, rfl, by rw [same]; rfl⟩
          · exact later inside
        · exact later member
      · exact later member

theorem Facts.shape_of_mem_lengths {sequence level : Nat}
    (member : level ∈ facts.lengths sequence) : facts.shape level = .length sequence := by
  obtain ⟨index, at_, found⟩ := Facts.mem_lengthsFrom facts.shapes 0 member
  rw [Nat.zero_add] at at_
  subst at_
  show facts.shapes.getD level .other = _
  rw [List.getD_eq_getElem?_getD, found]
  rfl

theorem entry_nat {x y : Nat} (same : (⟨.nat, x⟩ : Sigma model.Value) = ⟨.nat, y⟩) : x = y :=
  entry_eq same

theorem store_nat {store : Store model} {level x y : Nat} (one : store level = some ⟨.nat, x⟩)
    (other : store level = some ⟨.nat, y⟩) : x = y :=
  store_eq one other

/-- The element at a position below the length exists. -/
theorem at_defined {element : Ty} (elements : List (model.Value element)) (position : Nat)
    (inside : position < elements.length) :
    ((elements[position]?).map fun value =>
      Values.cons (Value := model.Value) value Values.nil).isSome = true := by
  rw [List.getElem?_eq_getElem inside]
  rfl

/-- The slice between ordered bounds within the length exists, at a size that is their
difference. -/
theorem slice_defined {element : Ty} (elements : List (model.Value element)) (first last : Nat)
    (result : Option Nat) (ordered : first ≤ last) (inside : last ≤ elements.length)
    (sized : ∀ count, result = some count → last - first = count) :
    (if (Nat.ble first last && Nat.ble last elements.length) = true then
        (Ty.sequence (Carrier := model.Carrier) result
          ((elements.drop first).take (last - first))).map fun slice =>
            Values.cons (Value := model.Value) slice Values.nil
      else none).isSome = true := by
  simp only [Nat.ble_eq_true_of_le ordered, Nat.ble_eq_true_of_le inside, Bool.and_self,
    ↓reduceIte]
  cases result with
  | none => rfl
  | some count =>
      have counted : ((elements.drop first).take (last - first)).length = count := by
        have difference := sized count rfl
        rw [List.length_take, List.length_drop]
        omega
      simp only [Ty.sequence, counted, ↓reduceDIte]
      rfl

/-- A sequence whose length is a size is the sequence at that size. -/
theorem sized_defined {element : Ty} (elements : List (model.Value element)) (size : Nat)
    (counted : elements.length = size) :
    ((Ty.sequence (Carrier := model.Carrier) (some size) elements).map fun sized =>
      Values.cons (Value := model.Value) sized Values.nil).isSome = true := by
  simp only [Ty.sequence, counted, ↓reduceDIte]
  rfl

/-- A natural below a bound is a value below it. -/
theorem below_defined (value bound : Nat) (inside : value < bound) :
    (if below : value < bound then
        some (Values.cons (Value := model.Value) (ty := .fin bound) (⟨value, below⟩ : Fin bound)
          Values.nil)
      else none).isSome = true := by
  simp only [inside, ↓reduceDIte]
  rfl

/-- A justified application of an operation the core owns has a value, and the facts
after it hold of the environment that binds the value. -/
theorem Builtin.sound (sound : facts.Sound env) : ∀ (operation : Builtin)
    (arguments : Operands Γ operation.arguments),
    operation.justified facts (Scope.numbers Γ.length arguments) = true →
      Yields (fun results =>
          (facts.after [operation.shape (Scope.numbers Γ.length arguments)]
            (boundOf facts.depth
              (operation.interval facts (Scope.numbers Γ.length arguments)))).Sound
            (Environment.bindAll env results))
        (definedProcess model (operation.eval (Operands.eval env arguments)))
  | .natAdd, arguments, _ => by
      obtain ⟨a, b, rfl⟩ := operands_two arguments
      refine sound.single (type := .nat) (env a + env b : Nat) _ _ ?_ ?_
      · exact ⟨_, _, storeOf_number env a, storeOf_number env b, rfl⟩
      intro found same
      cases Option.some.inj same
      exact ⟨_, rfl, Nat.add_le_add (sound.2.lo_le (storeOf_number env a))
          (sound.2.lo_le (storeOf_number env b)),
        plus_le (fun _ at_ => sound.2.le_hi (storeOf_number env a) at_)
          (fun _ at_ => sound.2.le_hi (storeOf_number env b) at_)⟩
  | .natMul, arguments, _ => by
      obtain ⟨a, b, rfl⟩ := operands_two arguments
      refine sound.single (type := .nat) (env a * env b : Nat) _ _ ?_ ?_
      · trivial
      intro found same
      cases Option.some.inj same
      exact ⟨_, rfl, Nat.mul_le_mul (sound.2.lo_le (storeOf_number env a))
          (sound.2.lo_le (storeOf_number env b)),
        times_le (fun _ at_ => sound.2.le_hi (storeOf_number env a) at_)
          (fun _ at_ => sound.2.le_hi (storeOf_number env b) at_)⟩
  | .natPow, arguments, _ => by
      obtain ⟨a, b, rfl⟩ := operands_two arguments
      refine sound.single (type := .nat) (env a ^ env b : Nat) _ _ ?_ ?_
      · trivial
      intro found same
      cases Option.some.inj same
      refine ⟨_, rfl, pow_low (sound.2.lo_le (storeOf_number env a))
          (sound.2.lo_le (storeOf_number env b))
          (fun _ at_ => sound.2.le_hi (storeOf_number env b) at_), ?_⟩
      intro hi at_
      dsimp only at at_
      split at at_
      · rename_i base exponent first second
        cases Option.some.inj at_
        exact pow_high (sound.2.le_hi (storeOf_number env a) first)
          (sound.2.le_hi (storeOf_number env b) second) (sound.2.lo_le (storeOf_number env b))
      · cases at_
  | .natEqual, arguments, _ => by
      obtain ⟨a, b, rfl⟩ := operands_two arguments
      refine sound.single (type := .bool) (Nat.beq (env a) (env b)) _ _ ?_ ?_
      · exact ⟨_, _, storeOf_number env a, storeOf_number env b, rfl⟩
      · intro _ absent
        cases absent
  | .natLess, arguments, _ => by
      obtain ⟨a, b, rfl⟩ := operands_two arguments
      refine sound.single (type := .bool) (Nat.blt (env a) (env b)) _ _ ?_ ?_
      · exact ⟨_, _, storeOf_number env a, storeOf_number env b, rfl⟩
      · intro _ absent
        cases absent
  | .natSub, arguments, justified => by
      obtain ⟨a, b, rfl⟩ := operands_two arguments
      have least := sound.2.knownLe (storeOf_number env b) (storeOf_number env a) justified
      have defined : Builtin.natSub.eval (Carrier := model.Carrier)
          (Operands.eval env (.cons a (.cons b .nil))) =
            some (.cons (env a - env b : Nat) .nil) := by
        show (if Nat.ble (env b) (env a) = true then _ else _) = _
        simp only [Nat.ble_eq_true_of_le least, ↓reduceIte]
      rw [defined]
      refine sound.single (type := .nat) (env a - env b : Nat) _ _ ?_ ?_
      · exact ⟨_, _, storeOf_number env a, storeOf_number env b, least, rfl⟩
      intro found same
      cases Option.some.inj same
      have low := sound.2.lo_le (storeOf_number env a)
      have under := sound.2.lo_le (storeOf_number env b)
      refine ⟨_, rfl, ?_, ?_⟩
      · dsimp only
        split
        · rename_i hi at_
          have := sound.2.le_hi (storeOf_number env b) at_
          omega
        · exact Nat.zero_le _
      · intro hi at_
        dsimp only at at_
        split at at_
        · rename_i top first
          have := sound.2.le_hi (storeOf_number env a) first
          cases Option.some.inj at_
          omega
        · cases at_
  | .natDiv, arguments, justified => by
      obtain ⟨a, b, rfl⟩ := operands_two arguments
      have under := sound.2.lo_le (storeOf_number env b)
      have positive := Nat.le_trans (of_decide_eq_true justified) under
      have defined : Builtin.natDiv.eval (Carrier := model.Carrier)
          (Operands.eval env (.cons a (.cons b .nil))) =
            some (.cons (env a / env b : Nat) .nil) := by
        show (if Nat.ble 1 (env b) = true then _ else _) = _
        simp only [Nat.ble_eq_true_of_le positive, ↓reduceIte]
      rw [defined]
      refine sound.single (type := .nat) (env a / env b : Nat) _ _ ?_ ?_
      · trivial
      intro found same
      cases Option.some.inj same
      have low := sound.2.lo_le (storeOf_number env a)
      have nonzero := Nat.ne_of_gt positive
      refine ⟨_, rfl, ?_, ?_⟩
      · dsimp only
        split
        · rename_i hi at_
          exact Nat.div_le_div low (sound.2.le_hi (storeOf_number env b) at_) nonzero
        · exact Nat.zero_le _
      · intro hi at_
        dsimp only at at_
        split at at_
        · rename_i top first
          have least : 1 ≤ facts.lo (Scope.number Γ.length b) := of_decide_eq_true justified
          simp only [least, decide_true, Bool.cond_true] at at_
          cases Option.some.inj at_
          exact Nat.div_le_div (sound.2.le_hi (storeOf_number env a) first) under
            (Nat.ne_of_gt least)
        · cases at_
  | .natRem, arguments, justified => by
      obtain ⟨a, b, rfl⟩ := operands_two arguments
      have under := sound.2.lo_le (storeOf_number env b)
      have positive := Nat.le_trans (of_decide_eq_true justified) under
      have defined : Builtin.natRem.eval (Carrier := model.Carrier)
          (Operands.eval env (.cons a (.cons b .nil))) =
            some (.cons (env a % env b : Nat) .nil) := by
        show (if Nat.ble 1 (env b) = true then _ else _) = _
        simp only [Nat.ble_eq_true_of_le positive, ↓reduceIte]
      rw [defined]
      refine sound.single (type := .nat) (env a % env b : Nat) _ _ ?_ ?_
      · trivial
      intro found same
      cases Option.some.inj same
      exact ⟨_, rfl, Nat.zero_le _,
        atMost_le
          (fun _ at_ => Nat.le_trans (Nat.mod_le _ _) (sound.2.le_hi (storeOf_number env a) at_))
          (before_le (Nat.mod_lt _ positive)
            fun _ at_ => sound.2.le_hi (storeOf_number env b) at_)⟩
  | .boolAnd, arguments, _ => by
      obtain ⟨a, b, rfl⟩ := operands_two arguments
      refine sound.single (type := .bool) (env a && env b) _ _ ?_ ?_
      · exact ⟨_, _, storeOf_number env a, storeOf_number env b, rfl⟩
      · intro _ absent
        cases absent
  | .boolOr, arguments, _ => by
      obtain ⟨a, b, rfl⟩ := operands_two arguments
      refine sound.single (type := .bool) (env a || env b) _ _ ?_ ?_
      · exact ⟨_, _, storeOf_number env a, storeOf_number env b, rfl⟩
      · intro _ absent
        cases absent
  | .boolNot, arguments, _ => by
      obtain ⟨a, rfl⟩ := operands_one arguments
      refine sound.single (type := .bool) (!env a) _ _ ?_ ?_
      · exact ⟨_, storeOf_number env a, rfl⟩
      · intro _ absent
        cases absent
  | .seqLength element size, arguments, _ => by
      obtain ⟨a, rfl⟩ := operands_one arguments
      refine sound.single (type := .nat) (Ty.elements size (env a)).length _ _ ?_ ?_
      · exact ⟨element, size, env a, storeOf_number env a, rfl⟩
      intro found same
      cases size with
      | none =>
          cases Option.some.inj same
          exact ⟨_, rfl, Nat.zero_le _, fun _ absent => nomatch absent⟩
      | some count =>
          cases Option.some.inj same
          have counted : (Ty.elements (some count) (env a)).length = count := (env a).property
          exact ⟨_, rfl, Nat.le_of_eq counted.symm, fun hi at_ => by
            cases Option.some.inj at_
            exact Nat.le_of_eq counted⟩
  | .finToNat bound, arguments, _ => by
      obtain ⟨a, rfl⟩ := operands_one arguments
      refine sound.single (type := .nat) (env a).val _ _ ?_ ?_
      · exact ⟨bound, env a, storeOf_number env a, rfl⟩
      intro found same
      cases Option.some.inj same
      exact ⟨_, rfl, Nat.zero_le _, fun hi at_ => by
        cases Option.some.inj at_
        have := (env a).isLt
        omega⟩
  | .seqAt element size, arguments, justified => by
      obtain ⟨a, b, rfl⟩ := operands_two arguments
      refine yields_defined ?_ fun results _ => sound.afterAny results
      refine at_defined (Ty.elements size (env a)) (env b) ?_
      cases size with
      | some count =>
          obtain ⟨end_, high, less⟩ := below_lt justified
          have most := sound.2.le_hi (storeOf_number env b) high
          have counted : (Ty.elements (some count) (env a)).length = count := (env a).property
          omega
      | none =>
          obtain ⟨level, member, less⟩ := List.any_eq_true.mp justified
          exact sound.2.knownLt (storeOf_number env b)
            (sound.length_at a (Facts.shape_of_mem_lengths member)) less
  | .seqSlice element size result, arguments, justified => by
      obtain ⟨a, b, c, rfl⟩ := operands_three arguments
      refine yields_defined ?_ fun results _ => sound.afterAny results
      simp only [Builtin.justified, Scope.numbers, Bool.and_eq_true] at justified
      obtain ⟨⟨ordered, ends⟩, sized⟩ := justified
      have least := sound.2.knownLe (storeOf_number env b) (storeOf_number env c) ordered
      refine slice_defined (Ty.elements size (env a)) (env b) (env c) result least ?_ ?_
      · cases size with
        | some count =>
            obtain ⟨end_, high, most⟩ := within_le ends
            have top := sound.2.le_hi (storeOf_number env c) high
            have counted : (Ty.elements (some count) (env a)).length = count := (env a).property
            omega
        | none =>
            obtain ⟨level, member, most⟩ := List.any_eq_true.mp ends
            exact sound.2.knownLe (storeOf_number env c)
              (sound.length_at a (Facts.shape_of_mem_lengths member)) most
      · intro count same
        subst same
        simp only [Bool.or_eq_true] at sized
        rcases sized with points | sum
        · split at points
          · rename_i start stop first last
            simp only [Bool.and_eq_true, decide_eq_true_eq] at points
            have one := sound.2.point_eq (storeOf_number env b) points.1.1
            have two := sound.2.point_eq (storeOf_number env c) points.1.2
            omega
          · cases points
        · have shaped := sound.2.shapes _ _ (storeOf_number env c)
          split at sum
          · rename_i left right shape
            rw [shape] at shaped
            obtain ⟨x, y, first, second, value⟩ := shaped
            have total := entry_nat value
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at sum
            rcases sum with ⟨rfl, point⟩ | ⟨rfl, point⟩
            · have := store_nat (storeOf_number env b) first
              have := sound.2.point_eq second point
              omega
            · have := store_nat (storeOf_number env b) second
              have := sound.2.point_eq first point
              omega
          · cases sum
  | .seqSized element size, arguments, justified => by
      obtain ⟨a, rfl⟩ := operands_one arguments
      refine yields_defined ?_ fun results _ => sound.afterAny results
      obtain ⟨level, member, point⟩ := List.any_eq_true.mp justified
      exact sized_defined (Ty.elements none (env a)) size
        (sound.2.point_eq (sound.length_at a (Facts.shape_of_mem_lengths member)) point)
  | .natBelow bound, arguments, justified => by
      obtain ⟨a, rfl⟩ := operands_one arguments
      refine yields_defined ?_ fun results _ => sound.afterAny results
      obtain ⟨end_, high, less⟩ := below_lt justified
      exact below_defined (env a) bound
        (Nat.lt_of_le_of_lt (sound.2.le_hi (storeOf_number env a) high) less)
  | .boolEqual, arguments, _ =>
      yields_defined (Builtin.eval_isSome _ rfl _) fun results _ => sound.afterAny results
  | .seqConcat .., arguments, _ =>
      yields_defined (Builtin.eval_isSome _ rfl _) fun results _ => sound.afterAny results
  | .seqFill .., arguments, _ =>
      yields_defined (Builtin.eval_isSome _ rfl _) fun results _ => sound.afterAny results
  | .seqMake .., arguments, _ =>
      yields_defined (Builtin.eval_isSome _ rfl _) fun results _ => sound.afterAny results
  | .seqUnsized .., arguments, _ =>
      yields_defined (Builtin.eval_isSome _ rfl _) fun results _ => sound.afterAny results
  | .finWiden .., arguments, _ =>
      yields_defined (Builtin.eval_isSome _ rfl _) fun results _ => sound.afterAny results
  | .tupleMake .., arguments, _ =>
      yields_defined (Builtin.eval_isSome _ rfl _) fun results _ => sound.afterAny results
  | .tupleGet .., arguments, _ =>
      yields_defined (Builtin.eval_isSome _ rfl _) fun results _ => sound.afterAny results
  | .recordMake .., arguments, _ =>
      yields_defined (Builtin.eval_isSome _ rfl _) fun results _ => sound.afterAny results
  | .recordGet .., arguments, _ =>
      yields_defined (Builtin.eval_isSome _ rfl _) fun results _ => sound.afterAny results
  | .variantMake .., arguments, _ =>
      yields_defined (Builtin.eval_isSome _ rfl _) fun results _ => sound.afterAny results

end Builtin

/-! ## Operations and regions -/

section Local

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

/-- Every function of a table never stops `undefined`, on any arguments. -/
@[expose] def DefinedTable (table : FunctionTable model functions) : Prop :=
  ∀ {header : FunctionHeader} (callee : Var functions header)
    (arguments : Values model.Value header.inputs),
    NeverStops .undefined (table.get callee arguments)

/-- Each nested region, on inputs of which the facts of its number hold, never stops
`undefined` and returns what the check says it returns. -/
def RegionsSound (factsOf : Nat → Facts) : (number : Nat) → List Outcome →
    {signatures : List (List Ty × List Ty)} →
      Values (RegionFunction model.Value (Effects model)) signatures → Prop
  | _, outcomes, _, .nil => outcomes = []
  | number, outcomes, _, .cons (ty := signature) body rest =>
      ∃ outcome others, outcomes = outcome :: others ∧
        (∀ arguments : Values model.Value signature.1,
          (factsOf number).Sound (Environment.ofValues arguments) →
            Yields (outcome.Holds (storeOf (Environment.ofValues arguments))) (body arguments)) ∧
        RegionsSound factsOf (number + 1) others rest

/-- Nested regions that are sound from the facts of their numbers with their inputs in
scope are sound from the facts of their numbers: inputs on which a region runs exist. -/
theorem RegionsSound.entered {factsOf : Nat → Facts} {inputsOf : Nat → List Ty} :
    ∀ {signatures : List (List Ty × List Ty)} (number : Nat) (outcomes : List Outcome)
      (regions : Values (RegionFunction model.Value (Effects model)) signatures),
      (∀ (index : Nat) (signature : List Ty × List Ty), signatures[index]? = some signature →
        inputsOf (number + index) = signature.1) →
      RegionsSound (fun number => (factsOf number).inScope (inputsOf number)) number outcomes
        regions →
      RegionsSound factsOf number outcomes regions
  | _, _, _, .nil, _, sound => sound
  | _, number, _, .cons (ty := signature) body rest, inputs, sound => by
      obtain ⟨outcome, others, same, here, there⟩ := sound
      refine ⟨outcome, others, same, fun arguments holds => ?_, ?_⟩
      · have first := inputs 0 signature rfl
        rw [Nat.add_zero] at first
        have entered : ((factsOf number).inScope (inputsOf number)).Sound
            (Environment.ofValues arguments) := by
          rw [first]
          exact holds.inScope arguments
        exact here arguments entered
      · refine RegionsSound.entered (number + 1) others rest (fun index found at_ => ?_) there
        have later := inputs (index + 1) found at_
        rw [← Nat.add_assoc, Nat.add_right_comm] at later
        exact later

/-- The inputs of the nested region with a number are the inputs of its signature. -/
theorem LocalOp.regionInputs_at (op : LocalOp operations functions deployed) (index : Nat)
    (signature : List Ty × List Ty) (found : op.regions[index]? = some signature) :
    op.regionInputs (0 + index) = signature.1 := by
  rw [Nat.zero_add]
  show (match op.regions[index]? with
    | some signature => signature.1
    | none => []) = _
  rw [found]

theorem operands_cons {Γ : List Ty} {type : Ty} {types : List Ty}
    (operands : Operands Γ (type :: types)) : ∃ first rest, operands = .cons first rest := by
  cases operands with
  | cons first rest => exact ⟨first, rest, rfl⟩

theorem Facts.Sound.one {Γ : List Ty} {env : Environment model.Value Γ} {facts : Facts}
    (sound : facts.Sound env) {type : Ty} (values : Values model.Value [type]) (shape : Shape)
    (shaped : shape.Holds (storeOf env) ⟨type, values.get .here⟩) :
    (facts.after [shape] []).Sound (Environment.bindAll env values) := by
  cases values with
  | cons value rest =>
      cases rest with
      | nil => exact sound.single value shape none shaped fun _ absent => nomatch absent

theorem Facts.Sound.orderWhen {Γ : List Ty} {env : Environment model.Value Γ} {facts : Facts}
    (sound : facts.Sound env) {captured : Option Nat} {x : Nat}
    (first : storeOf env 0 = some ⟨.nat, x⟩)
    (holds : ∀ inner, captured = some inner →
      ∃ y : Nat, storeOf env inner = some ⟨.nat, y⟩ ∧ x < y) :
    (facts.orderWhen captured).Sound env := by
  cases captured with
  | none => exact sound
  | some inner =>
      obtain ⟨y, second, less⟩ := holds inner rfl
      exact sound.order first second (Nat.le_of_lt less) fun _ => less

/-- The domain row is true on the operands of the application when a value that is the
domain row applied at their levels is true. -/
theorem domain_true {row : Nat} {inputs others : List Ty} {values : Values model.Value inputs}
    {values' : Values model.Value others}
    (same : (⟨others, values'⟩ : (types : List Ty) × Values model.Value types) = ⟨inputs, values⟩)
    (holds : (⟨.bool, true⟩ : Sigma model.Value) =
      ⟨.bool, (model.pure ⟨row, others, [.bool]⟩ allPopulated_bool values').get .here⟩) :
    (model.pure ⟨row, inputs, [.bool]⟩ allPopulated_bool values).get .here = true := by
  cases same
  exact (entry_eq holds).symm

/-- A `match` over regions that never stop `undefined` never does, and returns what one
of them returns. -/
theorem matchProcess_yields {captures outputs : List Ty} (captured : Values model.Value captures)
    (factsOf : Nat → Facts)
    (enters : ∀ (number : Nat) {payload : Ty} (value : model.Value payload),
      (factsOf number).Sound (Environment.ofValues (Values.cons value captured))) :
    ∀ (alternatives : List Ty)
      (regions : Values (RegionFunction model.Value (Effects model))
        (alternatives.map fun payload => (payload :: captures, outputs)))
      (value : Ty.Variant model.Carrier alternatives) (number : Nat) (outcomes : List Outcome),
      RegionsSound factsOf number outcomes regions →
        Yields (Outcome.joinAll outcomes).Bounds
          (matchProcess model captures outputs alternatives regions value captured)
  | [], _, value, _, _, _ => nomatch value
  | _ :: _, .cons body rest, .inl payload, number, outcomes, sound => by
      obtain ⟨outcome, others, rfl, here, _⟩ := sound
      exact (here (.cons payload captured) (enters number payload)).weaken
        fun values holds => holds.1.join_left _
  | _ :: alternatives, .cons body rest, .inr later, number, outcomes, sound => by
      obtain ⟨outcome, others, rfl, _, there⟩ := sound
      exact (matchProcess_yields captured factsOf enters alternatives rest later (number + 1)
        others there).weaken fun values holds => holds.join_right _

theorem none_ne_some {α : Type} {value : α} (same : (none : Option α) = some value) : False :=
  nomatch same

theorem storeOf_grows {Γ added : List Ty} (env : Environment model.Value Γ)
    (values : Values model.Value added) (level : Nat) (entry : Sigma model.Value)
    (found : storeOf env level = some entry) :
    storeOf (Environment.bindAll env values) level = some entry := by
  rw [storeOf_bindAll]
  by_cases earlier : level < Γ.length
  · simp only [earlier, ↓reduceIte]
    exact found
  · rw [storeOf_none env (Nat.not_lt.mp earlier)] at found
    cases found

theorem entryOf_append_left : ∀ {first rest : List Ty} (values : Values model.Value first)
    (others : Values model.Value rest) (index : Nat), index < first.length →
      entryOf (values.append others) index = entryOf values index
  | _, _, .nil, _, _, inside => absurd inside (Nat.not_lt_zero _)
  | _, _, .cons _ _, _, 0, _ => rfl
  | _, _, .cons _ values, others, index + 1, inside =>
      entryOf_append_left values others index (Nat.lt_of_succ_lt_succ inside)

theorem entryOf_split_left : ∀ (first : List Ty) {rest : List Ty}
    (values : Values model.Value (first ++ rest)) (index : Nat), index < first.length →
      entryOf (values.split first).1 index = entryOf values index
  | [], _, _, _, inside => absurd inside (Nat.not_lt_zero _)
  | _ :: _, _, .cons _ _, 0, _ => rfl
  | _ :: first, _, .cons _ values, index + 1, inside =>
      entryOf_split_left first values index (Nat.lt_of_succ_lt_succ inside)

theorem entryOf_split_right : ∀ (first : List Ty) {rest : List Ty}
    (values : Values model.Value (first ++ rest)) (index : Nat),
      entryOf (values.split first).2 index = entryOf values (first.length + index)
  | [], _, _, index => by
      show _ = entryOf _ (0 + index)
      rw [Nat.zero_add]
      rfl
  | _ :: first, _, .cons _ values, index => by
      rw [List.length_cons, Nat.add_right_comm]
      exact entryOf_split_right first values index

theorem entryOf_nat {types : List Ty} (values : Values model.Value types) {index : Nat}
    (typed : types[index]? = some .nat) :
    ∃ value : Nat, entryOf values index = some ⟨.nat, value⟩ :=
  entryOf_type values index .nat typed

theorem Shape.holds_other {store : Store model} (added : List Ty) (index : Nat)
    (entry : Sigma model.Value) :
    ((added.map fun _ => Shape.other).getD index Shape.other).Holds store entry := by
  have other : (added.map fun _ => Shape.other).getD index Shape.other = Shape.other := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases added[index]? <;> rfl
  rw [other]
  trivial

/-! ## Loops that carry a sum -/

theorem findStep_mem {source : Nat} {interval : Interval} : ∀ (steps : List (Nat × Interval)),
    findStep source steps = some interval → (source, interval) ∈ steps
  | [], found => nomatch found
  | step :: rest, found => by
      unfold findStep at found
      split at found
      · rename_i same
        cases Option.some.inj found
        rw [← same]
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (findStep_mem rest found)

theorem mem_sumBounds {facts : Facts} {count : Interval} {bound : Bound} :
    ∀ (level position : Nat) (types : List Ty) (inits : List Nat) (returned : List Returned),
      bound ∈ sumBounds facts count level position types inits returned →
        ∃ (index init : Nat) (found : Returned) (step : Interval),
          bound.level = level + index ∧ types[index]? = some .nat ∧
            inits[index]? = some init ∧ returned[index]? = some found ∧
            findStep (position + index + 1) found.steps = some step ∧
            bound.lo = facts.lo init + count.lo * step.lo ∧
            bound.hi = plusTimes (facts.hi init) count.hi step.hi
  | _, _, [], _, _, member => by
      unfold sumBounds at member
      cases member
  | _, _, _ :: _, [], _, member => by
      unfold sumBounds at member
      cases member
  | _, _, _ :: _, _ :: _, [], member => by
      unfold sumBounds at member
      cases member
  | level, position, type :: types, init :: inits, item :: rest, member => by
      have later : bound ∈ sumBounds facts count (level + 1) (position + 1) types inits rest →
          ∃ (index init' : Nat) (found : Returned) (step : Interval),
            bound.level = level + index ∧ (type :: types)[index]? = some .nat ∧
              (init :: inits)[index]? = some init' ∧ (item :: rest)[index]? = some found ∧
              findStep (position + index + 1) found.steps = some step ∧
              bound.lo = facts.lo init' + count.lo * step.lo ∧
              bound.hi = plusTimes (facts.hi init') count.hi step.hi := fun inside => by
        obtain ⟨index, other, found, step, at_, typed, initial, returnedAt, stepped, low, high⟩ :=
          mem_sumBounds (level + 1) (position + 1) types inits rest inside
        have same : position + (index + 1) + 1 = position + 1 + index + 1 := by omega
        exact ⟨index + 1, other, found, step, by omega, typed, initial, returnedAt,
          by rw [same]; exact stepped, low, high⟩
      unfold sumBounds at member
      split at member
      · rename_i step stepped
        rcases List.mem_cons.mp member with rfl | inside
        · exact ⟨0, init, item, step, rfl, rfl, rfl, rfl, stepped, rfl, rfl⟩
        · exact later inside
      · exact later member

/-- After `count` iterations, a carried natural whose region returns it plus a term is its
first value plus `count` terms. -/
def SumInvariant (carried : List Ty) (returned : List Returned)
    (initial : Values model.Value carried) (count : Nat) (state : Values model.Value carried) :
    Prop :=
  ∀ (position : Nat) (found : Returned) (step : Interval), carried[position]? = some .nat →
    returned[position]? = some found → findStep (position + 1) found.steps = some step →
      ∃ first value : Nat, entryOf initial position = some ⟨.nat, first⟩ ∧
        entryOf state position = some ⟨.nat, value⟩ ∧ first + count * step.lo ≤ value ∧
          ∀ hi, step.hi = some hi → value ≤ first + count * hi

theorem SumInvariant.start (carried : List Ty) (returned : List Returned)
    (initial : Values model.Value carried) : SumInvariant carried returned initial 0 initial := by
  intro position found step typed _ _
  obtain ⟨value, at_⟩ := entryOf_nat initial typed
  exact ⟨value, value, at_, at_, by omega, fun hi _ => by omega⟩

theorem SumInvariant.step {carried collected captures : List Ty} {returned : List Returned}
    {initial state : Values model.Value carried} {count iteration : Nat}
    (holds : SumInvariant carried (returned.drop collected.length) initial count state)
    (captured : Values model.Value captures)
    (produced : Values model.Value (collected ++ carried))
    (steps : StepsHold
      (entryOf (Values.cons (Value := model.Value) (ty := .nat) iteration (state.append captured)))
      returned produced) :
    SumInvariant carried (returned.drop collected.length) initial (count + 1)
      (produced.split collected).2 := by
  intro position found step typed at_ stepped
  obtain ⟨first, value, start, current, low, high⟩ := holds position found step typed at_ stepped
  have inside : position < carried.length := (List.getElem?_eq_some_iff.mp typed).1
  have typed' : (collected ++ carried)[collected.length + position]? = some .nat := by
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact typed
  obtain ⟨next, here⟩ := entryOf_nat produced typed'
  rw [List.getElem?_drop] at at_
  have source : entryOf (Values.cons (Value := model.Value) (ty := .nat) iteration
      (state.append captured)) (position + 1) = some ⟨.nat, value⟩ := by
    show entryOf (state.append captured) position = _
    rw [entryOf_append_left _ _ _ inside]
    exact current
  obtain ⟨term, sum, least', most'⟩ :=
    steps (collected.length + position) found _ at_ here _ (findStep_mem _ stepped) value source
  have least : step.lo ≤ term := least'
  have most : ∀ hi, step.hi = some hi → term ≤ hi := most'
  refine ⟨first, value + term, start, ?_, ?_, ?_⟩
  · rw [entryOf_split_right collected produced position, here, sum]
  · rw [Nat.add_one_mul]
    omega
  · intro hi top
    have := high hi top
    have := most hi top
    rw [Nat.add_one_mul]
    omega

/-- The bounds of the carried results of a loop that are sums contain them; the carried
results follow the collected ones. -/
theorem sum_bounded {Γ : List Ty} {env : Environment model.Value Γ} {facts : Facts}
    (sound : facts.Sound env) {carried rest : List Ty} {inits : List Nat}
    {returned : List Returned} {count : Interval} {iterations : Nat}
    {initial final : Values model.Value carried} (others : Values model.Value rest)
    {skipped : Nat} (before : rest.length = skipped)
    (reads : ∀ index init, inits[index]? = some init → index < carried.length →
      entryOf initial index = storeOf env init)
    (invariant : SumInvariant carried returned initial iterations final)
    (least : count.lo ≤ iterations) (most : ∀ hi, count.hi = some hi → iterations ≤ hi) :
    ∀ bound ∈ sumBounds facts count (facts.depth + skipped) 0 carried inits returned,
      ∃ (index value : Nat), bound.level = Γ.length + index ∧
        entryOf (others.append final) index = some ⟨.nat, value⟩ ∧ bound.lo ≤ value ∧
          ∀ hi, bound.hi = some hi → value ≤ hi := by
  intro bound member
  obtain ⟨index, init, found, step, level, typed, initialAt, returnedAt, stepped, low, high⟩ :=
    mem_sumBounds _ _ _ _ _ member
  rw [Nat.zero_add] at stepped
  have inside : index < carried.length := (List.getElem?_eq_some_iff.mp typed).1
  obtain ⟨first, value, start, current, lower, upper⟩ :=
    invariant index found step typed returnedAt stepped
  have source : storeOf env init = some ⟨.nat, first⟩ := by
    rw [← reads index init initialAt inside]
    exact start
  refine ⟨rest.length + index, value, by rw [level, sound.1, before, Nat.add_assoc], ?_, ?_, ?_⟩
  · rw [entryOf_append]
    exact current
  · rw [low]
    have one := sound.2.lo_le source
    have two := Nat.mul_le_mul_right step.lo least
    omega
  · intro hi top
    rw [high] at top
    cases first' : facts.hi init with
    | none => rw [first'] at top; cases top
    | some a =>
        cases second : count.hi with
        | none => rw [first', second] at top; cases top
        | some c =>
            cases third : step.hi with
            | none => rw [first', second, third] at top; cases top
            | some h =>
                rw [first', second, third] at top
                cases Option.some.inj top
                have one := sound.2.le_hi source first'
                have two := upper h third
                have three := Nat.mul_le_mul_right h (most c second)
                omega

/-! ## An `if` that is a conjunction or a disjunction -/

section Literal

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

/-- A region that is one `bool` literal and the return of its value returns the literal. -/
theorem literalBool_denote {table : FunctionTable model functions} :
    ∀ {Γ out : List Ty} (region : Region (LocalDialect operations functions deployed) Γ out)
      (value : Bool), literalBool region = some value → ∀ (env : Environment model.Value Γ),
        ∃ values, region.denote (localMeaning model table) env = .done values ∧
          entryOf values 0 = some ⟨.bool, value⟩
  | _, _, .letOp (.literal (.bool flag)) _ _ (.ret (.cons (ty := type) reference .nil)), value,
      found, env => by
      have reduced : cond (decide (reference.index = 0)) (some flag) none = some value := found
      have zero : reference.index = 0 := by
        apply Classical.byContradiction
        intro other
        rw [decide_eq_false other] at reduced
        cases reduced
      rw [decide_eq_true zero] at reduced
      cases Option.some.inj reduced
      obtain ⟨index, valid⟩ := reference
      have first : index = 0 := zero
      subst first
      have typed : Ty.bool = type := Option.some.inj valid
      subst typed
      exact ⟨_, rfl, rfl⟩
  | _, _, .letOp (.literal (.bool _)) _ _ (.ret .nil), _, found, _ => (none_ne_some found).elim
  | _, _, .letOp (.literal (.bool _)) _ _ (.ret (.cons _ (.cons _ _))), _, found, _ =>
      (none_ne_some found).elim
  | _, _, .letOp (.literal (.bool _)) _ _ (.stop _), _, found, _ => (none_ne_some found).elim
  | _, _, .letOp (.literal (.bool _)) _ _ (.letOp ..), _, found, _ => (none_ne_some found).elim
  | _, _, .letOp (.literal (.bool _)) _ _ (.bind ..), _, found, _ => (none_ne_some found).elim
  | _, _, .letOp (.literal (.nat _)) .., _, found, _ => (none_ne_some found).elim
  | _, _, .letOp (.literal (.fin ..)) .., _, found, _ => (none_ne_some found).elim
  | _, _, .letOp (.literal (.nominal ..)) .., _, found, _ => (none_ne_some found).elim
  | _, _, .letOp (.literal (.bytes _)) .., _, found, _ => (none_ne_some found).elim
  | _, _, .letOp (.op ..) .., _, found, _ => (none_ne_some found).elim
  | _, _, .letOp (.call ..) .., _, found, _ => (none_ne_some found).elim
  | _, _, .letOp (.conditional ..) .., _, found, _ => (none_ne_some found).elim
  | _, _, .letOp (.match ..) .., _, found, _ => (none_ne_some found).elim
  | _, _, .letOp (.loop ..) .., _, found, _ => (none_ne_some found).elim
  | _, _, .letOp (.guard _) .., _, found, _ => (none_ne_some found).elim
  | _, _, .letOp (.builtin _) .., _, found, _ => (none_ne_some found).elim
  | _, _, .ret _, _, found, _ => (none_ne_some found).elim
  | _, _, .stop _, _, found, _ => (none_ne_some found).elim
  | _, _, .bind .., _, found, _ => (none_ne_some found).elim

/-- What an `if` that is a conjunction or a disjunction returns has the shape that says
so: its first result is true only when the condition is, or false only when it is. -/
theorem LocalOp.branch_returns {table : FunctionTable model functions} {Γ : List Ty}
    {env : Environment model.Value Γ} :
    ∀ (op : LocalOp operations functions deployed) (arguments : Operands Γ op.arguments)
      (bodies : Regions (LocalDialect operations functions deployed) op.regions),
      Returns (fun results =>
          ∀ shape, op.branchShape (Scope.numbers Γ.length arguments) bodies = some shape →
            ∀ entry, entryOf results 0 = some entry → shape.Holds (storeOf env) entry)
        (localOperation model table op (Operands.eval env arguments)
          (bodies.denote (localMeaning model table)))
  | .conditional captures outputs, arguments, .cons onTrue (.cons onFalse .nil) => by
      obtain ⟨condition, rest, rfl⟩ := operands_cons arguments
      have found := storeOf_number env condition
      show Returns _ (cond (env condition)
        (onTrue.denote (localMeaning model table) (Environment.ofValues (Operands.eval env rest)))
        (onFalse.denote (localMeaning model table) (Environment.ofValues (Operands.eval env rest))))
      by_cases conjunction : literalBool onFalse = some false
      · have shaped : LocalOp.branchShape (.conditional captures outputs)
            (Scope.numbers Γ.length (Values.cons condition rest))
            (.cons onTrue (.cons onFalse .nil)) =
              some (.conjunct (Scope.number Γ.length condition)) := by
          show (if _ then _ else _) = _
          simp only [conjunction, ↓reduceIte]
        cases truth : env condition with
        | true =>
            rw [truth] at found
            exact Returns.of_forall (fun results shape same entry _ => by
              rw [shaped] at same
              cases Option.some.inj same
              exact ⟨true, found, fun _ => rfl⟩) _
        | false =>
            rw [truth] at found
            obtain ⟨values, run, first⟩ := literalBool_denote (table := table) onFalse false
              conjunction (Environment.ofValues (Operands.eval env rest))
            show Returns _ (onFalse.denote (localMeaning model table)
              (Environment.ofValues (Operands.eval env rest)))
            rw [run]
            intro shape same entry at_
            rw [shaped] at same
            cases Option.some.inj same
            rw [first] at at_
            cases Option.some.inj at_
            exact ⟨false, found, fun impossible => entry_eq impossible⟩
      · by_cases disjunction : literalBool onTrue = some true
        · have shaped : LocalOp.branchShape (.conditional captures outputs)
              (Scope.numbers Γ.length (Values.cons condition rest))
              (.cons onTrue (.cons onFalse .nil)) =
                some (.disjunct (Scope.number Γ.length condition)) := by
            show (if _ then _ else _) = _
            simp only [conjunction, disjunction, ↓reduceIte]
          cases truth : env condition with
          | false =>
              rw [truth] at found
              exact Returns.of_forall (fun results shape same entry _ => by
                rw [shaped] at same
                cases Option.some.inj same
                exact ⟨false, found, fun _ => rfl⟩) _
          | true =>
              rw [truth] at found
              obtain ⟨values, run, first⟩ := literalBool_denote (table := table) onTrue true
                disjunction (Environment.ofValues (Operands.eval env rest))
              show Returns _ (onTrue.denote (localMeaning model table)
                (Environment.ofValues (Operands.eval env rest)))
              rw [run]
              intro shape same entry at_
              rw [shaped] at same
              cases Option.some.inj same
              rw [first] at at_
              cases Option.some.inj at_
              exact ⟨true, found, fun impossible => entry_eq impossible⟩
        · have shaped : LocalOp.branchShape (.conditional captures outputs)
              (Scope.numbers Γ.length (Values.cons condition rest))
              (.cons onTrue (.cons onFalse .nil)) = none := by
            show (if _ then _ else _) = _
            simp only [conjunction, disjunction, ↓reduceIte]
          exact Returns.of_forall (fun results shape same => by
            rw [shaped] at same
            cases same) _
  | .op .., _, _ => Returns.of_forall (fun _ _ same => (none_ne_some same).elim) _
  | .call .., _, _ => Returns.of_forall (fun _ _ same => (none_ne_some same).elim) _
  | .match .., _, _ => Returns.of_forall (fun _ _ same => (none_ne_some same).elim) _
  | .loop .., _, _ => Returns.of_forall (fun _ _ same => (none_ne_some same).elim) _
  | .guard _, _, _ => Returns.of_forall (fun _ _ same => (none_ne_some same).elim) _
  | .literal _, _, _ => Returns.of_forall (fun _ _ same => (none_ne_some same).elim) _
  | .builtin _, _, _ => Returns.of_forall (fun _ _ same => (none_ne_some same).elim) _

end Literal

/-- A justified instruction over regions and functions that never stop `undefined` never
does, and the facts after it hold of the environment that binds its results. -/
theorem LocalOp.sound (laws : model.DomainLaws operations) {table : FunctionTable model functions}
    (defined : DefinedTable table) {Γ : List Ty} {env : Environment model.Value Γ} {facts : Facts}
    (sound : facts.Sound env) :
    ∀ (op : LocalOp operations functions deployed) (arguments : Operands Γ op.arguments)
      (regions : Values (RegionFunction model.Value (Effects model)) op.regions)
      (outcomes : List Outcome),
      op.unjustified facts (Scope.numbers Γ.length arguments) = none →
      RegionsSound (op.regionEntry facts (Scope.numbers Γ.length arguments)) 0 outcomes regions →
        Yields (fun results =>
            (op.resultFacts facts (Scope.numbers Γ.length arguments) outcomes).Sound
              (Environment.bindAll env results))
          (localOperation model table op (Operands.eval env arguments) regions)
  | .op (inputs := inputs) (outputs := outputs) (kind := kind) row applies, arguments, _,
      outcomes, justified, _ => by
      cases kind with
      | pure =>
          show (facts.after (LocalOp.resultShapes (functions := functions) (deployed := deployed) (.op row applies) _) []).Sound
            (Environment.bindAll env (model.pure (.of row) applies (Operands.eval env arguments)))
          by_cases single : outputs = [.bool]
          · subst single
            have shapes : LocalOp.resultShapes (functions := functions) (deployed := deployed) (.op row applies)
                (Scope.numbers Γ.length arguments) =
                  [Shape.domain row.index (Scope.numbers Γ.length arguments)] := by
              show cond (decide ([Ty.bool] = [Ty.bool])) _ _ = _
              rw [decide_eq_true rfl]
              rfl
            rw [shapes]
            exact sound.one _ _ ⟨inputs, Operands.eval env arguments, reads_eval env arguments, rfl⟩
          · have shapes : LocalOp.resultShapes (functions := functions) (deployed := deployed) (.op row applies)
                (Scope.numbers Γ.length arguments) = outputs.map fun _ => Shape.other := by
              show cond (decide (outputs = [Ty.bool])) _ _ = _
              rw [decide_eq_false single]
              rfl
            rw [shapes]
            exact sound.afterAny _
      | restricted domain =>
          cases domain with
          | none =>
              have reduced : (some Requirement.noDomain : Option Requirement) = none := justified
              cases reduced
          | some domain =>
              have reduced : cond (facts.known.any fun condition =>
                  decide (facts.shape condition =
                    Shape.domain domain (Scope.numbers Γ.length arguments)))
                  none (some Requirement.domain) = none := justified
              cases found : (facts.known.any fun condition =>
                  decide (facts.shape condition =
                    Shape.domain domain (Scope.numbers Γ.length arguments))) with
              | false =>
                  rw [found] at reduced
                  cases reduced
              | true =>
                  obtain ⟨condition, member, shaped⟩ := List.any_eq_true.mp found
                  have true_ := sound.2.known condition member
                  have holds := sound.2.shapes condition _ true_
                  rw [of_decide_eq_true shaped] at holds
                  obtain ⟨others, values', reads, value⟩ := holds
                  have same := Reads.unique reads (reads_eval env arguments)
                  have defined : (model.restricted (.of row) (Operands.eval env arguments)).isSome =
                      true :=
                    (laws row.index domain inputs outputs row.valid _).trans (domain_true same value)
                  exact yields_defined defined fun results _ => sound.afterAny results
      | sampling => exact absurd applies Bool.false_ne_true
  | .call callee _, arguments, _, outcomes, _, _ =>
      (defined callee _).yields.weaken fun results _ => sound.afterAny results
  | .conditional captures outputs, arguments, .cons onTrue (.cons onFalse .nil), outcomes, _,
      nested => by
      obtain ⟨condition, rest, rfl⟩ := operands_cons arguments
      obtain ⟨first, others, rfl, whenTrue, more⟩ := nested
      obtain ⟨second, others, rfl, whenFalse, last⟩ := more
      have empty : others = [] := last
      subst empty
      have reads := reads_eval env rest
      have found := storeOf_number env condition
      show Yields _ (cond (env condition) (onTrue (Operands.eval env rest))
        (onFalse (Operands.eval env rest)))
      cases truth : env condition with
      | true =>
          rw [truth] at found
          exact (whenTrue _ ((sound.assume facts.depth found).enter Values.nil reads)).weaken
            fun results holds => sound.afterOutcome results (holds.1.join_left _)
      | false =>
          rw [truth] at found
          exact (whenFalse _ ((sound.assume facts.depth found).enter Values.nil reads)).weaken
            fun results holds =>
              sound.afterOutcome results ((holds.1.join_left none).join_right first)
  | .match declaration alternatives captures outputs, arguments, regions, outcomes, _, nested => by
      obtain ⟨value, rest, rfl⟩ := operands_cons arguments
      have reads := reads_eval env rest
      exact (matchProcess_yields (Operands.eval env rest) _
        (fun number payload value => sound.enter (Values.cons value Values.nil) reads)
        alternatives regions (env value) 0 outcomes nested).weaken
          fun results holds => sound.afterOutcome results holds
  | .loop (.static count) carried collected captures, arguments, .cons body .nil, outcomes, _,
      nested => by
      obtain ⟨outcome, others, rfl, inner, last⟩ := nested
      have empty : others = [] := last
      subst empty
      have reads := reads_eval env arguments
      have captured := Reads.split carried reads
      refine Yields.bind (loopIterations_invariant
        (SumInvariant carried ((Outcome.joinAll [outcome]).returned.drop collected.length)
          ((Operands.eval env arguments).split carried).1) ?_ count 0 _ _
        (Nat.le_of_eq (Nat.zero_add _)) (SumInvariant.start _ _ _)) ?_
      · intro iteration state below invariant
        have live : decide (count = 0) = false := decide_eq_false (by omega)
        refine (inner _ ?_).weaken fun produced holds =>
          invariant.step (iteration := iteration) ((Operands.eval env arguments).split carried).2
            produced ?_
        · have target : LocalOp.regionEntry facts
              (.loop (.static count) carried collected captures :
                LocalOp operations functions deployed)
              (Scope.numbers Γ.length arguments) 0 =
                (facts.enter (List.replicate (carried.length + 1) none ++
                  ((Scope.numbers Γ.length arguments).drop carried.length).map some)).bound 0 0
                    (some (count - 1)) := by
            show cond (decide (count = 0)) _ _ = _
            rw [live]
            rfl
          rw [target]
          refine (sound.enter (Values.cons (Value := model.Value) (ty := .nat) iteration state)
            captured).bound (value := iteration) ?_ (Nat.zero_le _) ?_
          · rw [storeOf_ofValues]
            rfl
          · intro end_ at_
            cases Option.some.inj at_
            omega
        · have same : storeOf (Environment.ofValues (Values.cons (Value := model.Value)
              (ty := .nat) iteration (state.append ((Operands.eval env arguments).split carried).2))) =
                entryOf (Values.cons (Value := model.Value) (ty := .nat) iteration
                  (state.append ((Operands.eval env arguments).split carried).2)) :=
            funext fun level => storeOf_ofValues _ level
          rw [Outcome.joinAll_single, ← same]
          exact holds.2
      · intro final invariant
        rw [Nat.zero_add] at invariant
        exact sound.after _ _ _ (List.length_map _) (fun index entry _ => Shape.holds_other _ index entry)
          (sum_bounded sound _ (List.length_map _)
            (fun index init found inside => by
              rw [entryOf_split_left carried _ index inside]
              exact reads.entry index init found)
            invariant (Nat.le_refl _) fun hi top => by
              cases Option.some.inj top
              exact Nat.le_refl _)
  | .loop (.runtime maximum) carried collected captures, arguments, .cons body .nil, outcomes,
      justified, nested => by
      obtain ⟨counter, rest, rfl⟩ := operands_cons arguments
      obtain ⟨outcome, others, rfl, inner, last⟩ := nested
      have empty : others = [] := last
      subst empty
      have reads := reads_eval env rest
      have captured := Reads.split carried reads
      have counted := storeOf_number env counter
      show Yields _ (loopProcess model maximum carried collected captures body (env counter)
        ((Operands.eval env rest).split carried).1 ((Operands.eval env rest).split carried).2)
      unfold loopProcess
      cases inside : withinMaximum (env counter) maximum with
      | false =>
          -- the count is known to be within the maximum
          cases maximum with
          | none => cases inside
          | some limit =>
              have known : within (facts.hi (Scope.number Γ.length counter)) limit = true := by
                have checked : cond (within (facts.hi (Scope.number Γ.length counter)) limit) none
                    (some Requirement.maximum) = none := justified
                cases held : within (facts.hi (Scope.number Γ.length counter)) limit with
                | true => rfl
                | false => rw [held] at checked; cases checked
              obtain ⟨top, at_, below⟩ := within_le known
              have bounded := sound.holds.le_hi counted at_
              have within_ : withinMaximum (env counter) (some limit) = true :=
                Nat.ble_eq_true_of_le (Nat.le_trans bounded below)
              rw [within_] at inside
              cases inside
      | true =>
          refine Yields.bind (loopIterations_invariant
            (SumInvariant carried ((Outcome.joinAll [outcome]).returned.drop collected.length)
              ((Operands.eval env rest).split carried).1) ?_ (env counter) 0 _ _
            (Nat.le_of_eq (Nat.zero_add _)) (SumInvariant.start _ _ _)) ?_
          · intro iteration state below invariant
            refine (inner _ ?_).weaken fun produced holds =>
              invariant.step (iteration := iteration) ((Operands.eval env rest).split carried).2
                produced ?_
            · have first : storeOf (Environment.ofValues
                  ((Values.cons (Value := model.Value) (ty := .nat) iteration state).append
                    ((Operands.eval env rest).split carried).2)) 0 =
                    some ⟨.nat, iteration⟩ := by
                rw [storeOf_ofValues]
                rfl
              refine ((sound.enter (Values.cons (Value := model.Value) (ty := .nat) iteration state)
                captured).bound first (Nat.zero_le _)
                (before_le below fun _ at_ => sound.2.le_hi counted at_)).orderWhen first ?_
              intro inside found
              refine ⟨env counter, ?_, below⟩
              rw [storeOf_ofValues]
              exact (sourced_append (Values.cons (Value := model.Value) (ty := .nat) iteration state)
                captured).maps _ _ _ found counted
            · have same : storeOf (Environment.ofValues (Values.cons (Value := model.Value)
                  (ty := .nat) iteration (state.append ((Operands.eval env rest).split carried).2))) =
                    entryOf (Values.cons (Value := model.Value) (ty := .nat) iteration
                      (state.append ((Operands.eval env rest).split carried).2)) :=
                funext fun level => storeOf_ofValues _ level
              rw [Outcome.joinAll_single, ← same]
              exact holds.2
          · intro final invariant
            rw [Nat.zero_add] at invariant
            exact sound.after _ _ _ (List.length_map _)
              (fun index entry _ => Shape.holds_other _ index entry)
              (sum_bounded sound _ (List.length_map _)
                (fun index init found inside => by
                  rw [entryOf_split_left carried _ index inside]
                  exact reads.entry index init found)
                invariant (sound.2.lo_le counted) fun hi top => sound.2.le_hi counted top)
  | .guard reason, arguments, _, outcomes, _, _ => by
      obtain ⟨condition, rfl⟩ := operands_one arguments
      have found := storeOf_number env condition
      show Yields _ (cond (env condition) (PIR.Process.done Values.nil)
        (PIR.Process.halt reason.stop))
      cases truth : env condition with
      | false => exact reason.stop_ne_undefined
      | true =>
          rw [truth] at found
          exact sound.assume facts.depth found
  | .literal value, _, _, outcomes, _, _ => by
      cases value with
      | nat number =>
          refine sound.single (type := .nat) number .other (some ⟨number, some number⟩) trivial ?_
          intro found same
          cases Option.some.inj same
          exact ⟨number, rfl, Nat.le_refl _, fun hi at_ => by
            cases Option.some.inj at_
            exact Nat.le_refl _⟩
      | bool flag => exact sound.afterAny _
      | fin bound number => exact sound.afterAny _
      | nominal row data => exact sound.afterAny _
      | bytes data => exact sound.afterAny _
  | .builtin operation, arguments, _, outcomes, justified, _ => by
      have reduced : cond (operation.justified facts (Scope.numbers Γ.length arguments)) none
          (some operation.requirement) = none := justified
      cases passes : operation.justified facts (Scope.numbers Γ.length arguments) with
      | false =>
          rw [passes] at reduced
          cases reduced
      | true => exact Builtin.sound sound operation arguments passes

mutual
  /-- A region that passes the check, on an environment of which the facts at its start
  hold, never stops `undefined`, and returns what the check says it returns. -/
  theorem justifyRegion_sound (laws : model.DomainLaws operations)
      {table : FunctionTable model functions} (defined : DefinedTable table) :
      ∀ {Γ out : List Ty} (region : Region (LocalDialect operations functions deployed) Γ out)
        (path : List Nat) (index : Nat) (facts : Facts) (outcome : Outcome),
        justifyRegion path index facts region = .ok outcome →
          ∀ (env : Environment model.Value Γ), facts.Sound env →
            Yields (outcome.Holds (storeOf env)) (region.denote (localMeaning model table) env)
    | Γ, _, .ret values, path, index, facts, outcome, passes, env, sound => by
        unfold justifyRegion at passes
        cases passes
        have reads := reads_eval env values
        have located : ∀ (position : Nat) (found : Returned),
            ((Scope.numbers facts.depth values).map facts.returned)[position]? = some found →
              ∃ source : Nat, (Scope.numbers Γ.length values)[position]? = some source ∧
                found = facts.returned source := by
          intro position found at_
          rw [List.getElem?_map, sound.1] at at_
          cases level : (Scope.numbers Γ.length values)[position]? with
          | none =>
              rw [level] at at_
              cases at_
          | some source =>
              rw [level] at at_
              exact ⟨source, rfl, (Option.some.inj at_).symm⟩
        refine ⟨?_, ?_⟩
        · show IntervalsHold (((Scope.numbers facts.depth values).map facts.returned).map
            (·.interval)) (Operands.eval env values)
          intro position interval entry found at_
          rw [List.getElem?_map] at found
          cases inner : ((Scope.numbers facts.depth values).map facts.returned)[position]? with
          | none =>
              rw [inner] at found
              cases found
          | some item =>
              rw [inner] at found
              obtain ⟨source, level, rfl⟩ := located position item inner
              cases Option.some.inj found
              rw [reads.entry position source level] at at_
              intro value same
              subst same
              exact ⟨sound.2.lo_le at_, fun hi top => sound.2.le_hi at_ top⟩
        · intro position item entry found at_ step member x first
          obtain ⟨source, level, rfl⟩ := located position item found
          rw [reads.entry position source level] at at_
          have shaped := sound.2.shapes source entry at_
          unfold Facts.returned at member
          dsimp only at member
          split at member
          · rename_i left right shape
            rw [shape] at shaped
            obtain ⟨p, q, one, two, value⟩ := shaped
            rcases List.mem_cons.mp member with rfl | other
            · have same := store_nat first one
              subst same
              exact ⟨q, value, sound.2.lo_le two, fun hi top => sound.2.le_hi two top⟩
            · rcases List.mem_cons.mp other with rfl | impossible
              · have same := store_nat first two
                subst same
                exact ⟨p, by rw [value, Nat.add_comm], sound.2.lo_le one,
                  fun hi top => sound.2.le_hi one top⟩
              · cases impossible
          · cases member
    | _, _, .stop reason, path, index, facts, outcome, passes, env, sound => by
        unfold justifyRegion at passes
        split at passes
        · cases passes
        · rename_i other
          exact other
    | Γ, _, .letOp op arguments bodies next, path, index, facts, outcome, passes, env, sound => by
        unfold justifyRegion at passes
        simp only [sound.2.alive, Bool.cond_false] at passes
        split at passes
        · cases passes
        · rename_i justified
          split at passes
          · cases passes
          · rename_i outcomes nested
            rw [sound.1] at justified nested passes
            refine Yields.bind
              ((LocalOp.sound laws defined sound op arguments _ outcomes justified
                (RegionsSound.entered 0 outcomes _ (LocalOp.regionInputs_at op)
                  (justifyRegions_sound laws defined bodies _ _ 0 outcomes nested))).and
                (LocalOp.branch_returns op arguments bodies)) fun results after => ?_
            refine (justifyRegion_sound laws defined next path (index + 1) _ outcome passes _
              ((after.1.inScope results).reshape _ _ ?_)).weaken
                fun values holds => holds.shrink (storeOf_grows env results)
            intro shape found entry at_
            rw [storeOf_bindAll] at at_
            simp only [Nat.lt_irrefl, ↓reduceIte, Nat.sub_self] at at_
            exact (after.2 shape found entry at_).grow (storeOf_grows env results)
    | _, _, .bind body next, path, index, facts, outcome, passes, env, sound => by
        unfold justifyRegion at passes
        split at passes
        · cases passes
        · rename_i middle first
          exact Yields.bind (justifyRegion_sound laws defined body _ 0 facts middle first env sound)
            fun values holds =>
              (justifyRegion_sound laws defined next path (index + 1) _ outcome passes _
                ((sound.afterOutcome values holds.1).inScope values)).weaken
                  fun results final => final.shrink (storeOf_grows env values)

  /-- Nested regions that pass the check, each from the facts of its number, are sound. -/
  theorem justifyRegions_sound (laws : model.DomainLaws operations)
      {table : FunctionTable model functions} (defined : DefinedTable table) :
      ∀ {signatures : List (List Ty × List Ty)}
        (bodies : Regions (LocalDialect operations functions deployed) signatures)
        (path : List Nat) (factsOf : Nat → Facts) (number : Nat) (outcomes : List Outcome),
        justifyRegions path factsOf number bodies = .ok outcomes →
          RegionsSound factsOf number outcomes (bodies.denote (localMeaning model table))
    | _, .nil, _, _, _, outcomes, passes => by
        unfold justifyRegions at passes
        cases passes
        rfl
    | _, .cons body tail, path, factsOf, number, outcomes, passes => by
        unfold justifyRegions at passes
        split at passes
        · cases passes
        · rename_i outcome first
          split at passes
          · cases passes
          · rename_i others rest
            cases passes
            exact ⟨outcome, others, rfl,
              fun arguments sound =>
                justifyRegion_sound laws defined body _ 0 _ outcome first _ sound,
              justifyRegions_sound laws defined tail path factsOf (number + 1) others rest⟩
end

end Local

/-! ## Functions and programs -/

section Programs

variable {operations : List OperationSignature} {functions : List FunctionHeader}

/-- A function whose body passes the check of facts, over functions that never stop
`undefined`, never stops `undefined`, on any arguments. -/
theorem FunctionDefinition.neverUndefined (laws : model.DomainLaws operations)
    {table : FunctionTable model functions} (defined : DefinedTable table)
    {header : FunctionHeader} (definition : FunctionDefinition operations functions header)
    (passes : definition.justified = true) (arguments : Values model.Value header.inputs) :
    NeverStops .undefined (definition.meaning model table arguments) := by
  unfold FunctionDefinition.justified FunctionDefinition.unjustified at passes
  split at passes
  · cases passes
  · rename_i outcome checked
    exact (justifyRegion_sound laws defined definition.body [] 0 _ outcome checked _
      ((Facts.start_sound arguments).inScope arguments)).neverStops

/-- The functions of a program that all pass the check of facts never stop `undefined`. -/
theorem Functions.table_defined (laws : model.DomainLaws operations) {typeTable : TypeTable} :
    ∀ {functions : List FunctionHeader} (program : Functions typeTable operations functions),
      program.justified = true → DefinedTable (program.table model)
  | _, .nil, _ => fun callee => callee.elimNil
  | _, .snoc earlier definition wellFormed, passes => by
      have both : earlier.justified = true ∧ definition.justified = true :=
        Bool.and_eq_true_iff.mp passes
      intro callee
      exact Var.cases
        (motive := fun header callee => ∀ arguments : Values model.Value header.inputs,
          NeverStops (I := Effects model) (A := Values model.Value header.outputs) .undefined
            (Values.get ((Functions.snoc earlier definition wellFormed).table model) callee
              arguments))
        (fun arguments => definition.neverUndefined laws
          (Functions.table_defined laws earlier both.1) both.2 arguments)
        (fun callee => Functions.table_defined laws earlier both.1 callee) callee
  | _, .opaque earlier other named, passes => by
      intro callee
      exact Var.cases
        (motive := fun header callee => ∀ arguments : Values model.Value header.inputs,
          NeverStops (I := Effects model) (A := Values model.Value header.outputs) .undefined
            (Values.get ((Functions.opaque earlier other named).table model) callee arguments))
        (fun arguments => partialProcess_neverStops _)
        (fun callee => Functions.table_defined laws earlier passes callee) callee

/-- For every model that satisfies the domain laws of its restricted rows, a function
whose body passes the check of facts, in a program whose earlier functions all pass it,
never stops `undefined`, on any arguments. -/
theorem Functions.never_undefined (laws : model.DomainLaws operations) {typeTable : TypeTable}
    {header : FunctionHeader} (earlier : Functions typeTable operations functions)
    (definition : FunctionDefinition operations functions header)
    (wellFormed : definition.violation typeTable = none)
    (earlierPass : earlier.justified = true) (passes : definition.justified = true)
    (arguments : Values model.Value header.inputs) :
    NeverStops .undefined
      (((Functions.snoc earlier definition wellFormed).table model).get .here arguments) :=
  definition.neverUndefined laws (Functions.table_defined laws earlier earlierPass) passes arguments

/-- For functions that all pass the check of facts and a model that satisfies the domain
laws, the process of every function on every arguments has no `undefined` stop. -/
theorem Functions.all_never_undefined (laws : model.DomainLaws operations)
    {typeTable : TypeTable} (program : Functions typeTable operations functions)
    (passes : program.justified = true) {header : FunctionHeader}
    (callee : Var functions header) (arguments : Values model.Value header.inputs) :
    NeverStops .undefined ((program.table model).get callee arguments) :=
  Functions.table_defined laws program passes callee arguments

/-- For a program all of whose functions and protocols pass the check of facts and a model
that satisfies the domain laws, the process of every function on every arguments has no
`undefined` stop. -/
theorem Program.never_undefined (laws : model.DomainLaws operations) {typeTable : TypeTable}
    {protocols : List ProtocolHeader}
    (program : Program typeTable operations functions protocols)
    (passes : program.justified = true) {header : FunctionHeader}
    (callee : Var functions header) (arguments : Values model.Value header.inputs) :
    NeverStops .undefined ((program.functionTable model).get callee arguments) :=
  Functions.all_never_undefined laws program.functions (Bool.and_eq_true_iff.mp passes).1 callee
    arguments

end Programs

end Zkc.Core
