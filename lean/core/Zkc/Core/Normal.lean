module

public import Zkc.Core.Flatten

public section

/-! The normal form of a region, for any dialect: nested regions opened, equal applications
shared.

A nested region of an operation is closed: it sees its own inputs, which are the values that
the operation gives it (an iteration number, a payload, carried values) and the values that
the operation captures. Two things follow for a reader of a region that looks at one region
at a time. What is known of a value outside a nested region is known inside only when the
value is captured. And a second application of an operation to the same operands is a new
value, of which nothing is known.

The normal form removes both. `Region.normalize` walks a region and builds another in a
context that renames the region's, as `Region.spliceInto` does, and carries a table of the
applications already made there.

- **Sharing.** An application of an operation that the dialect names as shared, to operands
  of an application in the table, is not made again: what follows reads the results of the
  first.
- **Opening.** An operation with nested regions is rebuilt by the dialect (`Normalizer.reopen`)
  so that its regions take every value in scope. The table passes into each region, since
  every application in it is on values that are now inputs.

`Region.normalize_denote`: the pass keeps the denotation, for every meaning in which the
shared operations are deterministic and the rebuilt operations mean what the original ones
mean (`Normalizer.Sound`). So a check that is run on the normal form speaks for the region
as written, and the check does not change.
-/

set_option autoImplicit false

namespace Zkc.Source

variable {Ty : Type}

/-! ## Operands under bindings -/

namespace Operands

variable {Value : Ty → Type}

/-- Operands of a context, under new bindings. -/
@[expose] def weaken {Δ : List Ty} (added : List Ty) :
    {types : List Ty} → Operands Δ types → Operands (bindAll Δ added) types
  | _, .nil => .nil
  | _, .cons reference rest => .cons (reference.weaken added) (weaken added rest)

theorem eval_weaken {Δ added : List Ty} (env : Environment Value Δ) (values : Values Value added) :
    ∀ {types : List Ty} (operands : Operands Δ types),
      Operands.eval (Environment.bindAll env values) (operands.weaken added) =
        Operands.eval env operands
  | _, .nil => rfl
  | _, .cons reference rest =>
      congr (congrArg Values.cons (Environment.bindAll_weaken env values reference))
        (eval_weaken env values rest)

/-- The values just bound, as operands. -/
@[expose] def bound : (added : List Ty) → {Δ : List Ty} → Operands (bindAll Δ added) added
  | [], _ => .nil
  | ty :: rest, Δ => .cons ((Var.here : Var (ty :: Δ) ty).weaken rest) (bound rest (Δ := ty :: Δ))

theorem eval_bound :
    ∀ (added : List Ty) {Δ : List Ty} (env : Environment Value Δ) (values : Values Value added),
      Operands.eval (Environment.bindAll env values) (bound added) = values
  | [], _, _, .nil => rfl
  | ty :: rest, Δ, env, .cons value values => by
      show Values.cons ((Environment.bindAll (env.push value) values)
          ((Var.here : Var (ty :: Δ) ty).weaken rest))
          (Operands.eval (Environment.bindAll (env.push value) values) (bound rest)) =
        Values.cons value values
      rw [Environment.bindAll_weaken, eval_bound rest (env.push value) values]
      rfl

/-- The same operands, decided on their positions. -/
@[expose] def same {Δ : List Ty} :
    {types : List Ty} → Operands Δ types → Operands Δ types → Bool
  | _, .nil, .nil => true
  | _, .cons first rest, .cons second others =>
      Nat.beq first.index second.index && same rest others

theorem same_eq {Δ : List Ty} :
    ∀ {types : List Ty} (first second : Operands Δ types), same first second = true → first = second
  | _, .nil, .nil, _ => rfl
  | _, .cons first rest, .cons second others, equal => by
      simp only [same, Bool.and_eq_true] at equal
      rw [Var.ext (Nat.eq_of_beq_eq_true equal.1), same_eq rest others equal.2]

/-- Operands of a context, under one more binding. -/
@[expose] def lift {Δ : List Ty} (head : Ty) :
    {types : List Ty} → Operands Δ types → Operands (head :: Δ) types
  | _, .nil => .nil
  | _, .cons reference rest => .cons reference.there (lift head rest)

theorem eval_lift {Δ : List Ty} {head : Ty} (env : Environment Value (head :: Δ)) :
    ∀ {types : List Ty} (operands : Operands Δ types),
      Operands.eval env (operands.lift head) =
        Operands.eval (fun {_} reference => env reference.there) operands
  | _, .nil => rfl
  | _, .cons _ rest => congrArg (Values.cons _) (eval_lift env rest)

theorem eval_append {Δ first second : List Ty} (env : Environment Value Δ)
    (left : Operands Δ first) (right : Operands Δ second) :
    Operands.eval env (left.append right) =
      (Operands.eval env left).append (Operands.eval env right) := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      show Values.cons _ (Operands.eval env (tail.append right)) = Values.cons _ _
      rw [ih]
      rfl

theorem eval_split {Δ : List Ty} (env : Environment Value Δ) (added : List Ty) {rest : List Ty}
    (operands : Operands Δ (added ++ rest)) :
    (Operands.eval env operands).split added =
      (Operands.eval env (operands.split added).1, Operands.eval env (operands.split added).2) := by
  have whole := Values.append_split added operands
  have evaluated := congrArg (Operands.eval env) whole
  rw [eval_append] at evaluated
  rw [← evaluated, Values.split_append]

theorem get_lift {Δ : List Ty} {head : Ty} :
    ∀ {types : List Ty} (operands : Operands Δ types) {ty : Ty} (position : Var types ty),
      (operands.lift head).get position = (operands.get position).there
  | _, .nil, _, position => position.elimNil
  | _, .cons _ rest, _, position => by
      cases position with
      | here => rfl
      | there position => exact get_lift rest position

theorem eval_tail {Δ : List Ty} (env : Environment Value Δ) {head : Ty} {rest : List Ty}
    (operands : Operands Δ (head :: rest)) :
    (Operands.eval env operands).tail = Operands.eval env operands.tail := by
  cases operands with
  | cons _ _ => rfl

theorem eval_cons {Δ : List Ty} (env : Environment Value Δ) {head : Ty} {rest : List Ty}
    (operands : Operands Δ (head :: rest)) :
    Operands.eval env operands =
      .cons (env (operands.get .here)) (Operands.eval env operands.tail) := by
  cases operands with
  | cons _ _ => rfl

/-- Every value of a context, the most recent first. -/
@[expose] def every : (Δ : List Ty) → Operands Δ Δ
  | [] => .nil
  | ty :: rest => .cons .here ((every rest).lift ty)

/-! The operands of every value are built by one lift per value, which is quadratic in the
size of the context. Compiled code builds them by position (`every_eq_everyFast`); the pass
and its theorems are stated with `every`. -/

/-- Every value of the end of a context, as references into the whole context, by position. -/
def everyFrom {Γ : List Ty} : (start : Nat) → (Δ : List Ty) →
    (∀ (index : Nat) (ty : Ty), Δ[index]? = some ty → Γ[start + index]? = some ty) →
      Operands Γ Δ
  | _, [], _ => .nil
  | start, ty :: rest, within =>
      .cons ⟨start, within 0 ty rfl⟩
        (everyFrom (start + 1) rest fun index other found => by
          have shifted := within (index + 1) other found
          rw [Nat.add_assoc, Nat.add_comm 1 index]
          exact shifted)

theorem get_everyFrom {Γ : List Ty} : ∀ (start : Nat) (Δ : List Ty)
    (within : ∀ (index : Nat) (ty : Ty), Δ[index]? = some ty → Γ[start + index]? = some ty)
    {ty : Ty} (position : Var Δ ty),
    ((everyFrom start Δ within).get position).index = start + position.index
  | _, [], _, _, position => position.elimNil
  | start, _ :: rest, within, _, position => by
      cases position with
      | here => rfl
      | there position =>
          show ((everyFrom (start + 1) rest _).get position).index = start + (position.index + 1)
          rw [get_everyFrom (start + 1) rest _ position, Nat.add_assoc, Nat.add_comm 1]

/-- The operand at a position of every value of a context is the value at that position. -/
theorem index_get_every : ∀ {Δ : List Ty} {ty : Ty} (position : Var Δ ty),
    ((every Δ).get position).index = position.index
  | [], _, position => position.elimNil
  | head :: rest, _, position => by
      cases position with
      | here => rfl
      | there position =>
          show (((every rest).lift head).get position).index = position.index + 1
          rw [get_lift]
          exact congrArg (· + 1) (index_get_every position)

/-- Operands that name the same values, position by position, are the same. -/
theorem ext_index {Δ : List Ty} : ∀ {types : List Ty} (first second : Operands Δ types),
    (∀ {ty : Ty} (position : Var types ty),
      (first.get position).index = (second.get position).index) → first = second
  | _, .nil, .nil, _ => rfl
  | _, .cons one rest, .cons two others, same => by
      have head : one = two := Var.ext (same .here)
      have tail := ext_index rest others fun position => same position.there
      rw [head, tail]

/-- Every value of a context, the most recent first, by position. -/
def everyFast (Δ : List Ty) : Operands Δ Δ :=
  everyFrom 0 Δ fun index ty found => by
    rw [Nat.zero_add]
    exact found

@[csimp] theorem every_eq_everyFast : @every = @everyFast := by
  funext Ty Δ
  exact ext_index _ _ fun position => by
    rw [index_get_every, everyFast, get_everyFrom, Nat.zero_add]

/-- The values of every operand of a context are the environment. -/
theorem get_eval_every :
    ∀ {Δ : List Ty} (env : Environment Value Δ) {ty : Ty} (reference : Var Δ ty),
      (Operands.eval env (every Δ)).get reference = env reference
  | [], _, _, reference => reference.elimNil
  | head :: rest, env, _, reference => by
      show (Values.cons (env .here) (Operands.eval env ((every rest).lift head))).get reference = _
      rw [eval_lift]
      cases reference with
      | here => rfl
      | there reference =>
          exact get_eval_every (fun {_} reference => env reference.there) reference

end Operands

/-- A position among mapped items. -/
@[expose] def Var.mapped {α β : Type} (f : α → β) {items : List α} {item : α}
    (position : Var items item) : Var (items.map f) (f item) :=
  ⟨position.index, by rw [List.getElem?_map, position.valid]; rfl⟩

/-! ## A context that binds every value of another

A nested region that takes every value of a context `Δ` has the context
`bindAll base (own ++ Δ)`: its own inputs, then the values of `Δ`, the last one bound the
most recent. A value of `Δ` is a value of that context. -/

/-- A value just bound, by its position among the bound types. -/
@[expose] def Var.newest {added : List Ty} {ty : Ty} (position : Var added ty) {base : List Ty} :
    Var (bindAll base added) ty :=
  ⟨added.length - 1 - position.index,
    (getElem?_bindAll_new added base position.index position.index_lt).trans position.valid⟩

/-- A value of a context, in a context that binds `own` values and then every value of the
first. -/
@[expose] def Var.inward {Δ : List Ty} {ty : Ty} (reference : Var Δ ty) :
    (own : List Ty) → {base : List Ty} → Var (bindAll base (own ++ Δ)) ty
  | [], _ => reference.newest
  | _ :: own, _ => reference.inward own

/-- A value just bound is the value at its position. -/
theorem Environment.bindAll_newest {Value : Ty → Type} :
    ∀ {added base : List Ty} (env : Environment Value base) (values : Values Value added)
      {ty : Ty} (position : Var added ty),
      Environment.bindAll env values position.newest = values.get position
  | [], _, _, _, _, position => position.elimNil
  | head :: rest, base, env, .cons value values, _, position => by
      cases position with
      | here =>
          have same : (Var.newest (base := base) (Var.here : Var (head :: rest) head)) =
              ((Var.here : Var (head :: base) head).weaken rest) :=
            Var.ext (show rest.length + 1 - 1 - 0 = 0 + rest.length by omega)
          rw [same]
          exact Environment.bindAll_weaken (env.push value) values .here
      | there position =>
          have below := position.index_lt
          have same : (Var.newest (base := base) (position.there (head := head))) =
              (Var.newest (base := head :: base) position) :=
            Var.ext (show rest.length + 1 - 1 - (position.index + 1) =
              rest.length - 1 - position.index by omega)
          rw [same]
          exact Environment.bindAll_newest (env.push value) values position

/-- A value of `Δ` in a context that binds every value of `Δ` is that value. -/
theorem Environment.bindAll_inward {Value : Ty → Type} {Δ : List Ty} {ty : Ty}
    (reference : Var Δ ty) (every : Values Value Δ) :
    ∀ (own : List Ty) {base : List Ty} (env : Environment Value base) (owned : Values Value own),
      Environment.bindAll env (owned.append every) (reference.inward own) = every.get reference
  | [], _, env, .nil => Environment.bindAll_newest env every reference
  | _ :: own, _, env, .cons value owned =>
      Environment.bindAll_inward reference every own (env.push value) owned

/-- A value of a context, in a context that binds `first` values, then `second` values, and
then every value of the first context. The own inputs of a region are sometimes two lists (the
iteration numbers of the participants of a `repeat`, then the carried values), and their
concatenation with what follows is associated to the right. -/
@[expose] def Var.inwardAfter {Δ : List Ty} {ty : Ty} (reference : Var Δ ty) (second : List Ty) :
    (first : List Ty) → {base : List Ty} → Var (bindAll base (first ++ (second ++ Δ))) ty
  | [], _ => reference.inward second
  | _ :: first, _ => reference.inwardAfter second first

/-- The position of a value of a context among every value of that context bound last: the
values are bound in order, so the first of the context is the most recent. -/
theorem Var.index_inward {Δ : List Ty} {ty : Ty} (reference : Var Δ ty) :
    ∀ (own : List Ty) {base : List Ty},
      (reference.inward own (base := base)).index = Δ.length - 1 - reference.index
  | [], _ => rfl
  | _ :: own, _ => Var.index_inward reference own

theorem Var.index_inwardAfter {Δ : List Ty} {ty : Ty} (reference : Var Δ ty) (second : List Ty) :
    ∀ (first : List Ty) {base : List Ty},
      (reference.inwardAfter second first (base := base)).index = Δ.length - 1 - reference.index
  | [], _ => Var.index_inward reference second
  | _ :: first, _ => Var.index_inwardAfter reference second first

theorem Environment.bindAll_inwardAfter {Value : Ty → Type} {Δ : List Ty} {ty : Ty}
    (reference : Var Δ ty) (every : Values Value Δ) (second : List Ty)
    (after : Values Value second) :
    ∀ (first : List Ty) {base : List Ty} (env : Environment Value base)
      (before : Values Value first),
      Environment.bindAll env (before.append (after.append every))
          (reference.inwardAfter second first) = every.get reference
  | [], _, env, .nil => Environment.bindAll_inward reference every second env after
  | _ :: first, _, env, .cons value before =>
      Environment.bindAll_inwardAfter reference every second after first (env.push value) before

namespace Operands

variable {Value : Ty → Type}

/-- Operands of a context, in a context that binds `own` values and then every value of the
first. -/
@[expose] def inward {Δ : List Ty} (own : List Ty) {base : List Ty} :
    {types : List Ty} → Operands Δ types → Operands (bindAll base (own ++ Δ)) types
  | _, .nil => .nil
  | _, .cons reference rest => .cons (reference.inward own) (inward own rest)

theorem eval_inward {Δ : List Ty} (image : Environment Value Δ) (own : List Ty) {base : List Ty}
    (env : Environment Value base) (owned : Values Value own) :
    ∀ {types : List Ty} (operands : Operands Δ types),
      Operands.eval (Environment.bindAll env (owned.append (Operands.eval image (every Δ))))
          (operands.inward own) =
        Operands.eval image operands
  | _, .nil => rfl
  | _, .cons reference rest =>
      congr (congrArg Values.cons ((Environment.bindAll_inward reference _ own env owned).trans
          (get_eval_every image reference)))
        (eval_inward image own env owned rest)

/-- Operands of a context, in a context that binds `first` values, then `second` values, and
then every value of the first context. -/
@[expose] def inwardAfter {Δ : List Ty} (second first : List Ty) {base : List Ty} :
    {types : List Ty} → Operands Δ types → Operands (bindAll base (first ++ (second ++ Δ))) types
  | _, .nil => .nil
  | _, .cons reference rest => .cons (reference.inwardAfter second first) (inwardAfter second first rest)

theorem eval_inwardAfter {Δ : List Ty} (image : Environment Value Δ) (second first : List Ty)
    {base : List Ty} (env : Environment Value base) (before : Values Value first)
    (after : Values Value second) :
    ∀ {types : List Ty} (operands : Operands Δ types),
      Operands.eval
          (Environment.bindAll env (before.append (after.append (Operands.eval image (every Δ)))))
          (operands.inwardAfter second first) =
        Operands.eval image operands
  | _, .nil => rfl
  | _, .cons reference rest =>
      congr (congrArg Values.cons
          ((Environment.bindAll_inwardAfter reference _ second after first env before).trans
            (get_eval_every image reference)))
        (eval_inwardAfter image second first env before after rest)

/-! A reference moved into a region that binds every value of its context is at a position
that depends on the length of the context alone. The definitions above find that length once
per reference; compiled code finds it once per list of operands (`inward_eq_inwardFast`,
`inwardAfter_eq_inwardAfterFast`) and once per table (`Entry.inwardAll`). -/

/-- As `inward`, with the length of the context given. -/
def inwardAt {Δ : List Ty} (own : List Ty) {base : List Ty} (depth : Nat)
    (counted : depth = Δ.length) :
    {types : List Ty} → Operands Δ types → Operands (bindAll base (own ++ Δ)) types
  | _, .nil => .nil
  | _, .cons reference rest =>
      .cons ⟨depth - 1 - reference.index, by
          rw [counted, ← Var.index_inward reference own]
          exact (reference.inward own).valid⟩
        (inwardAt own depth counted rest)

theorem inwardAt_eq {Δ : List Ty} (own : List Ty) {base : List Ty} (depth : Nat)
    (counted : depth = Δ.length) :
    ∀ {types : List Ty} (operands : Operands Δ types),
      inwardAt own (base := base) depth counted operands = operands.inward own
  | _, .nil => rfl
  | _, .cons reference rest => by
      show Values.cons _ (inwardAt own depth counted rest) =
        Values.cons (reference.inward own) (inward own rest)
      rw [inwardAt_eq own depth counted rest]
      congr 1
      exact Var.ext ((congrArg (· - 1 - reference.index) counted).trans
        (Var.index_inward reference own).symm)

/-- As `inward`, finding the length of the context once. -/
def inwardFast {Δ : List Ty} (own : List Ty) {base : List Ty} {types : List Ty}
    (operands : Operands Δ types) : Operands (bindAll base (own ++ Δ)) types :=
  inwardAt own Δ.length rfl operands

@[csimp] theorem inward_eq_inwardFast : @inward = @inwardFast := by
  funext Ty Δ own base types operands
  exact (inwardAt_eq own Δ.length rfl operands).symm

/-- As `inwardAfter`, with the length of the context given. -/
def inwardAfterAt {Δ : List Ty} (second first : List Ty) {base : List Ty} (depth : Nat)
    (counted : depth = Δ.length) :
    {types : List Ty} → Operands Δ types →
      Operands (bindAll base (first ++ (second ++ Δ))) types
  | _, .nil => .nil
  | _, .cons reference rest =>
      .cons ⟨depth - 1 - reference.index, by
          rw [counted, ← Var.index_inwardAfter reference second first]
          exact (reference.inwardAfter second first).valid⟩
        (inwardAfterAt second first depth counted rest)

theorem inwardAfterAt_eq {Δ : List Ty} (second first : List Ty) {base : List Ty} (depth : Nat)
    (counted : depth = Δ.length) :
    ∀ {types : List Ty} (operands : Operands Δ types),
      inwardAfterAt second first (base := base) depth counted operands =
        operands.inwardAfter second first
  | _, .nil => rfl
  | _, .cons reference rest => by
      show Values.cons _ (inwardAfterAt second first depth counted rest) =
        Values.cons (reference.inwardAfter second first) (inwardAfter second first rest)
      rw [inwardAfterAt_eq second first depth counted rest]
      congr 1
      exact Var.ext ((congrArg (· - 1 - reference.index) counted).trans
        (Var.index_inwardAfter reference second first).symm)

/-- As `inwardAfter`, finding the length of the context once. -/
def inwardAfterFast {Δ : List Ty} (second first : List Ty) {base : List Ty} {types : List Ty}
    (operands : Operands Δ types) : Operands (bindAll base (first ++ (second ++ Δ))) types :=
  inwardAfterAt second first Δ.length rfl operands

@[csimp] theorem inwardAfter_eq_inwardAfterFast : @inwardAfter = @inwardAfterFast := by
  funext Ty Δ second first base types operands
  exact (inwardAfterAt_eq second first Δ.length rfl operands).symm

end Operands

/-- The renaming of a nested region's context into the context that binds the same `own`
values and then every value of `Δ`: an own value is itself, and a capture is the value of
`Δ` that it captures. -/
@[expose] def Renaming.inward {Δ captures : List Ty} (captured : Operands Δ captures) :
    (own : List Ty) → {source target : List Ty} → Renaming source target →
      Renaming (bindAll source (own ++ captures)) (bindAll target (own ++ Δ))
  | [], _, _, map => Renaming.bindOperands (map.weaken Δ) captures (captured.inward [])
  | ty :: own, _, _, map =>
      Renaming.inward captured own (map.keep ty ty fun _ same => same.symm)

theorem Renaming.Holds.weaken {Value : Ty → Type} {Γ Δ : List Ty} {map : Renaming Γ Δ}
    {env : Environment Value Γ} {image : Environment Value Δ} (holds : map.Holds env image)
    {added : List Ty} (values : Values Value added) :
    Renaming.Holds (map.weaken added) env (Environment.bindAll image values) :=
  ⟨fun reference =>
    (congrArg (Environment.bindAll image values) (Mapping.apply_weaken map added reference rfl)).trans
      ((Environment.bindAll_weaken image values _).trans (holds.value reference))⟩

/-- The inner context holds, at the image of every value of the nested region, that value:
the own values are the same, and the captures are the values of the operands that are
captured. -/
theorem Renaming.Holds.inward {Value : Ty → Type} {Δ captures : List Ty}
    (captured : Operands Δ captures) (image : Environment Value Δ) :
    ∀ (own : List Ty) {source target : List Ty} {map : Renaming source target}
      {env : Environment Value source} {inner : Environment Value target},
      map.Holds env inner → ∀ (owned : Values Value own),
        Renaming.Holds (Renaming.inward captured own map)
          (Environment.bindAll env (owned.append (Operands.eval image captured)))
          (Environment.bindAll inner (owned.append (Operands.eval image (Operands.every Δ))))
  | [], _, _, _, _, inner, holds, .nil => by
      have bound := Renaming.Holds.bindOperands captures
        (holds.weaken (Operands.eval image (Operands.every Δ))) (captured.inward [])
      have same : Operands.eval
            (Environment.bindAll inner (Operands.eval image (Operands.every Δ)))
            (captured.inward []) = Operands.eval image captured :=
        Operands.eval_inward image [] inner .nil captured
      rw [same] at bound
      exact bound
  | ty :: own, _, _, _, _, _, holds, .cons value owned =>
      Renaming.Holds.inward captured image own (holds.keep ty value) owned

/-- The renaming of a nested region's context into the context that binds the same `first`
and `second` values and then every value of `Δ`. -/
@[expose] def Renaming.inwardAfter {Δ captures : List Ty} (captured : Operands Δ captures)
    (second : List Ty) :
    (first : List Ty) → {source target : List Ty} → Renaming source target →
      Renaming (bindAll source (first ++ (second ++ captures)))
        (bindAll target (first ++ (second ++ Δ)))
  | [], _, _, map => Renaming.inward captured second map
  | ty :: first, _, _, map =>
      Renaming.inwardAfter captured second first (map.keep ty ty fun _ same => same.symm)

theorem Renaming.Holds.inwardAfter {Value : Ty → Type} {Δ captures : List Ty}
    (captured : Operands Δ captures) (image : Environment Value Δ) (second : List Ty)
    (after : Values Value second) :
    ∀ (first : List Ty) {source target : List Ty} {map : Renaming source target}
      {env : Environment Value source} {inner : Environment Value target},
      map.Holds env inner → ∀ (before : Values Value first),
        Renaming.Holds (Renaming.inwardAfter captured second first map)
          (Environment.bindAll env (before.append (after.append (Operands.eval image captured))))
          (Environment.bindAll inner
            (before.append (after.append (Operands.eval image (Operands.every Δ)))))
  | [], _, _, _, _, _, holds, .nil => Renaming.Holds.inward captured image second holds after
  | ty :: first, _, _, _, _, _, holds, .cons value before =>
      Renaming.Holds.inwardAfter captured image second after first (holds.keep ty value) before

/-! ## The table of applications -/

/-- An application already made: its operation, its operands and its results, all in the
context built so far. -/
structure Entry (dialect : Dialect) (Δ : List dialect.Ty) where
  op : dialect.Op
  arguments : Operands Δ (dialect.arguments op)
  results : Operands Δ (dialect.results op)

namespace Entry

variable {dialect : Dialect} {Δ : List dialect.Ty}

/-- An application, under new bindings. -/
@[expose] def weaken (added : List dialect.Ty) (entry : Entry dialect Δ) :
    Entry dialect (bindAll Δ added) :=
  ⟨entry.op, entry.arguments.weaken added, entry.results.weaken added⟩

/-- An application, in a context that binds `own` values and then every value of `Δ`. -/
@[expose] def inward (own : List dialect.Ty) {base : List dialect.Ty} (entry : Entry dialect Δ) :
    Entry dialect (bindAll base (own ++ Δ)) :=
  ⟨entry.op, entry.arguments.inward own, entry.results.inward own⟩

/-- An application, in a context that binds `first` values, then `second` values, and then
every value of `Δ`. -/
@[expose] def inwardAfter (second first : List dialect.Ty) {base : List dialect.Ty}
    (entry : Entry dialect Δ) : Entry dialect (bindAll base (first ++ (second ++ Δ))) :=
  ⟨entry.op, entry.arguments.inwardAfter second first, entry.results.inwardAfter second first⟩

/-- The applications of a table, in a context that binds `own` values and then every value of
`Δ`. -/
@[expose] def inwardAll (own : List dialect.Ty) {base : List dialect.Ty}
    (table : List (Entry dialect Δ)) : List (Entry dialect (bindAll base (own ++ Δ))) :=
  table.map (Entry.inward own)

/-- As `inwardAll`, finding the length of the context once. -/
def inwardAllFast (own : List dialect.Ty) {base : List dialect.Ty}
    (table : List (Entry dialect Δ)) : List (Entry dialect (bindAll base (own ++ Δ))) :=
  let depth := Δ.length
  table.map fun entry =>
    ⟨entry.op, entry.arguments.inwardAt own depth rfl, entry.results.inwardAt own depth rfl⟩

@[csimp] theorem inwardAll_eq_inwardAllFast : @inwardAll = @inwardAllFast := by
  funext dialect Δ own base table
  unfold inwardAll inwardAllFast Entry.inward
  simp only [Operands.inwardAt_eq]

/-- The applications of a table, in a context that binds `first` values, then `second` values,
and then every value of `Δ`. -/
@[expose] def inwardAfterAll (second first : List dialect.Ty) {base : List dialect.Ty}
    (table : List (Entry dialect Δ)) :
    List (Entry dialect (bindAll base (first ++ (second ++ Δ)))) :=
  table.map (Entry.inwardAfter second first)

/-- As `inwardAfterAll`, finding the length of the context once. -/
def inwardAfterAllFast (second first : List dialect.Ty) {base : List dialect.Ty}
    (table : List (Entry dialect Δ)) :
    List (Entry dialect (bindAll base (first ++ (second ++ Δ)))) :=
  let depth := Δ.length
  table.map fun entry =>
    ⟨entry.op, entry.arguments.inwardAfterAt second first depth rfl,
      entry.results.inwardAfterAt second first depth rfl⟩

@[csimp] theorem inwardAfterAll_eq_inwardAfterAllFast :
    @inwardAfterAll = @inwardAfterAllFast := by
  funext dialect Δ second first base table
  unfold inwardAfterAll inwardAfterAllFast Entry.inwardAfter
  simp only [Operands.inwardAfterAt_eq]

end Entry

/-- Which operations are shared, and when two of them are one: a partial decision of
equality. An operation that is not equal to itself here is never shared. -/
abbrev SameOp (dialect : Dialect) := (first second : dialect.Op) → Option (PLift (first = second))

/-- The results of the application of an operation to operands, when the table has it. -/
@[expose] def Entry.find? {dialect : Dialect} (sameOp : SameOp dialect) {Δ : List dialect.Ty}
    (op : dialect.Op) (arguments : Operands Δ (dialect.arguments op)) :
    List (Entry dialect Δ) → Option (Operands Δ (dialect.results op))
  | [] => none
  | entry :: rest =>
      match sameOp entry.op op with
      | some ⟨equal⟩ =>
          cond (Operands.same (equal ▸ entry.arguments : Operands Δ (dialect.arguments op)) arguments)
            (some (equal ▸ entry.results))
            (Entry.find? sameOp op arguments rest)
      | none => Entry.find? sameOp op arguments rest

/-! ## Rebuilt operations -/

/-- How the nested regions of an operation are rebuilt: for each, its new inputs, the
renaming of its context into the new one, and the table at its start. The outputs of a
region do not change. -/
inductive Plan (dialect : Dialect) :
    List (List dialect.Ty × List dialect.Ty) → List (List dialect.Ty × List dialect.Ty) → Type where
  | nil : Plan dialect [] []
  | cons {inputs inputs' outputs : List dialect.Ty}
      {rest rest' : List (List dialect.Ty × List dialect.Ty)}
      (map : Renaming (bindAll [] inputs) (bindAll [] inputs'))
      (table : List (Entry dialect (bindAll [] inputs')))
      (tail : Plan dialect rest rest') :
      Plan dialect ((inputs, outputs) :: rest) ((inputs', outputs) :: rest')

/-- An operation rebuilt at a context: the signatures of its new regions, how each is made
from the old one, and the instruction, given the new regions and what follows. What follows
is in the context of the original operation's results: a rebuilt operation has the same
results. -/
structure Reopened (dialect : Dialect) (Δ : List dialect.Ty) (op : dialect.Op) where
  regions : List (List dialect.Ty × List dialect.Ty)
  plan : Plan dialect (dialect.regions op) regions
  build : {out : List dialect.Ty} → Regions dialect regions →
    Region dialect (bindAll Δ (dialect.results op)) out → Region dialect Δ out

/-- What a dialect gives the pass: which operations are shared, and how an operation is
rebuilt at a context, from its operands and the table there. -/
structure Normalizer (dialect : Dialect) where
  sameOp : SameOp dialect
  reopen : {Δ : List dialect.Ty} → (op : dialect.Op) → Operands Δ (dialect.arguments op) →
    List (Entry dialect Δ) → Reopened dialect Δ op

/-- The table after an application: with the application, when its operation is shared. -/
@[expose] def Entry.after {dialect : Dialect} (sameOp : SameOp dialect) {Δ : List dialect.Ty}
    (op : dialect.Op) (arguments : Operands Δ (dialect.arguments op))
    (table : List (Entry dialect Δ)) : List (Entry dialect (bindAll Δ (dialect.results op))) :=
  cond (sameOp op op).isSome
    (⟨op, arguments.weaken _, Operands.bound _⟩ :: table.map (Entry.weaken (dialect.results op)))
    (table.map (Entry.weaken (dialect.results op)))

/-! ## The pass -/

mutual
  /-- The normal form of a region, in a context that renames the region's, after the
  applications of a table. -/
  @[expose] def Region.normalize {dialect : Dialect} (normalizer : Normalizer dialect) :
      {Γ out : List dialect.Ty} → Region dialect Γ out → {Δ : List dialect.Ty} →
        Renaming Γ Δ → List (Entry dialect Δ) → Region dialect Δ out
    | _, _, .ret values, _, map, _ => .ret (map.operands values)
    | _, _, .stop reason, _, _, _ => .stop reason
    | _, _, .letOp op arguments bodies rest, _, map, table =>
        match Entry.find? normalizer.sameOp op (map.operands arguments) table with
        | some results =>
            Region.normalize normalizer rest
              (Renaming.bindOperands map (dialect.results op) results) table
        | none =>
            (normalizer.reopen op (map.operands arguments) table).build
              (Regions.normalize normalizer bodies
                (normalizer.reopen op (map.operands arguments) table).plan)
              (Region.normalize normalizer rest (map.keepAll (dialect.results op))
                (Entry.after normalizer.sameOp op (map.operands arguments) table))
    | _, _, .bind (mid := mid) body rest, _, map, table =>
        .bind (Region.normalize normalizer body map table)
          (Region.normalize normalizer rest (map.keepAll mid) (table.map (Entry.weaken mid)))

  /-- The nested regions of an operation, each rebuilt as its plan says. -/
  @[expose] def Regions.normalize {dialect : Dialect} (normalizer : Normalizer dialect) :
      {signatures signatures' : List (List dialect.Ty × List dialect.Ty)} →
        Regions dialect signatures → Plan dialect signatures signatures' →
          Regions dialect signatures'
    | _, _, .nil, .nil => .nil
    | _, _, .cons body tail, .cons map table plan =>
        .cons (Region.normalize normalizer body map table) (Regions.normalize normalizer tail plan)
end

/-- The normal form of a closed region: its blocks removed, its nested regions opened, its
equal applications shared. -/
@[expose] def Region.normal {dialect : Dialect} (normalizer : Normalizer dialect)
    {inputs out : List dialect.Ty} (region : Region dialect (bindAll [] inputs) out) :
    Region dialect (bindAll [] inputs) out :=
  region.flatten.normalize normalizer
    (Renaming.keepAll (Mapping.start (Δ := ([] : List dialect.Ty)) 0 rfl) inputs) []

/-! ## Where an instruction of the normal form comes from

A refusal of the check of facts names the path of an instruction of the normal form. The
normal form has the instructions of the body as written without its blocks and without the
applications that are shared, so its paths are not those of the body. `Region.origins` gives,
for the instructions of the normal form in their order, the paths as written: the instructions
of the body in the order of flattening (`Region.traces`), without those that the pass drops
(`Region.kept`, the recursion of `Region.normalize` with the same decisions). It is used to
place a refusal, and no theorem reads it. -/

/-- An instruction, by its path in the body as written, and the instructions of each of its
nested regions. -/
inductive Trace where
  | instruction (path : List Nat) (regions : List (List Trace))
  deriving Repr, Inhabited

/-- What the normal form keeps of an instruction: nothing when its application is shared, or
what it keeps of each nested region. -/
inductive Kept where
  | dropped
  | kept (regions : List (List Kept))
  deriving Repr, Inhabited

/-- What a dialect adds for the regions that an operation carries inside itself: their
instructions, and what the normal form keeps of them. -/
structure Tracer (dialect : Dialect) where
  traces : dialect.Op → List Nat → List (List Trace)
  kept : {Δ : List dialect.Ty} → (op : dialect.Op) → Operands Δ (dialect.arguments op) →
    List (Entry dialect Δ) → List (List Kept)

/-- A dialect whose operations carry no region inside themselves. -/
@[expose] def Tracer.none {dialect : Dialect} : Tracer dialect :=
  ⟨fun _ _ => [], fun _ _ _ => []⟩

mutual
  /-- The instructions of a region in the order of flattening, each with its path as
  written. `path` and `index` say where the region's next instruction is. -/
  @[expose] def Region.traces {dialect : Dialect} (tracer : Tracer dialect) :
      {Γ out : List dialect.Ty} → Region dialect Γ out → List Nat → Nat → List Trace
    | _, _, .ret _, _, _ => []
    | _, _, .stop _, _, _ => []
    | _, _, .letOp op _ bodies rest, path, index =>
        .instruction (path ++ [index])
            (tracer.traces op (path ++ [index]) ++ Regions.traces tracer bodies (path ++ [index]) 0) ::
          Region.traces tracer rest path (index + 1)
    | _, _, .bind body rest, path, index =>
        Region.traces tracer body (path ++ [index]) 0 ++ Region.traces tracer rest path (index + 1)

  @[expose] def Regions.traces {dialect : Dialect} (tracer : Tracer dialect) :
      {signatures : List (List dialect.Ty × List dialect.Ty)} → Regions dialect signatures →
        List Nat → Nat → List (List Trace)
    | _, .nil, _, _ => []
    | _, .cons body tail, path, number =>
        Region.traces tracer body (path ++ [number]) 0 :: Regions.traces tracer tail path (number + 1)
end

mutual
  /-- What the normal form keeps of the instructions of a region, in order: the recursion of
  `Region.normalize`, with its decisions. -/
  @[expose] def Region.kept {dialect : Dialect} (normalizer : Normalizer dialect)
      (tracer : Tracer dialect) :
      {Γ out : List dialect.Ty} → Region dialect Γ out → {Δ : List dialect.Ty} →
        Renaming Γ Δ → List (Entry dialect Δ) → List Kept
    | _, _, .ret _, _, _, _ => []
    | _, _, .stop _, _, _, _ => []
    | _, _, .letOp op arguments bodies rest, _, map, table =>
        match Entry.find? normalizer.sameOp op (map.operands arguments) table with
        | some results =>
            .dropped :: Region.kept normalizer tracer rest
              (Renaming.bindOperands map (dialect.results op) results) table
        | none =>
            .kept (tracer.kept op (map.operands arguments) table ++
                Regions.kept normalizer tracer bodies
                  (normalizer.reopen op (map.operands arguments) table).plan) ::
              Region.kept normalizer tracer rest (map.keepAll (dialect.results op))
                (Entry.after normalizer.sameOp op (map.operands arguments) table)
    | _, _, .bind (mid := mid) body rest, _, map, table =>
        Region.kept normalizer tracer body map table ++
          Region.kept normalizer tracer rest (map.keepAll mid) (table.map (Entry.weaken mid))

  @[expose] def Regions.kept {dialect : Dialect} (normalizer : Normalizer dialect)
      (tracer : Tracer dialect) :
      {signatures signatures' : List (List dialect.Ty × List dialect.Ty)} →
        Regions dialect signatures → Plan dialect signatures signatures' → List (List Kept)
    | _, _, .nil, .nil => []
    | _, _, .cons body tail, .cons map table plan =>
        Region.kept normalizer tracer body map table :: Regions.kept normalizer tracer tail plan
end

mutual
  /-- The instructions that are kept, with their paths as written. -/
  @[expose] def Trace.keptOf : List Trace → List Kept → List Trace
    | .instruction path regions :: traces, .kept nested :: kept =>
        .instruction path (Trace.keptRegions regions nested) :: Trace.keptOf traces kept
    | _ :: traces, .dropped :: kept => Trace.keptOf traces kept
    | _, _ => []

  @[expose] def Trace.keptRegions : List (List Trace) → List (List Kept) → List (List Trace)
    | traces :: rest, kept :: others => Trace.keptOf traces kept :: Trace.keptRegions rest others
    | _, _ => []
end

/-- The path as written of the instruction at a path of the normal form. -/
@[expose] def Trace.written : List Trace → List Nat → Option (List Nat)
  | traces, [index] =>
      match traces[index]? with
      | some (.instruction path _) => some path
      | none => none
  | traces, index :: number :: rest =>
      match traces[index]? with
      | some (.instruction _ regions) =>
          match regions[number]? with
          | some inner => Trace.written inner rest
          | none => none
      | none => none
  | _, [] => none

/-- The instructions of the normal form of a closed region, in their order, with their paths
as written. -/
@[expose] def Region.origins {dialect : Dialect} (normalizer : Normalizer dialect)
    (tracer : Tracer dialect) {inputs out : List dialect.Ty}
    (region : Region dialect (bindAll [] inputs) out) : List Trace :=
  Trace.keptOf (Region.traces tracer region [] 0)
    (Region.kept normalizer tracer region.flatten
      (Renaming.keepAll (Mapping.start (Δ := ([] : List dialect.Ty)) 0 rfl) inputs) [])

/-! ## The pass keeps the denotation -/

section Denote

variable {dialect : Dialect} {interface : PIR.Signature} (meaning : RegionMeaning dialect interface)

/-- An operation whose application returns values or stops, performs nothing, and does not
depend on its nested regions. -/
structure Deterministic (op : dialect.Op) : Prop where
  ends : ∀ arguments bodies,
    (∃ values, meaning.operation op arguments bodies = .done values) ∨
      (∃ reason, meaning.operation op arguments bodies = .halt reason)
  closed : ∀ arguments bodies others,
    meaning.operation op arguments bodies = meaning.operation op arguments others

/-- Every application of the table returned the results that the table names. -/
@[expose] def TableHolds {Δ : List dialect.Ty} (table : List (Entry dialect Δ))
    (image : Environment meaning.Value Δ) : Prop :=
  ∀ entry ∈ table, ∀ bodies,
    meaning.operation entry.op (Operands.eval image entry.arguments) bodies =
      .done (Operands.eval image entry.results)

theorem TableHolds.nil {Δ : List dialect.Ty} (image : Environment meaning.Value Δ) :
    TableHolds meaning ([] : List (Entry dialect Δ)) image :=
  fun _ member => nomatch member

/-- An instruction followed by the return of its results is the operation. -/
theorem Region.denote_letOp_bound (op : dialect.Op) {Δ : List dialect.Ty}
    (arguments : Operands Δ (dialect.arguments op)) (bodies : Regions dialect (dialect.regions op))
    (env : Environment meaning.Value Δ) :
    (Region.letOp op arguments bodies (.ret (Operands.bound (dialect.results op)))).denote
        meaning env =
      meaning.operation op (Operands.eval env arguments) (bodies.denote meaning) := by
  show (meaning.operation op (Operands.eval env arguments) (bodies.denote meaning)).bind
      (fun values => PIR.Process.done
        (Operands.eval (Environment.bindAll env values) (Operands.bound (dialect.results op)))) = _
  have returned : (fun values : Values meaning.Value (dialect.results op) =>
      (PIR.Process.done (Operands.eval (Environment.bindAll env values)
        (Operands.bound (dialect.results op))) :
        PIR.Process interface (Values meaning.Value (dialect.results op)))) = PIR.Process.done := by
    funext values
    rw [Operands.eval_bound]
  rw [returned, PIR.Process.bind_done]

/-- A process followed by the return of its results is the process. -/
theorem Region.bind_ret_bound {Δ types : List dialect.Ty} (env : Environment meaning.Value Δ)
    (process : PIR.Process interface (Values meaning.Value types)) :
    (process.bind fun values =>
        (Region.ret (dialect := dialect) (Operands.bound types)).denote meaning
          (Environment.bindAll env values)) = process := by
  have returned : (fun values : Values meaning.Value types =>
      (Region.ret (dialect := dialect) (Operands.bound types)).denote meaning
        (Environment.bindAll env values)) = PIR.Process.done := by
    funext values
    show PIR.Process.done _ = _
    rw [Operands.eval_bound]
  rw [returned, PIR.Process.bind_done]

theorem TableHolds.weaken {Δ : List dialect.Ty} {table : List (Entry dialect Δ)}
    {image : Environment meaning.Value Δ} (known : TableHolds meaning table image)
    (added : List dialect.Ty) (values : Values meaning.Value added) :
    TableHolds meaning (table.map (Entry.weaken added)) (Environment.bindAll image values) := by
  intro entry member bodies
  obtain ⟨original, inTable, rfl⟩ := List.mem_map.mp member
  show meaning.operation original.op (Operands.eval _ (original.arguments.weaken added)) bodies =
    .done (Operands.eval _ (original.results.weaken added))
  rw [Operands.eval_weaken, Operands.eval_weaken]
  exact known original inTable bodies

/-- The table of a context holds in a context that binds every value of the first. -/
theorem TableHolds.inward {Δ : List dialect.Ty} {table : List (Entry dialect Δ)}
    {image : Environment meaning.Value Δ} (known : TableHolds meaning table image)
    (own : List dialect.Ty) {base : List dialect.Ty} (env : Environment meaning.Value base)
    (owned : Values meaning.Value own) :
    TableHolds meaning (table.map (Entry.inward own))
      (Environment.bindAll env (owned.append (Operands.eval image (Operands.every Δ)))) := by
  intro entry member bodies
  obtain ⟨original, inTable, rfl⟩ := List.mem_map.mp member
  show meaning.operation original.op (Operands.eval _ (original.arguments.inward own)) bodies =
    .done (Operands.eval _ (original.results.inward own))
  rw [Operands.eval_inward, Operands.eval_inward]
  exact known original inTable bodies

theorem TableHolds.inwardAfter {Δ : List dialect.Ty} {table : List (Entry dialect Δ)}
    {image : Environment meaning.Value Δ} (known : TableHolds meaning table image)
    (second first : List dialect.Ty) {base : List dialect.Ty}
    (env : Environment meaning.Value base) (before : Values meaning.Value first)
    (after : Values meaning.Value second) :
    TableHolds meaning (table.map (Entry.inwardAfter second first))
      (Environment.bindAll env
        (before.append (after.append (Operands.eval image (Operands.every Δ))))) := by
  intro entry member bodies
  obtain ⟨original, inTable, rfl⟩ := List.mem_map.mp member
  show meaning.operation original.op
      (Operands.eval _ (original.arguments.inwardAfter second first)) bodies =
    .done (Operands.eval _ (original.results.inwardAfter second first))
  rw [Operands.eval_inwardAfter, Operands.eval_inwardAfter]
  exact known original inTable bodies

theorem Entry.find?_sound (sameOp : SameOp dialect) {Δ : List dialect.Ty}
    (image : Environment meaning.Value Δ) :
    ∀ (table : List (Entry dialect Δ)), TableHolds meaning table image →
      ∀ (op : dialect.Op) (arguments : Operands Δ (dialect.arguments op))
        (results : Operands Δ (dialect.results op)),
        Entry.find? sameOp op arguments table = some results →
          ∀ bodies, meaning.operation op (Operands.eval image arguments) bodies =
            .done (Operands.eval image results)
  | [], _, _, _, _, found => by cases found
  | ⟨made, operands, made_results⟩ :: rest, known, op, arguments, results, found => by
      have later : TableHolds meaning rest image :=
        fun entry member => known entry (List.mem_cons_of_mem _ member)
      unfold Entry.find? at found
      split at found
      · rename_i equal _
        cases equal
        cases sameOperands : Operands.same operands arguments with
        | true =>
            rw [sameOperands] at found
            cases found
            have equalOperands := Operands.same_eq _ _ sameOperands
            intro bodies
            rw [← equalOperands]
            exact known _ (List.mem_cons_self ..) bodies
        | false =>
            rw [sameOperands] at found
            exact Entry.find?_sound sameOp image rest later _ _ _ found
      · exact Entry.find?_sound sameOp image rest later op arguments results found

/-- The table after an application that returned holds of the context with its results. -/
theorem TableHolds.after (sameOp : SameOp dialect)
    {Δ : List dialect.Ty} {table : List (Entry dialect Δ)} {image : Environment meaning.Value Δ}
    (known : TableHolds meaning table image) (op : dialect.Op)
    (arguments : Operands Δ (dialect.arguments op))
    (values : Values meaning.Value (dialect.results op))
    (returned : ∀ bodies, (sameOp op op).isSome = true →
      meaning.operation op (Operands.eval image arguments) bodies = .done values) :
    TableHolds meaning (Entry.after sameOp op arguments table) (Environment.bindAll image values) := by
  unfold Entry.after
  cases shared : (sameOp op op).isSome with
  | false => exact known.weaken meaning _ values
  | true =>
      intro entry member others
      cases member with
      | head =>
          show meaning.operation op (Operands.eval _ (arguments.weaken _)) others =
            .done (Operands.eval _ (Operands.bound _))
          rw [Operands.eval_weaken, Operands.eval_bound]
          exact returned others shared
      | tail _ inTable => exact known.weaken meaning _ values entry inTable others

/-- The new regions of a plan do what the old ones do: on inputs that hold, at the image of
every old input, that input, and of which the table of the region holds. -/
@[expose] def Plan.Agrees :
    {signatures signatures' : List (List dialect.Ty × List dialect.Ty)} →
      Plan dialect signatures signatures' →
      Values (RegionFunction meaning.Value interface) signatures →
      Values (RegionFunction meaning.Value interface) signatures' → Prop
  | _, _, .nil, _, _ => True
  | _, _, .cons map table tail, functions, functions' =>
      (∀ values values', map.Holds (Environment.ofValues values) (Environment.ofValues values') →
        TableHolds meaning table (Environment.ofValues values') →
          functions'.get .here values' = functions.get .here values) ∧
        Plan.Agrees tail functions.tail functions'.tail

/-- What the pass needs of a dialect's choices, for a meaning: a shared operation is
deterministic, and a rebuilt operation with regions that agree with the old ones is the
operation. -/
structure Normalizer.Sound (normalizer : Normalizer dialect) : Prop where
  deterministic : ∀ op, (normalizer.sameOp op op).isSome = true → Deterministic meaning op
  reopen : ∀ {Δ : List dialect.Ty} (op : dialect.Op) (arguments : Operands Δ (dialect.arguments op))
    (table : List (Entry dialect Δ)) (image : Environment meaning.Value Δ),
    TableHolds meaning table image →
    ∀ (functions : Values (RegionFunction meaning.Value interface) (dialect.regions op))
      (bodies : Regions dialect (normalizer.reopen op arguments table).regions),
      Plan.Agrees meaning (normalizer.reopen op arguments table).plan functions
        (bodies.denote meaning) →
      ∀ {out : List dialect.Ty} (rest : Region dialect (bindAll Δ (dialect.results op)) out),
        ((normalizer.reopen op arguments table).build bodies rest).denote meaning image =
          (meaning.operation op (Operands.eval image arguments) functions).bind fun values =>
            rest.denote meaning (Environment.bindAll image values)

/-- The empty renaming holds of the empty environments. -/
theorem Renaming.Holds.start {Value : dialect.Ty → Type} :
    Renaming.Holds (Mapping.start (Δ := ([] : List dialect.Ty)) 0 rfl)
      (Environment.empty : Environment Value []) Environment.empty :=
  ⟨fun reference => reference.elimNil⟩

/-- A region rebuilt over its own inputs and every value of a context does, on the own
values and the values of the context, what the old one does on the own values and the values
that it captures. -/
theorem Plan.agrees_inward {Δ captures own : List dialect.Ty} (captured : Operands Δ captures)
    {table : List (Entry dialect Δ)} {image : Environment meaning.Value Δ}
    (known : TableHolds meaning table image) {outputs : List dialect.Ty}
    (old : RegionFunction meaning.Value interface (own ++ captures, outputs))
    (new : RegionFunction meaning.Value interface (own ++ Δ, outputs))
    (agrees : ∀ values values',
      Renaming.Holds (Renaming.inward captured own (Mapping.start (Δ := ([] : List dialect.Ty)) 0 rfl))
          (Environment.ofValues values) (Environment.ofValues values') →
        TableHolds meaning (table.map (Entry.inward own (base := [])))
          (Environment.ofValues values') → new values' = old values)
    (owned : Values meaning.Value own) :
    new (owned.append (Operands.eval image (Operands.every Δ))) =
      old (owned.append (Operands.eval image captured)) :=
  agrees _ _ (Renaming.Holds.inward captured image own Renaming.Holds.start owned)
    (known.inward meaning own Environment.empty owned)

/-- The same for a region whose own inputs are two lists. -/
theorem Plan.agrees_inwardAfter {Δ captures first second : List dialect.Ty}
    (captured : Operands Δ captures) {table : List (Entry dialect Δ)}
    {image : Environment meaning.Value Δ} (known : TableHolds meaning table image)
    {outputs : List dialect.Ty}
    (old : RegionFunction meaning.Value interface (first ++ (second ++ captures), outputs))
    (new : RegionFunction meaning.Value interface (first ++ (second ++ Δ), outputs))
    (agrees : ∀ values values',
      Renaming.Holds
          (Renaming.inwardAfter captured second first
            (Mapping.start (Δ := ([] : List dialect.Ty)) 0 rfl))
          (Environment.ofValues values) (Environment.ofValues values') →
        TableHolds meaning (table.map (Entry.inwardAfter second first (base := [])))
          (Environment.ofValues values') → new values' = old values)
    (before : Values meaning.Value first) (after : Values meaning.Value second) :
    new (before.append (after.append (Operands.eval image (Operands.every Δ)))) =
      old (before.append (after.append (Operands.eval image captured))) :=
  agrees _ _ (Renaming.Holds.inwardAfter captured image second after first Renaming.Holds.start before)
    (known.inwardAfter meaning second first Environment.empty before after)

variable {meaning}

mutual
  /-- The normal form keeps the denotation. -/
  theorem Region.normalize_denote {normalizer : Normalizer dialect}
      (sound : normalizer.Sound meaning) :
      ∀ {Γ out : List dialect.Ty} (region : Region dialect Γ out) {Δ : List dialect.Ty}
        (map : Renaming Γ Δ) (table : List (Entry dialect Δ)) (env : Environment meaning.Value Γ)
        (image : Environment meaning.Value Δ), map.Holds env image →
        TableHolds meaning table image →
          (region.normalize normalizer map table).denote meaning image = region.denote meaning env
    | _, _, .ret values, _, map, _, env, image, holds, _ => by
        show PIR.Process.done _ = PIR.Process.done _
        rw [holds.eval]
    | _, _, .stop reason, _, _, _, _, _, _, _ => rfl
    | _, _, .letOp op arguments bodies rest, _, map, table, env, image, holds, known => by
        unfold Region.normalize
        split
        · rename_i results found
          have earlier := Entry.find?_sound meaning normalizer.sameOp image table known op
            (map.operands arguments) results found (bodies.denote meaning)
          rw [holds.eval] at earlier
          show _ = (meaning.operation op (Operands.eval env arguments) (bodies.denote meaning)).bind _
          rw [earlier]
          exact Region.normalize_denote sound rest _ table _ image
            (Renaming.Holds.bindOperands _ holds results) known
        · rw [sound.reopen op (map.operands arguments) table image known (bodies.denote meaning) _
            (Regions.normalize_agrees sound bodies _)]
          show (meaning.operation op (Operands.eval image (map.operands arguments))
              (bodies.denote meaning)).bind _ =
            (meaning.operation op (Operands.eval env arguments) (bodies.denote meaning)).bind _
          rw [holds.eval]
          by_cases shared : (normalizer.sameOp op op).isSome = true
          · obtain ⟨values, returned⟩ | ⟨reason, stopped⟩ :=
              (sound.deterministic op shared).ends (Operands.eval env arguments)
                (bodies.denote meaning)
            · rw [returned]
              refine Region.normalize_denote sound rest _ _ _ _
                (Renaming.Holds.keepAll _ holds values) ?_
              refine TableHolds.after meaning normalizer.sameOp known op _ values ?_
              intro others _
              rw [holds.eval, (sound.deterministic op shared).closed _ others (bodies.denote meaning)]
              exact returned
            · rw [stopped]
              rfl
          · congr 1
            funext values
            refine Region.normalize_denote sound rest _ _ _ _
              (Renaming.Holds.keepAll _ holds values) ?_
            exact TableHolds.after meaning normalizer.sameOp known op _ values
              fun _ isShared => absurd isShared shared
    | _, _, .bind (mid := mid) body rest, _, map, table, env, image, holds, known => by
        show ((body.normalize normalizer map table).denote meaning image).bind _ =
          (body.denote meaning env).bind _
        rw [Region.normalize_denote sound body map table env image holds known]
        congr 1
        funext values
        exact Region.normalize_denote sound rest _ _ _ _
          (Renaming.Holds.keepAll _ holds values) (known.weaken meaning mid values)

  /-- The rebuilt regions agree with the old ones. -/
  theorem Regions.normalize_agrees {normalizer : Normalizer dialect}
      (sound : normalizer.Sound meaning) :
      ∀ {signatures signatures' : List (List dialect.Ty × List dialect.Ty)}
        (regions : Regions dialect signatures) (plan : Plan dialect signatures signatures'),
        Plan.Agrees meaning plan (regions.denote meaning)
          ((regions.normalize normalizer plan).denote meaning)
    | _, _, .nil, .nil => trivial
    | _, _, .cons body tail, .cons map table plan =>
        ⟨fun values values' holds known =>
            Region.normalize_denote sound body map table (Environment.ofValues values)
              (Environment.ofValues values') holds known,
          Regions.normalize_agrees sound tail plan⟩
end

/-- The normal form of a closed region keeps its denotation. -/
theorem Region.normal_denote {normalizer : Normalizer dialect} (sound : normalizer.Sound meaning)
    {inputs out : List dialect.Ty} (region : Region dialect (bindAll [] inputs) out)
    (values : Values meaning.Value inputs) :
    (region.normal normalizer).denote meaning (Environment.ofValues values) =
      region.denote meaning (Environment.ofValues values) :=
  (Region.normalize_denote sound region.flatten _ [] (Environment.ofValues values)
    (Environment.ofValues values)
    (Renaming.Holds.keepAll inputs ⟨fun reference => reference.elimNil⟩ values)
    (fun _ member => nomatch member)).trans (Region.flatten_denote meaning region values)

end Denote

end Zkc.Source
