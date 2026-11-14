module

public import Zkc.Core.Facts
public import Zkc.Core.Meaning

public section

/-! What the tracked facts say of an environment.

The check of facts names a value by its level. The *store* of an environment gives the
value at each level, with its type. `Facts.Holds` states what tracked facts mean for a
store: every bound contains its value, every order holds, every known condition is true,
and every shape is the operation that made the value, on the values at the levels it
names. Every statement names values that exist, so it survives when the store grows, and
it follows its values into a nested region when all of them are captured.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

variable {model : Model}

/-- The values of a context by level, each with its type. -/
abbrev Store (model : Model) := Nat → Option (Sigma model.Value)

theorem entry_eq {type : Ty} {first second : model.Value type}
    (same : (⟨type, first⟩ : Sigma model.Value) = ⟨type, second⟩) : first = second := by
  cases same; rfl

theorem store_eq {store : Store model} {level : Nat} {type : Ty} {first second : model.Value type}
    (one : store level = some ⟨type, first⟩) (other : store level = some ⟨type, second⟩) :
    first = second :=
  entry_eq (Option.some.inj (one.symm.trans other))

theorem store_length {store : Store model} {level : Nat} {element other : Ty}
    {size otherSize : Option Nat} {first : model.Value (.seq element size)}
    {second : model.Value (.seq other otherSize)}
    (one : store level = some ⟨_, first⟩) (two : store level = some ⟨_, second⟩) :
    (Ty.elements size first).length = (Ty.elements otherSize second).length := by
  have same := Option.some.inj (one.symm.trans two)
  cases same
  rfl

/-! ## Values by position -/

/-- The value at a position of a tuple of values, with its type. -/
@[expose] def entryOf : {types : List Ty} → Values model.Value types → Nat → Option (Sigma model.Value)
  | _, .nil, _ => none
  | _, .cons (ty := type) value _, 0 => some ⟨type, value⟩
  | _, .cons _ rest, index + 1 => entryOf rest index

theorem entryOf_append : ∀ {first rest : List Ty} (values : Values model.Value first)
    (others : Values model.Value rest) (index : Nat),
    entryOf (values.append others) (first.length + index) = entryOf others index
  | _, _, .nil, others, index => by
      show entryOf others (0 + index) = _
      rw [Nat.zero_add]
  | _, _, .cons value values, others, index => by
      rw [Values.cons_append, List.length_cons, Nat.add_right_comm]
      exact entryOf_append values others index

theorem entryOf_type : ∀ {types : List Ty} (values : Values model.Value types) (index : Nat)
    (type : Ty), types[index]? = some type →
      ∃ value : model.Value type, entryOf values index = some ⟨type, value⟩
  | _, .nil, _, _, found => nomatch found
  | _, .cons value _, 0, _, found => by
      cases Option.some.inj found
      exact ⟨value, rfl⟩
  | _, .cons _ rest, index + 1, type, found => entryOf_type rest index type found

/-- The values at the levels of a list are the values of a tuple, in order. -/
@[expose] def Reads (store : Store model) : List Nat → {types : List Ty} → Values model.Value types → Prop
  | [], _, .nil => True
  | level :: rest, _, .cons (ty := type) value values =>
      store level = some ⟨type, value⟩ ∧ Reads store rest values
  | [], _, .cons _ _ => False
  | _ :: _, _, .nil => False

theorem Reads.entry {store : Store model} : ∀ {levels : List Nat} {types : List Ty}
    {values : Values model.Value types}, Reads store levels values →
      ∀ (index level : Nat), levels[index]? = some level → entryOf values index = store level
  | [], _, .nil, _, _, _, found => nomatch found
  | level :: _, _, .cons _ _, reads, 0, _, found => by
      cases Option.some.inj found
      exact reads.1.symm
  | _ :: _, _, .cons _ _, reads, index + 1, level, found => reads.2.entry index level found
  | [], _, .cons _ _, reads, _, _, _ => reads.elim
  | _ :: _, _, .nil, reads, _, _, _ => reads.elim

/-- The values at the levels of a list are one tuple. -/
theorem Reads.unique {store : Store model} : ∀ {levels : List Nat} {types others : List Ty}
    {values : Values model.Value types} {values' : Values model.Value others},
    Reads store levels values → Reads store levels values' →
      (⟨types, values⟩ : (types : List Ty) × Values model.Value types) = ⟨others, values'⟩
  | [], _, _, .nil, .nil, _, _ => rfl
  | level :: rest, _, _, .cons value values, .cons value' values', one, two => by
      have head := Option.some.inj (one.1.symm.trans two.1)
      have tail := Reads.unique one.2 two.2
      cases head
      cases tail
      rfl
  | [], _, _, .cons _ _, _, one, _ => one.elim
  | [], _, _, .nil, .cons _ _, _, two => two.elim
  | _ :: _, _, _, .nil, _, one, _ => one.elim
  | _ :: _, _, _, .cons _ _, .nil, _, two => two.elim

theorem Reads.tail {store : Store model} {level : Nat} {levels : List Nat} {type : Ty}
    {types : List Ty} {values : Values model.Value (type :: types)}
    (reads : Reads store (level :: levels) values) : Reads store levels values.tail := by
  cases values with
  | cons value rest => exact reads.2

theorem Reads.head {store : Store model} {level : Nat} {levels : List Nat} {type : Ty}
    {types : List Ty} {values : Values model.Value (type :: types)}
    (reads : Reads store (level :: levels) values) :
    store level = some ⟨type, values.get .here⟩ := by
  cases values with
  | cons value rest => exact reads.1

/-- The values after a prefix are read at the levels after it. -/
theorem Reads.split {store : Store model} : ∀ (first : List Ty) {rest : List Ty}
    {levels : List Nat} {values : Values model.Value (first ++ rest)},
    Reads store levels values → Reads store (levels.drop first.length) (values.split first).2
  | [], _, _, _, reads => reads
  | _ :: first, _, [], .cons _ _, reads => reads.elim
  | _ :: first, _, _ :: _, .cons _ _, reads => Reads.split first reads.2

/-! ## The store of an environment -/

section Environment

variable {Γ : List Ty}

/-- The value at a position of an environment, the most recent first. -/
@[expose] def entryAt (env : Environment model.Value Γ) (index : Nat) : Option (Sigma model.Value) :=
  match found : Γ[index]? with
  | some type => some ⟨type, env ⟨index, found⟩⟩
  | none => none

/-- The store of an environment: the value at a level, counted from the oldest. -/
@[expose] def storeOf (env : Environment model.Value Γ) : Store model := fun level =>
  if level < Γ.length then entryAt env (Γ.length - 1 - level) else none

theorem entryAt_index (env : Environment model.Value Γ) {type : Ty} (reference : Var Γ type) :
    entryAt env reference.index = some ⟨type, env reference⟩ := by
  unfold entryAt
  split
  · rename_i other found
    have same : other = type := Option.some.inj (found.symm.trans reference.valid)
    subst same
    rfl
  · rename_i missing
    rw [reference.valid] at missing
    cases missing

/-- The value at the level of a reference is the value of the reference. -/
theorem storeOf_number (env : Environment model.Value Γ) {type : Ty} (reference : Var Γ type) :
    storeOf env (Scope.number Γ.length reference) = some ⟨type, env reference⟩ := by
  have bound := reference.index_lt
  have below : Scope.number Γ.length reference < Γ.length := by
    simp only [Scope.number, Scope.position]; omega
  have back : Γ.length - 1 - Scope.number Γ.length reference = reference.index := by
    simp only [Scope.number, Scope.position]; omega
  simp only [storeOf, below, ↓reduceIte, back, entryAt_index]

theorem storeOf_defined (env : Environment model.Value Γ) {level : Nat} (below : level < Γ.length) :
    ∃ entry, storeOf env level = some entry := by
  have inside : Γ.length - 1 - level < Γ.length := by omega
  simp only [storeOf, below, ↓reduceIte]
  unfold entryAt
  split
  · exact ⟨_, rfl⟩
  · rename_i missing
    rw [List.getElem?_eq_getElem inside] at missing
    cases missing

theorem storeOf_none (env : Environment model.Value Γ) {level : Nat} (beyond : Γ.length ≤ level) :
    storeOf env level = none := by
  simp only [storeOf, Nat.not_lt.mpr beyond, ↓reduceIte]

theorem entryAt_push_succ (env : Environment model.Value Γ) {type : Ty} (value : model.Value type)
    (index : Nat) : entryAt (env.push value) (index + 1) = entryAt env index := rfl

theorem entryAt_push_zero (env : Environment model.Value Γ) {type : Ty} (value : model.Value type) :
    entryAt (env.push value) 0 = some ⟨type, value⟩ := rfl

/-- The store after one more value: the earlier levels are unchanged, and the new level
has the value. -/
theorem storeOf_push (env : Environment model.Value Γ) {type : Ty} (value : model.Value type)
    (level : Nat) :
    storeOf (env.push value) level =
      if level < Γ.length then storeOf env level
      else if level = Γ.length then some ⟨type, value⟩ else none := by
  by_cases earlier : level < Γ.length
  · have below : level < (type :: Γ).length := by rw [List.length_cons]; omega
    have position : (type :: Γ).length - 1 - level = (Γ.length - 1 - level) + 1 := by
      rw [List.length_cons]; omega
    simp only [storeOf, below, earlier, ↓reduceIte, position, entryAt_push_succ]
  · by_cases same : level = Γ.length
    · subst same
      have below : Γ.length < (type :: Γ).length := by rw [List.length_cons]; omega
      have position : (type :: Γ).length - 1 - Γ.length = 0 := by rw [List.length_cons]; omega
      simp only [storeOf, below, ↓reduceIte, position, entryAt_push_zero, Nat.lt_irrefl]
    · have beyond : ¬ level < (type :: Γ).length := by rw [List.length_cons]; omega
      simp only [storeOf, beyond, earlier, same, ↓reduceIte]

/-- The store after more values: the earlier levels are unchanged, and the new levels
have the new values, in order. -/
theorem storeOf_bindAll : ∀ {added : List Ty} {Γ : List Ty} (env : Environment model.Value Γ)
    (values : Values model.Value added) (level : Nat),
    storeOf (Environment.bindAll env values) level =
      if level < Γ.length then storeOf env level else entryOf values (level - Γ.length)
  | _, Γ, env, .nil, level => by
      by_cases earlier : level < Γ.length
      · simp only [earlier, ↓reduceIte]; rfl
      · simp only [earlier, ↓reduceIte]
        exact storeOf_none env (Nat.not_lt.mp earlier)
  | _, Γ, env, .cons (ty := type) value values, level => by
      refine (storeOf_bindAll (env.push value) values level).trans ?_
      have pushed := storeOf_push env value level
      by_cases earlier : level < Γ.length
      · have below : level < (type :: Γ).length := by rw [List.length_cons]; omega
        simp only [earlier, ↓reduceIte] at pushed
        simp only [earlier, below, ↓reduceIte]
        exact pushed
      · by_cases same : level = Γ.length
        · subst same
          have below : Γ.length < (type :: Γ).length := by rw [List.length_cons]; omega
          simp only [Nat.lt_irrefl, ↓reduceIte] at pushed
          simp only [below, ↓reduceIte, Nat.lt_irrefl, Nat.sub_self]
          exact pushed
        · have beyond : ¬ level < (type :: Γ).length := by rw [List.length_cons]; omega
          have position : level - Γ.length = (level - (type :: Γ).length) + 1 := by
            rw [List.length_cons]; omega
          simp only [earlier, beyond, ↓reduceIte, position]
          rfl

/-- The store of a region's inputs is the inputs by position. -/
theorem storeOf_ofValues {types : List Ty} (values : Values model.Value types) (level : Nat) :
    storeOf (Environment.ofValues values) level = entryOf values level := by
  have bound := storeOf_bindAll (Environment.empty (Value := model.Value)) values level
  simp only [List.length_nil, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero] at bound
  exact bound

/-- The operands of an instruction are read at their levels. -/
theorem reads_eval (env : Environment model.Value Γ) : ∀ {types : List Ty}
    (operands : Operands Γ types),
    Reads (storeOf env) (Scope.numbers Γ.length operands) (Operands.eval env operands)
  | _, .nil => trivial
  | _, .cons reference rest => ⟨storeOf_number env reference, reads_eval env rest⟩

end Environment

/-! ## What facts say of a store -/

/-- The value `entry` has a shape: it is the result of the shape's operation on the values
at the levels that the shape names. -/
@[expose] def Shape.Holds (store : Store model) (entry : Sigma model.Value) : Shape → Prop
  | .other => True
  | .add left right =>
      ∃ x y : Nat, store left = some ⟨.nat, x⟩ ∧ store right = some ⟨.nat, y⟩ ∧
        entry = ⟨.nat, (x + y : Nat)⟩
  | .sub left right =>
      ∃ x y : Nat, store left = some ⟨.nat, x⟩ ∧ store right = some ⟨.nat, y⟩ ∧ y ≤ x ∧
        entry = ⟨.nat, (x - y : Nat)⟩
  | .length sequence =>
      ∃ (element : Ty) (size : Option Nat) (values : model.Value (.seq element size)),
        store sequence = some ⟨.seq element size, values⟩ ∧
          entry = ⟨.nat, (Ty.elements size values).length⟩
  | .toNat value =>
      ∃ (bound : Nat) (number : Fin bound), store value = some ⟨.fin bound, number⟩ ∧
        entry = ⟨.nat, number.val⟩
  | .less left right =>
      ∃ x y : Nat, store left = some ⟨.nat, x⟩ ∧ store right = some ⟨.nat, y⟩ ∧
        entry = ⟨.bool, Nat.blt x y⟩
  | .equal left right =>
      ∃ x y : Nat, store left = some ⟨.nat, x⟩ ∧ store right = some ⟨.nat, y⟩ ∧
        entry = ⟨.bool, Nat.beq x y⟩
  | .not condition =>
      ∃ p : Bool, store condition = some ⟨.bool, p⟩ ∧ entry = ⟨.bool, !p⟩
  | .and left right =>
      ∃ p q : Bool, store left = some ⟨.bool, p⟩ ∧ store right = some ⟨.bool, q⟩ ∧
        entry = ⟨.bool, p && q⟩
  | .or left right =>
      ∃ p q : Bool, store left = some ⟨.bool, p⟩ ∧ store right = some ⟨.bool, q⟩ ∧
        entry = ⟨.bool, p || q⟩
  | .domain row operands =>
      ∃ (inputs : List Ty) (arguments : Values model.Value inputs),
        Reads store operands arguments ∧
          entry = ⟨.bool, (model.pure ⟨row, inputs, [.bool]⟩ allPopulated_bool arguments).get .here⟩
  | .conjunct condition =>
      ∃ p : Bool, store condition = some ⟨.bool, p⟩ ∧ (entry = ⟨.bool, true⟩ → p = true)
  | .disjunct condition =>
      ∃ p : Bool, store condition = some ⟨.bool, p⟩ ∧ (entry = ⟨.bool, false⟩ → p = false)

/-- What the facts say of a store. -/
structure Facts.Holds (store : Store model) (facts : Facts) : Prop where
  shapes : ∀ (level : Nat) (entry : Sigma model.Value), store level = some entry →
    (facts.shape level).Holds store entry
  bounds : ∀ bound ∈ facts.bounds, ∃ value : Nat, store bound.level = some ⟨.nat, value⟩ ∧
    bound.lo ≤ value ∧ ∀ hi, bound.hi = some hi → value ≤ hi
  orders : ∀ order ∈ facts.orders, ∃ x y : Nat, store order.left = some ⟨.nat, x⟩ ∧
    store order.right = some ⟨.nat, y⟩ ∧ x ≤ y ∧ (order.strict = true → x < y)
  known : ∀ condition ∈ facts.known, store condition = some ⟨.bool, true⟩
  alive : facts.dead = false

/-- The facts hold of an environment: they have a shape for each of its values, and they
hold of its store. -/
structure Facts.Sound (facts : Facts) {Γ : List Ty} (env : Environment model.Value Γ) : Prop where
  depth : facts.depth = Γ.length
  holds : facts.Holds (storeOf env)

/-! ## Lower and upper ends -/

theorem lowest_le {store : Store model} {level value : Nat}
    (found : store level = some ⟨.nat, value⟩) : ∀ (bounds : List Bound),
    (∀ bound ∈ bounds, ∃ value : Nat, store bound.level = some ⟨.nat, value⟩ ∧
      bound.lo ≤ value ∧ ∀ hi, bound.hi = some hi → value ≤ hi) →
    lowest bounds level ≤ value
  | [], _ => Nat.zero_le _
  | bound :: rest, holds => by
      have later := lowest_le found rest fun other member =>
        holds other (List.mem_cons_of_mem _ member)
      unfold lowest
      split
      · rename_i same
        obtain ⟨other, at_, low, _⟩ := holds bound (List.mem_cons_self ..)
        rw [same] at at_
        have equal := store_eq at_ found
        subst equal
        exact Nat.max_le.mpr ⟨low, later⟩
      · exact later

theorem le_highest {store : Store model} {level value : Nat}
    (found : store level = some ⟨.nat, value⟩) : ∀ (bounds : List Bound),
    (∀ bound ∈ bounds, ∃ value : Nat, store bound.level = some ⟨.nat, value⟩ ∧
      bound.lo ≤ value ∧ ∀ hi, bound.hi = some hi → value ≤ hi) →
    ∀ hi, highest bounds level = some hi → value ≤ hi
  | [], _, _, found => nomatch found
  | bound :: rest, holds, hi, at_ => by
      have later := le_highest found rest fun other member =>
        holds other (List.mem_cons_of_mem _ member)
      unfold highest at at_
      split at at_
      · rename_i same
        obtain ⟨other, here, _, high⟩ := holds bound (List.mem_cons_self ..)
        rw [same] at here
        have equal := store_eq here found
        subst equal
        cases first : bound.hi with
        | none =>
            rw [first] at at_
            exact later hi at_
        | some end_ =>
            rw [first] at at_
            have one := high end_ first
            cases second : highest rest level with
            | none =>
                rw [second] at at_
                cases Option.some.inj at_
                exact one
            | some other =>
                rw [second] at at_
                have two := later other second
                cases Option.some.inj at_
                exact Nat.le_min.mpr ⟨one, two⟩
      · exact later hi at_

theorem Facts.Holds.lo_le {store : Store model} {facts : Facts} (holds : facts.Holds store)
    {level value : Nat} (found : store level = some ⟨.nat, value⟩) : facts.lo level ≤ value :=
  lowest_le found facts.bounds holds.bounds

theorem Facts.Holds.le_hi {store : Store model} {facts : Facts} (holds : facts.Holds store)
    {level value hi : Nat} (found : store level = some ⟨.nat, value⟩)
    (at_ : facts.hi level = some hi) : value ≤ hi :=
  le_highest found facts.bounds holds.bounds hi at_

theorem within_le {hi : Option Nat} {limit : Nat} (holds : within hi limit = true) :
    ∃ end_, hi = some end_ ∧ end_ ≤ limit := by
  cases hi with
  | none => cases holds
  | some end_ => exact ⟨end_, rfl, of_decide_eq_true holds⟩

theorem below_lt {hi : Option Nat} {limit : Nat} (holds : below hi limit = true) :
    ∃ end_, hi = some end_ ∧ end_ < limit := by
  cases hi with
  | none => cases holds
  | some end_ => exact ⟨end_, rfl, of_decide_eq_true holds⟩

/-- A point interval is its value. -/
theorem Facts.Holds.point_eq {store : Store model} {facts : Facts} (holds : facts.Holds store)
    {level value point : Nat} (found : store level = some ⟨.nat, value⟩)
    (at_ : facts.point level point = true) : value = point := by
  simp only [Facts.point, Bool.and_eq_true, decide_eq_true_eq] at at_
  obtain ⟨end_, high, most⟩ := within_le at_.2
  have low := holds.lo_le found
  have top := holds.le_hi found high
  omega

/-! ## Growing and renaming -/

/-- Every value of one store that a renaming keeps is the value of the other store at the
renamed level. -/
@[expose] def Maps (rename : Nat → Option Nat) (store other : Store model) : Prop :=
  ∀ (level inner : Nat) (entry : Sigma model.Value), rename level = some inner →
    store level = some entry → other inner = some entry

theorem Reads.rename {rename : Nat → Option Nat} {store other : Store model}
    (maps : Maps rename store other) : ∀ {levels inner : List Nat} {types : List Ty}
    {values : Values model.Value types}, Facts.renameAll rename levels = some inner →
      Reads store levels values → Reads other inner values
  | [], _, _, .nil, renamed, _ => by
      cases Option.some.inj renamed
      trivial
  | level :: rest, inner, _, .cons value values, renamed, reads => by
      unfold Facts.renameAll at renamed
      split at renamed
      · rename_i first others head tail
        cases Option.some.inj renamed
        exact ⟨maps _ _ _ head reads.1, Reads.rename maps tail reads.2⟩
      · cases renamed
  | [], _, _, .cons _ _, _, reads => reads.elim
  | _ :: _, _, _, .nil, _, reads => reads.elim

theorem Shape.Holds.rename {rename : Nat → Option Nat} {store other : Store model}
    (maps : Maps rename store other) {entry : Sigma model.Value} :
    ∀ {shape : Shape}, shape.Holds store entry → (shape.rename rename).Holds other entry
  | .other, _ => trivial
  | .add left right, holds => by
      obtain ⟨x, y, first, second, value⟩ := holds
      cases one : rename left with
      | none => simp only [Shape.rename, one]; trivial
      | some a =>
          cases two : rename right with
          | none => simp only [Shape.rename, one, two]; trivial
          | some b =>
              simp only [Shape.rename, one, two]
              exact ⟨x, y, maps _ _ _ one first, maps _ _ _ two second, value⟩
  | .sub left right, holds => by
      obtain ⟨x, y, first, second, least, value⟩ := holds
      cases one : rename left with
      | none => simp only [Shape.rename, one]; trivial
      | some a =>
          cases two : rename right with
          | none => simp only [Shape.rename, one, two]; trivial
          | some b =>
              simp only [Shape.rename, one, two]
              exact ⟨x, y, maps _ _ _ one first, maps _ _ _ two second, least, value⟩
  | .length sequence, holds => by
      obtain ⟨element, size, values, first, value⟩ := holds
      cases one : rename sequence with
      | none => simp only [Shape.rename, one]; trivial
      | some a =>
          simp only [Shape.rename, one]
          exact ⟨element, size, values, maps _ _ _ one first, value⟩
  | .toNat number, holds => by
      obtain ⟨bound, index, first, value⟩ := holds
      cases one : rename number with
      | none => simp only [Shape.rename, one]; trivial
      | some a =>
          simp only [Shape.rename, one]
          exact ⟨bound, index, maps _ _ _ one first, value⟩
  | .less left right, holds => by
      obtain ⟨x, y, first, second, value⟩ := holds
      cases one : rename left with
      | none => simp only [Shape.rename, one]; trivial
      | some a =>
          cases two : rename right with
          | none => simp only [Shape.rename, one, two]; trivial
          | some b =>
              simp only [Shape.rename, one, two]
              exact ⟨x, y, maps _ _ _ one first, maps _ _ _ two second, value⟩
  | .equal left right, holds => by
      obtain ⟨x, y, first, second, value⟩ := holds
      cases one : rename left with
      | none => simp only [Shape.rename, one]; trivial
      | some a =>
          cases two : rename right with
          | none => simp only [Shape.rename, one, two]; trivial
          | some b =>
              simp only [Shape.rename, one, two]
              exact ⟨x, y, maps _ _ _ one first, maps _ _ _ two second, value⟩
  | .not condition, holds => by
      obtain ⟨p, first, value⟩ := holds
      cases one : rename condition with
      | none => simp only [Shape.rename, one]; trivial
      | some a =>
          simp only [Shape.rename, one]
          exact ⟨p, maps _ _ _ one first, value⟩
  | .and left right, holds => by
      obtain ⟨p, q, first, second, value⟩ := holds
      cases one : rename left with
      | none => simp only [Shape.rename, one]; trivial
      | some a =>
          cases two : rename right with
          | none => simp only [Shape.rename, one, two]; trivial
          | some b =>
              simp only [Shape.rename, one, two]
              exact ⟨p, q, maps _ _ _ one first, maps _ _ _ two second, value⟩
  | .or left right, holds => by
      obtain ⟨p, q, first, second, value⟩ := holds
      cases one : rename left with
      | none => simp only [Shape.rename, one]; trivial
      | some a =>
          cases two : rename right with
          | none => simp only [Shape.rename, one, two]; trivial
          | some b =>
              simp only [Shape.rename, one, two]
              exact ⟨p, q, maps _ _ _ one first, maps _ _ _ two second, value⟩
  | .domain row operands, holds => by
      obtain ⟨inputs, arguments, reads, value⟩ := holds
      cases renamed : Facts.renameAll rename operands with
      | none => simp only [Shape.rename, renamed]; trivial
      | some inner =>
          simp only [Shape.rename, renamed]
          exact ⟨inputs, arguments, reads.rename maps renamed, value⟩
  | .conjunct condition, holds => by
      obtain ⟨p, first, value⟩ := holds
      cases one : rename condition with
      | none => simp only [Shape.rename, one]; trivial
      | some a =>
          simp only [Shape.rename, one]
          exact ⟨p, maps _ _ _ one first, value⟩
  | .disjunct condition, holds => by
      obtain ⟨p, first, value⟩ := holds
      cases one : rename condition with
      | none => simp only [Shape.rename, one]; trivial
      | some a =>
          simp only [Shape.rename, one]
          exact ⟨p, maps _ _ _ one first, value⟩

theorem Facts.renameAll_some : ∀ (levels : List Nat), Facts.renameAll some levels = some levels
  | [] => rfl
  | level :: rest => by
      unfold Facts.renameAll
      rw [Facts.renameAll_some rest]

theorem Shape.rename_some (shape : Shape) : shape.rename some = shape := by
  cases shape <;> simp only [Shape.rename, Facts.renameAll_some]

/-- A shape of a value still holds when the store has more values. -/
theorem Shape.Holds.grow {store other : Store model}
    (grows : ∀ level entry, store level = some entry → other level = some entry)
    {entry : Sigma model.Value} {shape : Shape} (holds : shape.Holds store entry) :
    shape.Holds other entry := by
  have renamed := holds.rename (rename := some) (other := other) fun level inner entry same found => by
    cases Option.some.inj same
    exact grows level entry found
  rwa [Shape.rename_some] at renamed

/-! ## New facts -/

theorem Facts.Holds.bound {store : Store model} {facts : Facts} (holds : facts.Holds store)
    {level lo value : Nat} {hi : Option Nat} (found : store level = some ⟨.nat, value⟩)
    (low : lo ≤ value) (high : ∀ end_, hi = some end_ → value ≤ end_) :
    (facts.bound level lo hi).Holds store :=
  { shapes := holds.shapes
    bounds := fun bound member => by
      rcases List.mem_cons.mp member with rfl | earlier
      · exact ⟨value, found, low, high⟩
      · exact holds.bounds bound earlier
    orders := holds.orders
    known := holds.known
    alive := holds.alive }

theorem Facts.Holds.order {store : Store model} {facts : Facts} (holds : facts.Holds store)
    {strict : Bool} {left right x y : Nat} (first : store left = some ⟨.nat, x⟩)
    (second : store right = some ⟨.nat, y⟩) (most : x ≤ y) (less : strict = true → x < y) :
    (facts.order strict left right).Holds store :=
  { shapes := holds.shapes
    bounds := holds.bounds
    orders := fun order member => by
      rcases List.mem_cons.mp member with rfl | earlier
      · exact ⟨x, y, first, second, most, less⟩
      · exact holds.orders order earlier
    known := holds.known
    alive := holds.alive }

theorem Facts.Holds.mark {store : Store model} {facts : Facts} (holds : facts.Holds store)
    {condition : Nat} (found : store condition = some ⟨.bool, true⟩) :
    (facts.mark condition).Holds store :=
  { shapes := holds.shapes
    bounds := holds.bounds
    orders := holds.orders
    known := fun other member => by
      rcases List.mem_cons.mp member with rfl | earlier
      · exact found
      · exact holds.known other earlier
    alive := holds.alive }

/-- The facts of a condition that has the given truth hold. -/
theorem Facts.Holds.assume {store : Store model} : ∀ (fuel : Nat) {facts : Facts}
    {condition : Nat} {truth : Bool}, facts.Holds store →
      store condition = some ⟨.bool, truth⟩ → (facts.assume fuel condition truth).Holds store
  | 0, facts, condition, truth, holds, found => by
      cases truth with
      | false => exact holds
      | true => exact holds.mark found
  | fuel + 1, facts, condition, truth, holds, found => by
      have marked : (cond truth (facts.mark condition) facts).Holds store := by
        cases truth with
        | false => exact holds
        | true => exact holds.mark found
      have shaped := holds.shapes condition _ found
      unfold Facts.assume
      split
      · -- `left < right` holds.
        rename_i left right shape
        rw [shape] at shaped
        obtain ⟨x, y, first, second, value⟩ := shaped
        have less : x < y := Nat.blt_eq.mp (entry_eq value).symm
        refine ((marked.order (strict := true) first second (Nat.le_of_lt less) fun _ => less).bound first
          (Nat.zero_le _) ?_).bound second ?_ (fun _ absent => nomatch absent)
        · intro end_ at_
          cases high : facts.hi right with
          | none => rw [high] at at_; cases at_
          | some top =>
              rw [high] at at_
              have most := holds.le_hi second high
              cases Option.some.inj at_
              omega
        · have low := holds.lo_le first
          omega
      · -- `left < right` does not hold.
        rename_i left right shape
        rw [shape] at shaped
        obtain ⟨x, y, first, second, value⟩ := shaped
        have notLess : ¬ x < y := fun less =>
          Bool.false_ne_true ((entry_eq value).trans (Nat.blt_eq.mpr less))
        have most : y ≤ x := Nat.le_of_not_lt notLess
        refine ((marked.order (strict := false) second first most Bool.noConfusion).bound second
          (Nat.zero_le _) ?_).bound first ?_ (fun _ absent => nomatch absent)
        · intro end_ at_
          exact Nat.le_trans most (holds.le_hi first at_)
        · exact Nat.le_trans (holds.lo_le second) most
      · -- `left == right` holds.
        rename_i left right shape
        rw [shape] at shaped
        obtain ⟨x, y, first, second, value⟩ := shaped
        have same : x = y := Nat.eq_of_beq_eq_true (entry_eq value).symm
        subst same
        refine (((marked.order (strict := false) first second (Nat.le_refl _)
          Bool.noConfusion).order (strict := false) second first (Nat.le_refl _)
          Bool.noConfusion).bound first
          (holds.lo_le second) fun end_ at_ => holds.le_hi second at_).bound second
          (holds.lo_le first) fun end_ at_ => holds.le_hi first at_
      · -- `left == right` does not hold.
        rename_i left right shape
        rw [shape] at shaped
        obtain ⟨x, y, first, second, value⟩ := shaped
        have differ : x ≠ y := fun same => by
          subst same
          exact Bool.false_ne_true ((entry_eq value).trans (Nat.beq_refl x))
        have one : (cond (within (facts.hi right) 0)
            ((cond false (facts.mark condition) facts).bound left 1 none)
            (cond false (facts.mark condition) facts)).Holds store := by
          cases zero : within (facts.hi right) 0 with
          | false => exact marked
          | true =>
              obtain ⟨end_, high, most⟩ := within_le zero
              have top := holds.le_hi second high
              exact marked.bound first (by omega) fun _ absent => nomatch absent
        cases zero : within (facts.hi left) 0 with
        | false => exact one
        | true =>
            obtain ⟨end_, high, most⟩ := within_le zero
            have top := holds.le_hi first high
            exact one.bound second (by omega) fun _ absent => nomatch absent
      · -- `not inner`.
        rename_i truth _ _ inner shape
        rw [shape] at shaped
        obtain ⟨p, first, value⟩ := shaped
        have negated : truth = !p := entry_eq value
        have back : p = !truth := by rw [negated, Bool.not_not]
        rw [back] at first
        exact Facts.Holds.assume fuel marked first
      · -- `left and right` holds.
        rename_i left right shape
        rw [shape] at shaped
        obtain ⟨p, q, first, second, value⟩ := shaped
        have both : (p && q) = true := (entry_eq value).symm
        rw [Bool.and_eq_true] at both
        rw [both.1] at first
        rw [both.2] at second
        exact Facts.Holds.assume fuel (Facts.Holds.assume fuel marked first) second
      · -- `left or right` does not hold.
        rename_i left right shape
        rw [shape] at shaped
        obtain ⟨p, q, first, second, value⟩ := shaped
        have neither : (p || q) = false := (entry_eq value).symm
        rw [Bool.or_eq_false_iff] at neither
        rw [neither.1] at first
        rw [neither.2] at second
        exact Facts.Holds.assume fuel (Facts.Holds.assume fuel marked first) second
      · -- The result of an `if` that is a conjunction holds: so does its condition.
        rename_i inner shape
        rw [shape] at shaped
        obtain ⟨p, first, implies⟩ := shaped
        rw [implies rfl] at first
        exact Facts.Holds.assume fuel marked first
      · -- The result of an `if` that is a disjunction does not hold: nor does its condition.
        rename_i inner shape
        rw [shape] at shaped
        obtain ⟨p, first, implies⟩ := shaped
        rw [implies rfl] at first
        exact Facts.Holds.assume fuel marked first
      · exact marked

/-- A condition gives facts and no values. -/
theorem Facts.assume_shapes : ∀ (fuel : Nat) (facts : Facts) (condition : Nat) (truth : Bool),
    (facts.assume fuel condition truth).shapes = facts.shapes
  | 0, facts, condition, truth => by cases truth <;> rfl
  | fuel + 1, facts, condition, truth => by
      have marked : (cond truth (facts.mark condition) facts).shapes = facts.shapes := by
        cases truth <;> rfl
      unfold Facts.assume
      split
      · exact marked
      · exact marked
      · exact marked
      · cases within (facts.hi _) 0 <;> cases within (facts.hi _) 0 <;> exact marked
      · rw [Facts.assume_shapes fuel]; exact marked
      · rw [Facts.assume_shapes fuel, Facts.assume_shapes fuel]; exact marked
      · rw [Facts.assume_shapes fuel, Facts.assume_shapes fuel]; exact marked
      · rw [Facts.assume_shapes fuel]; exact marked
      · rw [Facts.assume_shapes fuel]; exact marked
      · exact marked

theorem Facts.Sound.assume {Γ : List Ty} {env : Environment model.Value Γ} {facts : Facts}
    (sound : facts.Sound env) (fuel : Nat) {condition : Nat} {truth : Bool}
    (found : storeOf env condition = some ⟨.bool, truth⟩) :
    (facts.assume fuel condition truth).Sound env :=
  ⟨by rw [Facts.depth, Facts.assume_shapes]; exact sound.1, sound.2.assume fuel found⟩

/-! ## What is known holds -/

theorem Facts.shape_defined {facts : Facts} {level : Nat} (shaped : facts.shape level ≠ .other) :
    level < facts.depth := by
  apply Classical.byContradiction
  intro beyond
  apply shaped
  simp only [Facts.shape, Facts.depth] at beyond ⊢
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt beyond)]
  rfl

theorem Facts.Holds.knownLe {store : Store model} {facts : Facts} (holds : facts.Holds store)
    {left right x y : Nat} (first : store left = some ⟨.nat, x⟩)
    (second : store right = some ⟨.nat, y⟩) (known : facts.knownLe left right = true) :
    x ≤ y := by
  simp only [Facts.knownLe, Bool.or_eq_true, decide_eq_true_eq] at known
  rcases known with (((byInterval | same) | byOrder) | bySum) | byDifference
  · obtain ⟨end_, high, most⟩ := within_le byInterval
    have top := holds.le_hi first high
    have low := holds.lo_le second
    omega
  · subst same
    exact Nat.le_of_eq (store_eq first second)
  · obtain ⟨order, member, names⟩ := List.any_eq_true.mp byOrder
    simp only [Bool.and_eq_true, decide_eq_true_eq] at names
    obtain ⟨a, b, one, two, most, _⟩ := holds.orders order member
    rw [names.1] at one
    rw [names.2] at two
    rw [store_eq first one, store_eq second two]
    exact most
  · have shaped := holds.shapes right _ second
    split at bySum
    · rename_i a b shape
      rw [shape] at shaped
      obtain ⟨p, q, one, two, value⟩ := shaped
      have sum : y = p + q := entry_eq value
      simp only [Bool.or_eq_true, decide_eq_true_eq] at bySum
      rcases bySum with rfl | rfl
      · have : (x : Nat) = p := store_eq first one
        omega
      · have : (x : Nat) = q := store_eq first two
        omega
    · cases bySum
  · have shaped := holds.shapes left _ first
    split at byDifference
    · rename_i a b shape
      rw [shape] at shaped
      obtain ⟨p, q, one, two, least, value⟩ := shaped
      have difference : x = p - q := entry_eq value
      have same : a = right := of_decide_eq_true byDifference
      subst same
      have : (y : Nat) = p := store_eq second one
      omega
    · cases byDifference

theorem Facts.Holds.knownLt {store : Store model} {facts : Facts} (holds : facts.Holds store)
    {left right x y : Nat} (first : store left = some ⟨.nat, x⟩)
    (second : store right = some ⟨.nat, y⟩) (known : facts.knownLt left right = true) :
    x < y := by
  simp only [Facts.knownLt, Bool.or_eq_true] at known
  rcases known with ((byInterval | byOrder) | bySum) | byShape
  · obtain ⟨end_, high, most⟩ := below_lt byInterval
    have top := holds.le_hi first high
    have low := holds.lo_le second
    omega
  · obtain ⟨order, member, names⟩ := List.any_eq_true.mp byOrder
    simp only [Bool.and_eq_true, decide_eq_true_eq] at names
    obtain ⟨a, b, one, two, _, less⟩ := holds.orders order member
    rw [names.1.2] at one
    rw [names.2] at two
    rw [store_eq first one, store_eq second two]
    exact less names.1.1
  · have shaped := holds.shapes right _ second
    split at bySum
    · rename_i a b shape
      rw [shape] at shaped
      obtain ⟨p, q, one, two, value⟩ := shaped
      have sum : y = p + q := entry_eq value
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at bySum
      rcases bySum with ⟨rfl, positive⟩ | ⟨rfl, positive⟩
      · have : (x : Nat) = p := store_eq first one
        have := holds.lo_le two
        omega
      · have : (x : Nat) = q := store_eq first two
        have := holds.lo_le one
        omega
    · cases bySum
  · have shaped := holds.shapes left _ first
    split at byShape
    · rename_i a b shape
      rw [shape] at shaped
      obtain ⟨p, q, one, two, least, value⟩ := shaped
      have difference : x = p - q := entry_eq value
      simp only [Bool.and_eq_true, decide_eq_true_eq] at byShape
      obtain ⟨rfl, positive⟩ := byShape
      have : (y : Nat) = p := store_eq second one
      have := holds.lo_le two
      omega
    · rename_i a b shape
      rw [shape] at shaped
      obtain ⟨p, q, one, two, value⟩ := shaped
      have sum : x = p + q := entry_eq value
      obtain ⟨order, member, names⟩ := List.any_eq_true.mp byShape
      simp only [Bool.and_eq_true] at names
      obtain ⟨u, d, lower, upper, _, less⟩ := holds.orders order member
      have strict := less names.1
      have limit := holds.shapes order.right _ upper
      have end_ := names.2
      split at end_
      · rename_i whole start shape'
        rw [shape'] at limit
        obtain ⟨w, s, three, four, least, value'⟩ := limit
        have difference : d = w - s := entry_eq value'
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at end_
        obtain ⟨rfl, sides⟩ := end_
        have : (y : Nat) = w := store_eq second three
        rcases sides with ⟨index, rfl⟩ | ⟨index, rfl⟩
        · rw [index] at lower
          have : (u : Nat) = q := store_eq lower two
          have : (s : Nat) = p := store_eq four one
          omega
        · rw [index] at lower
          have : (u : Nat) = p := store_eq lower one
          have : (s : Nat) = q := store_eq four two
          omega
      · cases end_
    · cases byShape

/-! ## Binding results -/

/-- The facts after new values hold of the environment that binds them, when the new
shapes are the shapes of the new values and the new bounds contain them. -/
theorem Facts.Sound.after {Γ added : List Ty} {env : Environment model.Value Γ} {facts : Facts}
    (sound : facts.Sound env) (values : Values model.Value added) (shapes : List Shape)
    (bounds : List Bound) (counted : shapes.length = added.length)
    (shaped : ∀ (index : Nat) (entry : Sigma model.Value), entryOf values index = some entry →
      (shapes.getD index .other).Holds (storeOf env) entry)
    (bounded : ∀ bound ∈ bounds, ∃ (index value : Nat), bound.level = Γ.length + index ∧
      entryOf values index = some ⟨.nat, value⟩ ∧ bound.lo ≤ value ∧
        ∀ hi, bound.hi = some hi → value ≤ hi) :
    (facts.after shapes bounds).Sound (Environment.bindAll env values) := by
  obtain ⟨depth, holds⟩ := sound
  have length : facts.shapes.length = Γ.length := depth
  have grows : ∀ level entry, storeOf env level = some entry →
      storeOf (Environment.bindAll env values) level = some entry := by
    intro level entry found
    rw [storeOf_bindAll]
    by_cases earlier : level < Γ.length
    · simp only [earlier, ↓reduceIte]; exact found
    · rw [storeOf_none env (Nat.not_lt.mp earlier)] at found
      cases found
  refine ⟨?_, ?_, ?_, ?_, ?_, holds.alive⟩
  · show (facts.shapes ++ shapes).length = _
    rw [List.length_append, length_bindAll, length, counted]
  · intro level entry found
    rw [storeOf_bindAll] at found
    show ((facts.shapes ++ shapes).getD level .other).Holds _ entry
    by_cases earlier : level < Γ.length
    · simp only [earlier, ↓reduceIte] at found
      have old := holds.shapes level entry found
      have same : (facts.shapes ++ shapes).getD level .other = facts.shape level := by
        simp only [Facts.shape, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by rw [length]; exact earlier)]
      rw [same]
      exact old.grow grows
    · simp only [earlier, ↓reduceIte] at found
      have same : (facts.shapes ++ shapes).getD level .other =
          shapes.getD (level - Γ.length) .other := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by rw [length]; exact Nat.not_lt.mp earlier), length]
      rw [same]
      exact (shaped _ entry found).grow grows
  · intro bound member
    rcases List.mem_append.mp member with new | old
    · obtain ⟨index, value, level, found, low, high⟩ := bounded bound new
      refine ⟨value, ?_, low, high⟩
      rw [level, storeOf_bindAll]
      simp only [Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte, Nat.add_sub_cancel_left]
      exact found
    · obtain ⟨value, found, low, high⟩ := holds.bounds bound old
      exact ⟨value, grows _ _ found, low, high⟩
  · intro order member
    obtain ⟨x, y, first, second, most, less⟩ := holds.orders order member
    exact ⟨x, y, grows _ _ first, grows _ _ second, most, less⟩
  · intro condition member
    exact grows _ _ (holds.known condition member)

/-- A shape that the value at a level has may replace the one tracked for it. -/
theorem Facts.Sound.reshape {Γ : List Ty} {env : Environment model.Value Γ} {facts : Facts}
    (sound : facts.Sound env) (level : Nat) (hint : Option Shape)
    (holds : ∀ shape, hint = some shape → ∀ entry, storeOf env level = some entry →
      shape.Holds (storeOf env) entry) :
    (facts.reshape level hint).Sound env := by
  cases hint with
  | none => exact sound
  | some shape =>
      refine ⟨?_, ?_, sound.2.bounds, sound.2.orders, sound.2.known, sound.2.alive⟩
      · show (facts.shapes.set level shape).length = _
        rw [List.length_set]
        exact sound.1
      · intro other entry found
        show ((facts.shapes.set level shape).getD other Shape.other).Holds _ entry
        rw [List.getD_eq_getElem?_getD]
        by_cases same : level = other
        · subst same
          by_cases inside : level < facts.shapes.length
          · rw [List.getElem?_set_self inside]
            exact holds shape rfl entry found
          · rw [List.getElem?_eq_none (by rw [List.length_set]; omega)]
            trivial
        · rw [List.getElem?_set_ne same]
          have old := sound.2.shapes other entry found
          simp only [Facts.shape, List.getD_eq_getElem?_getD] at old
          exact old

/-- New values of which nothing is tracked. -/
theorem Facts.Sound.afterAny {Γ added : List Ty} {env : Environment model.Value Γ} {facts : Facts}
    (sound : facts.Sound env) (values : Values model.Value added) :
    (facts.after (added.map fun _ => Shape.other) []).Sound (Environment.bindAll env values) := by
  refine sound.after values _ [] (List.length_map _) ?_ fun _ member => nomatch member
  intro index entry _
  have other : (added.map fun _ => Shape.other).getD index Shape.other = Shape.other := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases added[index]? <;> rfl
  rw [other]
  trivial

/-! ## Entering a nested region -/

theorem Facts.sourceOf_spec {level : Nat} : ∀ (sources : List (Option Nat)) (first inner : Nat),
    Facts.sourceOf level sources first = some inner →
      ∃ index, inner = first + index ∧ sources[index]? = some (some level)
  | [], _, _, found => nomatch found
  | source :: rest, first, inner, found => by
      unfold Facts.sourceOf at found
      split at found
      · rename_i same
        cases Option.some.inj found
        exact ⟨0, rfl, by rw [same]; rfl⟩
      · obtain ⟨index, at_, later⟩ := Facts.sourceOf_spec rest (first + 1) inner found
        exact ⟨index + 1, by omega, later⟩

/-- Each input of a region that captures a value is that value. -/
@[expose] def Sourced (sources : List (Option Nat)) (store inner : Store model) : Prop :=
  ∀ (index level : Nat), sources[index]? = some (some level) → inner index = store level

theorem Sourced.maps {sources : List (Option Nat)} {store inner : Store model}
    (sourced : Sourced sources store inner) :
    Maps (fun level => Facts.sourceOf level sources 0) store inner := by
  intro level index entry found at_
  obtain ⟨position, same, source⟩ := Facts.sourceOf_spec sources 0 index found
  rw [Nat.zero_add] at same
  subst same
  rw [sourced _ level source]
  exact at_

theorem Facts.mem_renameBounds {rename : Nat → Option Nat} {inner : Bound} :
    ∀ (bounds : List Bound), inner ∈ Facts.renameBounds rename bounds →
      ∃ bound ∈ bounds, rename bound.level = some inner.level ∧ inner.lo = bound.lo ∧
        inner.hi = bound.hi
  | [], member => nomatch member
  | bound :: rest, member => by
      unfold Facts.renameBounds at member
      split at member
      · rename_i level found
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨bound, List.mem_cons_self .., found, rfl, rfl⟩
        · obtain ⟨other, inside, facts⟩ := Facts.mem_renameBounds rest later
          exact ⟨other, List.mem_cons_of_mem _ inside, facts⟩
      · obtain ⟨other, inside, facts⟩ := Facts.mem_renameBounds rest member
        exact ⟨other, List.mem_cons_of_mem _ inside, facts⟩

theorem Facts.mem_renameOrders {rename : Nat → Option Nat} {inner : Order} :
    ∀ (orders : List Order), inner ∈ Facts.renameOrders rename orders →
      ∃ order ∈ orders, rename order.left = some inner.left ∧
        rename order.right = some inner.right ∧ inner.strict = order.strict
  | [], member => nomatch member
  | order :: rest, member => by
      unfold Facts.renameOrders at member
      split at member
      · rename_i left right one two
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨order, List.mem_cons_self .., one, two, rfl⟩
        · obtain ⟨other, inside, facts⟩ := Facts.mem_renameOrders rest later
          exact ⟨other, List.mem_cons_of_mem _ inside, facts⟩
      · obtain ⟨other, inside, facts⟩ := Facts.mem_renameOrders rest member
        exact ⟨other, List.mem_cons_of_mem _ inside, facts⟩

theorem Facts.mem_renameKnown {rename : Nat → Option Nat} {inner : Nat} :
    ∀ (known : List Nat), inner ∈ Facts.renameKnown rename known →
      ∃ condition ∈ known, rename condition = some inner
  | [], member => nomatch member
  | condition :: rest, member => by
      unfold Facts.renameKnown at member
      split at member
      · rename_i level found
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨condition, List.mem_cons_self .., found⟩
        · obtain ⟨other, inside, facts⟩ := Facts.mem_renameKnown rest later
          exact ⟨other, List.mem_cons_of_mem _ inside, facts⟩
      · obtain ⟨other, inside, facts⟩ := Facts.mem_renameKnown rest member
        exact ⟨other, List.mem_cons_of_mem _ inside, facts⟩

/-- The facts that enter a nested region hold of its inputs. -/
theorem Facts.Holds.enter {sources : List (Option Nat)} {store inner : Store model}
    {facts : Facts} (holds : facts.Holds store) (sourced : Sourced sources store inner) :
    (facts.enter sources).Holds inner := by
  have maps := sourced.maps
  refine ⟨?_, ?_, ?_, ?_, holds.alive⟩
  · intro index entry found
    show ((sources.map _).getD index Shape.other).Holds inner entry
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases source : sources[index]? with
    | none => trivial
    | some captured =>
        cases captured with
        | none => trivial
        | some level =>
            rw [sourced index level source] at found
            exact (holds.shapes level entry found).rename maps
  · intro bound member
    obtain ⟨outer, inside, level, low, high⟩ := Facts.mem_renameBounds _ member
    obtain ⟨value, found, least, most⟩ := holds.bounds outer inside
    exact ⟨value, maps _ _ _ level found, by rw [low]; exact least, by rw [high]; exact most⟩
  · intro order member
    obtain ⟨outer, inside, left, right, strict⟩ := Facts.mem_renameOrders _ member
    obtain ⟨x, y, first, second, most, less⟩ := holds.orders outer inside
    exact ⟨x, y, maps _ _ _ left first, maps _ _ _ right second, most, by rw [strict]; exact less⟩
  · intro condition member
    obtain ⟨outer, inside, level⟩ := Facts.mem_renameKnown _ member
    exact maps _ _ _ level (holds.known outer inside)

/-- The inputs of a region that are captures, after inputs that are not, are the captured
values. -/
theorem sourced_append {store : Store model} {fresh captures : List Ty} {levels : List Nat}
    (values : Values model.Value fresh) {captured : Values model.Value captures}
    (reads : Reads store levels captured) :
    Sourced (List.replicate fresh.length none ++ levels.map some) store
      (entryOf (values.append captured)) := by
  intro index level source
  by_cases early : index < fresh.length
  · rw [List.getElem?_append_left (by rw [List.length_replicate]; exact early),
      List.getElem?_replicate] at source
    simp only [early, ↓reduceIte] at source
    cases Option.some.inj source
  · have position : index = fresh.length + (index - fresh.length) := by omega
    rw [List.getElem?_append_right (by rw [List.length_replicate]; omega),
      List.length_replicate, List.getElem?_map] at source
    rw [position, entryOf_append]
    cases found : levels[index - fresh.length]? with
    | none => rw [found] at source; cases source
    | some other =>
        rw [found] at source
        cases Option.some.inj (Option.some.inj source)
        exact reads.entry _ _ found

end Zkc.Core
