module

public import Zkc.Core.Sequence

public section

/-! Typed contexts and references with constant-time access.

A context is a list of types, the most recently bound value first. A reference is the
position of a value in its context together with a proof that the context has the
reference's type there. In compiled code the proof is erased and a reference is one
number: making a reference to a value any number of bindings back is constant time,
and so is weakening it under new bindings.

`Var.here` and `Var.there` are the two ways to build a reference by position, and
`Var.cases` is the case analysis on a reference into a nonempty context: a proof that
used to take a reference apart by its constructors applies `Var.cases` (or
`Var.induction`) in the same two cases. Proofs that only compare references use
`Var.ext`: two references are equal when their positions are.

Binding several values pushes them in order: after `bindAll Γ [a, b]` the value `b` is
the most recent. A sequence of results is therefore the same context as a sequence of
single bindings, and the value with number `n`, counted in binding order from the
oldest, is at position `depth - 1 - n`.
-/

set_option autoImplicit false

universe u

namespace Zkc.Source

variable {Ty : Type}

/-- A reference to a value of a context: its position, the most recent value first,
and the fact that the context has the type there. -/
structure Var (Γ : List Ty) (ty : Ty) where
  index : Nat
  valid : Γ[index]? = some ty

instance {Γ : List Ty} {ty : Ty} : Repr (Var Γ ty) := ⟨fun reference _ => repr reference.index⟩

namespace Var

variable {Γ : List Ty} {ty head : Ty}

/-- Two references are equal when their positions are. -/
theorem ext {first second : Var Γ ty} (same : first.index = second.index) : first = second := by
  cases first; cases second; cases same; rfl

instance : DecidableEq (Var Γ ty) := fun first second =>
  if same : first.index = second.index then isTrue (ext same)
  else isFalse fun equal => same (congrArg Var.index equal)

/-- The most recent value. -/
@[expose, reducible] def here : Var (ty :: Γ) ty := ⟨0, rfl⟩

/-- A value under one more binding. -/
@[expose, reducible] def there (reference : Var Γ ty) : Var (head :: Γ) ty :=
  ⟨reference.index + 1, reference.valid⟩

@[simp] theorem index_here : (here : Var (ty :: Γ) ty).index = 0 := rfl

@[simp] theorem index_there (reference : Var Γ ty) :
    (reference.there : Var (head :: Γ) ty).index = reference.index + 1 := rfl

theorem index_lt (reference : Var Γ ty) : reference.index < Γ.length :=
  (List.getElem?_eq_some_iff.mp reference.valid).1

/-- A reference at a type that is equal to its own: the position is unchanged, so no
cast of a term is involved. -/
@[expose] def retype {target : Ty} (reference : Var Γ ty) (same : ty = target) : Var Γ target :=
  ⟨reference.index, same ▸ reference.valid⟩

/-- An empty context has no reference. -/
def elimNil {α : Sort u} (reference : Var ([] : List Ty) ty) : α :=
  nomatch reference.valid

/-- Case analysis on a reference into a nonempty context: it is the most recent value,
or a reference into the rest. It is registered as the eliminator of `cases`, so
`cases reference with | here => _ | there reference => _` reads as it did when a
reference was an inductive type. -/
@[expose, elab_as_elim, cases_eliminator] def cases {Γ : List Ty} {head : Ty}
    {motive : (ty : Ty) → Var (head :: Γ) ty → Sort u}
    (here : motive head .here) (there : {ty : Ty} → (reference : Var Γ ty) → motive ty reference.there)
    {ty : Ty} (reference : Var (head :: Γ) ty) : motive ty reference :=
  match reference with
  | ⟨0, valid⟩ => by
      have same : head = ty := Option.some.inj valid
      subst same
      exact here
  | ⟨index + 1, valid⟩ => there ⟨index, valid⟩

@[simp] theorem cases_here {Γ : List Ty} {head : Ty}
    {motive : (ty : Ty) → Var (head :: Γ) ty → Sort u}
    (onHere : motive head .here)
    (onThere : {ty : Ty} → (reference : Var Γ ty) → motive ty reference.there) :
    cases (motive := motive) onHere onThere .here = onHere := rfl

@[simp] theorem cases_there {Γ : List Ty} {head ty : Ty}
    {motive : (ty : Ty) → Var (head :: Γ) ty → Sort u}
    (onHere : motive head .here)
    (onThere : {ty : Ty} → (reference : Var Γ ty) → motive ty reference.there)
    (reference : Var Γ ty) :
    cases (motive := motive) onHere onThere reference.there = onThere reference := rfl

/-- Induction on a reference, over every context. It is registered as the eliminator of
`induction`. -/
@[elab_as_elim, induction_eliminator] theorem induction
    {motive : (Γ : List Ty) → (ty : Ty) → Var Γ ty → Prop}
    (here : ∀ {Γ : List Ty} {ty : Ty}, motive (ty :: Γ) ty .here)
    (there : ∀ {Γ : List Ty} {ty head : Ty} (reference : Var Γ ty),
      motive Γ ty reference → motive (head :: Γ) ty reference.there) :
    ∀ {Γ : List Ty} {ty : Ty} (reference : Var Γ ty), motive Γ ty reference
  | [], _, reference => reference.elimNil
  | _ :: _, _, reference =>
      cases (motive := fun ty reference => motive _ ty reference) here
        (fun reference => there reference (induction here there reference)) reference

end Var

/-! ## Binding several values -/

/-- The context after binding values of the given types in order: the last is the
most recent. -/
@[expose] def bindAll (Γ : List Ty) : List Ty → List Ty
  | [] => Γ
  | ty :: rest => bindAll (ty :: Γ) rest

@[simp] theorem bindAll_nil (Γ : List Ty) : bindAll Γ [] = Γ := rfl

@[simp] theorem bindAll_cons (Γ : List Ty) (ty : Ty) (rest : List Ty) :
    bindAll Γ (ty :: rest) = bindAll (ty :: Γ) rest := rfl

theorem bindAll_append (Γ : List Ty) : ∀ (first second : List Ty),
    bindAll Γ (first ++ second) = bindAll (bindAll Γ first) second
  | [], _ => rfl
  | ty :: rest, second => bindAll_append (ty :: Γ) rest second

theorem length_bindAll : ∀ (added Γ : List Ty), (bindAll Γ added).length = Γ.length + added.length
  | [], _ => rfl
  | _ :: rest, Γ => by
      rw [bindAll_cons, length_bindAll rest, List.length_cons, List.length_cons]
      omega

/-- An earlier value keeps its type; its position grows by the number of new values. -/
theorem getElem?_bindAll_old : ∀ (added Γ : List Ty) (index : Nat),
    (bindAll Γ added)[index + added.length]? = Γ[index]?
  | [], _, _ => rfl
  | ty :: rest, Γ, index => by
      rw [bindAll_cons, List.length_cons, ← Nat.add_assoc, Nat.add_right_comm,
        getElem?_bindAll_old rest (ty :: Γ) (index + 1)]
      rfl

/-- A new value: the one bound at position `index` of the added types is
`added.length - 1 - index` bindings back. -/
theorem getElem?_bindAll_new : ∀ (added Γ : List Ty) (index : Nat), index < added.length →
    (bindAll Γ added)[added.length - 1 - index]? = added[index]?
  | [], _, _, bound => absurd bound (Nat.not_lt_zero _)
  | ty :: rest, Γ, 0, _ => by
      have old := getElem?_bindAll_old rest (ty :: Γ) 0
      simp only [Nat.zero_add] at old
      simpa using old
  | ty :: rest, Γ, index + 1, bound => by
      have bound' : index < rest.length := Nat.lt_of_succ_lt_succ bound
      have new := getElem?_bindAll_new rest (ty :: Γ) index bound'
      have position : (ty :: rest).length - 1 - (index + 1) = rest.length - 1 - index := by
        simp only [List.length_cons]; omega
      rw [bindAll_cons, position, new]
      rfl

namespace Var

variable {Γ : List Ty} {ty : Ty}

/-- An earlier value under new bindings. -/
@[expose] def weaken (added : List Ty) (reference : Var Γ ty) : Var (bindAll Γ added) ty :=
  ⟨reference.index + added.length, (getElem?_bindAll_old added Γ reference.index).trans reference.valid⟩

/-- A new value, by its position among the added types. -/
def bound {added : List Ty} (position : Var added ty) : Var (bindAll Γ added) ty :=
  ⟨added.length - 1 - position.index,
    (getElem?_bindAll_new added Γ position.index position.index_lt).trans position.valid⟩

@[simp] theorem weaken_nil (reference : Var Γ ty) : reference.weaken [] = reference := rfl

theorem weaken_cons (head : Ty) (rest : List Ty) (reference : Var Γ ty) :
    reference.weaken (head :: rest) = (reference.there (head := head)).weaken rest :=
  ext (by simp only [weaken, List.length_cons]; omega)

end Var

/-! ## Values and environments -/

/-- A heterogeneous list; its order is part of the binding contract. -/
inductive Values (Value : Ty → Type) : List Ty → Type where
  | nil : Values Value []
  | cons {ty : Ty} {Γ : List Ty} : Value ty → Values Value Γ → Values Value (ty :: Γ)

namespace Values

variable {Value : Ty → Type}

/-- The value at a position. -/
@[expose] def get : {Γ : List Ty} → Values Value Γ → {ty : Ty} → Var Γ ty → Value ty
  | _, .nil, _, reference => reference.elimNil
  | _, .cons value rest, _, reference =>
      Var.cases (motive := fun ty _ => Value ty) value (fun reference => rest.get reference) reference

@[simp] theorem get_here {Γ : List Ty} {ty : Ty} (value : Value ty) (tail : Values Value Γ) :
    (Values.cons value tail).get .here = value := rfl

@[simp] theorem get_there {Γ : List Ty} {ty result : Ty} (value : Value ty)
    (tail : Values Value Γ) (reference : Var Γ result) :
    (Values.cons value tail).get reference.there = tail.get reference := rfl

@[expose] def tail {Γ : List Ty} {ty : Ty} (values : Values Value (ty :: Γ)) : Values Value Γ :=
  match values with | .cons _ rest => rest

/-- Concatenation, by recursion on the types of the first tuple: the first tuple is read by
`get` and `tail`, so that the concatenation of a tuple that is a variable reduces to its
positions. -/
@[expose] def append : {Γ Δ : List Ty} → Values Value Γ → Values Value Δ → Values Value (Γ ++ Δ)
  | [], _, _, right => right
  | _ :: _, _, values, right => .cons (values.get .here) (append values.tail right)

@[simp] theorem nil_append {Δ : List Ty} (right : Values Value Δ) :
    (Values.nil : Values Value []).append right = right := rfl

@[simp] theorem cons_append {Γ Δ : List Ty} {ty : Ty} (value : Value ty) (rest : Values Value Γ)
    (right : Values Value Δ) :
    (Values.cons value rest).append right = .cons value (rest.append right) :=
  rfl

/-- Separate an explicitly typed prefix from the rest. -/
@[expose] def split (added : List Ty) {Γ : List Ty} (values : Values Value (added ++ Γ)) :
    Values Value added × Values Value Γ :=
  match added, values with
  | [], values => (.nil, values)
  | _ :: rest, .cons value values =>
      let parts := Values.split rest values
      (.cons value parts.1, parts.2)

@[simp] theorem split_append {Γ Δ : List Ty} (first : Values Value Γ) (rest : Values Value Δ) :
    Values.split Γ (first.append rest) = (first, rest) := by
  induction first with
  | nil => rfl
  | cons value tail ih =>
    show (Values.cons value (Values.split _ (tail.append rest)).1,
      (Values.split _ (tail.append rest)).2) = _
    rw [ih]

@[simp] theorem append_split (added : List Ty) {Γ : List Ty} (values : Values Value (added ++ Γ)) :
    (Values.split added values).1.append (Values.split added values).2 = values := by
  induction added with
  | nil => rfl
  | cons ty rest ih =>
    cases values with
    | cons value tail =>
      change Values.cons value
        ((Values.split rest tail).1.append (Values.split rest tail).2) = .cons value tail
      rw [ih]

@[expose] def singleton {ty : Ty} (value : Value ty) : Values Value [ty] := .cons value .nil

/-- Apply a function to every value. -/
@[expose] def map {Other : Ty → Type} (f : {ty : Ty} → Value ty → Other ty) :
    {Γ : List Ty} → Values Value Γ → Values Other Γ
  | _, .nil => .nil
  | _, .cons value rest => .cons (f value) (rest.map f)

end Values

abbrev Environment (Value : Ty → Type) (Γ : List Ty) :=
  {ty : Ty} → Var Γ ty → Value ty

namespace Environment

variable {Value : Ty → Type}

/-- The environment of the empty context. -/
def empty : Environment Value [] := fun reference => reference.elimNil

@[expose] def push {Γ : List Ty} {ty : Ty} (env : Environment Value Γ) (value : Value ty) :
    Environment Value (ty :: Γ) :=
  fun reference => Var.cases (motive := fun ty _ => Value ty) value (fun reference => env reference) reference

@[simp] theorem push_here {Γ : List Ty} {ty : Ty} (env : Environment Value Γ) (value : Value ty) :
    env.push value .here = value := rfl

@[simp] theorem push_there {Γ : List Ty} {ty result : Ty} (env : Environment Value Γ)
    (value : Value ty) (reference : Var Γ result) :
    env.push value reference.there = env reference := rfl

/-- Bind values in order: the last is the most recent. The recursion is on the types: the
values are read by `get` and `tail`, so that binding a tuple that is a variable reduces to its
positions. -/
@[expose] def bindAll : {Γ added : List Ty} → Environment Value Γ → Values Value added →
    Environment Value (Zkc.Source.bindAll Γ added)
  | _, [], env, _ => env
  | _, _ :: _, env, values => bindAll (push env (values.get .here)) values.tail

@[simp] theorem bindAll_nil {Γ : List Ty} (env : Environment Value Γ) :
    @Eq (Environment Value Γ) (bindAll env (.nil : Values Value [])) env := rfl

@[simp] theorem bindAll_cons {Γ added : List Ty} {ty : Ty} (env : Environment Value Γ)
    (value : Value ty) (rest : Values Value added) :
    @Eq (Environment Value (Zkc.Source.bindAll Γ (ty :: added)))
      (bindAll env (.cons value rest)) (bindAll (push env value) rest) := rfl

/-- An earlier value is unchanged by new bindings. -/
@[simp] theorem bindAll_weaken {ty : Ty} :
    ∀ {Γ added : List Ty} (env : Environment Value Γ) (values : Values Value added)
      (reference : Var Γ ty), bindAll env values (reference.weaken added) = env reference
  | _, _, _, .nil, _ => rfl
  | _, _, env, .cons (ty := head) (Γ := rest) value values, reference => by
      rw [Var.weaken_cons]
      exact bindAll_weaken (push env value) values reference.there

/-- The environment of a region's inputs. -/
@[expose] def ofValues {Γ : List Ty} (values : Values Value Γ) : Environment Value (Zkc.Source.bindAll [] Γ) :=
  bindAll empty values

end Environment

/-- An explicit, ordered map of operands into the surrounding context. -/
abbrev Operands (Γ : List Ty) := Values (Var Γ)

namespace Operands

variable {Value : Ty → Type}

@[expose] def eval {Γ args : List Ty} (env : Environment Value Γ) : Operands Γ args → Values Value args
  | .nil => .nil
  | .cons reference tail => .cons (env reference) (Operands.eval env tail)

theorem get_eval {Γ args : List Ty} {ty : Ty} (env : Environment Value Γ)
    (operands : Operands Γ args) (position : Var args ty) :
    (Operands.eval env operands).get position = env (operands.get position) := by
  induction operands with
  | nil => exact position.elimNil
  | cons head tail ih =>
      cases position with
      | here => rfl
      | there position => exact ih position

end Operands

/-! ## A context mirrored for lookup

Elaboration finds a value by its number. A `Scope` holds the context as a sequence
with logarithmic access, and its length, so that neither the lookup nor the validation
of a reference walks the context. -/

/-- A context with fast access. -/
structure Scope {α : Type} (Γ : List α) where
  entries : Sequence α
  depth : Nat
  mirrors : entries.toList = Γ
  counted : depth = Γ.length

namespace Scope

variable {α : Type} {Γ : List α}

@[expose] def empty : Scope ([] : List α) := ⟨.empty, 0, rfl, rfl⟩

def push (scope : Scope Γ) (entry : α) : Scope (entry :: Γ) :=
  ⟨scope.entries.push entry, scope.depth + 1,
    by rw [Sequence.toList_push, scope.mirrors], by rw [scope.counted, List.length_cons]⟩

def bindAll : {Γ : List α} → Scope Γ → (added : List α) → Scope (Zkc.Source.bindAll Γ added)
  | _, scope, [] => scope
  | _, scope, entry :: rest => bindAll (scope.push entry) rest

@[simp] theorem depth_bindAll : ∀ (added : List α) {Γ : List α} (scope : Scope Γ),
    (scope.bindAll added).depth = scope.depth + added.length
  | [], _, _ => rfl
  | entry :: rest, _, scope => by
      show (bindAll (scope.push entry) rest).depth = _
      rw [depth_bindAll rest, List.length_cons]
      show scope.depth + 1 + rest.length = _
      omega

/-- The entry at a position, the most recent first. -/
def entry? (scope : Scope Γ) (index : Nat) : Option α := scope.entries.get? index

theorem entry?_eq (scope : Scope Γ) (index : Nat) : scope.entry? index = Γ[index]? := by
  rw [entry?, Sequence.get?_eq, scope.mirrors]

/-- The reference at a position, with its type. -/
def at? (scope : Scope Γ) (index : Nat) : Option ((entry : α) × Var Γ entry) :=
  match found : scope.entry? index with
  | some entry => some ⟨entry, index, (scope.entry?_eq index).symm.trans found⟩
  | none => none

/-- The reference at a position, when the context has the given type there. -/
@[expose] def atType? [DecidableEq α] (scope : Scope Γ) (entry : α) (index : Nat) : Option (Var Γ entry) :=
  if found : scope.entry? index = some entry then
    some ⟨index, (scope.entry?_eq index).symm.trans found⟩
  else none

/-- The position of the value with a number: values are numbered in binding order from
zero. -/
@[expose] def position (depth number : Nat) : Nat := depth - 1 - number

/-- The value with a number, with its type. -/
def value? (scope : Scope Γ) (number : Nat) : Option ((entry : α) × Var Γ entry) :=
  cond (Nat.blt number scope.depth) (scope.at? (position scope.depth number)) none

/-- The value with a number, at a required type. -/
def find? [DecidableEq α] (scope : Scope Γ) (entry : α) (number : Nat) : Option (Var Γ entry) :=
  cond (Nat.blt number scope.depth) (scope.atType? entry (position scope.depth number)) none

/-- The type of the value with a number. -/
def type? (scope : Scope Γ) (number : Nat) : Option α :=
  cond (Nat.blt number scope.depth) (scope.entry? (position scope.depth number)) none

/-- The number of the value that a reference names, in a context of the given depth. -/
@[expose] def number (depth : Nat) {entry : α} (reference : Var Γ entry) : Nat := position depth reference.index

theorem at?_index {entry : α} (scope : Scope Γ) (reference : Var Γ entry) :
    scope.at? reference.index = some ⟨entry, reference⟩ := by
  have found : scope.entry? reference.index = some entry :=
    (scope.entry?_eq _).trans reference.valid
  unfold at?
  split
  · rename_i other found'
    have same : other = entry := Option.some.inj (found'.symm.trans found)
    subst same
    rfl
  · rename_i missing
    rw [found] at missing
    cases missing

theorem atType?_index [DecidableEq α] {entry : α} (scope : Scope Γ) (reference : Var Γ entry) :
    scope.atType? entry reference.index = some reference := by
  have found : scope.entry? reference.index = some entry :=
    (scope.entry?_eq _).trans reference.valid
  simp only [atType?, found, ↓reduceDIte]

theorem number_lt {entry : α} (scope : Scope Γ) (reference : Var Γ entry) :
    Nat.blt (number scope.depth reference) scope.depth = true := by
  have bound := reference.index_lt
  rw [← scope.counted] at bound
  exact Nat.blt_eq.mpr (by simp only [number, position]; omega)

theorem position_number {entry : α} (scope : Scope Γ) (reference : Var Γ entry) :
    position scope.depth (number scope.depth reference) = reference.index := by
  have bound := reference.index_lt
  rw [← scope.counted] at bound
  simp only [number, position]
  omega

/-- The value with the number of a reference is the reference. -/
theorem value?_number {entry : α} (scope : Scope Γ) (reference : Var Γ entry) :
    scope.value? (number scope.depth reference) = some ⟨entry, reference⟩ := by
  rw [value?, number_lt, position_number, Bool.cond_true, at?_index]

theorem find?_number [DecidableEq α] {entry : α} (scope : Scope Γ) (reference : Var Γ entry) :
    scope.find? entry (number scope.depth reference) = some reference := by
  rw [find?, number_lt, position_number, Bool.cond_true, atType?_index]

theorem type?_number {entry : α} (scope : Scope Γ) (reference : Var Γ entry) :
    scope.type? (number scope.depth reference) = some entry := by
  rw [type?, number_lt, position_number, Bool.cond_true, entry?_eq, reference.valid]

/-- A value found by its number is in the context, at the position of the number. -/
theorem find?_position [DecidableEq α] {entry : α} (scope : Scope Γ) {number : Nat}
    {reference : Var Γ entry} (found : scope.find? entry number = some reference) :
    number < scope.depth ∧ reference.index = position scope.depth number := by
  unfold find? at found
  cases inside : Nat.blt number scope.depth with
  | false =>
      rw [inside] at found
      cases found
  | true =>
      rw [inside, Bool.cond_true] at found
      unfold atType? at found
      split at found
      · cases Option.some.inj found
        exact ⟨Nat.blt_eq.mp inside, rfl⟩
      · cases found

/-- Operands at required types, by their numbers. -/
def operands? [DecidableEq α] (scope : Scope Γ) :
    (types : List α) → List Nat → Option (Operands Γ types)
  | [], [] => some .nil
  | type :: types, number :: numbers =>
      match scope.find? type number, operands? scope types numbers with
      | some reference, some rest => some (.cons reference rest)
      | _, _ => none
  | [], _ :: _ => none
  | _ :: _, [] => none

/-- The numbers of operands. -/
@[expose] def numbers (depth : Nat) : {types : List α} → Operands Γ types → List Nat
  | _, .nil => []
  | _, .cons reference rest => number depth reference :: numbers depth rest

theorem operands?_numbers [DecidableEq α] (scope : Scope Γ) :
    ∀ {types : List α} (operands : Operands Γ types),
      scope.operands? types (numbers scope.depth operands) = some operands
  | _, .nil => rfl
  | _, .cons reference rest => by
      simp only [numbers, operands?, find?_number, operands?_numbers scope rest]

/-- Operands found by their numbers have those numbers. -/
theorem numbers_operands? [DecidableEq α] (scope : Scope Γ) :
    ∀ {types : List α} (values : List Nat) (operands : Operands Γ types),
      scope.operands? types values = some operands → numbers scope.depth operands = values
  | [], [], .nil, _ => rfl
  | type :: types, value :: values, .cons reference rest, found => by
      unfold operands? at found
      split at found
      · rename_i first others here later
        obtain ⟨inside, at_⟩ := find?_position scope here
        have tail := numbers_operands? scope values others later
        cases Option.some.inj found
        show number scope.depth _ :: numbers scope.depth _ = _
        rw [tail]
        simp only [number, position, at_]
        congr 1
        omega
      · cases found
  | [], _ :: _, _, found => by
      unfold operands? at found
      cases found
  | _ :: _, [], _, found => by
      unfold operands? at found
      cases found

end Scope

/-! ## Maps between contexts as data

A step that rewrites a region gives every value of the old context a value of the new
one. A `Mapping` records, for each old value, the level of its image: its position in
the new context counted from the oldest value. A level does not change when the new
context grows, so extending a mapping is constant time and looking a value up is
logarithmic; no chain of closures grows with the body.

The relation `R` says which new types an old type may be read at: equality for a
renaming, "the role holds it" for a projection. An old value that is related to no
new type needs no image. -/

/-- The entry at a level: a position counted from the oldest value. -/
@[expose] def atLevel? {β : Type} (Δ : List β) (depth level : Nat) : Option β :=
  if level < depth then Δ[depth - 1 - level]? else none

theorem atLevel?_cons {β : Type} (Δ : List β) (head : β) {depth level : Nat} {entry : β}
    (found : atLevel? Δ depth level = some entry) :
    atLevel? (head :: Δ) (depth + 1) level = some entry := by
  unfold atLevel? at found ⊢
  split at found
  · rename_i below
    have position : depth + 1 - 1 - level = (depth - 1 - level) + 1 := by omega
    have below' : level < depth + 1 := by omega
    simp only [below', ↓reduceIte, position]
    exact found
  · cases found

theorem atLevel?_bindAll {β : Type} : ∀ (added Δ : List β) {depth level : Nat} {entry : β},
    atLevel? Δ depth level = some entry →
      atLevel? (bindAll Δ added) (depth + added.length) level = some entry
  | [], _, _, _, _, found => found
  | head :: rest, Δ, depth, level, entry, found => by
      have next := atLevel?_bindAll rest (head :: Δ) (atLevel?_cons Δ head found)
      rw [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]
      exact next

theorem atLevel?_index {β : Type} {Δ : List β} {entry : β} (reference : Var Δ entry) :
    atLevel? Δ Δ.length (Δ.length - 1 - reference.index) = some entry := by
  have bound := reference.index_lt
  unfold atLevel?
  have position : Δ.length - 1 - (Δ.length - 1 - reference.index) = reference.index := by omega
  have below : Δ.length - 1 - reference.index < Δ.length := by omega
  simp only [below, ↓reduceIte, position]
  exact reference.valid

/-- A map from the values of one context to values of another. -/
structure Mapping {α β : Type} (R : α → β → Prop) (Γ : List α) (Δ : List β) where
  /-- For each value of `Γ`, the most recent first: the level of its image in `Δ`. -/
  levels : Sequence Nat
  depth : Nat
  counted : depth = Δ.length
  sound : ∀ (index : Nat) (source : α), Γ[index]? = some source →
    ∃ level, levels.toList[index]? = some level ∧
      ∀ target, R source target → atLevel? Δ depth level = some target

namespace Mapping

variable {α β : Type} {R : α → β → Prop} {Γ : List α} {Δ : List β}

/-- The map of the empty context. -/
def start (depth : Nat) (counted : depth = Δ.length) : Mapping R ([] : List α) Δ :=
  ⟨.empty, depth, counted, fun _ _ found => nomatch found⟩

/-- The level of the image of the value at a position. -/
@[expose] def level (map : Mapping R Γ Δ) (index : Nat) : Nat := (map.levels.get? index).getD 0

theorem level_sound (map : Mapping R Γ Δ) {source : α} {target : β} (reference : Var Γ source)
    (related : R source target) :
    atLevel? Δ map.depth (map.level reference.index) = some target := by
  obtain ⟨level, found, image⟩ := map.sound reference.index source reference.valid
  rw [Mapping.level, Sequence.get?_eq, found]
  exact image target related

/-- The image of a value, at a type it is related to. -/
@[expose] def apply (map : Mapping R Γ Δ) {source : α} {target : β} (reference : Var Γ source)
    (related : R source target) : Var Δ target :=
  ⟨map.depth - 1 - map.level reference.index, by
    have found := map.level_sound reference related
    unfold atLevel? at found
    split at found
    · exact found
    · cases found⟩

/-- The same map into a context with one more value. -/
def weakenOne (map : Mapping R Γ Δ) (head : β) : Mapping R Γ (head :: Δ) :=
  ⟨map.levels, map.depth + 1, by rw [map.counted, List.length_cons], fun index source found => by
    obtain ⟨level, at_, image⟩ := map.sound index source found
    exact ⟨level, at_, fun target related => atLevel?_cons Δ head (image target related)⟩⟩

/-- The same map into a context with more values. -/
def weaken (map : Mapping R Γ Δ) (added : List β) : Mapping R Γ (bindAll Δ added) :=
  ⟨map.levels, map.depth + added.length, by rw [map.counted, length_bindAll],
    fun index source found => by
      obtain ⟨level, at_, image⟩ := map.sound index source found
      exact ⟨level, at_, fun target related => atLevel?_bindAll added Δ (image target related)⟩⟩

/-- One more old value, whose image is a given value of the new context. -/
def bind (map : Mapping R Γ Δ) (source : α) {target : β} (image : Var Δ target)
    (only : ∀ other, R source other → other = target) : Mapping R (source :: Γ) Δ :=
  ⟨map.levels.push (map.depth - 1 - image.index), map.depth, map.counted, fun index found valid => by
    rw [Sequence.toList_push]
    cases index with
    | zero =>
        have same : source = found := Option.some.inj valid
        subst same
        refine ⟨_, rfl, fun other related => ?_⟩
        rw [only other related, map.counted]
        exact atLevel?_index image
    | succ index => exact map.sound index found valid⟩

/-- One more old value that has no image: it is related to no new type. -/
def skip (map : Mapping R Γ Δ) (source : α) (unrelated : ∀ target, ¬ R source target) :
    Mapping R (source :: Γ) Δ :=
  ⟨map.levels.push 0, map.depth, map.counted, fun index found valid => by
    rw [Sequence.toList_push]
    cases index with
    | zero =>
        have same : source = found := Option.some.inj valid
        subst same
        exact ⟨_, rfl, fun other related => absurd related (unrelated other)⟩
    | succ index => exact map.sound index found valid⟩

/-- One more old value whose image is one more new value. -/
def keep (map : Mapping R Γ Δ) (source : α) (target : β)
    (only : ∀ other, R source other → other = target) : Mapping R (source :: Γ) (target :: Δ) :=
  (map.weakenOne target).bind source .here only

theorem apply_ext {map : Mapping R Γ Δ} {source : α} {target : β} {reference : Var Γ source}
    {related : R source target} {image : Var Δ target}
    (same : map.depth - 1 - map.level reference.index = image.index) :
    map.apply reference related = image :=
  Var.ext same

/-- The image under a weakened map is the weakened image. -/
theorem apply_weakenOne (map : Mapping R Γ Δ) (head : β) {source : α} {target : β}
    (reference : Var Γ source) (related : R source target) :
    (map.weakenOne head).apply reference related = (map.apply reference related).there := by
  apply Var.ext
  have found := map.level_sound reference related
  unfold atLevel? at found
  split at found
  · rename_i below
    show map.depth + 1 - 1 - map.level reference.index = map.depth - 1 - map.level reference.index + 1
    omega
  · cases found

theorem apply_weaken (map : Mapping R Γ Δ) (added : List β) {source : α} {target : β}
    (reference : Var Γ source) (related : R source target) :
    (map.weaken added).apply reference related = (map.apply reference related).weaken added := by
  apply Var.ext
  have found := map.level_sound reference related
  unfold atLevel? at found
  split at found
  · rename_i below
    show map.depth + added.length - 1 - map.level reference.index =
      map.depth - 1 - map.level reference.index + added.length
    omega
  · cases found

theorem level_push_zero (levels : Sequence Nat) (level : Nat) :
    ((levels.push level).get? 0).getD 0 = level := by
  rw [Sequence.get?_eq, Sequence.toList_push]
  rfl

theorem level_push_succ (levels : Sequence Nat) (level index : Nat) :
    ((levels.push level).get? (index + 1)).getD 0 = (levels.get? index).getD 0 := by
  rw [Sequence.get?_eq, Sequence.toList_push, Sequence.get?_eq]
  rfl

/-- The image of the bound value is the given one. -/
theorem apply_bind_here (map : Mapping R Γ Δ) (source : α) {target : β} (image : Var Δ target)
    (only : ∀ other, R source other → other = target) (related : R source target) :
    (map.bind source image only).apply .here related = image := by
  apply Var.ext
  have bound := image.index_lt
  rw [← map.counted] at bound
  show map.depth - 1 - ((map.levels.push (map.depth - 1 - image.index)).get? 0).getD 0 = image.index
  rw [level_push_zero]
  omega

/-- The image of an earlier value is unchanged. -/
theorem apply_bind_there (map : Mapping R Γ Δ) (source : α) {target : β} (image : Var Δ target)
    (only : ∀ other, R source other → other = target) {earlier : α} {type : β}
    (reference : Var Γ earlier) (related : R earlier type) :
    (map.bind source image only).apply reference.there related = map.apply reference related := by
  apply Var.ext
  show map.depth - 1 - ((map.levels.push _).get? (reference.index + 1)).getD 0 = _
  rw [level_push_succ]
  rfl

theorem apply_skip_there (map : Mapping R Γ Δ) (source : α)
    (unrelated : ∀ target, ¬ R source target) {earlier : α} {type : β}
    (reference : Var Γ earlier) (related : R earlier type) :
    (map.skip source unrelated).apply reference.there related = map.apply reference related := by
  apply Var.ext
  show map.depth - 1 - ((map.levels.push _).get? (reference.index + 1)).getD 0 = _
  rw [level_push_succ]
  rfl

theorem apply_keep_here (map : Mapping R Γ Δ) (source : α) (target : β)
    (only : ∀ other, R source other → other = target) (related : R source target) :
    (map.keep source target only).apply .here related = .here :=
  apply_bind_here _ _ _ _ _

theorem apply_keep_there (map : Mapping R Γ Δ) (source : α) (target : β)
    (only : ∀ other, R source other → other = target) {earlier : α} {type : β}
    (reference : Var Γ earlier) (related : R earlier type) :
    (map.keep source target only).apply reference.there related =
      (map.apply reference related).there := by
  rw [keep, apply_bind_there, apply_weakenOne]

end Mapping

/-- A renaming: every old value has an image of its own type. -/
abbrev Renaming (Γ Δ : List Ty) := Mapping (α := Ty) (β := Ty) Eq Γ Δ

namespace Renaming

variable {Γ Δ : List Ty}

/-- The image of a value. -/
@[expose] def rename (map : Renaming Γ Δ) {ty : Ty} (reference : Var Γ ty) : Var Δ ty := map.apply reference rfl

/-- One more old value, renamed to a given value. -/
@[expose] def to (map : Renaming Γ Δ) {ty : Ty} (image : Var Δ ty) : Renaming (ty :: Γ) Δ :=
  map.bind ty image fun _ same => same.symm

/-- The same new values on both sides. -/
@[expose] def keepAll : {Γ Δ : List Ty} → Renaming Γ Δ → (added : List Ty) →
    Renaming (bindAll Γ added) (bindAll Δ added)
  | _, _, map, [] => map
  | _, _, map, ty :: rest => keepAll (map.keep ty ty fun _ same => same.symm) rest

/-- The operands of an operation, renamed. -/
@[expose] def operands (map : Renaming Γ Δ) : {types : List Ty} → Operands Γ types → Operands Δ types
  | _, .nil => .nil
  | _, .cons reference rest => .cons (map.rename reference) (operands map rest)

end Renaming

end Zkc.Source
