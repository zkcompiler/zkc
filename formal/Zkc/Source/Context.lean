import Std

/-! Finite typed contexts shared by source formation and execution plans.

Variable positions are de Bruijn indices: position zero is the most recently
bound value. Semantic values are supplied separately from portable syntax.
-/

set_option autoImplicit false

namespace Zkc.Source

variable {Ty : Type}

/-- Membership in an ordered typed context. -/
inductive Var : List Ty → Ty → Type where
  | here {Γ : List Ty} {ty : Ty} : Var (ty :: Γ) ty
  | there {Γ : List Ty} {ty head : Ty} : Var Γ ty → Var (head :: Γ) ty
  deriving Repr

def Var.index {Γ : List Ty} {ty : Ty} : Var Γ ty → Nat
  | .here => 0
  | .there v => v.index + 1

/-- Compute a position without retaining one stack frame per preceding binding. -/
def Var.indexFrom {Γ : List Ty} {ty : Ty} (value : Var Γ ty) (offset : Nat) : Nat :=
  match value with
  | .here => offset
  | .there rest => rest.indexFrom (offset + 1)

theorem Var.indexFrom_eq {Γ : List Ty} {ty : Ty} (value : Var Γ ty) (offset : Nat) :
    value.indexFrom offset = value.index + offset := by
  induction value generalizing offset with
  | here => simp [indexFrom, index]
  | there value ih => simp [indexFrom, index, ih, Nat.add_assoc, Nat.add_comm]

def Var.indexIterative {Γ : List Ty} {ty : Ty} (value : Var Γ ty) : Nat :=
  value.indexFrom 0

@[csimp] theorem Var.index_eq_indexIterative : @Var.index = @Var.indexIterative := by
  funext Ty Γ ty value
  simp [indexIterative, indexFrom_eq]

theorem Var.type_at_index {Γ : List Ty} {ty : Ty} (value : Var Γ ty) :
    Γ[value.index]? = some ty := by
  induction value with
  | here => rfl
  | there value ih => simpa only [index, List.getElem?_cons_succ] using ih

theorem Var.type_eq_of_index {Γ : List Ty} {first second : Ty}
    (left : Var Γ first) (right : Var Γ second) (same : left.index = right.index) : first = second := by
  have leftType := left.type_at_index
  rw [same, right.type_at_index] at leftType
  exact (Option.some.inj leftType).symm

theorem Var.eq_of_index {Γ : List Ty} {ty : Ty} (left right : Var Γ ty)
    (same : left.index = right.index) : left = right := by
  induction left with
  | here =>
    cases right with
    | here => rfl
    | there right => simp [index] at same
  | there left ih =>
    cases right with
    | here => simp [index] at same
    | there right => exact congrArg Var.there (ih right (Nat.add_right_cancel same))

/-- Resolve an external position against its required type, without defaults. -/
def Var.decode [DecidableEq Ty] : (Γ : List Ty) → (ty : Ty) → Nat → Option (Var Γ ty)
  | [], _, _ => none
  | head :: _, ty, 0 => if h : head = ty then h ▸ some .here else none
  | _ :: Γ, ty, n + 1 => (decode Γ ty n).map .there

@[simp] theorem Var.decode_index [DecidableEq Ty] {Γ : List Ty} {ty : Ty}
    (v : Var Γ ty) : Var.decode Γ ty v.index = some v := by
  induction v with
  | here => simp [decode, index]
  | there v ih => simp [decode, index, ih]

/-- A heterogeneous list; its order is part of the binding contract. -/
inductive Values (Value : Ty → Type) : List Ty → Type where
  | nil : Values Value []
  | cons {ty : Ty} {Γ : List Ty} : Value ty → Values Value Γ → Values Value (ty :: Γ)

instance {Value : Ty → Type} [∀ ty, Subsingleton (Value ty)] {Γ : List Ty} :
    Subsingleton (Values Value Γ) where
  allEq first second := by
    induction first with
    | nil => cases second; rfl
    | cons first rest ih =>
      cases second with
      | cons other tail =>
        have same := Subsingleton.elim first other
        cases same
        cases ih tail
        rfl

def Values.get {Value : Ty → Type} {Γ : List Ty} {ty : Ty}
    (values : Values Value Γ) (v : Var Γ ty) : Value ty :=
  match v, values with
  | .here, .cons value _ => value
  | .there tail, .cons _ values => values.get tail

@[inline] def Values.castContext {Value : Ty → Type} {Γ Δ : List Ty} (same : Γ = Δ)
    (values : Values Value Γ) : Values Value Δ := same ▸ values

theorem Values.castContext_heq {Value : Ty → Type} {Γ Δ : List Ty} (same : Γ = Δ)
    (values : Values Value Γ) : HEq (values.castContext same) values := by
  cases same
  rfl

/-- Reverse a heterogeneous list onto a suffix without retaining a stack frame
for each element. The context equations are erased from executable code. -/
def Values.reverseAppend {Value : Ty → Type} {Γ Δ : List Ty}
    (values : Values Value Γ) (suffix : Values Value Δ) : Values Value (Γ.reverse ++ Δ) :=
  match values with
  | .nil => suffix
  | .cons first rest =>
      (rest.reverseAppend (.cons first suffix)).castContext
        (by simp only [List.reverse_cons, List.append_assoc, List.singleton_append])

def Values.reverse {Value : Ty → Type} {Γ : List Ty} (values : Values Value Γ) :
    Values Value Γ.reverse :=
  (values.reverseAppend .nil).castContext (List.append_nil _)

def Values.append {Value : Ty → Type} {Γ Δ : List Ty}
    (first : Values Value Γ) (rest : Values Value Δ) : Values Value (Γ ++ Δ) :=
  match first with
  | .nil => rest
  | .cons head tail => .cons head (tail.append rest)

theorem Values.reverseAppend_castContext {Value : Ty → Type} {Γ Γ' Δ : List Ty}
    (same : Γ = Γ') (values : Values Value Γ) (suffix : Values Value Δ) :
    HEq ((values.castContext same).reverseAppend suffix) (values.reverseAppend suffix) := by
  cases same
  rfl

theorem Values.cons_heq {Value : Ty → Type} {Γ Δ : List Ty} {ty : Ty}
    (same : Γ = Δ) (first : Value ty) (left : Values Value Γ) (right : Values Value Δ)
    (rest : HEq left right) : HEq (Values.cons first left) (Values.cons first right) := by
  cases same
  cases eq_of_heq rest
  rfl

theorem Values.append_nil {Value : Ty → Type} {Γ : List Ty} (values : Values Value Γ) :
    HEq (values.append .nil) values := by
  induction values with
  | nil => rfl
  | @cons ty types first rest ih =>
    exact cons_heq (List.append_nil types) first _ _ ih

theorem Values.reverseAppend_twice {Value : Ty → Type} {Γ Δ Ξ : List Ty}
    (values : Values Value Γ) (suffix : Values Value Δ) (tail : Values Value Ξ) :
    HEq ((values.reverseAppend suffix).reverseAppend tail)
      (suffix.reverseAppend (values.append tail)) := by
  induction values generalizing Δ with
  | nil => rfl
  | cons first rest ih =>
    exact (reverseAppend_castContext _ _ _).trans
      ((ih (.cons first suffix)).trans (castContext_heq _ _))

theorem Values.reverse_reverse {Value : Ty → Type} {Γ : List Ty}
    (values : Values Value Γ) : HEq values.reverse.reverse values := by
  exact (castContext_heq _ _).trans ((reverseAppend_castContext _ _ _).trans
    ((values.reverseAppend_twice .nil .nil).trans values.append_nil))

def Values.appendIterative {Value : Ty → Type} {Γ Δ : List Ty}
    (first : Values Value Γ) (rest : Values Value Δ) : Values Value (Γ ++ Δ) :=
  (first.reverse.reverseAppend rest).castContext (by simp only [List.reverse_reverse])

@[csimp] theorem Values.append_eq_appendIterative : @Values.append = @Values.appendIterative := by
  funext Ty Value Γ Δ first rest
  apply Eq.symm
  apply eq_of_heq
  exact (castContext_heq _ _).trans ((reverseAppend_castContext _ _ _).trans
    (first.reverseAppend_twice .nil rest))

def Values.map {Value Other : Ty → Type} (transform : {ty : Ty} → Value ty → Other ty)
    {Γ : List Ty} (values : Values Value Γ) : Values Other Γ :=
  match values with
  | .nil => .nil
  | .cons first rest => .cons (transform first) (rest.map transform)

def Values.mapReverseAppend {Value Other : Ty → Type}
    (transform : {ty : Ty} → Value ty → Other ty) {Γ Δ : List Ty}
    (values : Values Value Γ) (suffix : Values Other Δ) : Values Other (Γ.reverse ++ Δ) :=
  match values with
  | .nil => suffix
  | .cons first rest =>
      (rest.mapReverseAppend transform (.cons (transform first) suffix)).castContext
        (by simp only [List.reverse_cons, List.append_assoc, List.singleton_append])

theorem Values.mapReverseAppend_eq {Value Other : Ty → Type}
    (transform : {ty : Ty} → Value ty → Other ty) {Γ Δ : List Ty}
    (values : Values Value Γ) (suffix : Values Other Δ) :
    values.mapReverseAppend transform suffix = (values.map transform).reverseAppend suffix := by
  induction values generalizing Δ with
  | nil => rfl
  | cons first rest ih => simp only [mapReverseAppend, map, reverseAppend, ih]

def Values.mapIterative {Value Other : Ty → Type}
    (transform : {ty : Ty} → Value ty → Other ty) {Γ : List Ty}
    (values : Values Value Γ) : Values Other Γ :=
  ((values.mapReverseAppend transform .nil).reverseAppend .nil).castContext
    (by simp only [List.append_nil, List.reverse_reverse])

@[csimp] theorem Values.map_eq_mapIterative : @Values.map = @Values.mapIterative := by
  funext Ty Value Other transform Γ values
  apply Eq.symm
  apply eq_of_heq
  unfold mapIterative
  rw [mapReverseAppend_eq]
  exact (castContext_heq _ _).trans
    (((values.map transform).reverseAppend_twice .nil .nil).trans
      (values.map transform).append_nil)

/-- A typed map that also changes the type index of each element. -/
def Values.mapTypes {OtherTy : Type} {Value : Ty → Type} {Other : OtherTy → Type}
    (typeMap : Ty → OtherTy) (transform : {ty : Ty} → Value ty → Other (typeMap ty))
    {Γ : List Ty} (values : Values Value Γ) : Values Other (Γ.map typeMap) :=
  match values with
  | .nil => .nil
  | .cons first rest => .cons (transform first) (rest.mapTypes typeMap transform)

def Values.mapTypesReverseAppend {OtherTy : Type} {Value : Ty → Type} {Other : OtherTy → Type}
    (typeMap : Ty → OtherTy) (transform : {ty : Ty} → Value ty → Other (typeMap ty))
    {Γ : List Ty} {Δ : List OtherTy} (values : Values Value Γ) (suffix : Values Other Δ) :
    Values Other ((Γ.map typeMap).reverse ++ Δ) :=
  match values with
  | .nil => suffix
  | .cons first rest =>
      (rest.mapTypesReverseAppend typeMap transform (.cons (transform first) suffix)).castContext
        (by simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append])

theorem Values.mapTypesReverseAppend_eq {OtherTy : Type} {Value : Ty → Type}
    {Other : OtherTy → Type} (typeMap : Ty → OtherTy)
    (transform : {ty : Ty} → Value ty → Other (typeMap ty)) {Γ : List Ty} {Δ : List OtherTy}
    (values : Values Value Γ) (suffix : Values Other Δ) :
    values.mapTypesReverseAppend typeMap transform suffix =
      (values.mapTypes typeMap transform).reverseAppend suffix := by
  induction values generalizing Δ with
  | nil => rfl
  | cons first rest ih => simp only [mapTypesReverseAppend, mapTypes, reverseAppend, ih]

def Values.mapTypesIterative {OtherTy : Type} {Value : Ty → Type} {Other : OtherTy → Type}
    (typeMap : Ty → OtherTy) (transform : {ty : Ty} → Value ty → Other (typeMap ty))
    {Γ : List Ty} (values : Values Value Γ) : Values Other (Γ.map typeMap) :=
  ((values.mapTypesReverseAppend typeMap transform .nil).reverseAppend .nil).castContext
    (by simp only [List.append_nil, List.reverse_reverse])

@[csimp] theorem Values.mapTypes_eq_mapTypesIterative :
    @Values.mapTypes = @Values.mapTypesIterative := by
  funext Ty OtherTy Value Other typeMap transform Γ values
  apply Eq.symm
  apply eq_of_heq
  unfold mapTypesIterative
  rw [mapTypesReverseAppend_eq]
  exact (castContext_heq _ _).trans
    (((values.mapTypes typeMap transform).reverseAppend_twice .nil .nil).trans
      (values.mapTypes typeMap transform).append_nil)

def Values.toList {Value : Ty → Type} {A : Type}
    (transform : {ty : Ty} → Value ty → A) {Γ : List Ty} (values : Values Value Γ) : List A :=
  match values with
  | .nil => []
  | .cons first rest => transform first :: rest.toList transform

def Values.toReversedList {Value : Ty → Type} {A : Type}
    (transform : {ty : Ty} → Value ty → A) {Γ : List Ty}
    (values : Values Value Γ) (suffix : List A) : List A :=
  match values with
  | .nil => suffix
  | .cons first rest => rest.toReversedList transform (transform first :: suffix)

theorem Values.toReversedList_eq {Value : Ty → Type} {A : Type}
    (transform : {ty : Ty} → Value ty → A) {Γ : List Ty}
    (values : Values Value Γ) (suffix : List A) :
    values.toReversedList transform suffix = (values.toList transform).reverse ++ suffix := by
  induction values generalizing suffix with
  | nil => rfl
  | cons first rest ih =>
    simp only [toReversedList, toList, ih, List.reverse_cons, List.append_assoc, List.singleton_append]

def Values.toListIterative {Value : Ty → Type} {A : Type}
    (transform : {ty : Ty} → Value ty → A) {Γ : List Ty} (values : Values Value Γ) : List A :=
  (values.toReversedList transform []).reverse

@[csimp] theorem Values.toList_eq_toListIterative : @Values.toList = @Values.toListIterative := by
  funext Ty Value A transform Γ values
  simp [toListIterative, toReversedList_eq]

@[simp] theorem Values.toList_castContext {Value : Ty → Type} {A : Type}
    (transform : {ty : Ty} → Value ty → A) {Γ Δ : List Ty}
    (same : Γ = Δ) (values : Values Value Γ) :
    (values.castContext same).toList transform = values.toList transform := by
  cases same
  rfl

theorem Values.toList_reverseAppend {Value : Ty → Type} {A : Type}
    (transform : {ty : Ty} → Value ty → A) {Γ Δ : List Ty}
    (values : Values Value Γ) (suffix : Values Value Δ) :
    (values.reverseAppend suffix).toList transform =
      (values.toList transform).reverse ++ suffix.toList transform := by
  induction values generalizing Δ with
  | nil => rfl
  | cons first rest ih =>
    simp only [reverseAppend, toList_castContext, ih, toList,
      List.reverse_cons, List.append_assoc, List.singleton_append]

@[simp] theorem Values.toList_reverse {Value : Ty → Type} {A : Type}
    (transform : {ty : Ty} → Value ty → A) {Γ : List Ty} (values : Values Value Γ) :
    values.reverse.toList transform = (values.toList transform).reverse := by
  simp only [reverse, toList_castContext, toList_reverseAppend, toList, List.append_nil]

@[inline] def Values.castOption {Value : Ty → Type} {Γ Δ : List Ty} (same : Γ = Δ)
    (values : Option (Values Value Γ)) : Option (Values Value Δ) := same ▸ values

@[simp] theorem Values.castOption_isSome {Value : Ty → Type} {Γ Δ : List Ty} (same : Γ = Δ)
    (values : Option (Values Value Γ)) : (castOption same values).isSome = values.isSome := by
  cases same
  rfl

@[simp] theorem Values.castOption_none {Value : Ty → Type} {Γ Δ : List Ty} (same : Γ = Δ) :
    castOption (Value := Value) same none = none := by cases same; rfl

@[simp] theorem Values.castOption_some {Value : Ty → Type} {Γ Δ : List Ty} (same : Γ = Δ)
    (values : Values Value Γ) : castOption same (some values) = some (values.castContext same) := by
  cases same
  rfl

/-- Partial typed mapping. The compiler uses the proved accumulator variant. -/
def Values.mapTypesOption {OtherTy : Type} {Value : Ty → Type} {Other : OtherTy → Type}
    (typeMap : Ty → OtherTy) (transform : {ty : Ty} → Value ty → Option (Other (typeMap ty)))
    {Γ : List Ty} (values : Values Value Γ) : Option (Values Other (Γ.map typeMap)) :=
  match values with
  | .nil => some .nil
  | .cons first rest => do
      let first ← transform first
      let rest ← rest.mapTypesOption typeMap transform
      return .cons first rest

def Values.mapTypesOptionReverseAppend {OtherTy : Type} {Value : Ty → Type} {Other : OtherTy → Type}
    (typeMap : Ty → OtherTy) (transform : {ty : Ty} → Value ty → Option (Other (typeMap ty)))
    {Γ : List Ty} {Δ : List OtherTy} (values : Values Value Γ) (suffix : Values Other Δ) :
    Option (Values Other ((Γ.map typeMap).reverse ++ Δ)) :=
  match values with
  | .nil => some suffix
  | .cons first rest => do
      let first ← transform first
      castOption (by simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append])
        (rest.mapTypesOptionReverseAppend typeMap transform (.cons first suffix))

theorem Values.mapTypesOptionReverseAppend_eq {OtherTy : Type} {Value : Ty → Type}
    {Other : OtherTy → Type} (typeMap : Ty → OtherTy)
    (transform : {ty : Ty} → Value ty → Option (Other (typeMap ty)))
    {Γ : List Ty} {Δ : List OtherTy} (values : Values Value Γ) (suffix : Values Other Δ) :
    values.mapTypesOptionReverseAppend typeMap transform suffix =
      (values.mapTypesOption typeMap transform).map (fun mapped => mapped.reverseAppend suffix) := by
  induction values generalizing Δ with
  | nil => rfl
  | cons first rest ih =>
    cases transformed : transform first with
    | none => simp [mapTypesOptionReverseAppend, mapTypesOption, transformed]
    | some firstValue =>
      simp only [mapTypesOptionReverseAppend, mapTypesOption, transformed]
      dsimp only [Bind.bind, Pure.pure, Option.bind]
      rw [ih]
      cases rest.mapTypesOption typeMap transform <;>
        simp [reverseAppend]

def Values.mapTypesOptionIterative {OtherTy : Type} {Value : Ty → Type} {Other : OtherTy → Type}
    (typeMap : Ty → OtherTy) (transform : {ty : Ty} → Value ty → Option (Other (typeMap ty)))
    {Γ : List Ty} (values : Values Value Γ) : Option (Values Other (Γ.map typeMap)) :=
  (values.mapTypesOptionReverseAppend typeMap transform .nil).map fun reversed =>
    (reversed.reverseAppend .nil).castContext (by simp only [List.append_nil, List.reverse_reverse])

@[csimp] theorem Values.mapTypesOption_eq_mapTypesOptionIterative :
    @Values.mapTypesOption = @Values.mapTypesOptionIterative := by
  funext Ty OtherTy Value Other typeMap transform Γ values
  unfold mapTypesOptionIterative
  rw [mapTypesOptionReverseAppend_eq]
  cases mapped : values.mapTypesOption typeMap transform with
  | none => rfl
  | some result =>
    apply congrArg some
    apply Eq.symm
    apply eq_of_heq
    exact (castContext_heq _ _).trans
      ((result.reverseAppend_twice .nil .nil).trans result.append_nil)

/-- Build a typed list from left to right, retaining a reversed accumulator.
Both this loop and the final reversal use constant stack for sibling elements. -/
def Values.ofListLoop? {Value : Ty → Type} (select : (ty : Ty) → Option (Value ty)) :
    (types : List Ty) → {seen : List Ty} → Values Value seen →
      Option (Values Value (seen.reverse ++ types))
  | [], _, seen => castOption (List.append_nil _).symm (some seen.reverse)
  | ty :: types, _, seen => do
      let value ← select ty
      castOption (by simp only [List.reverse_cons, List.append_assoc, List.singleton_append])
        (ofListLoop? select types (.cons value seen))

def Values.ofList? {Value : Ty → Type} (select : (ty : Ty) → Option (Value ty))
    (types : List Ty) : Option (Values Value types) :=
  ofListLoop? select types .nil

theorem Values.ofListLoop?_isSome_iff {Value : Ty → Type} (select : (ty : Ty) → Option (Value ty))
    (types : List Ty) {seen : List Ty} (values : Values Value seen) :
    (ofListLoop? select types values).isSome = true ↔
      ∀ ty ∈ types, (select ty).isSome = true := by
  induction types generalizing seen with
  | nil => simp [ofListLoop?]
  | cons ty types ih =>
    cases found : select ty with
    | none => simp [ofListLoop?, found]
    | some first => simpa [ofListLoop?, found] using ih (.cons first values)

theorem Values.ofList?_isSome_iff {Value : Ty → Type} (select : (ty : Ty) → Option (Value ty))
    (types : List Ty) :
    (ofList? select types).isSome = true ↔ ∀ ty ∈ types, (select ty).isSome = true :=
  ofListLoop?_isSome_iff select types .nil

abbrev Environment (Value : Ty → Type) (Γ : List Ty) :=
  {ty : Ty} → Var Γ ty → Value ty

def Environment.push {Value : Ty → Type} {Γ : List Ty} {ty : Ty}
    (env : Environment Value Γ) (value : Value ty) : Environment Value (ty :: Γ)
  | _, .here => value
  | _, .there v => env v

/-- Bind ordered results in front of the retained caller context. -/
def Environment.prepend {Value : Ty → Type} {Γ Δ : List Ty}
    (env : Environment Value Γ) (values : Values Value Δ) : Environment Value (Δ ++ Γ) :=
  match values with
  | .nil => env
  | .cons value rest => Environment.push (Environment.prepend env rest) value

/-- Preserve a variable while adding a prefix to its context. -/
def Var.weakenPrefix {Γ : List Ty} {ty : Ty} (extra : List Ty)
    (value : Var Γ ty) : Var (extra ++ Γ) ty :=
  match extra with
  | [] => value
  | _ :: rest => .there (value.weakenPrefix rest)

@[inline] def Var.castContext {Γ Δ : List Ty} {ty : Ty} (same : Γ = Δ)
    (value : Var Γ ty) : Var Δ ty := same ▸ value

@[simp] theorem Var.index_castContext {Γ Δ : List Ty} {ty : Ty} (same : Γ = Δ)
    (value : Var Γ ty) : (value.castContext same).index = value.index := by
  cases same
  rfl

/-- Add a prefix recorded in reverse order. Both the variable and its context
are constructed one cell at a time, without an outstanding recursive frame. -/
def Var.weakenReversed {Γ : List Ty} {ty : Ty} (extra : List Ty)
    (value : Var Γ ty) : Var (extra.reverse ++ Γ) ty :=
  match extra with
  | [] => value
  | head :: rest =>
      ((Var.there (head := head) value).weakenReversed rest).castContext
        (by simp only [List.reverse_cons, List.append_assoc, List.singleton_append])

@[simp] theorem Var.index_weakenReversed {Γ : List Ty} {ty : Ty} (extra : List Ty)
    (value : Var Γ ty) : (value.weakenReversed extra).index = extra.length + value.index := by
  induction extra generalizing Γ with
  | nil => simp [weakenReversed]
  | cons head rest ih =>
    simpa [weakenReversed, index, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (Var.there (head := head) value)

@[simp] theorem Environment.prepend_weakenPrefix {Value : Ty → Type} {Γ Δ : List Ty}
    {ty : Ty} (env : Environment Value Γ) (values : Values Value Δ) (value : Var Γ ty) :
    env.prepend values (value.weakenPrefix Δ) = env value := by
  induction values with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- An explicit, ordered map of operands into the surrounding context. -/
abbrev Operands (Γ : List Ty) := Values (Var Γ)

def Operands.eval {Value : Ty → Type} {Γ args : List Ty}
    (env : Environment Value Γ) : Operands Γ args → Values Value args
  | .nil => .nil
  | .cons v tail => .cons (env v) (Operands.eval env tail)

def Operands.evalMapped {Value : Ty → Type} {Γ args : List Ty}
    (env : Environment Value Γ) (operands : Operands Γ args) : Values Value args :=
  operands.map env

@[csimp] theorem Operands.eval_eq_evalMapped : @Operands.eval = @Operands.evalMapped := by
  funext Ty Value Γ args env operands
  induction operands with
  | nil => rfl
  | cons first rest ih => simpa only [eval, evalMapped, Values.map] using congrArg (Values.cons (env first)) ih

theorem Operands.get_eval {Value : Ty → Type} {Γ args : List Ty} {ty : Ty}
    (env : Environment Value Γ) (operands : Operands Γ args) (value : Var args ty) :
    (Operands.eval env operands).get value = env (operands.get value) := by
  induction operands with
  | nil => cases value
  | cons head tail ih => cases value with
    | here => rfl
    | there value => exact ih value

abbrev Renaming (Γ Δ : List Ty) := {ty : Ty} → Var Γ ty → Var Δ ty

def Renaming.lift {Γ Δ : List Ty} {ty : Ty} (rename : Renaming Γ Δ) :
    Renaming (ty :: Γ) (ty :: Δ)
  | _, .here => .here
  | _, .there v => .there (rename v)

def Operands.rename {Γ Δ args : List Ty} (rename : Renaming Γ Δ) :
    Operands Γ args → Operands Δ args
  | .nil => .nil
  | .cons v tail => .cons (rename v) (Operands.rename rename tail)

theorem Operands.eval_rename {Value : Ty → Type} {Γ Δ args : List Ty}
    (rename : Renaming Γ Δ) (env : Environment Value Δ) (operands : Operands Γ args) :
    Operands.eval env (Operands.rename rename operands) =
      Operands.eval (fun v => env (rename v)) operands := by
  induction operands with
  | nil => rfl
  | cons v tail ih => simp only [Operands.rename, eval, ih]

theorem Environment.push_rename {Value : Ty → Type} {Γ Δ : List Ty} {ty : Ty}
    (rename : Renaming Γ Δ) (env : Environment Value Δ) (value : Value ty) :
    @Eq (Environment Value (ty :: Γ))
      (fun v => env.push value (Renaming.lift rename v))
      (Environment.push (fun v => env (rename v)) value) := by
  funext result v
  cases v <;> rfl

end Zkc.Source
