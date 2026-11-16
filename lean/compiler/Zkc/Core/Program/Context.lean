module

public import Zkc.Core.Program.Vocabulary

@[expose] public section

/-!
Contexts whose variables are names.

A context is the names in scope with their types: a finite map behind a small interface
(`Ctx.empty`, `Ctx.find?`, `Ctx.insert`, `Ctx.find?_empty`, `Ctx.find?_insert`). It is a binary
trie on the digits of the name, so that the kernel finds or binds a name in as many steps as the
name has binary digits, however far the binding is. Nothing outside this file looks inside a
context.

A variable is a name that the context has at its type: its only data is the name. A binding
carries the names that it binds, one per type, and extends the context by them. An environment
gives the value of every name in scope; one value changes its type along an equation, in
`Env.insert`, and nowhere else.
-/

namespace Zkc.Core

/-! ## The map -/

/-- A finite map from naturals, as a binary trie. -/
inductive NatMap (α : Type) where
  | leaf
  | node (here : Option α) (zero one : NatMap α)

namespace NatMap
variable {α : Type}

/-- The value at a key. -/
def find : NatMap α → Nat → Option α
  | leaf, _ => none
  | node here _ _, 0 => here
  | node _ zero one, k + 1 => cond (Nat.beq (k % 2) 0) (find zero (k / 2)) (find one (k / 2))

/-- Insertion with a bound on the depth (the key plus one always suffices). -/
def insertAux (v : α) : Nat → NatMap α → Nat → NatMap α
  | 0, t, _ => t
  | _ + 1, leaf, 0 => node (some v) leaf leaf
  | _ + 1, node _ zero one, 0 => node (some v) zero one
  | fuel + 1, leaf, k + 1 =>
      cond (Nat.beq (k % 2) 0) (node none (insertAux v fuel leaf (k / 2)) leaf)
        (node none leaf (insertAux v fuel leaf (k / 2)))
  | fuel + 1, node here zero one, k + 1 =>
      cond (Nat.beq (k % 2) 0) (node here (insertAux v fuel zero (k / 2)) one)
        (node here zero (insertAux v fuel one (k / 2)))

/-- The map with the value `v` at the key `k`. -/
def insert (t : NatMap α) (k : Nat) (v : α) : NatMap α := insertAux v (k + 1) t k

theorem find_leaf (k : Nat) : (leaf : NatMap α).find k = none := rfl

/-- The test of a parity, as its decision. -/
theorem beq_parity (k : Nat) : Nat.beq (k % 2) 0 = decide (k % 2 = 0) := by
  cases test : Nat.beq (k % 2) 0
  · have odd : k % 2 ≠ 0 := Nat.ne_of_beq_eq_false test
    simp [odd]
  · have even : k % 2 = 0 := Nat.eq_of_beq_eq_true test
    simp [even]

theorem find_insertAux (v : α) :
    ∀ (fuel : Nat) (t : NatMap α) (k k' : Nat), k < fuel →
      (insertAux v fuel t k).find k' = if k' = k then some v else t.find k'
  | 0, _, _, _, bound => absurd bound (Nat.not_lt_zero _)
  | _ + 1, leaf, 0, 0, _ => rfl
  | _ + 1, leaf, 0, k' + 1, _ => by
      cases parity : Nat.beq (k' % 2) 0 <;> simp [insertAux, find, parity]
  | _ + 1, node .., 0, 0, _ => rfl
  | _ + 1, node .., 0, k' + 1, _ => by simp [insertAux, find]
  | fuel + 1, leaf, k + 1, 0, _ => by
      cases parity : Nat.beq (k % 2) 0 <;> simp [insertAux, find, parity]
  | fuel + 1, node .., k + 1, 0, _ => by
      cases parity : Nat.beq (k % 2) 0 <;> simp [insertAux, find, parity]
  | fuel + 1, leaf, k + 1, k' + 1, bound => by
      have inner := find_insertAux v fuel leaf (k / 2) (k' / 2) (by omega)
      simp only [insertAux, find, beq_parity]
      by_cases even : k % 2 = 0 <;> by_cases even' : k' % 2 = 0 <;>
        simp only [even, even', decide_true, decide_false, Bool.cond_true, Bool.cond_false, find,
          beq_parity, inner] <;>
        first
          | (have same : (k' / 2 = k / 2) ↔ (k' = k) := by omega
             simp [same])
          | (have differ : ¬ (k' = k) := by omega
             simp [differ])
  | fuel + 1, node here zero one, k + 1, k' + 1, bound => by
      have inZero := find_insertAux v fuel zero (k / 2) (k' / 2) (by omega)
      have inOne := find_insertAux v fuel one (k / 2) (k' / 2) (by omega)
      simp only [insertAux, find, beq_parity]
      by_cases even : k % 2 = 0 <;> by_cases even' : k' % 2 = 0 <;>
        simp only [even, even', decide_true, decide_false, Bool.cond_true, Bool.cond_false, find,
          beq_parity, inZero, inOne] <;>
        first
          | (have same : (k' / 2 = k / 2) ↔ (k' = k) := by omega
             simp [same])
          | (have differ : ¬ (k' = k) := by omega
             simp [differ])

/-- What a key gives after an insertion. -/
theorem find_insert (t : NatMap α) (k : Nat) (v : α) (k' : Nat) :
    (t.insert k v).find k' = if k' = k then some v else t.find k' :=
  find_insertAux v (k + 1) t k k' (Nat.lt_succ_self k)

end NatMap

/-- The names in scope with their types. -/
structure Ctx (T : Type) where
  map : NatMap T

namespace Ctx
variable {T : Type}

/-- No name in scope. -/
def empty : Ctx T := ⟨.leaf⟩

/-- The type of a name in scope. -/
def find? (Γ : Ctx T) (name : Name) : Option T := Γ.map.find name

/-- The context with a name bound to a type; a name bound before is bound anew. -/
def insert (Γ : Ctx T) (name : Name) (τ : T) : Ctx T := ⟨Γ.map.insert name τ⟩

theorem find?_empty (name : Name) : (empty : Ctx T).find? name = none := rfl

theorem find?_insert (Γ : Ctx T) (bound : Name) (τ : T) (name : Name) :
    (Γ.insert bound τ).find? name = if name = bound then some τ else Γ.find? name :=
  NatMap.find_insert Γ.map bound τ name

end Ctx

/-! ## Names of a binding, variables, environments -/

section
variable {T : Type}

/-- One name for each of the types. -/
abbrev Names (types : List T) : Type := HList (fun _ : T => Name) types

/-- The names, as a list. -/
def Names.toList : {types : List T} → Names types → List Name
  | [], .nil => []
  | _ :: _, .cons name rest => name :: Names.toList rest

/-- The names of a list, one for each of the types, when there are as many. -/
def Names.ofList : (types : List T) → List Name → Option (Names types)
  | [], [] => some .nil
  | _ :: types, name :: names => (Names.ofList types names).map fun rest => .cons name rest
  | _, _ => none

theorem Names.ofList_toList : ∀ {types : List T} (bound : Names types),
    Names.ofList types bound.toList = some bound
  | [], .nil => rfl
  | _ :: _, .cons name rest => by
      simp only [Names.toList, Names.ofList, Names.ofList_toList rest, Option.map_some]

theorem Names.toList_of_ofList : ∀ (types : List T) (names : List Name) (bound : Names types),
    Names.ofList types names = some bound → bound.toList = names
  | [], [], .nil, _ => rfl
  | [], _ :: _, _, found => nomatch found
  | _ :: _, [], _, found => nomatch found
  | _ :: types, name :: names, bound, found => by
      simp only [Names.ofList] at found
      cases rest : Names.ofList types names with
      | none => simp [rest] at found
      | some inner =>
          simp only [rest, Option.map_some, Option.some.injEq] at found
          subst found
          simp only [Names.toList, Names.toList_of_ofList types names inner rest]

theorem Names.length_toList : ∀ {types : List T} (bound : Names types),
    bound.toList.length = types.length
  | [], .nil => rfl
  | _ :: _, .cons _ rest => congrArg (· + 1) (Names.length_toList rest)

/-- The context with the names bound to the types, in order: a later name is bound anew. -/
def Ctx.extend (Γ : Ctx T) : {types : List T} → Names types → Ctx T
  | [], .nil => Γ
  | τ :: _, .cons name rest => (Γ.insert name τ).extend rest

/-- A variable: a name that the context has at the type. -/
structure Var (Γ : Ctx T) (τ : T) where
  name : Name
  typed : Γ.find? name = some τ

theorem Var.ext {Γ : Ctx T} {τ : T} : ∀ {x y : Var Γ τ}, x.name = y.name → x = y
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- The names of variables. -/
def HList.names {Γ : Ctx T} : {items : List T} → HList (Var Γ) items → List Name
  | [], .nil => []
  | _ :: _, .cons x rest => x.name :: HList.names rest

/-- The values of the names in scope. -/
def Env (V : T → Type) (Γ : Ctx T) : Type :=
  ∀ (name : Name) (τ : T), Γ.find? name = some τ → V τ

variable {V : T → Type}

/-- The value of a variable. -/
def Env.get {Γ : Ctx T} {τ : T} (env : Env V Γ) (x : Var Γ τ) : V τ := env x.name τ x.typed

/-- The values of variables. -/
def Env.all {Γ : Ctx T} (env : Env V Γ) : {items : List T} → HList (Var Γ) items → HList V items
  | [], .nil => .nil
  | _ :: _, .cons x rest => .cons (env.get x) (env.all rest)

/-- No value: no name is in scope. -/
def Env.empty : Env V (Ctx.empty : Ctx T) :=
  fun name _ found => nomatch (Ctx.find?_empty (T := T) name).symm.trans found

/-- The values with one more name bound. This is the one place where a value changes its
type along an equation. -/
def Env.insert {Γ : Ctx T} (env : Env V Γ) (bound : Name) {τ : T} (v : V τ) :
    Env V (Γ.insert bound τ) :=
  fun name σ found =>
    if same : name = bound then
      cast (congrArg V (Option.some.inj
        ((ite_eq_left same).symm.trans ((Ctx.find?_insert Γ bound τ name).symm.trans found)))) v
    else
      env name σ ((ite_eq_right same).symm.trans ((Ctx.find?_insert Γ bound τ name).symm.trans found))

/-- The values with the names of a binding bound to its values. -/
def Env.extend {Γ : Ctx T} (env : Env V Γ) :
    {types : List T} → (bound : Names types) → HList V types → Env V (Γ.extend bound)
  | [], .nil, .nil => env
  | _ :: _, .cons name rest, .cons v vs => (env.insert name v).extend rest vs

end

end Zkc.Core
