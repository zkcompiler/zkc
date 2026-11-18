module

public import Zkc.Core.Program.Typed

@[expose] public section

/-!
The description of a handler: a layer of a role, as a deployment holds it.

The code of a layer reads its inputs by position: it is a term in the context that binds the
inputs of the types given to the names `0, 1, 2, …` in order (`Ctx.positional`), and it runs on
the environment of their values in order (`Env.positional`). This is the one such context of the
core.
-/

namespace Zkc.Core

/-! ## The context of inputs by position -/

section
variable {T : Type}

/-- The names `start, start + 1, …`, one for each of the types, in order. -/
def Names.counting (start : Name) : (types : List T) → Names types
  | [] => .nil
  | _ :: rest => .cons start (Names.counting (start + 1) rest)

/-- The context that binds inputs of the types given to the names `0, 1, 2, …` in order: a
name is the position of its input. -/
def Ctx.positional (types : List T) : Ctx T := Ctx.empty.extend (Names.counting 0 types)

/-- What a context extended by the names counted from `start` has at a name: the type at the
name's position among them when it is one of them, and otherwise what the context had. -/
theorem Ctx.find?_extend_counting : ∀ (types : List T) (Γ : Ctx T) (start name : Nat),
    (Γ.extend (Names.counting start types)).find? name =
      if start ≤ name ∧ name < start + types.length then types[name - start]?
      else Γ.find? name
  | [], Γ, start, name => by
      have outside : ¬ (start ≤ name ∧ name < start + 0) := by omega
      simp only [Names.counting, Ctx.extend, List.length_nil, outside, ↓reduceIte]
  | τ :: rest, Γ, start, name => by
      simp only [Names.counting, Ctx.extend, Ctx.find?_extend_counting rest, Ctx.find?_insert,
        List.length_cons]
      by_cases below : name < start
      · have outside : ¬ (start ≤ name ∧ name < start + (rest.length + 1)) := by omega
        have outsideRest : ¬ (start + 1 ≤ name ∧ name < start + 1 + rest.length) := by omega
        have other : name ≠ start := by omega
        simp only [outside, outsideRest, other, ↓reduceIte]
      · by_cases here : name = start
        · subst here
          have outsideRest : ¬ (name + 1 ≤ name ∧ name < name + 1 + rest.length) := by omega
          simp only [outsideRest, ↓reduceIte, Nat.le_refl, Nat.sub_self,
            List.getElem?_cons_zero, true_and]
          have inside : name < name + (rest.length + 1) := by omega
          simp only [inside, ↓reduceIte]
        · have position : name - start = (name - (start + 1)) + 1 := by omega
          have atLeast : start ≤ name := by omega
          simp only [here, ↓reduceIte, position, List.getElem?_cons_succ, atLeast, true_and]
          by_cases inside : name < start + 1 + rest.length
          · have inside' : name < start + (rest.length + 1) := by omega
            have atLeast' : start + 1 ≤ name := by omega
            simp only [inside, inside', atLeast', true_and, ↓reduceIte]
          · have outside' : ¬ name < start + (rest.length + 1) := by omega
            simp only [inside, outside', and_false, ↓reduceIte]

/-- The context of inputs by position has at each position the type of the input there, and
nothing past the last. -/
theorem Ctx.find?_positional (types : List T) (position : Nat) :
    (Ctx.positional types).find? position = types[position]? := by
  rw [Ctx.positional, Ctx.find?_extend_counting, Ctx.find?_empty, Nat.zero_add]
  by_cases inside : position < types.length
  · rw [ite_eq_left ⟨Nat.zero_le position, inside⟩, Nat.sub_zero]
  · rw [ite_eq_right fun both => inside both.2]
    exact (List.getElem?_eq_none (Nat.le_of_not_lt inside)).symm

/-- The environment of inputs by position, from their values in order. -/
def Env.positional {V : T → Type} {types : List T} (values : HList V types) :
    Env V (Ctx.positional types) :=
  Env.empty.extend (Names.counting 0 types) values

end

/-! ## The description of a handler -/

/-- One effect of a role program: the site of its event, the role's part, what the effect
takes and what it gives back. -/
structure EffectSite (V : Vocabulary) where
  site : Site
  part : Part V
  takes : List V.Ty
  gives : List V.Ty

/-- The values of a role alone. -/
def alone {V : Vocabulary} (r : Role) (types : List V.Ty) : List (LTy V) :=
  types.map fun τ => ⟨τ, [r]⟩

/-- A clause: the code that answers one effect, from what the effect takes and the state to
what it gives back and the next state. It is a role's code: operations of the vocabulary,
functions of the program, and effects, which the layer below answers. It reads what the effect
takes and the state by position. -/
structure Clause (V : Vocabulary) (hs : Headers V) (r : Role) (state : V.Ty) where
  site : EffectSite V
  code : Term (roleDialect V hs r) (Ctx.positional (alone r (site.takes ++ [state])))
    (alone r (site.gives ++ [state]))

/-- The types of the inputs that a role holds, in order. -/
def held {V : Vocabulary} (r : Role) : List (LTy V) → List V.Ty
  | [] => []
  | a :: rest => if r ∈ a.holders then a.ty :: held r rest else held r rest

/-- The part of a scheme's declaration that a layer is: the construction, the layout, the
derivation of the samples, the context, or one of the grinds or commitments, by its position
among them. -/
inductive LineTag where
  | construction
  | layout
  | samples
  | context
  | grind (index : Nat)
  | commitment (index : Nat)
deriving DecidableEq, Repr

/-- One handler of a role, as a deployment holds it: a checked description, which the
executor interprets and the back end specialises into the role program. `ins` are the
located types of the inputs of the entry. -/
structure Layer (V : Vocabulary) (hs : Headers V) (r : Role) (ins : List (LTy V)) where
  /-- The part of the declaration that the layer is. -/
  line : LineTag
  state : V.Ty
  /-- What it is given from outside the run at its start (a proof to read), and what it
  gives at the end (the proof written). -/
  takes : List V.Ty
  gives : List V.Ty
  /-- The effects that it answers; every other effect goes below. -/
  clauses : List (Clause V hs r state)
  /-- The state of the next attempt, from its number, the state at the attempt and the state
  at the stop, by position: what is taken from the first is local to an attempt, what is taken
  from the second grows. -/
  again : Term (localDialect V hs.fns) (Ctx.positional [.nat, state, state]) [state]
  /-- The first state: local code that reads what the layer takes and the inputs that the role
  holds, by position. It has no effects: effects belong to clauses. -/
  start : Term (localDialect V hs.fns) (Ctx.positional (takes ++ held r ins)) [state]
  /-- What the layer gives, from the last state at position `0`; it may stop. -/
  finish : Term (localDialect V hs.fns) (Ctx.positional [state]) gives

end Zkc.Core
