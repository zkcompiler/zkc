module

public import Zkc.Core.Program.Typed

@[expose] public section

/-!
The description of a handler: a layer of a role, as a deployment holds it.
-/

namespace Zkc.Core

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
functions of the program, and effects, which the layer below answers. -/
structure Clause (V : Vocabulary) (hs : Headers V) (r : Role) (state : V.Ty) where
  site : EffectSite V
  code : Term (roleDialect V hs r) (alone r (site.takes ++ [state])) (alone r (site.gives ++ [state]))

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
  at the stop: what is taken from the first is local to an attempt, what is taken from the
  second grows. -/
  again : Term (localDialect V hs.fns) [.nat, state, state] [state]
  /-- The first state: local code that reads what the layer takes and the inputs that the role
  holds. It has no effects: effects belong to clauses. -/
  start : Term (localDialect V hs.fns) (takes ++ held r ins) [state]
  /-- What the layer gives, from the last state; it may stop. -/
  finish : Term (localDialect V hs.fns) [state] gives

end Zkc.Core
