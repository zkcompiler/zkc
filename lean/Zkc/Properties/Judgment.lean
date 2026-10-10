import Std

/-! Conditional evidence over a fixed mathematical subject.

Contexts may package types, relation families and interpretations. Their universe
is independent of the `Type`-level executable process and source carriers.
-/

set_option autoImplicit false

namespace PIR.Properties

universe u

/-- Context fixes actual subjects, interpretations, input scopes and observers.
    A premise is a proposition on that same context, not a name or hash. -/
structure Conditional (Context : Type u) (claim : Context → Prop) where
  requires : Context → Prop
  valid : ∀ ctx, requires ctx → claim ctx

variable {C : Type u} {P Q : C → Prop}

def Conditional.conjoin (left : Conditional C P) (right : Conditional C Q) :
    Conditional C (fun ctx => P ctx ∧ Q ctx) :=
  ⟨fun ctx => left.requires ctx ∧ right.requires ctx,
   fun ctx h => ⟨left.valid ctx h.1, right.valid ctx h.2⟩⟩

/-- Applying a transport rule retains both the producer and rule premises. -/
def Conditional.transport (producer : Conditional C P)
    (rule : Conditional C (fun ctx => P ctx → Q ctx)) : Conditional C Q :=
  ⟨fun ctx => producer.requires ctx ∧ rule.requires ctx,
   fun ctx h => rule.valid ctx h.2 (producer.valid ctx h.1)⟩

/-- A discharge proof must establish the actual contextual proposition. -/
theorem Conditional.use (j : Conditional C P) (ctx : C)
    (discharged : j.requires ctx) : P ctx := j.valid ctx discharged

inductive Inconclusive where
  | missingInterpretation | unsupported | resourceLimit | checkerDefect
  deriving DecidableEq, Repr

/-- Logical checking results. Runtime Stop and process death are other types.
    A native checker must be connected to this evidence-bearing result. -/
inductive Check (proposition : Prop) where
  | established : proposition → Check proposition
  | refuted : (¬ proposition) → Check proposition
  | unknown : Inconclusive → Check proposition

def Check.proves {proposition : Prop} : Check proposition → Prop
  | .established _ => True
  | _ => False

theorem Check.proves_sound {proposition : Prop} (out : Check proposition)
    (yes : out.proves) : proposition := by
  cases out with
  | established h => exact h
  | refuted h => exact False.elim yes
  | unknown why => exact False.elim yes

/-- Feasibility/legality and the caller's requirements are separate evidence. -/
structure Usable (legal requirement : Prop) : Prop where
  legality : legal
  requested : requirement

/-- An interval establishes a comparison only when both separating endpoints
    constrain the actual costs. Comparing two upper bounds is insufficient. -/
theorem separated_costs (actualA upperA lowerB actualB : Nat)
    (ha : actualA ≤ upperA) (separates : upperA ≤ lowerB) (hb : lowerB ≤ actualB) :
    actualA ≤ actualB := Nat.le_trans ha (Nat.le_trans separates hb)

end PIR.Properties
