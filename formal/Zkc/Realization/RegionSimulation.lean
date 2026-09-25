import Zkc.Source.Region
import Zkc.Realization.Simulation

/-! Complete execution refinement for compact regions with represented values.

Values may denote objects in the final store. Local operation correctness must
also preserve every existing represented value, so captures and old aliases
remain valid in continuations. This immutable-value frame is a sufficient rule;
mutable or releasing targets need a liveness-sensitive rule instead.

Control is the existing `Source.Region`, interpreted twice. This module neither
introduces a second control grammar nor proves an external decoder or allocator.
-/

set_option autoImplicit false
namespace Zkc.Realization
open Zkc.Source

structure Representation {Ty : Type} (Left Right : Ty → Type) (S T : Type) where
  states : S → T → Prop
  value : (ty : Ty) → Left ty → S → Right ty → T → Prop

namespace Representation
variable {Ty S T E F O : Type} {Left Right : Ty → Type}
variable (rep : Representation Left Right S T)

/-- All currently represented values survive. New allocation is permitted. -/
def Frame (s : S) (t : T) (s' : S) (t' : T) : Prop :=
  ∀ ty a b, rep.value ty a s b t → rep.value ty a s' b t'

theorem Frame.refl (s : S) (t : T) : rep.Frame s t s t := fun _ _ _ h => h

theorem Frame.trans {s s' s'' : S} {t t' t'' : T}
    (first : rep.Frame s t s' t') (second : rep.Frame s' t' s'' t'') :
    rep.Frame s t s'' t'' := fun ty a b h => second ty a b (first ty a b h)

def Environments {Γ : List Ty} (a : Environment Left Γ) (s : S)
    (b : Environment Right Γ) (t : T) : Prop :=
  ∀ ty (v : Var Γ ty), rep.value ty (a v) s (b v) t

theorem Environments.frame {Γ : List Ty} {a : Environment Left Γ}
    {b : Environment Right Γ} {s s' : S} {t t' : T}
    (env : rep.Environments a s b t) (kept : rep.Frame s t s' t') :
    rep.Environments a s' b t' := fun ty v => kept ty _ _ (env ty v)

theorem Environments.push {Γ : List Ty} {ty : Ty} {a : Environment Left Γ}
    {b : Environment Right Γ} {s : S} {t : T} {x : Left ty} {y : Right ty}
    (env : rep.Environments a s b t) (value : rep.value ty x s y t) :
    rep.Environments (a.push x) s (b.push y) t := by
  intro result v
  cases v with
  | here => exact value
  | there v => exact env result v

/-- In addition to the returned value, retain the frame on stopped executions. -/
abbrev Results (left : E → List O) (right : F → List O) {ty : Ty}
    (s : S) (t : T) (a : PIR.Execution S E (Left ty))
    (b : PIR.Execution T F (Right ty)) : Prop :=
  PIR.Execution.Relates
    (fun s' t' => rep.states s' t' ∧ rep.Frame s t s' t')
    (rep.value ty) left right a b

theorem Results.rebase {left : E → List O} {right : F → List O} {ty : Ty}
    {s s' : S} {t t' : T} {a : PIR.Execution S E (Left ty)}
    {b : PIR.Execution T F (Right ty)} (result : rep.Results left right s' t' a b)
    (kept : rep.Frame s t s' t') : rep.Results left right s t a b :=
  ⟨result.outcome, ⟨result.state.1, kept.trans rep result.state.2⟩, result.events⟩

theorem Results.follow {left : E → List O} {right : F → List O} {ty out : Ty}
    {s : S} {t : T} {a : PIR.Execution S E (Left ty)}
    {b : PIR.Execution T F (Right ty)}
    (result : rep.Results left right s t a b)
    (nextA : Left ty → S → PIR.Execution S E (Left out))
    (nextB : Right ty → T → PIR.Execution T F (Right out))
    (next : ∀ x s' y t', rep.states s' t' → rep.Frame s t s' t' →
      rep.value ty x s' y t' →
      rep.Results left right s' t' (nextA x s') (nextB y t')) :
    rep.Results left right s t (a.follow nextA) (b.follow nextB) := by
  apply PIR.Execution.Relates.follow _ _ _ _ _ _ _ result nextA nextB
  intro x s' y t' related value
  exact (next x s' y t' related.1 related.2 value).rebase rep related.2

theorem Results.repeat {I J : PIR.Signature} {left : E → List O} {right : F → List O}
    {ty : Ty} (h : PIR.Handler I S E) (g : PIR.Handler J T F)
    (bodyA : Left ty → PIR.Proc I (Left ty)) (bodyB : Right ty → PIR.Proc J (Right ty))
    (s : S) (t : T)
    (step : ∀ x s' y t', rep.states s' t' → rep.Frame s t s' t' →
      rep.value ty x s' y t' →
      rep.Results left right s' t' ((bodyA x).run h s') ((bodyB y).run g t'))
    (count : Nat) (x : Left ty) (y : Right ty) (related : rep.states s t)
    (value : rep.value ty x s y t) :
    rep.Results left right s t
      ((PIR.repeatN count bodyA x).run h s) ((PIR.repeatN count bodyB y).run g t) := by
  suffices all : ∀ count x s' y t', rep.states s' t' → rep.Frame s t s' t' →
      rep.value ty x s' y t' → rep.Results left right s' t'
        ((PIR.repeatN count bodyA x).run h s') ((PIR.repeatN count bodyB y).run g t') from
    all count x s y t related (Representation.Frame.refl rep s t) value
  intro count
  induction count with
  | zero =>
    intro x s' y t' related _ value
    exact ⟨value, ⟨related, Representation.Frame.refl rep s' t'⟩, rfl⟩
  | succ count ih =>
    intro x s' y t' related kept value
    simp only [PIR.repeatN, PIR.run_bind]
    apply Results.follow rep (step x s' y t' related kept value)
    intro a u b v related more value
    exact ih a u b v related (kept.trans rep more) value

end Representation

variable {language : Language} {I J : PIR.Signature} {S T E F O : Type}

/-- Supply local execution laws for the actual interpretations and handlers.
This does not follow from matching operation names or equal handle numbers. -/
structure RegionSimulation (source : Interpretation language I)
    (target : Interpretation language J) (h : PIR.Handler I S E) (g : PIR.Handler J T F)
    (rep : Representation source.Value target.Value S T)
    (left : E → List O) (right : F → List O) : Prop where
  condition : ∀ s t a b, rep.states s t → rep.value language.condition a s b t →
    source.condition a = target.condition b
  operation : ∀ op s t (a : Values source.Value (language.arguments op))
      (b : Values target.Value (language.arguments op)), rep.states s t →
    rep.Environments a.get s b.get t →
    rep.Results left right s t
      ((source.operation op a).run h s) ((target.operation op b).run g t)

namespace RegionSimulation
variable {source : Interpretation language I} {target : Interpretation language J}
variable {h : PIR.Handler I S E} {g : PIR.Handler J T F}
variable {rep : Representation source.Value target.Value S T}
variable {left : E → List O} {right : F → List O}

private theorem operands_related {Γ args : List language.Ty}
    (operands : Operands Γ args) {a : Environment source.Value Γ}
    {b : Environment target.Value Γ} {s : S} {t : T} (env : rep.Environments a s b t) :
    rep.Environments (operands.eval a).get s (operands.eval b).get t := by
  induction operands with
  | nil => intro ty v; cases v
  | cons v rest ih =>
    intro ty index
    cases index with
    | here => exact env _ v
    | there index => exact ih ty index

/-- Lift operation and alias laws through branches, bounded loops and one shared
continuation. No flattening or unrolling is used to define the target. -/
theorem run (simulation : RegionSimulation source target h g rep left right)
    {Γ : List language.Ty} {ty : language.Ty} (region : Region language Γ ty)
    (a : Environment source.Value Γ) (b : Environment target.Value Γ)
    (s : S) (t : T) (related : rep.states s t) (env : rep.Environments a s b t) :
    rep.Results left right s t
      ((region.denote source a).run h s) ((region.denote target b).run g t) := by
  induction region generalizing s t with
  | ret v => exact ⟨env _ v, ⟨related, Representation.Frame.refl rep s t⟩, rfl⟩
  | stop why => exact ⟨rfl, ⟨related, Representation.Frame.refl rep s t⟩, rfl⟩
  | letOp op args next ih =>
    simp only [Region.denote, PIR.run_bind]
    apply Representation.Results.follow rep
      (simulation.operation op s t _ _ related (operands_related args env))
    intro x s' y t' related kept value
    exact ih (a.push x) (b.push y) s' t' related ((env.frame rep kept).push rep value)
  | branch condition yes no yesIH noIH =>
    simp only [Region.denote, simulation.condition s t _ _ related (env _ condition)]
    split
    · exact yesIH a b s t related env
    · exact noIH a b s t related env
  | iterate count initial body next bodyIH nextIH =>
    simp only [Region.denote, PIR.run_bind]
    have repeated := Representation.Results.repeat rep h g
      (fun value => body.denote source (a.push value))
      (fun value => body.denote target (b.push value)) s t
      (fun x s' y t' related kept value =>
        bodyIH (a.push x) (b.push y) s' t' related ((env.frame rep kept).push rep value))
      count (a initial) (b initial) related (env _ initial)
    apply Representation.Results.follow rep repeated
    intro x s' y t' related kept value
    exact nextIH (a.push x) (b.push y) s' t' related ((env.frame rep kept).push rep value)
  | bind body next bodyIH nextIH =>
    simp only [Region.denote, PIR.run_bind]
    apply Representation.Results.follow rep (bodyIH a b s t related env)
    intro x s' y t' related kept value
    exact nextIH (a.push x) (b.push y) s' t' related ((env.frame rep kept).push rep value)

end RegionSimulation
end Zkc.Realization
