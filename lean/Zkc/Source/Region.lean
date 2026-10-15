module

public import Zkc.Source.Structure
public import Zkc.Semantics.ExactRefinement
public import Zkc.Semantics.MonadExecution

@[expose] public section

/-! Contextual laws for the shared typed region foundation.

Equality preserves reply-dependent continuations, stopped post-state and ordered
events. These laws do not assume that external replies are honest.
-/
set_option autoImplicit false
namespace Zkc.Source

variable {dialect : Dialect} {interface : PIR.Signature}

theorem Region.rename_identity {Γ out} (region : Region dialect Γ out) :
    region.rename (fun value => value) = region := by
  induction region using Region.rec (motive_2 := fun _ _ => True) with
  | ret values => simp only [Region.rename, Operands.rename_identity]
  | stop reason => rfl
  | letOp op args bodies next _ nextIH =>
    simp only [Region.rename, Operands.rename_identity, Renaming.liftPrefix_identity, nextIH]
  | bind body next bodyIH nextIH =>
    simp only [Region.rename, Renaming.liftPrefix_identity, bodyIH, nextIH]
  | nil => trivial
  | cons body tail bodyIH tailIH => trivial

theorem Region.rename_comp {Γ Δ Ξ out} (region : Region dialect Γ out)
    (first : Renaming Γ Δ) (second : Renaming Δ Ξ) :
    (region.rename first).rename second = region.rename (fun value => second (first value)) := by
  induction region using Region.rec (motive_2 := fun _ _ => True) generalizing Δ Ξ with
  | ret values => simp only [Region.rename, Operands.rename_comp]
  | stop reason => rfl
  | letOp op args bodies next _ nextIH =>
    simp only [Region.rename, Operands.rename_comp, nextIH, Renaming.liftPrefix_comp]
  | bind body next bodyIH nextIH =>
    simp only [Region.rename, bodyIH, nextIH, Renaming.liftPrefix_comp]
  | nil => trivial
  | cons body tail bodyIH tailIH => trivial

/-- Equality of dynamic processes under one meaning. Static source admission,
relation annotations and external artifact identity require separate contracts. -/
def Region.Equivalent (meaning : RegionMeaning dialect interface) {Γ out}
    (left right : Region dialect Γ out) : Prop :=
  ∀ env, left.denote meaning env = right.denote meaning env

/-- Contextual equality discharges the existing implementation contract. -/
theorem Region.exactRefinement (meaning : RegionMeaning dialect interface) {Γ out}
    {left right : Region dialect Γ out} (same : Equivalent meaning left right)
    (env : Environment meaning.Value Γ) :
    PIR.ExactRefinement (left.denote meaning env) (right.denote meaning env) := ⟨same env⟩

theorem Region.bind_congr (meaning : RegionMeaning dialect interface) {Γ mid out}
    {left right : Region dialect Γ mid} {next tail : Region dialect (mid ++ Γ) out}
    (body : Equivalent meaning left right) (suffix : Equivalent meaning next tail) :
    Equivalent meaning (.bind left next) (.bind right tail) := by
  intro env
  simp only [denote, body env]
  congr 1
  funext values
  exact suffix _

/-- Regions may be repeated, reordered or skipped by their operation contract. -/
theorem Region.operation_congr (meaning : RegionMeaning dialect interface) {Γ out}
    (op : dialect.Op) (arguments : Operands Γ (dialect.arguments op))
    {left right : Regions dialect (dialect.regions op)}
    {next tail : Region dialect (dialect.results op ++ Γ) out}
    (bodies : left.denote meaning = right.denote meaning)
    (suffix : Equivalent meaning next tail) :
    Equivalent meaning (.letOp op arguments left next) (.letOp op arguments right tail) := by
  intro env
  simp only [denote, bodies]
  congr 1
  funext values
  exact suffix _

theorem Regions.cons_congr (meaning : RegionMeaning dialect interface) {inputs outputs rest}
    {left right : Region dialect inputs outputs} {tail suffix : Regions dialect rest}
    (body : Region.Equivalent meaning left right)
    (remaining : tail.denote meaning = suffix.denote meaning) :
    (Regions.cons left tail).denote meaning = (Regions.cons right suffix).denote meaning := by
  simp only [denote, remaining]
  congr 1
  funext values
  exact body _

theorem Region.run_bind (meaning : RegionMeaning dialect interface)
    {S E : Type} (handler : PIR.Handler interface S E) {Γ mid out}
    (body : Region dialect Γ mid) (next : Region dialect (mid ++ Γ) out)
    (env : Environment meaning.Value Γ) (state : S) :
    ((body.bind next).denote meaning env).run handler state =
      ((body.denote meaning env).run handler state).follow
        (fun values => (next.denote meaning (env.prepend values)).run handler) := by
  exact PIR.run_bind _ _ _ _

theorem Region.run_bind_stopped (meaning : RegionMeaning dialect interface)
    {S E : Type} (handler : PIR.Handler interface S E) {Γ mid out}
    (body : Region dialect Γ mid) (next : Region dialect (mid ++ Γ) out)
    (env : Environment meaning.Value Γ) (state final : S) (events : List E) (reason : PIR.Stop)
    (stopped : (body.denote meaning env).run handler state = ⟨.stopped reason, final, events⟩) :
    ((body.bind next).denote meaning env).run handler state = ⟨.stopped reason, final, events⟩ := by
  rw [run_bind, stopped]
  rfl

end Zkc.Source
