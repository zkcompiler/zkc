import Zkc.Source.Composition

/-! Typed computation regions with explicit, shared sequential composition.

The finite source remains a useful tree reference. `Region.bind` stores a
continuation once, even when its first region contains branches. This changes
the carrier, not the execution meaning: flattening denotes the same `PIR.Proc`.
Flattening is a specification bridge, never the compact execution/checking path.
-/

set_option autoImplicit false
namespace Zkc.Source

inductive Region (language : Language) : List language.Ty → language.Ty → Type where
  | ret {Γ ty} (value : Var Γ ty) : Region language Γ ty
  | stop {Γ ty} (reason : PIR.Stop) : Region language Γ ty
  | letOp {Γ ty} (op : language.Op) (arguments : Operands Γ (language.arguments op))
      (next : Region language (language.result op :: Γ) ty) : Region language Γ ty
  | branch {Γ ty} (condition : Var Γ language.condition)
      (yes no : Region language Γ ty) : Region language Γ ty
  | iterate {Γ ty acc} (count : Nat) (initial : Var Γ acc)
      (body : Region language (acc :: Γ) acc)
      (next : Region language (acc :: Γ) ty) : Region language Γ ty
  | bind {Γ a b} (body : Region language Γ a)
      (next : Region language (a :: Γ) b) : Region language Γ b

variable {language : Language} {interface : PIR.Signature}

def Region.denote (meaning : Interpretation language interface) {Γ ty} :
    Region language Γ ty → Environment meaning.Value Γ → PIR.Proc interface (meaning.Value ty)
  | .ret value, env => .done (env value)
  | .stop reason, _ => .halt reason
  | .letOp op arguments next, env =>
    (meaning.operation op (Operands.eval env arguments)).bind fun value =>
      next.denote meaning (env.push value)
  | .branch condition yes no, env =>
    if meaning.condition (env condition) then yes.denote meaning env else no.denote meaning env
  | .iterate count initial body next, env =>
    (PIR.repeatN count (fun value => body.denote meaning (env.push value)) (env initial)).bind
      fun value => next.denote meaning (env.push value)
  | .bind body next, env =>
    (body.denote meaning env).bind fun value => next.denote meaning (env.push value)

def Region.rename {Γ Δ ty} (rename : Renaming Γ Δ) :
    Region language Γ ty → Region language Δ ty
  | .ret value => .ret (rename value)
  | .stop reason => .stop reason
  | .letOp op arguments next =>
    .letOp op (Operands.rename rename arguments) (next.rename (Renaming.lift rename))
  | .branch condition yes no => .branch (rename condition) (yes.rename rename) (no.rename rename)
  | .iterate count initial body next =>
    .iterate count (rename initial) (body.rename (Renaming.lift rename))
      (next.rename (Renaming.lift rename))
  | .bind body next => .bind (body.rename rename) (next.rename (Renaming.lift rename))

theorem Region.denote_rename (meaning : Interpretation language interface)
    {Γ Δ ty} (region : Region language Γ ty) (rename : Renaming Γ Δ)
    (env : Environment meaning.Value Δ) :
    (region.rename rename).denote meaning env =
      region.denote meaning (fun value => env (rename value)) := by
  induction region generalizing Δ with
  | ret value => rfl
  | stop reason => rfl
  | letOp op arguments next ih =>
    simp only [Region.rename, denote, Operands.eval_rename]
    congr 1
    funext value
    rw [ih, Environment.push_rename]
  | branch condition yes no yesIH noIH => simp only [Region.rename, denote, yesIH, noIH]
  | iterate count initial body next bodyIH nextIH =>
    simp only [Region.rename, denote]
    have same :
        (fun value => (body.rename (Renaming.lift rename)).denote meaning (env.push value)) =
        (fun value => body.denote meaning (Environment.push (fun v => env (rename v)) value)) := by
      funext value
      rw [bodyIH, Environment.push_rename]
    rw [same]
    congr 1
    funext value
    rw [nextIH, Environment.push_rename]
  | bind body next bodyIH nextIH =>
    simp only [Region.rename, denote, bodyIH]
    congr 1
    funext value
    rw [nextIH, Environment.push_rename]

/-- Reference expansion may duplicate continuations; consumers execute regions directly. -/
def Region.flatten {Γ ty} : Region language Γ ty → Program language Γ ty
  | .ret value => .ret value
  | .stop reason => .stop reason
  | .letOp op arguments next => .letOp op arguments next.flatten
  | .branch condition yes no => .branch condition yes.flatten no.flatten
  | .iterate count initial body next => .iterate count initial body.flatten next.flatten
  | .bind body next => body.flatten.seq next.flatten

theorem Region.denote_flatten (meaning : Interpretation language interface)
    {Γ ty} (region : Region language Γ ty) (env : Environment meaning.Value Γ) :
    region.flatten.denote meaning env = region.denote meaning env := by
  induction region with
  | ret value => rfl
  | stop reason => rfl
  | letOp op arguments next ih => simp only [flatten, Program.denote, denote, ih]
  | branch condition yes no yesIH noIH =>
    simp only [flatten, Program.denote, denote, yesIH, noIH]
  | iterate count initial body next bodyIH nextIH =>
    simp only [flatten, Program.denote, denote, bodyIH, nextIH]
  | bind body next bodyIH nextIH =>
    simp only [flatten, Program.denote_seq, denote, bodyIH, nextIH]

/-- The compact route preserves the complete execution, including stopped post-state. -/
theorem Region.run_flatten (meaning : Interpretation language interface)
    {S E : Type} (handler : PIR.Handler interface S E) {Γ ty}
    (region : Region language Γ ty) (env : Environment meaning.Value Γ) (state : S) :
    (region.flatten.denote meaning env).run handler state =
      (region.denote meaning env).run handler state := by rw [denote_flatten]

theorem Region.run_bind (meaning : Interpretation language interface)
    {S E : Type} (handler : PIR.Handler interface S E) {Γ a b}
    (body : Region language Γ a) (next : Region language (a :: Γ) b)
    (env : Environment meaning.Value Γ) (state : S) :
    ((body.bind next).denote meaning env).run handler state =
      ((body.denote meaning env).run handler state).follow
        (fun value => (next.denote meaning (env.push value)).run handler) := by
  exact PIR.run_bind _ _ _ _

/-- A stopped body preserves its actual post-state and events and never runs the suffix. -/
theorem Region.run_bind_stopped (meaning : Interpretation language interface)
    {S E : Type} (handler : PIR.Handler interface S E) {Γ a b}
    (body : Region language Γ a) (next : Region language (a :: Γ) b)
    (env : Environment meaning.Value Γ) (state final : S) (events : List E) (reason : PIR.Stop)
    (stopped : (body.denote meaning env).run handler state = ⟨.stopped reason, final, events⟩) :
    ((body.bind next).denote meaning env).run handler state = ⟨.stopped reason, final, events⟩ := by
  rw [run_bind, stopped]
  rfl

def Program.toRegion {Γ ty} : Program language Γ ty → Region language Γ ty
  | .ret value => .ret value
  | .stop reason => .stop reason
  | .letOp op arguments next => .letOp op arguments next.toRegion
  | .branch condition yes no => .branch condition yes.toRegion no.toRegion
  | .iterate count initial body next => .iterate count initial body.toRegion next.toRegion

@[simp] theorem Program.flatten_toRegion {Γ ty} (program : Program language Γ ty) :
    program.toRegion.flatten = program := by
  induction program <;> simp_all [toRegion, Region.flatten]

theorem Program.denote_toRegion (meaning : Interpretation language interface)
    {Γ ty} (program : Program language Γ ty) (env : Environment meaning.Value Γ) :
    program.toRegion.denote meaning env = program.denote meaning env := by
  rw [← Region.denote_flatten, flatten_toRegion]

end Zkc.Source
