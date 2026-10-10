import Zkc.Source.RegionEncoding

/-! Checked elimination of operations that return an existing variable.

A fold law establishes equality of procedures for every environment. It cannot
erase an operation just because one handler succeeds or one run leaves its
result unused. The traversal substitutes aliases as it proceeds, retains compact
control, and checks actual candidates by comparing independently folded regions.
-/

set_option autoImplicit false
namespace Zkc.Compiler
open Source

variable {language : Language} {interface : PIR.Signature}

structure RegionEquivalence (meaning : Interpretation language interface)
    {Γ : List language.Ty} {ty : language.Ty} (source candidate : Region language Γ ty) : Type where
  denote : ∀ env : Environment meaning.Value Γ,
    candidate.denote meaning env = source.denote meaning env

structure OperationFolding (meaning : Interpretation language interface) where
  replacement : {Γ : List language.Ty} → (op : language.Op) →
    Operands Γ (language.arguments op) → Option (Var Γ (language.result op))
  correct : ∀ {Γ} op args value, replacement (Γ := Γ) op args = some value →
    ∀ env : Environment meaning.Value Γ,
      meaning.operation op (Operands.eval env args) = .done (env value)

namespace OperationFolding

variable {meaning : Interpretation language interface} (fold : OperationFolding meaning)

private def substitute {Γ Δ : List language.Ty} {ty : language.Ty}
    (rename : Renaming Γ Δ) (value : Var Δ ty) : Renaming (ty :: Γ) Δ
  | _, .here => value
  | _, .there old => rename old

/-- Renaming during traversal exposes subsequent folds without a fixed-point
loop or repeated copying of the remaining region. -/
def run (fold : OperationFolding meaning) {Γ Δ : List language.Ty} {ty : language.Ty}
    (rename : Renaming Γ Δ) :
    Region language Γ ty → Region language Δ ty
  | .ret value => .ret (rename value)
  | .stop why => .stop why
  | .letOp op args next =>
    let args := Operands.rename rename args
    match fold.replacement op args with
    | some value => fold.run (substitute rename value) next
    | none => .letOp op args (fold.run (Renaming.lift rename) next)
  | .branch condition yes no =>
    .branch (rename condition) (fold.run rename yes) (fold.run rename no)
  | .iterate count initial body next =>
    .iterate count (rename initial) (fold.run (Renaming.lift rename) body)
      (fold.run (Renaming.lift rename) next)
  | .bind body next => .bind (fold.run rename body) (fold.run (Renaming.lift rename) next)

theorem denote_run {Γ Δ : List language.Ty} {ty : language.Ty}
    (region : Region language Γ ty) (rename : Renaming Γ Δ)
    (env : Environment meaning.Value Δ) :
    (fold.run rename region).denote meaning env =
      region.denote meaning (fun value => env (rename value)) := by
  induction region generalizing Δ with
  | ret value => rfl
  | stop why => rfl
  | letOp op args next ih =>
    simp only [run]
    split
    next value selected =>
      rw [ih]
      simp only [Region.denote]
      rw [← Operands.eval_rename, fold.correct op _ value selected, PIR.Proc.bind]
      congr 1
      funext ty reference
      cases reference <;> rfl
    next selected =>
      simp only [Region.denote, Operands.eval_rename]
      congr 1
      funext value
      rw [ih, Environment.push_rename]
  | branch condition yes no yesIH noIH => simp only [run, Region.denote, yesIH, noIH]
  | iterate count initial body next bodyIH nextIH =>
    simp only [run, Region.denote]
    have same :
        (fun value => (fold.run (Renaming.lift rename) body).denote meaning (env.push value)) =
        (fun value => body.denote meaning (Environment.push (fun v => env (rename v)) value)) := by
      funext value
      rw [bodyIH, Environment.push_rename]
    rw [same]
    congr 1
    funext value
    rw [nextIH, Environment.push_rename]
  | bind body next bodyIH nextIH =>
    simp only [run, Region.denote, bodyIH]
    congr 1
    funext value
    rw [nextIH, Environment.push_rename]

def normalize {Γ : List language.Ty} {ty : language.Ty} (region : Region language Γ ty) :=
  fold.run (fun value => value) region

theorem denote_normalize {Γ : List language.Ty} {ty : language.Ty}
    (region : Region language Γ ty) (env : Environment meaning.Value Γ) :
    (fold.normalize region).denote meaning env = region.denote meaning env :=
  fold.denote_run region (fun value => value) env

/-- The source and candidate are already independently elaborated. Acceptance
gives equality of procedures, rather than equality under a chosen test handler. -/
def check [DecidableEq language.Ty] [DecidableEq language.Op]
    {Γ : List language.Ty} {ty : language.Ty} (source candidate : Region language Γ ty) :
    Option (RegionEquivalence meaning source candidate) :=
  if same : (fold.normalize candidate).erase = (fold.normalize source).erase then
    some ⟨by
      have typed := congrArg (RawRegion.elaborate (language := language) Γ ty) same
      simp only [Region.elaborate_erase] at typed
      have equal := Except.ok.inj typed
      intro env
      rw [← fold.denote_normalize candidate, equal, fold.denote_normalize]⟩
  else none

end OperationFolding
end Zkc.Compiler
