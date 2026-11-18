module

public import Zkc.Formal.Interactive.LocatedRound

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ReductionRound
open Core
variable {V : Vocabulary} {hs : Headers V} {t : V.Ty}

abbrev shared (t : V.Ty) : LTy V := ⟨t,[0,1]⟩

/-- The two public values in a block return are the next claim and the challenge.
The source may choose different result names in every iteration. -/
structure PublicResults {Γ : Ctx (LTy V)} {mid : List (LTy V)} (ns : Names mid) (residual t : V.Ty)
    (types : mid = outputs residual t) where
  claim : Var (Γ.extend ns) (shared t)
  draw : Var (Γ.extend ns) (shared t)
  values : ∀ (M : Model V) (env : Env (RV M 1) Γ) (r v : M.Val t),
    let env' := env.extend ns (types.symm ▸ returned M residual (r,v))
    env'.get claim = hide M 1 (shared t) v ∧ env'.get draw = hide M 1 (shared t) r

def readResults (Γ : Ctx (LTy V)) {mid : List (LTy V)} (ns : Names mid) (residual t : V.Ty)
    (types : mid = outputs residual t) : Option (PublicResults (Γ := Γ) ns residual t types) := by
  subst mid
  match ns with
  | .cons priv (.cons claim (.cons coin .nil)) =>
    exact if apart : claim ≠ coin then some {
      claim := ⟨claim,by simp [Ctx.extend,Ctx.find?_insert,apart]⟩
      draw := ⟨coin,by simp [Ctx.extend,Ctx.find?_insert]⟩
      values := by
        intro M env r v
        let hidden := nothing M (r := 1) (a := ⟨residual,[0]⟩) (by simp)
        let base := env.insert priv hidden
        let claimed := base.insert claim (hide M 1 (shared t) v)
        let result := claimed.insert coin (hide M 1 (shared t) r)
        constructor
        · change claimed.insert coin (hide M 1 (shared t) r) claim (shared t) (by simp [Ctx.find?_insert,apart]) = _
          rw [Env.insert_at_other _ _ _ apart]
          exact eq_of_heq (Env.insert_at_bound _ _ _ rfl _)
        · change result coin (shared t) (by simp [Ctx.find?_insert]) = _
          exact eq_of_heq (Env.insert_at_bound claimed coin _ rfl _)
    } else none

/-- A consecutive sequence of checked rounds in the given program. Every constructor
retains the caller's actual block and the original continuation. -/
inductive Sequence (hs : Headers V) (events : Events t) : {Γ : Ctx (LTy V)} → {outs : List (LTy V)} →
    V.Ty → Var Γ (shared t) → Term (protocolDialect V hs) Γ outs → Nat → Type where
  | done {Γ outs state running} (rest : Term (protocolDialect V hs) Γ outs) : Sequence hs events state running rest 0
  | more {Γ mid outs state running n} {inside : Term (protocolDialect V hs) Γ mid}
      (round : Located state events running inside) (key : Key) (index : Nat) (ns : Names mid)
      (binders : PublicResults (Γ := Γ) ns round.residual t round.types)
      {rest : Term (protocolDialect V hs) (Γ.extend ns) outs} (next : Sequence hs events round.residual binders.claim rest n) :
      Sequence hs events state running (.block key index inside ns rest) (n+1)

def readSequence (distinct : (hs.fns.map (·.key)).Nodup) (events : Events t) :
    (n : Nat) → {Γ : Ctx (LTy V)} → {outs : List (LTy V)} → (state : V.Ty) → (running : Var Γ (shared t)) →
    (actual : Term (protocolDialect V hs) Γ outs) → Option (Sequence hs events state running actual n)
  | 0, _, _, _, _, actual => some (.done actual)
  | n+1, _, _, state, running, .block key i inside ns rest => do
    let round ← readLocated distinct state events running inside
    let binders ← readResults _ ns round.residual t round.types
    let next ← readSequence distinct events n round.residual binders.claim rest
    return .more round key i ns binders next
  | _+1, _, _, _, _, _ => none

end Zkc.Formal.Interactive.Sumcheck.ReductionRound
