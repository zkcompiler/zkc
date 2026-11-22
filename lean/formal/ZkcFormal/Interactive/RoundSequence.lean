module

public import ZkcFormal.Interactive.LocatedRound

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck.ReductionRound
open Zkc.Core
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

/-- An instance of the common typed round body at one physical block. Its state and
residual types, operation references, captures and keys may vary with the iteration.
`checked.same` identifies the actual verifier projection with the common body. -/
structure IndexedRound (hs : Headers V) (events : Events t) where
  context : Ctx (LTy V)
  outputs : List (LTy V)
  state : V.Ty
  running : Var context (shared t)
  actual : Term (protocolDialect V hs) context outputs
  checked : Located state events running actual
  block : Key
  iteration : Nat

/-- Read all typed instances in execution order without copying the bodies or re-running
the correspondence check. Their enclosing sequence is indexed by the admitted term. -/
def Sequence.instances {events : Events t} {Γ outs state running}
    {term : Term (protocolDialect V hs) Γ outs} {count : Nat} :
    Sequence hs events state running term count → List (IndexedRound hs events)
  | .done _ => []
  | .more round block iteration _ _ rest =>
    ⟨_, _, _, _, _, round, block, iteration⟩ :: rest.instances

theorem Sequence.length_instances {events : Events t} {Γ outs state running}
    {term : Term (protocolDialect V hs) Γ outs} {n : Nat} (rounds : Sequence hs events state running term n) :
    rounds.instances.length = n := by
  induction rounds with
  | done => rfl
  | more _ _ _ _ _ _ ih => exact congrArg Nat.succ ih

def Sequence.instanceAt {events : Events t} {Γ outs state running}
    {term : Term (protocolDialect V hs) Γ outs} {n : Nat} (rounds : Sequence hs events state running term n)
    (i : Fin n) : IndexedRound hs events :=
  rounds.instances[i.val]'(rounds.length_instances.symm ▸ i.isLt)

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

end ZkcFormal.Interactive.Sumcheck.ReductionRound
