module

public import ZkcFormal.Interactive.SequenceMeaning

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck.ReductionRound
open Zkc.Core
variable {V : Vocabulary} {hs : Headers V} {t state : V.Ty} {events : Events t}
variable {Γ : Ctx (LTy V)} {mid : List (LTy V)} {running : Var Γ (shared t)}
variable {actual : Term (protocolDialect V hs) Γ mid}

private theorem transport_outputs {α β : List (LTy V)} (types : α = β)
    (inside : Term (protocolDialect V hs) Γ α) (M : Model V)
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) (path : List Frame) (env : Env (RV M 1) Γ) :
    (project 1 inside).denote (roleSem M 1 fns roles) path env =
      ((project 1 (types ▸ inside)).denote (roleSem M 1 fns roles) path env).map (fun v => types.symm ▸ v) := by
  subst β
  exact (Process.map_id' _).symm

/-- Discharge one actual block's probability obligation using the mathematics of the two
operations selected at this occurrence and the challenge distribution following its guard. -/
theorem Located.charge (round : Located state events running actual) (ns : Names mid)
    (binders : PublicResults (Γ := Γ) ns round.residual t round.types)
    (M : Model V) [DecidableEq (M.Val t)] (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (equalLaw : ScalarEquality.Law t events.equal events.equalType M)
    (boundary : M.Val round.msg → M.Val t) (evaluate : M.Val round.msg → M.Val t → M.Val t)
    (ends : ∀ m, localOp M fns round.members.boundary (.cons m .nil) = .done (.cons (boundary m) .nil))
    (atPoint : ∀ m r, localOp M fns round.members.evaluate (.cons m (.cons r .nil)) = .done (.cons (evaluate m r) .nil))
    {σ : Type} (K : Experiment (RSig M) σ) (s : σ) (points : List (M.Val t)) (positive : 0 < points.length)
    (path : List Frame) (env : Env (RV M 1) Γ) (truth : M.Val t → M.Val t) (degree : Nat)
    (fresh : ∀ m s', K.Reaches (receive M round.msg path (round.sites 1)) s m s' →
      boundary m = Sequence.scalar M env running → Fresh K points positive (challenge M events path (challengeSite round.sites)) s')
    (roots : ∀ m, boundary m = Sequence.scalar M env running →
      points.countP (fun r => decide (evaluate m r = truth r)) ≤ degree) :
    K.probability ((project 1 actual).denote (roleSem M 1 fns roles) path env) s
      (fun values _ =>
        let env' := env.extend ns values
        decide (Sequence.scalar M env' binders.claim = truth (Sequence.scalar M env' binders.draw))) ≤ roundCost degree points := by
  let claim := Sequence.scalar M env running
  have atClaim : env.get running = hide M 1 _ claim := by rfl
  rw [transport_outputs round.types actual,round.process M fns roles path env claim atClaim boundary evaluate equalLaw ends atPoint]
  have first := verifierRound_le K s points positive (receive M round.msg path (round.sites 1))
    (fun _ => challenge M events path (challengeSite round.sites)) (.declared .reject ⟨path,round.sites 4⟩)
    boundary evaluate truth claim degree fresh roots
  apply Mass.le_trans _ first
  simp only [Experiment.probability,Process.map_eq_bind,Experiment.expect_bind,Experiment.expect_done]
  apply K.expect_mono
  intro (r,v) _ _
  obtain ⟨cv,rv⟩ := binders.values M env r v
  simp only [Sequence.scalar,cv,rv,reveal_hide,Mass.le_refl]

#print axioms Located.charge
end ZkcFormal.Interactive.Sumcheck.ReductionRound
