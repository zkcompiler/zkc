module

public import Zkc.Formal.Interactive.RoundSequence
public import Zkc.Formal.Interactive.Reduction

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ReductionRound
open Core
namespace Sequence
variable {V : Vocabulary} {hs : Headers V} {t : V.Ty} {events : Events t}
variable {Γ : Ctx (LTy V)} {outs : List (LTy V)} {state : V.Ty}
variable {claim : Var Γ (shared t)} {term : Term (protocolDialect V hs) Γ outs} {count : Nat}

def finalContext {Γ : Ctx (LTy V)} {state : V.Ty} {claim : Var Γ (shared t)} {term : Term (protocolDialect V hs) Γ outs} {count : Nat} (rounds : Sequence hs events state claim term count) : Ctx (LTy V) :=
  match rounds with
  | .done _ => Γ
  | .more _ _ _ _ _ next => next.finalContext

def remainder {Γ : Ctx (LTy V)} {state : V.Ty} {claim : Var Γ (shared t)} {term : Term (protocolDialect V hs) Γ outs} {count : Nat} (rounds : Sequence hs events state claim term count) :
    Term (protocolDialect V hs) rounds.finalContext outs :=
  match rounds with
  | .done rest => rest
  | .more _ _ _ _ _ next => next.remainder

def scalar (M : Model V) (env : Env (RV M 1) Γ) (v : Var Γ (shared t)) : M.Val t :=
  reveal M (a := shared t) (by simp) (env.get v)

/-- Execute the exact projected blocks and retain their final environment for the original
continuation. The public trace records each returned challenge in source order. -/
def collect {Γ : Ctx (LTy V)} {state : V.Ty} {claim : Var Γ (shared t)} {term : Term (protocolDialect V hs) Γ outs} {count : Nat} (rounds : Sequence hs events state claim term count) (M : Model V)
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) (path : List Frame) (env : Env (RV M 1) Γ) :
    Program M (Env (RV M 1) rounds.finalContext × List (M.Val t) × M.Val t) :=
  match rounds with
  | .done _ => .done (env, [], scalar M env claim)
  | @more _ _ _ _ _ _ _ _ _ _ inside _ key index ns binders _ next =>
    ((project 1 inside).denote (roleSem M 1 fns roles) (path ++ [.iteration key index]) env).bind fun values =>
      let extended := env.extend ns values
      (next.collect M fns roles path extended).map fun (last,rs,v) => (last,scalar M extended binders.draw :: rs,v)

theorem meaning (rounds : Sequence hs events state claim term count) (M : Model V)
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) (path : List Frame) (env : Env (RV M 1) Γ) :
    (project 1 term).denote (roleSem M 1 fns roles) path env =
    (rounds.collect M fns roles path env).bind fun (last,_,_) =>
      (project 1 rounds.remainder).denote (roleSem M 1 fns roles) path last := by
  induction rounds with
  | done => rfl
  | @more _ _ _ _ _ _ inside round key index ns binders _ next ih =>
    change Process.bind _ _ = _
    simp only [collect,remainder,Process.bind_assoc,Process.bind_map]
    exact congrArg (Process.bind _) (funext fun values => ih (env.extend ns values))

variable (M : Model V) [DecidableEq (M.Val t)] (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
variable {σ : Type} (K : Experiment (RSig M) σ) (q : Claims (M.Val t)) (cost : Mass)

/-- Charge a block at its incoming environment and service state. Later obligations start
at positive-weight returns of this exact block with the corresponding public restriction. -/
def BoundsFrom {Γ : Ctx (LTy V)} {state : V.Ty} {claim : Var Γ (shared t)}
    {term : Term (protocolDialect V hs) Γ outs} {count : Nat}
    (rounds : Sequence hs events state claim term count) (path : List Frame)
    (env : Env (RV M 1) Γ) (s : σ) (x : q.State count) : Prop :=
  match rounds with
  | .done _ => True
  | @more _ _ _ _ _ _ _ _ _ n inside _ key index ns binders _ next =>
    let run := (project 1 inside).denote (roleSem M 1 fns roles) (path ++ [.iteration key index]) env
    (scalar M env claim ≠ q.value (n+1) x →
      K.probability run s (fun values _ =>
        let env' := env.extend ns values
        decide (scalar M env' binders.claim = q.value n (q.restrict n x (scalar M env' binders.draw)))) ≤ cost) ∧
    ∀ values after, K.Reaches run s values after →
      let env' := env.extend ns values
      next.BoundsFrom path env' after (q.restrict n x (scalar M env' binders.draw))

/-- The component may be invoked at any input and service state. -/
abbrev RoundBounds (rounds : Sequence hs events state claim term count) (path : List Frame) :=
  ∀ env s x, rounds.BoundsFrom M fns roles K q cost path env s x

/-- Sum the conditional error charges of the actual blocks. The intermediate state of the
service may depend on every earlier message and draw. -/
theorem soundFrom (rounds : Sequence hs events state claim term count) (path : List Frame)
    (nonneg : 0 ≤ cost)
    (env : Env (RV M 1) Γ) (s : σ) (x : q.State count) (bounds : rounds.BoundsFrom M fns roles K q cost path env s x) (wrong : scalar M env claim ≠ q.value count x) :
    K.probability (rounds.collect M fns roles path env) s
      (fun (_,rs,value) _ => decide (q.evaluate count x rs = some value)) ≤ (count : Mass) * cost := by
  induction rounds generalizing s with
  | @done ctx out st current rest =>
    change (if decide (some (q.value 0 x) = some (scalar M env current)) then (1 : Mass) else 0) ≤ 0 * cost
    simp [Ne.symm wrong]
  | @more _ _ _ _ _ n inside round key index ns binders rest next ih =>
    obtain ⟨first,later⟩ := bounds
    rw [collect, Mass.natCast_add, Mass.add_mul, show ((1 : Nat) : Mass) = 1 by rfl, Mass.one_mul, Mass.add_comm]
    apply K.reduction_bind _ _ _ _ _ (first wrong) (Mass.mul_nonneg Mass.natCast_nonneg nonneg)
    intro values after reached bad
    let env' := env.extend ns values
    let draw := scalar M env' binders.draw
    have tail := ih env' after (q.restrict n x draw) (later values after reached) (of_decide_eq_false bad)
    apply Mass.le_trans _ tail
    simp only [Experiment.probability, Process.map_eq_bind, Experiment.expect_bind, Experiment.expect]
    apply K.expect_mono
    intro output _ _
    obtain ⟨last,rs,v⟩ := output
    by_cases agrees : q.evaluate n (q.restrict n x draw) rs = some v <;> simp [Claims.evaluate, draw, env', agrees] at *

/-- Sum the conditional error charges of the actual blocks. The intermediate state of the
service may depend on every earlier message and draw. -/
theorem sound (rounds : Sequence hs events state claim term count) (path : List Frame)
    (nonneg : 0 ≤ cost) (bounds : rounds.RoundBounds M fns roles K q cost path)
    (env : Env (RV M 1) Γ) (s : σ) (x : q.State count) (wrong : scalar M env claim ≠ q.value count x) :
    K.probability (rounds.collect M fns roles path env) s
      (fun (_,rs,value) _ => decide (q.evaluate count x rs = some value)) ≤ (count : Mass) * cost := by
  exact rounds.soundFrom M fns roles K q cost path nonneg env s x
    (bounds env s x) wrong

#print axioms sound
#print axioms meaning
end Sequence
end Zkc.Formal.Interactive.Sumcheck.ReductionRound
