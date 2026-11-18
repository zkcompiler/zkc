module

public import Zkc.Formal.Interactive.SequenceMeaning

@[expose] public section
namespace Zkc.Formal.Interactive
open Core

theorem Experiment.Reaches.of_bind {S : Sig} {σ H A B : Type} {K : Experiment S σ}
    {p : Process S H A} {next : A → Process S H B} {s u : σ} {b : B}
    (found : K.Reaches (p.bind next) s b u) : ∃ a t, K.Reaches p s a t ∧ K.Reaches (next a) t b u := by
  induction p generalizing s with
  | done a => exact ⟨a,s,.done ..,found⟩
  | halt why => cases found
  | call op k ih =>
    cases found with
    | call reply tail =>
      obtain ⟨a,t,first,later⟩ := ih _ tail
      exact ⟨a,t,.call reply first,later⟩

theorem Experiment.Reaches.of_map {S : Sig} {σ H A B : Type} {K : Experiment S σ}
    {p : Process S H A} {f : A → B} {s u : σ} {b : B} (found : K.Reaches (p.map f) s b u) :
    ∃ a, K.Reaches p s a u ∧ f a = b := by
  rw [Process.map_eq_bind] at found
  obtain ⟨a,t,first,last⟩ := found.of_bind
  cases last
  exact ⟨a,first,rfl⟩

namespace Sumcheck.ReductionRound.Sequence
variable {V : Vocabulary} {hs : Headers V} {t state : V.Ty} {events : Events t} {Γ : Ctx (LTy V)}
variable {running : Var Γ (shared t)} {outs : List (LTy V)} {term : Term (protocolDialect V hs) Γ outs} {count : Nat}

theorem trace_length (rounds : Sequence hs events state running term count) (M : Model V)
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) (path : List Frame) (env : Env (RV M 1) Γ)
    {σ : Type} (K : Experiment (RSig M) σ) {s u : σ} {last : Env (RV M 1) rounds.finalContext}
    {rs : List (M.Val t)} {v : M.Val t} (reached : K.Reaches (rounds.collect M fns roles path env) s (last,rs,v) u) :
    rs.length = count := by
  induction rounds generalizing s rs v with
  | done => cases reached; rfl
  | more round key index ns ports next ih =>
    rw [collect] at reached
    obtain ⟨vs,after,_,tail⟩ := reached.of_bind
    obtain ⟨⟨endEnv,draws,value⟩,rest,same⟩ := tail.of_map
    obtain ⟨_,same,_⟩ := Prod.mk.inj same
    rw [List.length_cons,ih (env.extend ns vs) rest]

end Sumcheck.ReductionRound.Sequence
end Zkc.Formal.Interactive
