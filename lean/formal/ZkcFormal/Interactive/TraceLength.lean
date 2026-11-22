module

public import ZkcFormal.Interactive.SequenceMeaning

@[expose] public section
namespace ZkcFormal.Interactive
open Zkc.Core

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
end ZkcFormal.Interactive
