module

public import ZkcFormal.Interactive.Experiment
public import Zkc.Core.Meaning.Program

@[expose] public section

namespace ZkcFormal.Interactive
open Zkc.Core

variable {V : Vocabulary} {M : Model V} {σ A : Type}

/-- The response of the caller's experiment, observed through the callee's role names.
The occurrence, payload, state and returned reply retain their original values. -/
def Experiment.renamePeers (K : Experiment (RSig M) σ) (ρ : Role → Role) :
    Experiment (RSig M) σ where
  answer
    | .give kind getters loc ty x => K.answer (.give kind (getters.map ρ) loc ty x)
    | .get kind giver loc ty => K.answer (.get kind (ρ giver) loc ty)
    | .own kind hearers loc ins vs ty => K.answer (.own kind (hearers.map ρ) loc ins vs ty)
    | .hear kind owner loc ty => K.answer (.hear kind (ρ owner) loc ty)
    | .begin loc => K.answer (.begin loc)
    | .settle loc => K.answer (.settle loc)

theorem Experiment.expect_mapR (K : Experiment (RSig M) σ) (ρ : Role → Role)
    (post : A → σ → Mass) (p : Program M A) (s : σ) :
    K.expect post (mapR M ρ p) s = (K.renamePeers ρ).expect post p s := by
  induction p generalizing s with
  | done | halt => rfl
  | call op k ih =>
    cases op <;>
      exact congrArg (FiniteLaw.expect _) (funext fun reply => ih reply.1 reply.2)

/-- The probability of a caller observation evaluated on the actual role application.
All call-site transport comes from the typed instruction and its core meaning. The callee
sees the already-reached service state and the dynamic application frame. -/
theorem Experiment.probability_application {hs : Headers V} {hdr : ProtocolHeader V}
    (K : Experiment (RSig M) σ) (r : Role) (fns : FnTable M hs.fns) (protocols : RTable M hs.protocols)
    (callee : Member hs.protocols hdr) (roles : List Role) (distinct : roles.Nodup)
    (covers : roles.length = hdr.roles) (operands : List (LTy V))
    (fits : Fits operands (hdr.ins.map (LTy.map (RoleMap.ofList roles distinct).to)))
    (key : Key) (path : List Frame) (vs : HList (RV M r) operands) (s : σ)
    (post : HList (RV M r) (hdr.outs.map (LTy.map (RoleMap.ofList roles distinct).to)) → σ → Bool) :
    K.probability (roleOp M r fns protocols key (.apply callee roles distinct covers operands fits) path vs) s post =
      let ρ := RoleMap.ofList roles distinct
      (K.renamePeers ρ.to).probability
        (protocols _ callee (ρ.back r) (path ++ [.application key])
          (enterAll M ρ r (fitAllRV M fits vs))) s
        (fun out t => post (leaveAll M ρ r out) t) := by
  simp only [roleOp, Experiment.probability, Process.map_eq_bind, Experiment.expect_bind,
    Experiment.expect_mapR, Experiment.expect_done]

end ZkcFormal.Interactive
