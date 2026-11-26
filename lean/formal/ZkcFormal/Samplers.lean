module

public import ZkcFormal.ProbabilisticProcess
public import VCVio.OracleComp.EvalDist.Measure

@[expose] public section

/-!
What a statement about a process's returns knows of the effects: samplers, and a service that
draws as they do. Nothing here is of a judgment with fees; the fees of samplers are in
`ZkcFormal.ChargedProbability`.
-/

namespace ZkcFormal.ProbabilisticProcess
open Zkc.Core OracleComp
open scoped ENNReal

variable {S : Sig} {σ : Type}

/-- What is known of the effects: at some effects, how the reply is drawn. -/
abbrev Samplers (S : Sig) := (op : S.Op) → Option (ProbComp (S.Reply op))

/-- A service draws as the samplers do: at an effect with a sampler, in every state, a set of
replies has at most the toProbability under the service that it has under the sampler. The
service may still not answer, and may do with its state what it likes. -/
def Service.Follows (service : Service S σ) (samplers : Samplers S) : Prop :=
  ∀ op draw, samplers op = some draw → ∀ s (excluded : S.Reply op → Prop),
    Pr{let out ← service op s}[∃ v, out.1 = some v ∧ excluded v] ≤ Pr{let v ← draw}[excluded v]

/-- A service answers as the samplers draw: at an effect with a sampler, in every state, its
reply has the distribution of the sampler's draw. In particular it answers there with
probability one. What it does with its state is its own. -/
def Service.Draws (service : Service S σ) (samplers : Samplers S) : Prop :=
  ∀ op draw, samplers op = some draw → ∀ s,
    (Prod.fst <$> service op s) =ᵈ (Option.some <$> draw)

/-- A service that answers as the samplers draw answers within a set of replies with exactly
the probability that the sampler draws one there. -/
theorem Service.Draws.prEvent_reply {service : Service S σ} {samplers : Samplers S}
    (draws : service.Draws samplers) {op : S.Op} {draw : ProbComp (S.Reply op)}
    (has : samplers op = some draw) (s : σ) (excluded : S.Reply op → Prop) :
    Pr{let out ← service op s}[∃ v, out.1 = some v ∧ excluded v] =
      Pr{let v ← draw}[excluded v] := by
  simpa using (draws op draw has s).prEvent_eq fun reply ↦ ∃ v, reply = some v ∧ excluded v

/-- A service that answers as the samplers draw is no more likely than they are to answer
within a set. -/
theorem Service.Draws.follows {service : Service S σ} {samplers : Samplers S}
    (draws : service.Draws samplers) : service.Follows samplers :=
  fun _ _ has s excluded ↦ (draws.prEvent_reply has s excluded).le

end ZkcFormal.ProbabilisticProcess
