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

end ZkcFormal.ProbabilisticProcess
