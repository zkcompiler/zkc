module

public import ZkcSecurity.VCVio.UniformChallenge
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Reductions

@[expose] public section

/-! Cached replay and fixed failed-fork sampling, independent of endpoint evidence. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
namespace ZkcSecurity.Endpoint.Extraction
open OracleComp OracleSpec

section Replay
variable {F Commit Resp Wit M : Type} [DecidableEq M] [DecidableEq Commit]
  [DecidableEq F] [SampleableType F] [SampleableType Wit]

/-- Ordinary prover trace with its final verification query. -/
def runTrace (verify : (M × Commit →ₒ F).QueryCache → Commit → Resp → Bool)
    (prover : M → OracleComp (unifSpec + (M × Commit →ₒ F)) (Commit × Resp))
    (message : M) : OracleComp (_root_.FiatShamir.Fork.wrappedSpec F)
      (_root_.FiatShamir.Fork.Trace Commit F Resp M) := do
  let ((forgery, cache), state) ← StateT.run (simulateQ
    (_root_.FiatShamir.Fork.unifForward M Commit F + _root_.FiatShamir.Fork.roImpl M Commit F) (do
      let proof ← prover message
      let _ ← HasQuery.query (spec := M × Commit →ₒ F) (message, proof.1)
      return ((message, proof), ∅))) (∅, [])
  let verified := verify state.1 forgery.2.1 forgery.2.2
  return ⟨forgery, cache, state.1, state.2, verified⟩

/-- Failed forks use the fixed carrier sampler. Successful forks use exactly
`recover`; the claims layer fixes it to response difference. -/
def recoverFork (recover : F → Resp → F → Resp → ProbComp Wit) :
    Option (_root_.FiatShamir.Fork.Trace Commit F Resp M ×
      _root_.FiatShamir.Fork.Trace Commit F Resp M) →
      OracleComp (_root_.FiatShamir.Fork.wrappedSpec F) Wit
  | none => liftComp ($ᵗ Wit) (_root_.FiatShamir.Fork.wrappedSpec F)
  | some (first, second) =>
      if first.forgery.2.1 = second.forgery.2.1 then
        match first.roCache first.target, second.roCache second.target with
        | some left, some right =>
            if left ≠ right then
              liftComp (recover left first.forgery.2.2 right second.forgery.2.2)
                (_root_.FiatShamir.Fork.wrappedSpec F)
            else liftComp ($ᵗ Wit) (_root_.FiatShamir.Fork.wrappedSpec F)
        | _, _ => liftComp ($ᵗ Wit) (_root_.FiatShamir.Fork.wrappedSpec F)
      else liftComp ($ᵗ Wit) (_root_.FiatShamir.Fork.wrappedSpec F)

def replay (verify : (M × Commit →ₒ F).QueryCache → Commit → Resp → Bool)
    (recover : F → Resp → F → Resp → ProbComp Wit)
    (prover : M → OracleComp (unifSpec + (M × Commit →ₒ F)) (Commit × Resp))
    (message : M) (queries : Nat) : ProbComp Wit :=
  simulateQ (QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl (spec := Unit →ₒ F))
    (contextFork (runTrace verify prover message) (_root_.FiatShamir.nmaForkBudget queries)
      (Sum.inr ()) (_root_.FiatShamir.Fork.forkPoint Commit F Resp M queries) >>=
        recoverFork recover)

end Replay
end ZkcSecurity.Endpoint.Extraction
