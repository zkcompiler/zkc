module

public import ZkcExamples.Construction.SumcheckDomainRound
public import Zkc.Construction.Uniform.DomainIteration

@[expose] public section
/-! The actual selected loop at every received value and challenge answer. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Construction.SumcheckDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
open ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator
attribute [local irreducible] roundState
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem round_results : roundInstruction.results =
    [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"),
      .transcript "merlin3.bls12-381.fr64be/0"] := by kernel_rfl

def reduce : List Nat → List F → F → Domain.History (uniformCarriers F G) →
    PIR.Process (Domain.effects (uniformCarriers F G)) (RoundState F G)
  | [], point, scalar, history => .done ⟨point, scalar, history⟩
  | index :: rest, point, scalar, history =>
      (roundState index point scalar history).bind fun state =>
        reduce rest state.point state.scalar state.history

theorem loop_projection (a b c d e f g h : Domain.Value (uniformCarriers F G))
    (indices : List Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) :
    (Domain.iterate (bodyStep2Body (ringModel F G) SumcheckProof.program SumcheckProof.context)
      [a, b, c, d, e, f, g, h] [29, 34, 28] roundInstruction.results indices (carried point scalar history)).interpret
        Original.forgetCheckpoints =
      (reduce indices point scalar history).bind fun state => .done state.values := by
  induction indices generalizing point scalar history with
  | nil => rfl
  | cons index rest ih =>
      rw [iterate_bind, PIR.Process.interpret_bind]
      simp only [carried]
      have roundEq := round_projection a b c d e f g h index point scalar history
      simp only [roundProjection, roundInputs] at roundEq
      rw [roundEq]
      simp only [roundProcess, reduce, PIR.Process.bind_assoc, PIR.Process.bind]
      congr 1
      funext state
      exact ih state.point state.scalar state.history

end ZkcExamples.Construction.SumcheckDomainConnection
