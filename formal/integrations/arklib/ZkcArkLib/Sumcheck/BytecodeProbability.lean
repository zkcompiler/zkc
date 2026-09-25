import ZkcArkLib.Sumcheck.Bytecode
import Mathlib.Probability.Distributions.Uniform

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.Sumcheck.BytecodeProbability
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Compiler.Blocks Zkc.Protocols.ScalarBytecode.BlockExecution

/-- Canonical three-word payload with no trailing bytes and canonical binding.
    This is an explicit input restriction, not reduction of arbitrary bytes. -/
structure Input where
  claim : Fin Zkc.Protocols.ScalarBytecode.Parameters.modulus
  a : Fin Zkc.Protocols.ScalarBytecode.Parameters.modulus
  b : Fin Zkc.Protocols.ScalarBytecode.Parameters.modulus
  c : Fin Zkc.Protocols.ScalarBytecode.Parameters.modulus

def scalar (i : Input) : Zkc.Protocols.ScalarBytecode.Residue := (i.claim.val : Zkc.Protocols.ScalarBytecode.Residue)
def wire (hash : Hash) (i : Input) :=
  ZkcArkLib.Sumcheck.Bytecode.transcript i.a.val i.b.val i.c.val
    (Zkc.Protocols.ScalarBytecode.OneRound.Verifier.challenge hash i.claim.val i.a.val i.b.val i.c.val)

def concrete (hash : Hash) (i : Input) (r : Zkc.Protocols.ScalarBytecode.OneRound.Compilation.Ref)
    (literal : Zkc.Protocols.BackendProfiles.Literal → Zkc.Protocols.ScalarBytecode.Residue) (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool) (cache : Cache) :=
  Zkc.Protocols.ScalarBytecode.RoundValues.project (Zkc.Protocols.ScalarBytecode.OneRound.Compilation.integrated hash bufferSupplier r literal store cache
    (Zkc.Protocols.ScalarBytecode.RoundValues.initial i.claim.val i.a.val i.b.val i.c.val)).outcome

/-- Construct the transcript law from the SAME source input/hash experiment.
    No independent-field sampling law is substituted. The completed transcript
    contains a counterfactual challenge on an early-reject branch; only verdict
    is projected here. Zkc.Protocols.ScalarBytecode.Probability.sampled_caller retains the full operational observer. -/
theorem induced_consumer {Ω : Type} (μ : PMF Ω) (hash : Ω → Hash) (input : Ω → Input)
    (r : Zkc.Protocols.ScalarBytecode.OneRound.Compilation.Ref) (ok : Zkc.Protocols.ScalarBytecode.OneRound.Compilation.checkCaller r = true)
    (literal : Zkc.Protocols.BackendProfiles.Literal → Zkc.Protocols.ScalarBytecode.Residue) (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool)
    (cache : Cache) (valid : Zkc.Modules.ImmutableCache.Valid arithmetic cache) :
    μ.map (fun ω => concrete (hash ω) (input ω) r literal store cache) =
      (μ.map (fun ω => (scalar (input ω),wire (hash ω) (input ω)))).map
        (fun x => ZkcArkLib.Sumcheck.Scalar.accept 0 Zkc.Protocols.AlgebraicRounds.Scalar.value x.1 x.2) := by
  rw [PMF.map_comp]
  congr 1
  funext ω
  exact ZkcArkLib.Sumcheck.Bytecode.integrated_consumer (hash ω) _ _ _ _ (input ω).claim.isLt
    (input ω).a.isLt (input ω).b.isLt (input ω).c.isLt r ok literal store cache valid

/-- Exact acceptance-mass transport under the induced law, including randomness
    in both the source inputs and the modeled hash. This does not supply a
    soundness bound or an admissible-strategy interpreter. -/
theorem acceptance_mass {Ω : Type} (μ : PMF Ω) (hash : Ω → Hash) (input : Ω → Input)
    (r : Zkc.Protocols.ScalarBytecode.OneRound.Compilation.Ref) (ok : Zkc.Protocols.ScalarBytecode.OneRound.Compilation.checkCaller r = true)
    (literal : Zkc.Protocols.BackendProfiles.Literal → Zkc.Protocols.ScalarBytecode.Residue) (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool)
    (cache : Cache) (valid : Zkc.Modules.ImmutableCache.Valid arithmetic cache) :
    (μ.map (fun ω => concrete (hash ω) (input ω) r literal store cache)) (some ()) =
      ((μ.map (fun ω => (scalar (input ω),wire (hash ω) (input ω)))).map
        (fun x => ZkcArkLib.Sumcheck.Scalar.accept 0 Zkc.Protocols.AlgebraicRounds.Scalar.value x.1 x.2)) (some ()) := by
  rw [induced_consumer μ hash input r ok literal store cache valid]

end ZkcArkLib.Sumcheck.BytecodeProbability
