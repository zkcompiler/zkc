import Zkc.Protocols.ScalarBytecode.OneRound.Compilation
import Zkc.Protocols.ScalarBytecode.RoundValues
import ZkcArkLib.Sumcheck.Scalar

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.Sumcheck.Bytecode
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers Zkc.Compiler.Blocks Zkc.Protocols.ScalarBytecode.BlockExecution Zkc.Protocols.ScalarBytecode.RoundValues

def transcript (a b c r : Nat) : ProtocolSpec.FullTranscript (ZkcArkLib.Sumcheck.Scalar.protocol Zkc.Protocols.ScalarBytecode.Residue 0) :=
  fun i => if i.val = 0 then (a : Zkc.Protocols.ScalarBytecode.Residue) else if i.val = 1 then (b : Zkc.Protocols.ScalarBytecode.Residue) else if i.val = 2 then (c : Zkc.Protocols.ScalarBytecode.Residue) else (r : Zkc.Protocols.ScalarBytecode.Residue)

theorem consumer_accept (claim a b c r : Nat) :
    ZkcArkLib.Sumcheck.Scalar.accept 0 Zkc.Protocols.AlgebraicRounds.Scalar.value (claim : Zkc.Protocols.ScalarBytecode.Residue) (transcript a b c r) =
    if Zkc.Protocols.AlgebraicRounds.Scalar.boundary (round a b c r) = (claim : Zkc.Protocols.ScalarBytecode.Residue) then
      if Zkc.Protocols.AlgebraicRounds.Scalar.value (round a b c r) = (r : Zkc.Protocols.ScalarBytecode.Residue)+(r : Zkc.Protocols.ScalarBytecode.Residue) then some () else none
    else none := by
  simp [ZkcArkLib.Sumcheck.Scalar.accept,Zkc.Protocols.Sumcheck.ProductFamily.runWith,Zkc.Protocols.Sumcheck.ProductFamily.sourceEnv,ZkcArkLib.Sumcheck.Scalar.wire,transcript,
    Zkc.Protocols.Sumcheck.ProductFamily.loadRound,Zkc.Protocols.Sumcheck.ProductFamily.finalTarget,Zkc.Protocols.AlgebraicRounds.Scalar.boundary,Zkc.Protocols.AlgebraicRounds.Scalar.value,Zkc.Protocols.ScalarBytecode.RoundValues.round]
  split <;> simp_all
  by_cases hb : (a : Zkc.Protocols.ScalarBytecode.Residue) + (a : Zkc.Protocols.ScalarBytecode.Residue) + (b : Zkc.Protocols.ScalarBytecode.Residue) + (c : Zkc.Protocols.ScalarBytecode.Residue) = (claim : Zkc.Protocols.ScalarBytecode.Residue) <;> simp_all

theorem verdict_accept (claim a b c r : Nat) (hs : claim < Zkc.Protocols.ScalarBytecode.Parameters.modulus) :
    project (Zkc.Protocols.ScalarBytecode.OneRound.Verifier.verdict claim a b c r) =
      ZkcArkLib.Sumcheck.Scalar.accept 0 Zkc.Protocols.AlgebraicRounds.Scalar.value (claim : Zkc.Protocols.ScalarBytecode.Residue) (transcript a b c r) := by
  have hsval : (claim : Zkc.Protocols.ScalarBytecode.Residue).val = claim := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hs
  have htval : ((r : Zkc.Protocols.ScalarBytecode.Residue)+(r : Zkc.Protocols.ScalarBytecode.Residue)).val = (r+r)%Zkc.Protocols.ScalarBytecode.Parameters.modulus := by
    simp only [ZMod.val_add, ZMod.val_natCast]
    simp [Nat.add_mod]
  have hb : Zkc.Protocols.AlgebraicRounds.Scalar.boundary (round a b c r) = (claim : Zkc.Protocols.ScalarBytecode.Residue) ↔
      Zkc.Protocols.ScalarBytecode.OneRound.Verifier.boundary a b c = claim := by
    rw [← (ZMod.val_injective Zkc.Protocols.ScalarBytecode.Parameters.modulus).eq_iff,boundary_val,hsval]
  have hv : Zkc.Protocols.AlgebraicRounds.Scalar.value (round a b c r) = (r : Zkc.Protocols.ScalarBytecode.Residue)+(r : Zkc.Protocols.ScalarBytecode.Residue) ↔
      Zkc.Protocols.ScalarBytecode.OneRound.Verifier.value a b c r = (r+r)%Zkc.Protocols.ScalarBytecode.Parameters.modulus := by
    rw [← (ZMod.val_injective Zkc.Protocols.ScalarBytecode.Parameters.modulus).eq_iff,value_val,htval]
  simp only [consumer_accept,hb,hv]
  by_cases h1 : Zkc.Protocols.ScalarBytecode.OneRound.Verifier.boundary a b c = claim <;>
    by_cases h2 : Zkc.Protocols.ScalarBytecode.OneRound.Verifier.value a b c r = (r+r)%Zkc.Protocols.ScalarBytecode.Parameters.modulus <;>
    simp [Zkc.Protocols.ScalarBytecode.OneRound.Verifier.verdict,h1,h2,project]

/-- Canonical payload and claim. The projection forgets operational rejection
    details; it does not identify the state of early and completed executions. -/
theorem source_consumer (hash : Hash) (claim a b c : Nat)
    (hs : claim < Zkc.Protocols.ScalarBytecode.Parameters.modulus) (ha : a < Zkc.Protocols.ScalarBytecode.Parameters.modulus)
    (hb : b < Zkc.Protocols.ScalarBytecode.Parameters.modulus) (hc : c < Zkc.Protocols.ScalarBytecode.Parameters.modulus) :
    project (Zkc.Protocols.ScalarBytecode.OneRound.Verifier.flat hash claim a b c).outcome =
      ZkcArkLib.Sumcheck.Scalar.accept 0 Zkc.Protocols.AlgebraicRounds.Scalar.value (claim : Zkc.Protocols.ScalarBytecode.Residue)
        (transcript a b c (Zkc.Protocols.ScalarBytecode.OneRound.Verifier.challenge hash claim a b c)) := by
  rw [Zkc.Protocols.ScalarBytecode.OneRound.Verifier.flat_verdict hash claim a b c ha hb hc,verdict_accept claim a b c _ hs]

theorem integrated_consumer (hash : Hash) (claim a b c : Nat)
    (hs : claim < Zkc.Protocols.ScalarBytecode.Parameters.modulus) (ha : a < Zkc.Protocols.ScalarBytecode.Parameters.modulus)
    (hb : b < Zkc.Protocols.ScalarBytecode.Parameters.modulus) (hc : c < Zkc.Protocols.ScalarBytecode.Parameters.modulus)
    (r : Zkc.Protocols.ScalarBytecode.OneRound.Compilation.Ref) (ok : Zkc.Protocols.ScalarBytecode.OneRound.Compilation.checkCaller r = true)
    (literal : Zkc.Protocols.BackendProfiles.Literal → Zkc.Protocols.ScalarBytecode.Residue) (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool) (cache : Cache)
    (valid : Zkc.Modules.ImmutableCache.Valid arithmetic cache) :
    project (Zkc.Protocols.ScalarBytecode.OneRound.Compilation.integrated hash bufferSupplier r literal store cache
      (initial claim a b c)).outcome =
      ZkcArkLib.Sumcheck.Scalar.accept 0 Zkc.Protocols.AlgebraicRounds.Scalar.value (claim : Zkc.Protocols.ScalarBytecode.Residue)
        (transcript a b c (Zkc.Protocols.ScalarBytecode.OneRound.Verifier.challenge hash claim a b c)) := by
  rw [← (Zkc.Protocols.ScalarBytecode.OneRound.Compilation.caller_refinement hash bufferSupplier r ok literal store cache
    valid (initial claim a b c)).1,open_verdict hash claim a b c ha hb hc,
    verdict_accept claim a b c _ hs]

end ZkcArkLib.Sumcheck.Bytecode
