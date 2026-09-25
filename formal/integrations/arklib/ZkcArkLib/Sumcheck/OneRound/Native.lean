import ZkcArkLib.Sumcheck.OneRound.Protocol
import ZkcArkLib.Sumcheck.Bytecode

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.Sumcheck.OneRound
open Zkc.Protocols.Sumcheck.ProductFamily.OneRound Zkc.Probability.FiniteDomain

open OracleSpec OracleComp

abbrev NativeD := Fin Zkc.Protocols.ScalarBytecode.OneRound.Verifier.support

@[reducible] def native_sampleable : SampleableType NativeD := by
  change SampleableType (Fin (2305843009213693951 + 1))
  infer_instance

def nativeEmbed : NativeD → Zkc.Protocols.ScalarBytecode.Residue :=
  scalarEmbed (by decide : Zkc.Protocols.ScalarBytecode.OneRound.Verifier.support ≤ Zkc.Protocols.ScalarBytecode.Parameters.modulus)

def nativeChallenge (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (s a b c : Nat) : NativeD :=
  ⟨Zkc.Protocols.ScalarBytecode.OneRound.Verifier.challenge hash s a b c,Zkc.Protocols.ScalarBytecode.OneRound.Verifier.challenge_support hash s a b c⟩

theorem native_embed_injective : Function.Injective nativeEmbed := scalar_injective _

/-- Native modeled bytes determine a D-valued challenge. This is a deterministic
    interpretation, and supplies no equality with the fresh experiment. -/
theorem native_source_verifier (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (s a b c : Nat)
    (hs : s < Zkc.Protocols.ScalarBytecode.Parameters.modulus) (ha : a < Zkc.Protocols.ScalarBytecode.Parameters.modulus)
    (hb : b < Zkc.Protocols.ScalarBytecode.Parameters.modulus) (hc : c < Zkc.Protocols.ScalarBytecode.Parameters.modulus) :
    ((verifier nativeEmbed).verify (s : Zkc.Protocols.ScalarBytecode.Residue)
      (transcript (a : Zkc.Protocols.ScalarBytecode.Residue) (b : Zkc.Protocols.ScalarBytecode.Residue) (c : Zkc.Protocols.ScalarBytecode.Residue)
        (nativeChallenge hash s a b c))).run =
      pure (Zkc.Protocols.ScalarBytecode.RoundValues.project (Zkc.Protocols.ScalarBytecode.OneRound.Verifier.flat hash s a b c).outcome) := by
  rw [ZkcArkLib.Sumcheck.Bytecode.source_consumer hash s a b c hs ha hb hc]
  simp only [verifier,ZkcArkLib.Sumcheck.Scalar.verifier,interpret_transcript]
  rfl

/-- The modeled hash support is smaller than the residue modulus. -/
theorem native_parameters :
    Zkc.Protocols.ScalarBytecode.Parameters.modulus = Zkc.Protocols.ScalarBytecode.OneRound.Verifier.support + 3297 ∧ Zkc.Protocols.ScalarBytecode.OneRound.Verifier.support = 2^61 := by decide


end ZkcArkLib.Sumcheck.OneRound
