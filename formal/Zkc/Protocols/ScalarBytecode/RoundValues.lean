import Zkc.Protocols.ScalarBytecode.Residue
import Zkc.Protocols.ScalarBytecode.Suppliers.Representations
import Zkc.Protocols.ScalarBytecode.OneRound.Verifier
import Zkc.Protocols.AlgebraicRounds.Scalar

/-! Scalar round equations and the supplied bytecode verifier's verdict.
The residue interpretation and the natural-word verifier use the same modulus.
Native supplier implementation and arbitrary-hash security are separate claims.
-/

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.RoundValues

open Zkc.Realization.InstructionSequence Zkc.Realization.ByteEncoding
open Execution Endpoint Suppliers

def round (a b c r : Nat) : AlgebraicRounds.Scalar.Round Residue := ⟨a, b, c, r⟩

theorem boundary_val (a b c r : Nat) :
    (AlgebraicRounds.Scalar.boundary (round a b c r)).val =
      OneRound.Verifier.boundary a b c := by
  simp only [AlgebraicRounds.Scalar.boundary, round, ZMod.val_add, ZMod.val_natCast]
  simp [OneRound.Verifier.boundary, Parameters.modulus, Nat.add_mod]

theorem value_val (a b c r : Nat) :
    (AlgebraicRounds.Scalar.value (round a b c r)).val =
      OneRound.Verifier.value a b c r := by
  simp only [AlgebraicRounds.Scalar.value, round, add_assoc, ZMod.val_add,
    ZMod.val_mul, ZMod.val_natCast]
  simp [OneRound.Verifier.value, Parameters.modulus, Nat.add_mod, Nat.mul_mod]

def project : Exit → Option Unit
  | .accept => some ()
  | _ => none

def initial (claim a b c : Nat) : World Bytes :=
  OneRound.Source.initial claim (Codec.wire [a, b, c])

theorem open_verdict (hash : Hash) (claim a b c : Nat)
    (ha : a < Parameters.modulus) (hb : b < Parameters.modulus) (hc : c < Parameters.modulus) :
    (run (openStep hash bufferSupplier) OneRound.Source.code (initial claim a b c)).outcome =
      OneRound.Verifier.verdict claim a b c (OneRound.Verifier.challenge hash claim a b c) := by
  exact (buffer_run hash OneRound.Source.code (initial claim a b c)).1.trans
    (OneRound.Verifier.flat_verdict hash claim a b c ha hb hc)

end Zkc.Protocols.ScalarBytecode.RoundValues
