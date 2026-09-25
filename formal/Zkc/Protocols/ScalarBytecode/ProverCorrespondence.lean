import Zkc.Protocols.ScalarBytecode.Prover
import Zkc.Protocols.ScalarBytecode.Messages

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.ProverCorrespondence
open Zkc.Source.PublicDimensions Zkc.Protocols.AlgebraicRounds.ParameterFamily Zkc.Protocols.ScalarBytecode.Messages

open Zkc.Realization.ByteEncoding Zkc.Protocols.ScalarBytecode.Codec Zkc.Protocols.ScalarBytecode.Prover

def verifierPrefix (hash : Hash) (claim : Nat) (bs : Bytes) :
    Option (Bytes × Nat × Bytes) := do
  let s0 := absorb hash (hash Zkc.Protocols.ScalarBytecode.ProverPrograms.sourceASCII) (enc claim)
  let (a0, r0) ← readScalar bs
  let s1 := absorb hash s0 (enc a0)
  let (a1, r1) ← readScalar r0
  let s2 := absorb hash s1 (enc a1)
  let (a2, r2) ← readScalar r1
  let s3 := absorb hash s2 (enc a2)
  if (2*a0+a1+a2) % Zkc.Protocols.ScalarBytecode.Parameters.modulus = claim then
    let d := draw hash s3
    return (d.1,d.2,r2)
  else none

def reachableClaim (cheat : Bool) : Nat := if cheat then 5 else 3

theorem prefix_agreement (hash : Hash) (cheat : Bool) (claim : Nat)
    (hreach : claim = reachableClaim cheat) (rest : Bytes) :
    verifierPrefix hash claim (wire (first cheat) ++ rest) =
      some ((derived hash cheat claim).1,(derived hash cheat claim).2,rest) := by
  subst claim
  cases cheat <;>
    simp [verifierPrefix, reachableClaim, first, Zkc.Protocols.ScalarBytecode.ProverPrograms.honestFirst,
      Zkc.Protocols.ScalarBytecode.ProverPrograms.cheatFirst, wire, derived, prefixState, List.append_assoc,
      scalar_complete 0 (by decide), scalar_complete 1 (by decide),
      scalar_complete 3 (by decide), Zkc.Protocols.ScalarBytecode.Parameters.modulus]

theorem reachability_exact (cheat : Bool) (claim : Nat) :
    (2*(first cheat)[0]!+(first cheat)[1]!+(first cheat)[2]!) % Zkc.Protocols.ScalarBytecode.Parameters.modulus = claim
      ↔ claim = reachableClaim cheat := by
  cases cheat <;> simp [first, Zkc.Protocols.ScalarBytecode.ProverPrograms.honestFirst, Zkc.Protocols.ScalarBytecode.ProverPrograms.cheatFirst,
    Zkc.Protocols.ScalarBytecode.Parameters.modulus, reachableClaim, eq_comm]

theorem joined_prefix_and_local_output (hash : Hash) (cheat : Bool)
    (claim : Nat) (hreach : claim = reachableClaim cheat)
    (m : Zkc.Source.LocalArithmetic.Memory) (tail : Bytes) :
    let d := derived hash cheat claim
    let rest := wire (values cheat d.2) ++ tail
    verifierPrefix hash claim (wire (first cheat) ++ rest) =
        some (d.1,d.2,rest) ∧
      admittedExecute hash cheat claim m tail =
        some (d.1,d.2,values cheat d.2,tail,m) := by
  dsimp only
  constructor
  · exact prefix_agreement hash cheat claim hreach _
  · apply admitted_connection
    subst claim
    cases cheat <;> decide

-- Even a later full scalar block cannot make the honest first block reach c1
-- under a false statement. No hash-law assumption is needed.
theorem wrong_claim_stops (hash : Hash) (rest : Bytes) :
    verifierPrefix hash 4 (wire (first false) ++ rest) = none := by
  simp [verifierPrefix, first, Zkc.Protocols.ScalarBytecode.ProverPrograms.honestFirst, wire,
    List.append_assoc, scalar_complete 0 (by decide),
      scalar_complete 3 (by decide), Zkc.Protocols.ScalarBytecode.Parameters.modulus]


-- Real prior producer theorem is used, not reasserted as new work.
theorem fixed_producer_request (hash : Zkc.Protocols.ScalarBytecode.Prover.Hash) (cheat : Bool) (claim : Nat)
    (hreach : claim = Zkc.Protocols.ScalarBytecode.ProverCorrespondence.reachableClaim cheat) (m : Zkc.Source.LocalArithmetic.Memory) (tail : Zkc.Realization.ByteEncoding.Bytes) :
    let d := Zkc.Protocols.ScalarBytecode.Prover.derived hash cheat claim
    let xs := Zkc.Protocols.ScalarBytecode.Prover.values cheat d.2
    ∃ hc : ∀ x ∈ xs, x < Zkc.Protocols.ScalarBytecode.Parameters.modulus,
      let req := send fixed ⟨1,by decide⟩ .scalar 13 (scalarize xs hc)
      (signature fixed).legalArg req.op req.arg ∧
      Zkc.Protocols.ScalarBytecode.ProverCorrespondence.verifierPrefix hash claim (Zkc.Protocols.ScalarBytecode.Codec.wire (Zkc.Protocols.ScalarBytecode.Prover.first cheat) ++ Zkc.Protocols.ScalarBytecode.Codec.wire xs ++ tail) =
        some (d.1,d.2,Zkc.Protocols.ScalarBytecode.Codec.wire xs ++ tail) ∧
      Zkc.Protocols.ScalarBytecode.Prover.admittedExecute hash cheat claim m tail = some (d.1,d.2,xs,tail,m) := by
  dsimp only
  have hv := Zkc.Protocols.ScalarBytecode.Prover.values_valid cheat _ (Zkc.Protocols.ScalarBytecode.Prover.derived_canonical hash cheat claim)
  have hl := hv.2.2.2.2.2.2.1
  have hc := hv.2.2.2.2.2.2.2
  refine ⟨hc, ?_, ?_⟩
  · simpa [send, signature, fixed, scalarize, Zkc.Protocols.ScalarBytecode.Prover.raw, Zkc.Protocols.ScalarBytecode.AdaptiveProver.context] using hl
  · have joined := Zkc.Protocols.ScalarBytecode.ProverCorrespondence.joined_prefix_and_local_output hash cheat claim hreach m tail
    simpa [List.append_assoc] using joined

end Zkc.Protocols.ScalarBytecode.ProverCorrespondence
