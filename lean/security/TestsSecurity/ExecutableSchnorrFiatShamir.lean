import ZkcSecurity.VCVio.UniformChallenge
import ZkcSecurity.Examples.ExecutableSchnorrFiatShamir
import TestsSecurity.CompiledSchnorrFiatShamir
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! Controls for the executable Schnorr theorem. A finite instance uses `ZMod 5`
as both scalar field and additive group, a one-byte toy codec and an arbitrary
expected binding, with no hardness claim. The executable validator, run
directly, accepts the honest proof bytes at the 25-instruction budget and
rejects them below it, under another binding or with a trailing byte. The
query-bound premise is satisfiable, the honest byte prover decodes to the
honest typed prover of `CompiledSchnorrFiatShamir`'s controls, and its
acceptance and the conclusion are those of that prover: a strictly positive
extraction bound. -/

open scoped ZkcSecurity.VCVio.UniformChallenge

namespace TestsSecurity.ExecutableSchnorrFiatShamir
open OracleComp OracleSpec
open Zkc.Construction Zkc.Executable
open ZkcSecurity.Examples.CompiledSchnorrFiatShamir
open ZkcSecurity.Examples.ExecutableSchnorrFiatShamir

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev Scalar := ZMod 5
abbrev Message := History Scalar Scalar

def application : String := "example-application"
def base : Scalar := 1
/-- The statement `2 • base`, with witness `2`. -/
def key : Scalar := 2
/-- An arbitrary expected invocation binding. -/
def binding : List UInt8 := List.replicate 32 7

/-- A one-byte toy codec: a byte below 5 decodes at the receive's type. -/
def decodeToy : PhysicalType → List UInt8 → Option (Payload Scalar Scalar)
  | ⟨.data (.group domain), _⟩, [byte] =>
      if byte.toNat < 5 then some (.group domain (byte.toNat : ZMod 5)) else none
  | ⟨.data (.field domain), _⟩, [byte] =>
      if byte.toNat < 5 then some (.field domain (byte.toNat : ZMod 5)) else none
  | _, _ => none

/-- One length-framed message of one byte. -/
def frame (value : Scalar) : List UInt8 := [1, 0, 0, 0, 0, 0, 0, 0, value.val.toUInt8]

/-- Complete proof bytes: the framing header, then the commitment and response. -/
def proofBytes (commitment response : Scalar) : List UInt8 :=
  magic ++ binding ++ frame commitment ++ frame response

def challengeHistory (message : Message) : Message :=
  message ++ [.message commitmentOrigin (.group groupDomain 3), .challenge challengeOrigin]

/-- The honest byte prover with nonce `3` asks the oracle for its own challenge. -/
def honestBytes : ByteProver Scalar Scalar := fun _ message => do
  let challenge ← historyChallenge (challengeHistory message)
  pure (proofBytes 3 (3 + challenge * 2))

theorem honestBytes_bound :
    IsQueryBoundP (honestBytes key (initial application base key)) (· matches .inr _) 1 := by
  change IsQueryBoundP
    ((liftM ((HistorySpec Scalar Scalar).query
      (.inr (challengeHistory (initial application base key)))) :
        OracleComp (HistorySpec Scalar Scalar) Scalar) >>= fun challenge =>
      pure (proofBytes 3 (3 + challenge * 2))) _ 1
  simp

/-- Fixed oracle answers, for running the executable directly. -/
def fixed (challenge : Scalar) : QueryImpl (HistorySpec Scalar Scalar) Id :=
  QueryImpl.ofFn (fun n : Nat => (0 : Fin (n + 1))) + QueryImpl.ofFn (fun _ : Message => challenge)

theorem executable_accepts : evalWithAnswerFn (fixed 4)
    (verifyBytes decodeToy 25 binding application base key (proofBytes 3 (3 + 4 * 2))) = true := by
  decide +kernel

theorem executable_rejects_short_budget : evalWithAnswerFn (fixed 4)
    (verifyBytes decodeToy 24 binding application base key (proofBytes 3 (3 + 4 * 2))) = false := by
  decide +kernel

theorem executable_rejects_other_binding : evalWithAnswerFn (fixed 4)
    (verifyBytes decodeToy 25 (List.replicate 32 8) application base key
      (proofBytes 3 (3 + 4 * 2))) = false := by
  decide +kernel

theorem executable_rejects_trailing_byte : evalWithAnswerFn (fixed 4)
    (verifyBytes decodeToy 25 binding application base key (proofBytes 3 (3 + 4 * 2) ++ [0])) =
      false := by
  decide +kernel

theorem executable_rejects_wrong_response : evalWithAnswerFn (fixed 4)
    (verifyBytes decodeToy 25 binding application base key (proofBytes 3 2)) = false := by
  decide +kernel

/-- The honest proof bytes decode to the honest typed proof. -/
theorem decodePair_honest (response : Scalar) :
    decodePair decodeToy (proofBytes 3 response) = (3, response) := by
  revert response
  decide +kernel

/-- Every honest proof is validated exactly as the compiled verifier verifies
the honest typed proof. -/
theorem honest_validated (challenge : Scalar) :
    verifyBytes decodeToy 25 binding application base key (proofBytes 3 (3 + challenge * 2)) =
      verify application base key (3, 3 + challenge * 2) := by
  apply verifyBytes_eq_verify decodeToy (le_refl 25) binding application base key
  · rfl
  · revert challenge
    decide +kernel

/-- The honest byte prover's experiment is the honest typed prover's. -/
theorem honest_run : runBytes decodeToy 25 binding honestBytes application base key =
    run TestsSecurity.CompiledSchnorrFiatShamir.honest application base key := by
  unfold runBytes ZkcSecurity.Examples.CompiledSchnorrFiatShamir.run honestBytes TestsSecurity.CompiledSchnorrFiatShamir.honest
    challengeHistory TestsSecurity.CompiledSchnorrFiatShamir.challengeHistory
  simp only [bind_assoc, pure_bind, honest_validated]

/-- The executable accepts the honest byte prover with probability one. -/
theorem honest_acceptance : acceptanceBytes decodeToy 25 binding honestBytes application base key = 1 := by
  unfold acceptanceBytes
  rw [honest_run]
  exact TestsSecurity.CompiledSchnorrFiatShamir.honest_acceptance

/-- The conclusion is not vacuous: a strictly positive extraction bound for the
honest byte prover. -/
theorem positive_extraction : (2⁻¹ - 5⁻¹ : ENNReal) ≤
    Pr{let witness ← _root_.FiatShamir.knowledgeExtractor (_root_.Schnorr.sigma Scalar Scalar base)
        (ZkcSecurity.Examples.StructuredSchnorrFiatShamir.generable base) (Message ⊕ Message)
        (reduce (decoded decodeToy honestBytes)) (.inl (initial application base key)) 1 key}[
      ZkcExamples.Construction.SchnorrProofBinding.Relation base key witness] := by
  have bound := knowledge_soundness decodeToy 25 binding honestBytes application base key 1
    honestBytes_bound
  dsimp only at bound
  rw [honest_acceptance] at bound
  simpa only [_root_.FiatShamir.challengeSpaceInv, Scalar, ZMod.card,
    Nat.cast_ofNat, one_mul, one_div, Nat.cast_one, one_add_one_eq_two] using bound

end TestsSecurity.ExecutableSchnorrFiatShamir
