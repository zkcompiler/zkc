import ZkcArkLib.Sumcheck.Scalar
import Zkc.Protocols.Sumcheck.ProductFamily.OneRound
import Zkc.Probability.FiniteDomain

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.Sumcheck.OneRound
open Zkc.Protocols.Sumcheck.ProductFamily.OneRound Zkc.Probability.FiniteDomain OracleSpec OracleComp ProtocolSpec

open OracleSpec OracleComp ProtocolSpec

/-- The actual n1 wire has three scalar messages, followed by one D challenge. -/
@[reducible] def protocol (F D : Type) : ProtocolSpec 4 where
  dir i := if i.val = 3 then .V_to_P else .P_to_V
  «Type» i := if i.val = 3 then D else F

def challengeEquiv {F D : Type} (i : (protocol F D).ChallengeIdx) :
    (protocol F D).Challenge i ≃ D := by
  have h : i.val.val = 3 := by
    have := i.property
    simpa [protocol] using this
  simp only [Challenge, protocol, h, ↓reduceIte]
  exact Equiv.refl D

instance {F D : Type} [SampleableType D] (i : (protocol F D).ChallengeIdx) :
    SampleableType ((protocol F D).Challenge i) := by
  have h : i.val.val = 3 := by
    have := i.property
    simpa [protocol] using this
  simp only [Challenge, protocol, h, ↓reduceIte]
  infer_instance

def transcript {F D : Type} (a b c : F) (d : D) : FullTranscript (protocol F D) :=
  fun i => if h : i.val = 3 then by simpa [protocol,h] using d
    else by
      simpa [protocol,h] using (if i.val = 0 then a else if i.val = 1 then b else c)

def interpret {F D : Type} (embed : D → F) (tr : FullTranscript (protocol F D)) :
    FullTranscript (ZkcArkLib.Sumcheck.Scalar.protocol F 0) := fun i =>
  if h : i.val = 3 then embed (by simpa [protocol,h] using tr i)
  else by simpa [protocol,ZkcArkLib.Sumcheck.Scalar.protocol,h] using tr i

def scalarTranscript {F : Type} (a b c r : F) : FullTranscript (ZkcArkLib.Sumcheck.Scalar.protocol F 0) :=
  fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else r

theorem interpret_transcript {F D : Type} (embed : D → F) (a b c : F) (d : D) :
    interpret embed (transcript a b c d) = scalarTranscript a b c (embed d) := by
  funext i
  fin_cases i <;> simp [interpret,transcript,scalarTranscript] <;> rfl

def verifier {F D : Type} [CommRing F] [DecidableEq F] (embed : D → F) :
    Verifier []ₒ F Unit (protocol F D) where
  verify s tr := (ZkcArkLib.Sumcheck.Scalar.verifier []ₒ 0 Zkc.Protocols.AlgebraicRounds.Scalar.value).verify s (interpret embed tr)

theorem consumer_formula {F : Type} [CommRing F] [DecidableEq F] (s a b c r : F) :
    ZkcArkLib.Sumcheck.Scalar.accept 0 Zkc.Protocols.AlgebraicRounds.Scalar.value s (scalarTranscript a b c r) = verdict s a b c r := by
  simp [ZkcArkLib.Sumcheck.Scalar.accept,Zkc.Protocols.Sumcheck.ProductFamily.runWith,Zkc.Protocols.Sumcheck.ProductFamily.sourceEnv,ZkcArkLib.Sumcheck.Scalar.wire,scalarTranscript,
    Zkc.Protocols.Sumcheck.ProductFamily.loadRound,Zkc.Protocols.Sumcheck.ProductFamily.finalTarget,Zkc.Protocols.AlgebraicRounds.Scalar.boundary,Zkc.Protocols.AlgebraicRounds.Scalar.value,verdict,← add_assoc]
  split <;> simp_all

theorem actual_verifier {F D : Type} [CommRing F] [DecidableEq F]
    (embed : D → F) (s a b c : F) (d : D) :
    ((verifier embed).verify s (transcript a b c d)).run =
      pure (verdict s a b c (embed d)) := by
  simp only [verifier,ZkcArkLib.Sumcheck.Scalar.verifier,interpret_transcript,consumer_formula]
  rfl


end ZkcArkLib.Sumcheck.OneRound
