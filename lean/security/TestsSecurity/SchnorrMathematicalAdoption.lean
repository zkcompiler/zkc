import ZkcSecurityExamples.Subjects.SchnorrAnd.Registration
import ZkcSecurityExamples.Subjects.Schnorr.Registration

/-! Fixed registered recovery and actual retained AND formula controls. -/
set_option autoImplicit false
set_option smartUnfolding false

namespace TestsSecurity.SchnorrMathematicalAdoption
open OracleComp OracleSpec ZkcSecurity.Endpoint ZkcSecurity.Claims
open ZkcSecurity.Examples.Subjects
open Zkc.Source Zkc.Source.Structured

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
  [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]

/-- The registered scalar coordinates and response-difference recovery remain
fixed independently of the new source execution consumer. -/
example (first second : F) (firstResult secondResult : F × F) :
    (SchnorrAnd.Registration.extractionProfile (F := F) (G := G)).layout.recover
      first firstResult second secondResult =
      ((firstResult.1 - secondResult.1) / (first - second), (firstResult.2 - secondResult.2) / (first - second)) := rfl

example (statement : SchnorrAnd.artifacts.Statement F G)
    (first second : F) (firstResult secondResult : F × F) :
    ((SchnorrAnd.Registration.justification (F := F) (G := G)).family.sigma statement).extract
      first firstResult second secondResult =
      pure (((firstResult.1 - secondResult.1) / (first - second), (firstResult.2 - secondResult.2) / (first - second))) :=
  SchnorrAnd.Registration.justification.recovery statement first firstResult second secondResult

/-- Failed forks still use the fixed full witness carrier sampler. -/
example : Extraction.recoverFork (M := Unit) (Commit := G × G)
    (fun first (firstResult : F × F) second secondResult ↦ pure
      ((SchnorrAnd.Registration.extractionProfile (F := F) (G := G)).layout.recover
        first firstResult second secondResult)) none =
      liftComp ($ᵗ (F × F)) (_root_.FiatShamir.Fork.wrappedSpec F) := rfl

private def registeredRecovery (first : F) (firstResult : F × F) (second : F) (secondResult : F × F) :
    ProbComp (F × F) :=
  pure ((SchnorrAnd.Registration.extractionProfile (F := F) (G := G)).layout.recover
    first firstResult second secondResult)

/-- The replay boundary uses the registered quotient pair only with the same
commitments, both cached challenges and a nonzero challenge difference.
Verification/coupling evidence belongs to the surrounding fork construction. -/
example (firstResult secondResult : _root_.FiatShamir.Fork.Trace (G × G) F (F × F) Unit)
    (first second : F) (same : firstResult.forgery.2.1 = secondResult.forgery.2.1)
    (leftCache : firstResult.roCache firstResult.target = some first)
    (rightCache : secondResult.roCache secondResult.target = some second) (distinct : first ≠ second) :
    Extraction.recoverFork (registeredRecovery (F := F) (G := G)) (some (firstResult, secondResult)) =
      liftComp (pure
        ((firstResult.forgery.2.2.1 - secondResult.forgery.2.2.1) / (first - second),
         (firstResult.forgery.2.2.2 - secondResult.forgery.2.2.2) / (first - second)) :
        ProbComp (F × F))
        (_root_.FiatShamir.Fork.wrappedSpec F) := by
  simp only [Extraction.recoverFork, ite_eq_left same, leftCache, rightCache,
    ite_eq_left distinct, registeredRecovery]
  rfl

example (firstResult secondResult : _root_.FiatShamir.Fork.Trace (G × G) F (F × F) Unit)
    (different : firstResult.forgery.2.1 ≠ secondResult.forgery.2.1) :
    Extraction.recoverFork (registeredRecovery (F := F) (G := G)) (some (firstResult, secondResult)) =
      liftComp ($ᵗ (F × F)) (_root_.FiatShamir.Fork.wrappedSpec F) := by
  simp only [Extraction.recoverFork, ite_eq_right different]

example (firstResult secondResult : _root_.FiatShamir.Fork.Trace (G × G) F (F × F) Unit)
    (same : firstResult.forgery.2.1 = secondResult.forgery.2.1)
    (missing : firstResult.roCache firstResult.target = none) :
    Extraction.recoverFork (registeredRecovery (F := F) (G := G)) (some (firstResult, secondResult)) =
      liftComp ($ᵗ (F × F)) (_root_.FiatShamir.Fork.wrappedSpec F) := by
  simp only [Extraction.recoverFork, ite_eq_left same, missing]

example (firstResult secondResult : _root_.FiatShamir.Fork.Trace (G × G) F (F × F) Unit)
    (same : firstResult.forgery.2.1 = secondResult.forgery.2.1)
    (missing : secondResult.roCache secondResult.target = none) :
    Extraction.recoverFork (registeredRecovery (F := F) (G := G)) (some (firstResult, secondResult)) =
      liftComp ($ᵗ (F × F)) (_root_.FiatShamir.Fork.wrappedSpec F) := by
  simp only [Extraction.recoverFork, ite_eq_left same, missing]
  cases firstResult.roCache firstResult.target <;> rfl

example (firstResult secondResult : _root_.FiatShamir.Fork.Trace (G × G) F (F × F) Unit)
    (challenge : F) (same : firstResult.forgery.2.1 = secondResult.forgery.2.1)
    (leftCache : firstResult.roCache firstResult.target = some challenge)
    (rightCache : secondResult.roCache secondResult.target = some challenge) :
    Extraction.recoverFork (registeredRecovery (F := F) (G := G)) (some (firstResult, secondResult)) =
      liftComp ($ᵗ (F × F)) (_root_.FiatShamir.Fork.wrappedSpec F) := by
  simp only [Extraction.recoverFork, ite_eq_left same, leftCache, rightCache,
    ite_eq_right (not_not.mpr rfl)]

/-- Both actual selected decisions are used; the conclusion is the existing
retained formula, with the registered fixed quotient pair. -/
example (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (responses : F → F × F) (first second : F)
    (distinct : first ≠ second)
    (acceptFirst : SchnorrAnd.Contract.decisionSelector.read {}
      (SchnorrAnd.Contract.observedBoundary firstBase firstKey secondBase secondKey service
        (ZkcExamples.Construction.SchnorrAndExecution.verifierReplies
          commitments (responses first) first).handler ()) = some true)
    (acceptSecond : SchnorrAnd.Contract.decisionSelector.read {}
      (SchnorrAnd.Contract.observedBoundary firstBase firstKey secondBase secondKey service
        (ZkcExamples.Construction.SchnorrAndExecution.verifierReplies
          commitments (responses second) second).handler ()) = some true) :
    SchnorrAnd.Contract.holds
      (.cons firstBase (.cons firstKey (.cons secondBase (.cons secondKey .nil))))
      ((SchnorrAnd.Registration.extractionProfile (F := F) (G := G)).layout.recover
        first (responses first) second (responses second)) :=
  SchnorrAnd.Contract.extracted_holds firstBase firstKey secondBase secondKey service
    commitments responses first second distinct acceptFirst acceptSecond

/-- The single Schnorr subject keeps its original retained meaning as well. -/
example (statement : Schnorr.artifacts.Statement F G) (witness : F) :
    Schnorr.Contract.holds statement witness ↔
      Schnorr.Contract.retained.Holds ZkcExamples.Construction.SchnorrProofBinding.formulaBinding
        statement (Schnorr.Contract.embed witness) :=
  Schnorr.Contract.holds_pinned statement witness

end TestsSecurity.SchnorrMathematicalAdoption
