module

public import Zkc.Protocols.Schnorr.Construction
public import Zkc.Semantics.MonadExecution
public import Zkc.Specification
public import ZkcSecurity.VCVio.Schnorr.FiatShamir.Sigma
public import VCVio.CryptoFoundations.FiatShamir.Sigma.ExtractionCost

@[expose] public section

/-! Fixed-statement Schnorr extraction for realized constructed verifiers.

The event/game equations are proved from actual process realization and the
imported verifier contract. The only random oracle used by the adversary and
final verification is the same initially empty VCVio cache. Queries on any
binding/commitment are allowed. Typed binding does not establish byte encoding,
concrete hash security, efficiency, or an adaptive-statement theorem.
-/
namespace ZkcSecurity.VCVio.Schnorr.FiatShamir
open OracleComp OracleSpec
open Zkc.Protocols.Schnorr
open Zkc.Protocols.Schnorr.Common
open Zkc.Protocols.Schnorr.Construction

abbrev Prover (Context F G : Type) :=
  _root_.FiatShamir.KnowledgeProver G G F F (Binding Context G)

abbrev Oracle (Context F G : Type) := unifSpec + (Binding Context G × G →ₒ F)

variable {Context F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq G]

/-- One key query, with its execution event retained. Caching is supplied once
around the complete adversary/verifier computation, never reset here. -/
def oracleHandler : PIR.MonadHandler (OracleComp (Oracle Context F G))
    (oracleSignature Context F G) Unit (QueryKey Context G) :=
  fun key state => do
    let challenge ← HasQuery.query (spec := Binding Context G × G →ₒ F) key
    pure ⟨.returned challenge, state, [key]⟩

/-- All stopped, absent, and false results reject; the full execution is available
separately from this acceptance projection. -/
def accepted (result : PIR.Execution Unit (QueryKey Context G) (Option Bool)) : Bool :=
  match result.outcome with
  | .returned (some result) => result
  | _ => false

def verifierExecution (actual : Construction.Verifier Context F G)
    (binding : Binding Context G) (proof : G × F) :
    OracleComp (Oracle Context F G)
      (PIR.Execution Unit (QueryKey Context G) (Option Bool)) :=
  (actual binding proof).runM oracleHandler ()

def verify (actual : Construction.Verifier Context F G)
    (binding : Binding Context G) (proof : G × F) : OracleComp (Oracle Context F G) Bool :=
  accepted <$> verifierExecution actual binding proof

/-- Full execution equation: exactly one final query, no hidden stop or lost event. -/
theorem verifierExecution_eq {wiring : Wiring} {program : Common.Verifier F G}
    (certificate : VerifierContract wiring program)
    {actual : Construction.Verifier Context F G} {service : Nat}
    (realization : Realizes actual program service)
    (binding : Binding Context G) (proof : G × F) :
    verifierExecution actual binding proof = (do
      let challenge ← HasQuery.query (spec := Binding Context G × G →ₒ F) (binding, proof.1)
      pure ⟨.returned (some (decide
        (proof.2 • binding.base = proof.1 + challenge • binding.key))), (), [(binding, proof.1)]⟩) := by
  unfold verifierExecution
  rw [(realization binding proof).process_eq, construct_eq certificate]
  simp [PIR.Proc.runM, oracleHandler, PIR.Execution.followM]

variable [SampleableType F]

/-- Oracle programs agree before any choice of oracle answers or probability. -/
theorem verify_eq {wiring : Wiring} {program : Common.Verifier F G}
    (certificate : VerifierContract wiring program)
    {actual : Construction.Verifier Context F G} {service : Nat}
    (realization : Realizes actual program service)
    (binding : Binding Context G) (proof : G × F) :
    verify actual binding proof =
      (_root_.FiatShamir (sigma binding.base) (generable binding.base)
        (Binding Context G)).verify binding.key binding proof := by
  rw [verify, verifierExecution_eq certificate realization]
  simp [accepted, _root_.FiatShamir, sigma, map_eq_bind_pure_comp]

variable [DecidableEq Context]

/-- The adversary sees the statement and context before starting; its private
uniform coins and arbitrary RO queries precede final verification in one cache. -/
def verificationRun (actual : Construction.Verifier Context F G)
    (prover : Prover Context F G) (binding : Binding Context G) :
    OracleComp (_root_.FiatShamir.Fork.wrappedSpec F) Bool :=
  ((simulateQ (_root_.FiatShamir.Fork.unifForward (Binding Context G) G F +
      _root_.FiatShamir.Fork.roImpl (Binding Context G) G F) do
    let proof ← prover binding.key binding
    verify actual binding proof).run' (∅, []))

/-- Exact cached-game correspondence, derived rather than stored in a certificate. -/
theorem verificationRun_eq {wiring : Wiring} {program : Common.Verifier F G}
    (certificate : VerifierContract wiring program)
    {actual : Construction.Verifier Context F G} {service : Nat}
    (realization : Realizes actual program service)
    (prover : Prover Context F G) (binding : Binding Context G) :
    verificationRun actual prover binding =
      _root_.FiatShamir.knowledgeVerifyRun (sigma binding.base) (generable binding.base)
        (Binding Context G) prover binding.key binding := by
  unfold verificationRun _root_.FiatShamir.knowledgeVerifyRun
  simp_rw [verify_eq certificate realization]

/-- The actual acceptance flag is exactly the flag in VCVio's forkable trace. -/
theorem verificationRun_eq_trace {wiring : Wiring} {program : Common.Verifier F G}
    (certificate : VerifierContract wiring program)
    {actual : Construction.Verifier Context F G} {service : Nat}
    (realization : Realizes actual program service)
    (prover : Prover Context F G) (binding : Binding Context G) :
    verificationRun actual prover binding =
      (fun trace => trace.verified) <$>
        _root_.FiatShamir.Fork.runTrace (sigma binding.base) (generable binding.base)
          (Binding Context G)
          (_root_.FiatShamir.proverWithFinalQuery (sigma binding.base) (generable binding.base)
            (Binding Context G) prover binding) binding.key := by
  rw [verificationRun_eq certificate realization]
  exact _root_.FiatShamir.knowledgeVerifyRun_eq_trace _ _ _ _ _ _

local instance : ∀ t, MeasurableSpace ((_root_.FiatShamir.Fork.wrappedSpec F).Range t) := fun _ => ⊤
local instance : ∀ t, DiscreteMeasurableSpace ((_root_.FiatShamir.Fork.wrappedSpec F).Range t) :=
  fun _ => inferInstance
noncomputable local instance : IsUniformMeasureSpec (_root_.FiatShamir.Fork.wrappedSpec F) :=
  IsUniformMeasureSpec.ofFiniteNonempty _

noncomputable def acceptance (actual : Construction.Verifier Context F G)
    (prover : Prover Context F G) (binding : Binding Context G) : ENNReal :=
  Pr{let result ← verificationRun actual prover binding}[result = true]

theorem acceptance_eq {wiring : Wiring} {program : Common.Verifier F G}
    (certificate : VerifierContract wiring program)
    {actual : Construction.Verifier Context F G} {service : Nat}
    (realization : Realizes actual program service)
    (prover : Prover Context F G) (binding : Binding Context G) :
    acceptance actual prover binding =
      _root_.FiatShamir.knowledgeAcceptance (sigma binding.base) (generable binding.base)
        (Binding Context G) prover binding.key binding := by
  unfold acceptance _root_.FiatShamir.knowledgeAcceptance
  rw [verificationRun_eq certificate realization]

/-- The named replay extractor includes a uniform-witness fallback on failed forks. -/
def extractor [DecidableEq F] (prover : Prover Context F G)
    (binding : Binding Context G) (budget : Nat) : ProbComp F :=
  _root_.FiatShamir.knowledgeExtractor (sigma binding.base) (generable binding.base)
    (Binding Context G) prover binding budget binding.key

/-- Fixed-statement extraction for an actual realized constructed verifier.
`budget` counts every adversary RO call, including repeated keys; the added one
is final verification. Uniform coin queries and running time are not bounded.
Subtraction is truncated ENNReal subtraction, so positivity needs separate data. -/
theorem extraction [Fintype F] [Inhabited F] [DecidableEq F]
    {wiring : Wiring} {program : Common.Verifier F G}
    (certificate : VerifierContract wiring program)
    {actual : Construction.Verifier Context F G} {service : Nat}
    (realization : Realizes actual program service)
    (prover : Prover Context F G) (binding : Binding Context G) (budget : Nat)
    (queryBound : _root_.FiatShamir.nmaHashQueryBound (Binding Context G)
      (prover binding.key binding) budget) :
    let acc := acceptance actual prover binding
    acc * (acc / (budget + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← extractor prover binding budget}[
        witness • binding.base = binding.key] := by
  rw [acceptance_eq certificate realization]
  simpa only [extractor, relation, decide_eq_true_eq] using
    _root_.FiatShamir.knowledgeExtractor_success (sigma binding.base) (generable binding.base)
      (Binding Context G) (speciallySound binding.base) prover binding.key binding budget queryBound

/-- Replay's counted fresh challenge requests include both paths and all failed
forks. This is not a bound on uniform coins, native work or total running time. -/
theorem extractor_challenge_bound [DecidableEq F]
    (prover : Prover Context F G) (binding : Binding Context G) (budget : Nat)
    (queryBound : _root_.FiatShamir.nmaHashQueryBound (Binding Context G)
      (prover binding.key binding) budget) :
    IsQueryBoundP
      (_root_.FiatShamir.nmaForkExtract (sigma binding.base) (generable binding.base)
        (Binding Context G)
        (_root_.FiatShamir.proverWithFinalQuery (sigma binding.base) (generable binding.base)
          (Binding Context G) prover binding) budget binding.key)
      (· = .inr ()) (2 * (budget + 1)) :=
  _root_.FiatShamir.knowledgeExtractor_challenge_bound _ _ _ _ _ _ _ queryBound

/-- A reviewed consumer can request this precise experiment on a constructed
subject. The source contract and realization remain checked proof inputs. -/
noncomputable def extractionProperty [Fintype F] [Inhabited F] [DecidableEq F]
    (prover : Prover Context F G) (binding : Binding Context G) (budget : Nat) :
    Zkc.Verification.Property (Construction.Verifier Context F G) where
  assumptions _ := _root_.FiatShamir.nmaHashQueryBound (Binding Context G)
    (prover binding.key binding) budget
  conclusion actual :=
    let acc := acceptance actual prover binding
    acc * (acc / (budget + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← extractor prover binding budget}[witness • binding.base = binding.key]

theorem extractionConsumer [Fintype F] [Inhabited F] [DecidableEq F]
    {wiring : Wiring} {program : Common.Verifier F G}
    (certificate : VerifierContract wiring program) (service : Nat)
    (prover : Prover Context F G) (binding : Binding Context G) (budget : Nat) :
    Zkc.Verification.Consumer (fun actual => Realizes actual program service)
      (extractionProperty prover binding budget) :=
  ⟨fun _ realization queryBound => extraction certificate realization prover binding budget queryBound⟩

end ZkcSecurity.VCVio.Schnorr.FiatShamir
