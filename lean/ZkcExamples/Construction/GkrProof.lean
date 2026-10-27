module

public import ZkcExamples.Construction.GkrArtifact
public import ZkcExamples.Construction.GkrDomainConnection
public import Zkc.Construction.ScalarVerifier

@[expose] public section

/-! Selected canonical execution of the actual looped artifact. Admission
metadata and the complete all-reply source binding are separate dependencies.
No mathematical well-formedness premise is needed for this transport. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
namespace ZkcExamples.Construction.GkrProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The actual participant with its fixed scalar input/output and oracle ABI. -/
def compiledVerifier {m : Type → Type} [Monad m] (challenge : History F G → m F)
    (inputValues outputValues add mul : List F) (layers selector width : Nat) (initial : History F G) (proof : Proof F G) :
    m (PIR.Outcome (Option Bool) × Proof F G) :=
  ScalarVerifier.verify program context participant acceptancePosition challenge
    (inputs inputValues outputValues add mul layers selector width) initial proof

/-- All raw typed public inputs, every reply and initial history, exact stops
and unread suffixes. Reference mathematics is applied only by later consumers. -/
theorem compiled_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (inputValues outputValues add mul : List F) (layers selector width : Nat) (handle : Nat)
    (initial : History F G) (proof : Proof F G) :
    compiledVerifier challenge inputValues outputValues add mul layers selector width initial proof =
      transform context challenge (verifier inputValues outputValues add mul layers selector width handle) initial proof := by
  rw [compiledVerifier, ScalarVerifier.verify_eq_runK program context participant acceptancePosition
    challenge (inputs inputValues outputValues add mul layers selector width) (GkrDomainRoot.artifactInputs inputValues outputValues add mul layers selector width []) (by rfl) initial proof]
  have keys : ScalarVerifier.origin participant = Origin.withoutCoordinates := by funext origin; rfl
  rw [keys]
  have context_same : context = GkrSourceProtocol.context := by rw [context_eq]; rfl
  have accepts (result : Domain.Result (uniformCarriers F G)) :
      ScalarVerifier.acceptance acceptancePosition result = Uniform.SourceProcess.acceptance result.values := by
    rw [acceptancePosition_eq]
    unfold ScalarVerifier.acceptance
    cases result.values with
    | nil => rfl
    | cons head tail =>
      cases head with
      | data payload =>
        rcases payload with ⟨ty, admissible, value⟩
        cases ty <;> rfl
      | transcript => rfl
      | indices => rfl
  simp only [accepts, context_same]
  exact GkrDomainConnection.domain_to_source challenge inputValues outputValues add mul layers selector width handle initial proof

end ZkcExamples.Construction.GkrProof
