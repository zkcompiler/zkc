module

public import ZkcExamples.Construction.ComposedSumcheckArtifact
public import ZkcExamples.Construction.ComposedSumcheckScalarConnection
public import Zkc.Construction.ScalarVerifier

@[expose] public section
noncomputable section

/-! Selected canonical execution of the actual looped artifact. Admission
metadata and the complete all-reply source binding are separate dependencies.
No mathematical well-formedness premise is needed for this transport. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
namespace ZkcExamples.Construction.ComposedSumcheckProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction
/-- The endpoint uses the retained artifact's single stored checked root. -/
theorem sourceConnected : ConnectionAdmission.Required program context .validator participant :=
  ComposedSumcheckScalarConnection.requiredConnection

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The actual participant with its fixed scalar input/output and oracle ABI. -/
def compiledVerifier {m : Type → Type} [Monad m] (challenge : History F G → m F)
    (left right : List F) (leftSum rightSum : F) (rounds : Nat) (initial : History F G) (proof : Proof F G) :
    m (PIR.Outcome (Option Bool) × Proof F G) :=
  ScalarVerifier.verify program context participant acceptancePosition challenge
    (inputs left right leftSum rightSum rounds) initial proof

/-- All raw typed public inputs, every reply and initial history, exact stops
and unread suffixes. Reference mathematics is applied only by later consumers. -/
theorem compiled_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (left right : List F) (leftSum rightSum : F) (rounds : Nat) (handle : Nat)
    (initial : History F G) (proof : Proof F G) :
    compiledVerifier challenge left right leftSum rightSum rounds initial proof =
      transform context challenge (verifier left right leftSum rightSum rounds handle) initial proof := by
  rw [compiledVerifier, ScalarVerifier.verify_eq_runK program context participant acceptancePosition
    challenge (inputs left right leftSum rightSum rounds)
    [.data (.vector "bls12-381.fr" left), .data (.vector "bls12-381.fr" right),
      .data (.field "bls12-381.fr" leftSum), .data (.field "bls12-381.fr" rightSum),
      .data (.index rounds), .transcript context.suite []] rfl initial proof,
    acceptancePosition_eq]
  exact ComposedSumcheckScalarConnection.transform challenge left right leftSum rightSum rounds handle initial proof

end ZkcExamples.Construction.ComposedSumcheckProof
