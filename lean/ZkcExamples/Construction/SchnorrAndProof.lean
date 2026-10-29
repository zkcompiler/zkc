module

public import ZkcExamples.Construction.SchnorrAndDomainConnection
public import Zkc.Construction.ScalarVerifier

@[expose] public section

/-! The maintained endpoint over separate generated admission metadata and the
checked all-reply connection of the actual Domain artifact to its source. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
namespace ZkcExamples.Construction.SchnorrAndProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction

/-- The endpoint stores the same complete generic connection used by execution transport. -/
theorem sourceConnected : ConnectionAdmission.Required program context .validator participant :=
  SchnorrAndDomainConnection.requiredConnection

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Actual Domain execution with the fixed scalar ABI and oracle mapping. -/
def compiledVerifier {m : Type → Type} [Monad m] (challenge : History F G → m F)
    (firstBase firstPoint secondBase secondPoint : G) (initial : History F G) (proof : Proof F G) :
    m (PIR.Outcome (Option Bool) × Proof F G) :=
  ScalarVerifier.verify program context participant acceptancePosition challenge
    (inputs firstBase firstPoint secondBase secondPoint) initial proof

/-- All public inputs, replies, initial histories and exact unread suffixes.
This theorem is derived from the actual artifact binding, never from admission. -/
theorem compiled_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (firstBase firstPoint secondBase secondPoint : G) (handle : Nat)
    (initial : History F G) (proof : Proof F G) :
    compiledVerifier challenge firstBase firstPoint secondBase secondPoint initial proof =
      transform context challenge (verifier firstBase firstPoint secondBase secondPoint handle) initial proof := by
  rw [compiledVerifier, ScalarVerifier.verify_eq_runK program context participant acceptancePosition
    challenge (inputs firstBase firstPoint secondBase secondPoint) (SchnorrAndDomainConnection.inputs firstBase firstPoint secondBase secondPoint) (by rfl) initial proof]
  convert SchnorrAndDomainConnection.domain_transform challenge firstBase firstPoint secondBase secondPoint handle initial proof using 1 <;> kernel_rfl

end ZkcExamples.Construction.SchnorrAndProof
