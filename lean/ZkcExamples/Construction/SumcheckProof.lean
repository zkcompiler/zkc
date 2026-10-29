module

public import ZkcExamples.Construction.SumcheckSourceConnection
public import Zkc.Construction.ScalarVerifier

@[expose] public section

/-! Maintained actual Domain endpoint. Historical Instruction comparisons are
outside this module's dependencies. All raw typed public inputs are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Construction.SumcheckProof
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
/-- The endpoint stores the same complete generic connection used by execution transport. -/
theorem sourceConnected : ConnectionAdmission.Required program context .validator participant :=
  SumcheckSourceConnection.requiredConnection

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def compiledVerifier (challenge : History F G → m F) (values : List F) (claim : F) (rounds : Nat)
    (initial : History F G) (proof : Proof F G) : m (PIR.Outcome (Option Bool) × Proof F G) :=
  ScalarVerifier.verify program context participant acceptancePosition challenge
    (inputs values claim rounds) initial proof

/-- Actual Domain/source transport for every public vector, claim and round
count, every initial history and every typed proof and challenge function. -/
theorem compiled_transform (challenge : History F G → m F) (values : List F) (claim : F)
    (rounds handle : Nat) (initial : History F G) (proof : Proof F G) :
    compiledVerifier challenge values claim rounds initial proof =
      transform context challenge (verifier values claim rounds handle) initial proof := by
  rw [compiledVerifier, ScalarVerifier.verify_eq_runK program context participant acceptancePosition
    challenge (inputs values claim rounds)
    [.data (.vector "bls12-381.fr" values), .data (.field "bls12-381.fr" claim),
      .data (.index rounds), .transcript context.suite []] rfl initial proof,
    acceptancePosition_eq]
  exact SumcheckSourceConnection.transform challenge values claim rounds handle initial proof

end ZkcExamples.Construction.SumcheckProof
