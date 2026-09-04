/-
Generated from the admitted finite Schnorr formal source by an untrusted
generator.  The module is an interpretation artifact, not semantic authority.

Provider: VCVio de0a3108140e3e04a7ebf0075aa110b459ee6e8a
Toolchain: leanprover/lean4:v4.33.1
-/
import Examples.Schnorr.SigmaProtocol
import Mathlib.Algebra.Field.ZMod

open OracleComp SigmaProtocol

namespace ZkcProviderInterpretation

abbrev Z3 : Type := ZMod 3

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def generator : Z3 := 1

def relation (statement witness : Z3) : Bool :=
  decide (witness • generator = statement)

/-- The VCVio sigma protocol selected by the source relation and Plan. -/
def sigmaProtocol : SigmaProtocol Z3 Z3 Z3 Z3 Z3 Z3 relation :=
  Schnorr.sigma Z3 Z3 generator

/-- The interaction-only provider carrier used by the Fresh interpretation. -/
def freshProtocol : ChallengeVerifyProtocol Z3 Z3 Z3 Z3 Z3 Z3 relation :=
  sigmaProtocol.toChallengeVerifyProtocol

/-- The source public-coin declaration interpreted under its named premise. -/
def freshChallenge : ProbComp Z3 := $ᵗ Z3

/-- The source Plan's commitment recipe after fixing its nonce sample. -/
def candidateCommit (nonce : Z3) : Z3 := nonce

/-- The source Plan's response recipe. -/
def candidateRespond (witness nonce challenge : Z3) : Z3 :=
  nonce + challenge * witness

/-- The provider's randomized commit field is exactly the candidate recipe
after naming its sampled nonce. -/
theorem commitMatchesCandidate (statement witness : Z3) :
    freshProtocol.commit statement witness =
      (do
        let nonce ← $ᵗ Z3
        return (candidateCommit nonce, nonce)) := by
  simp [freshProtocol, sigmaProtocol, Schnorr.sigma, generator, candidateCommit]

/-- The provider's response field is exactly the candidate recipe. -/
theorem respondMatchesCandidate
    (statement witness privateState challenge : Z3) :
    freshProtocol.respond statement witness privateState challenge =
      pure (candidateRespond witness privateState challenge) := by
  rfl

/-- One generated Fresh execution.  Sampling semantics remain a named premise. -/
def interaction (statement witness : Z3) : ProbComp Bool := do
  let (commitment, privateState) ← freshProtocol.commit statement witness
  let challenge ← freshChallenge
  let response ← freshProtocol.respond statement witness privateState challenge
  return freshProtocol.verify statement commitment challenge response

def fromNat (value : Nat) : Z3 := value

def bit (value : Bool) : Nat := if value then 1 else 0

def providerCheck (statement commitment challenge response : Nat) : Bool :=
  freshProtocol.verify (fromNat statement) (fromNat commitment)
    (fromNat challenge) (fromNat response)

def emitCheckRows : IO Unit := do
  for statement in List.range 3 do
    for commitment in List.range 3 do
      for challenge in List.range 3 do
        for response in List.range 3 do
          IO.println s!"CHECK\t{statement}\t{commitment}\t{challenge}\t{response}\t{bit (providerCheck statement commitment challenge response)}"

def emitRunRows : IO Unit := do
  for statement in List.range 3 do
    for witness in List.range 3 do
      for nonce in List.range 3 do
        for challenge in List.range 3 do
          let commitment := candidateCommit (fromNat nonce)
          let response := candidateRespond (fromNat witness) commitment (fromNat challenge)
          let accepted := freshProtocol.verify (fromNat statement) commitment
            (fromNat challenge) response
          let lastOccurrence := if accepted then 4 else 5
          IO.println s!"RUN\t{statement}\t{witness}\t{nonce}\t{challenge}\t{commitment.val}\t{response.val}\t{bit accepted}\t{lastOccurrence}"

#eval emitCheckRows
#eval emitRunRows

#print axioms ZkcProviderInterpretation.sigmaProtocol
#print axioms ZkcProviderInterpretation.freshProtocol
#print axioms ZkcProviderInterpretation.interaction
#print axioms ZkcProviderInterpretation.commitMatchesCandidate
#print axioms ZkcProviderInterpretation.respondMatchesCandidate

end ZkcProviderInterpretation
