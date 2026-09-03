/-
Generated from the admitted finite Schnorr formal source by an untrusted
generator. The module is an interpretation artifact, not semantic authority.

Provider: ArkLib fad5cbf808774838924dc8273715724c6a6caa1f
Toolchain: leanprover/lean4:v4.31.0
-/
import ArkLib.OracleReduction.Execution
import Mathlib.Algebra.Field.ZMod

open OracleComp OracleSpec ProtocolSpec

namespace ZkcArkLibInterpretation

abbrev Z3 := ZMod 3

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The three-step public-coin schedule selected by the formal source. -/
def protocolSpec : ProtocolSpec 3 :=
  ⟨!v[.P_to_V, .V_to_P, .P_to_V], fun _ => Z3⟩

/-- A uniform draw transported from `Fin 3` to the challenge carrier. -/
def freshChallenge : ProbComp Z3 :=
  (ZMod.finEquiv 3) <$> $[0..2]

/-- An implementation of ArkLib's challenge oracle that samples the selected
finite carrier uniformly. The Fresh independence law remains a premise. -/
def freshChallengeQueryImpl : QueryImpl [protocolSpec.Challenge]ₒ ProbComp :=
  fun _ => freshChallenge

structure Memory where
  witness : Z3
  nonce : Z3
  challenge : Z3

/-- The selected Plan's commitment recipe after fixing its nonce sample. -/
def candidateCommit (nonce : Z3) : Z3 := nonce

/-- The selected Plan's response recipe. -/
def candidateRespond (witness nonce challenge : Z3) : Z3 :=
  nonce + challenge * witness

def roundZero (transcript : FullTranscript protocolSpec) : Z3 := by
  simpa [protocolSpec] using transcript (0 : Fin 3)

def roundOne (transcript : FullTranscript protocolSpec) : Z3 := by
  simpa [protocolSpec] using transcript (1 : Fin 3)

def roundTwo (transcript : FullTranscript protocolSpec) : Z3 := by
  simpa [protocolSpec] using transcript (2 : Fin 3)

/-- An ArkLib prover whose two sending rounds implement the selected recipes. -/
def prover (nonce : Z3) : Prover []ₒ Z3 Z3 Unit Unit protocolSpec where
  PrvState := fun _ => Memory
  input := fun (_, witness) => ⟨witness, nonce, 0⟩
  sendMessage
    | ⟨0, _⟩ => fun state => pure (candidateCommit state.nonce, state)
    | ⟨1, h⟩ => nomatch h
    | ⟨2, _⟩ => fun state =>
        pure (candidateRespond state.witness state.nonce state.challenge, state)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun state => pure fun challenge => { state with challenge }
    | ⟨2, h⟩ => nomatch h
  output := fun _ => pure ((), ())

/-- The portable Check represented as ArkLib verifier rejection or unit output. -/
def verifier : Verifier []ₒ Z3 Unit protocolSpec where
  verify := fun statement transcript => do
    guard (roundTwo transcript = roundZero transcript + roundOne transcript * statement)
    return ()

/-- The generated provider reduction. -/
def reduction (nonce : Z3) : Reduction []ₒ Z3 Z3 Unit Unit protocolSpec where
  prover := prover nonce
  verifier := verifier

/-- Kernel-checked equality for the commitment field of the generated prover. -/
theorem commitRoundMatchesCandidate (state : Memory) :
    (prover state.nonce).sendMessage ⟨0, rfl⟩ state =
      pure (candidateCommit state.nonce, state) := rfl

/-- Kernel-checked equality for the response field of the generated prover. -/
theorem responseRoundMatchesCandidate (state : Memory) :
    (prover state.nonce).sendMessage ⟨2, rfl⟩ state =
      pure (candidateRespond state.witness state.nonce state.challenge, state) := rfl

def challengeValues (challenge : Z3) (_ : protocolSpec.ChallengeIdx) : Z3 := challenge

def challengeImpl (challenge : Z3) :
    QueryImpl ([]ₒ + [protocolSpec.Challenge]ₒ) Id :=
  fun
    | Sum.inl i => nomatch i
    | Sum.inr query => challengeValues challenge query.1

def emptyImpl : QueryImpl []ₒ Id := fun i => nomatch i

def transcriptOf (commitment challenge response : Z3) : FullTranscript protocolSpec :=
  fun i => Fin.cases commitment (Fin.cases challenge (Fin.cases response Fin.elim0)) i

/-- Execute the actual ArkLib verifier against one complete transcript. -/
def executeCheck (statement commitment challenge response : Z3) : Option Unit :=
  evalWithAnswerFn emptyImpl
    (verifier.run statement (transcriptOf commitment challenge response)).run

/-- Execute all three rounds of the actual ArkLib prover with a fixed challenge. -/
def executeProver (statement witness nonce challenge : Z3) :
    FullTranscript protocolSpec × Unit × Unit :=
  evalWithAnswerFn (challengeImpl challenge)
    ((prover nonce).run statement witness)

/-- Execute the actual ArkLib reduction verdict with a fixed challenge. -/
def executeVerdict (statement witness nonce challenge : Z3) : Option Unit :=
  evalWithAnswerFn (challengeImpl challenge)
    ((reduction nonce).verdict statement witness).run

def fromNat (value : Nat) : Z3 := value

def bit (value : Bool) : Nat := if value then 1 else 0

def providerCheck (statement commitment challenge response : Nat) : Bool :=
  (executeCheck (fromNat statement) (fromNat commitment)
    (fromNat challenge) (fromNat response)).isSome

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
          let proverResult := executeProver (fromNat statement) (fromNat witness)
            (fromNat nonce) (fromNat challenge)
          let transcript := proverResult.1
          let verdict := executeVerdict (fromNat statement) (fromNat witness)
            (fromNat nonce) (fromNat challenge)
          let accepted := verdict.isSome
          let lastOccurrence := if accepted then 4 else 5
          IO.println s!"RUN\t{statement}\t{witness}\t{nonce}\t{challenge}\t{(roundZero transcript).val}\t{(roundTwo transcript).val}\t{bit accepted}\t{lastOccurrence}"

#eval emitCheckRows
#eval emitRunRows

#print axioms ZkcArkLibInterpretation.protocolSpec
#print axioms ZkcArkLibInterpretation.freshChallenge
#print axioms ZkcArkLibInterpretation.freshChallengeQueryImpl
#print axioms ZkcArkLibInterpretation.reduction
#print axioms ZkcArkLibInterpretation.commitRoundMatchesCandidate
#print axioms ZkcArkLibInterpretation.responseRoundMatchesCandidate
#print axioms ZkcArkLibInterpretation.executeCheck
#print axioms ZkcArkLibInterpretation.executeProver
#print axioms ZkcArkLibInterpretation.executeVerdict

end ZkcArkLibInterpretation
