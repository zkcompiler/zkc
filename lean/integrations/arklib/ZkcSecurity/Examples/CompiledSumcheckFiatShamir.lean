module

public import ZkcSecurity.Examples.SumcheckFiatShamir
public import ZkcExamples.Construction.SumcheckProof

@[expose] public section

/-! Fiat–Shamir soundness of the compiled Sumcheck proof Entry.

The subject is the compiler's constructed validator for the Sumcheck example's
`example::Proof` Entry (`ZkcExamples.Construction.SumcheckProof.participant`),
which the composed transcript-construction and participant projection check
accepts (`SumcheckProof.compiled`). Its meaning is the ideal interpretation of
the exported operations (`Zkc.Construction.ideal`) under the Entry's checked
occurrence context, with helper calls read by the original's checked helpers,
on the verifier's table values, claimed sum and round count, the initial
transcript and the proof's messages. The verifier accepts when the acceptance
output the policy selects is true (`compiledVerifier`).

Two proved links compose:

* Vertical. For every challenge function the compiled meaning is the
  Fiat–Shamir transform of the Proof Entry's original validator
  (`SumcheckProof.compiled_transform`, an instance of the composed rules'
  `Zkc.Construction.compiled_transform` with no Entry-specific equation). That
  original validator is the imported `example::Interactive` verifier of the
  security theorems (`verifier_imported`): both read the admitted Sumcheck
  source, and the construction bridge checks that the Proof Entry's fresh
  original export renders to exactly that source
  (`regenerated:lean/ZkcExamples/Structured/SumcheckSourceData.lean` for the
  `sumcheck` subject).
* Horizontal. The transform of the imported verifier has a round-by-round
  certificate with error `1 / |F|` per challenge, so its acceptance of a false
  claim is bounded (`SumcheckFiatShamir.imported_soundness` and its adaptive
  forms).

`soundness` bounds the probability that the compiled verifier accepts a false
claim, for a fixed well-formed statement (the raw values decode to a table at the
count) and initial transcript, in a random oracle on all typed histories, by
`(Q + count) / |F|`. `adaptive_soundness` covers
statements chosen after the oracle queries, with decoded challenges, by
`(Q + 2) * (1 / |F| + loss)`, under a binding whose initial histories determine
the statement (`Determined`); `reduced_soundness` instantiates the decoding with
the reduction of a uniform sample below `N` modulo the field size. The host's
binding of the vector and count public inputs is not modelled (the binding
model covers scalar public inputs only), so the adaptive theorems take the
determining binding as a premise rather than deriving it from the policy.
-/

set_option autoImplicit false

namespace ZkcSecurity.Examples.CompiledSumcheckFiatShamir
open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Construction
open ZkcSecurity.FiatShamir ZkcSecurity.Examples.SumcheckFiatShamir
open Zkc.Polynomial.Multilinear
open scoped ENNReal

variable {F G : Type}

section Compiled
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The compiled Sumcheck verifier: the ideal meaning of the exported validator
with the challenge function `challenge`, on the table values `raw`, the claimed
sum and the round count, from the initial transcript `initial`, read through
the acceptance output the policy selects. -/
def compiledVerifier {m : Type → Type} [Monad m] (challenge : History F G → m F) (raw : List F)
    (claim : F) (count : Nat) (initial : History F G) (proof : Proof F G) :
    m (PIR.Outcome (Option Bool) × Proof F G) :=
  (fun result => (mapOutcome SumcheckProof.acceptance result.1, result.2)) <$>
    ideal SumcheckProof.context challenge (helperTable SumcheckProof.program F G)
      SumcheckProof.participant.returned SumcheckProof.participant.instructions
      (SumcheckProof.inputs raw claim count ++ [.transcript initial]) proof

/-- The Proof Entry's original validator is the imported `example::Interactive`
verifier: both are the role-1 participant of the admitted Sumcheck source, read
through its Boolean output. -/
theorem verifier_imported (raw : List F) (claim : F) (count handle : Nat) :
    SumcheckProof.verifier (G := G) raw claim count handle = importedValidator raw claim count handle :=
  rfl

/-- The vertical link: for every challenge function and service handle, the
compiled verifier is the Fiat–Shamir transform of the imported verifier. -/
theorem construction {m : Type → Type} [Monad m] [LawfulMonad m] (challenge : History F G → m F)
    (raw : List F) (claim : F) (count handle : Nat) (initial : History F G) (proof : Proof F G) :
    compiledVerifier challenge raw claim count initial proof =
      transform SumcheckProof.context challenge (importedValidator raw claim count handle) initial proof := by
  rw [compiledVerifier, SumcheckProof.compiled_transform challenge raw claim count handle initial proof,
    verifier_imported]

end Compiled

section Security
variable [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Fiat–Shamir soundness of the compiled Sumcheck proof Entry for a fixed
statement: against every prover with at most `queries` queries to one lazily
sampled random oracle on all typed histories (empty initial cache, shared with
the verifier's challenges), the compiled verifier accepts a false claim on the
raw table values with probability at most `(queries + count) / |F|`, for every
initial transcript. Acceptance here ignores unread proof messages, so the bound
also covers an acceptance of the same ideal interpretation that additionally
requires the whole proof to be read; no executable meaning of this Entry is
covered. -/
theorem soundness (count : Nat) (raw : List F) (table : Table F count)
    (decoded : ofList? count raw = some table) (claim : F) (falseClaim : claim ≠ raw.sum)
    (initial : History F G) (prover : OracleComp (FieldOracle F G) (Proof F G)) (queries : Nat)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle
        (prover >>= compiledVerifier historyQuery raw claim count initial)).run' ∅}[
      Accepted (· = some true) result.1] ≤
      (queries + count) * (1 / (Fintype.card F : ENNReal)) :=
  compiled_imported_soundness SumcheckProof.context (compiledVerifier historyQuery raw claim count initial)
    count raw table decoded claim falseClaim 0 initial
    (fun proof => construction historyQuery raw claim count 0 initial proof) prover queries proverBound

/-- Adaptive Fiat–Shamir soundness of the compiled Sumcheck proof Entry: the
prover chooses a well-formed public statement after its oracle queries, the
verifier starts from that statement's initial transcript `initial statement`,
and challenges are decoded oracle answers whose events exceed the uniform
field's by at most `loss`. If the initial transcripts determine the statement,
a false claim is accepted with probability at most
`(queries + 2) * (1 / |F| + loss)`. -/
theorem adaptive_soundness {B : Type} [SampleableType B] (decode : B → F) (loss : ENNReal)
    (balanced : Balanced decode loss) (initial : PublicStatement F → History F G)
    (determined : Determined initial)
    (prover : OracleComp (Oracle F G B) (PublicStatement F × Proof F G)) (queries : Nat)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (prover >>= fun claimed =>
        (fun result => (claimed.1, result)) <$>
          compiledVerifier (decodedQuery decode) claimed.1.raw claimed.1.claim claimed.1.count
            (initial claimed.1) claimed.2)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = some true) result.2.1] ≤
      (queries + 2) * (1 / (Fintype.card F : ENNReal) + loss) :=
  compiled_adaptive_soundness SumcheckProof.context 0 decode loss balanced initial determined
    (fun statement proof => compiledVerifier (decodedQuery decode) statement.raw statement.claim
      statement.count (initial statement) proof)
    (fun statement proof => construction (decodedQuery decode) statement.raw statement.claim
      statement.count 0 (initial statement) proof)
    prover queries proverBound

/-- The adaptive bound with the suite's challenge derivation modelled as the
reduction modulo the field size of a uniform sample below `N`, read through a
numbering of the field (for a 64-byte squeeze, `N = 2 ^ 512`): the decoding
costs `|F| / N` per challenge. -/
theorem reduced_soundness (numbering : F ≃ Fin (Fintype.card F)) (N : Nat) [NeZero N]
    [SampleableType (Fin N)] (initial : PublicStatement F → History F G)
    (determined : Determined initial)
    (prover : OracleComp (Oracle F G (Fin N)) (PublicStatement F × Proof F G)) (queries : Nat)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (prover >>= fun claimed =>
        (fun result => (claimed.1, result)) <$>
          compiledVerifier (decodedQuery (reduce numbering N)) claimed.1.raw claimed.1.claim
            claimed.1.count (initial claimed.1) claimed.2)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = some true) result.2.1] ≤
      (queries + 2) * (1 / (Fintype.card F : ENNReal) + (Fintype.card F : ENNReal) / N) :=
  adaptive_soundness (reduce numbering N) _ (balanced_reduce numbering N) initial determined prover
    queries proverBound

end Security

end ZkcSecurity.Examples.CompiledSumcheckFiatShamir
