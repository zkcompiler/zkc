module

public import ZkcArkLib.Examples.SumcheckFiatShamir
public import ZkcSecurity.FiatShamir.Binding
public import ZkcExamples.Construction.SumcheckProof

@[expose] public section

/-! Fiat–Shamir soundness of the compiled Sumcheck proof Entry.

The subject is the compiler's constructed validator for the Sumcheck example's
`example::Proof` Entry (`ZkcExamples.Construction.SumcheckProof.participant`),
which the composed transcript-construction and participant projection check
accepts (`SumcheckProof.compiled`). Its meaning is actual checked Domain execution of
the exported operations under the Entry's checked
occurrence context, with helper calls read by the original's checked helpers,
on the verifier's table values, claimed sum and round count, the initial
transcript and the proof's messages. The verifier accepts when the acceptance
output the policy selects is true (`compiledVerifier`).

Two proved links compose:

* Vertical. For every challenge function the compiled meaning is the
  Fiat–Shamir transform of the Proof Entry's original validator
  (`SumcheckProof.compiled_transform`, derived from the actual all-reply
  Domain-to-source connection). That
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
the reduction of a uniform sample below `N` modulo the field size. The
adaptive theorems take a determining binding as a premise. The typed
public-value binding of the statement discharges it: one binding event whose row
holds the table values as a vector, the claimed sum as a scalar and the round
count as a count (`publicInitial`) determines the statement
(`publicInitial_determined`, from `ZkcSecurity.FiatShamir.determined_single`),
and `adaptive_soundness_public` is the adaptive bound from that binding.
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

/-- The compiled Sumcheck verifier: actual checked Domain execution of the exported validator
with the challenge function `challenge`, on the table values `raw`, the claimed
sum and the round count, from the initial transcript `initial`, read through
the acceptance output the policy selects. -/
def compiledVerifier {m : Type → Type} [Monad m] (challenge : History F G → m F) (raw : List F)
    (claim : F) (count : Nat) (initial : History F G) (proof : Proof F G) :
    m (PIR.Outcome (Option Bool) × Proof F G) :=
  SumcheckProof.compiledVerifier challenge raw claim count initial proof

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

section Binding

/-- The statement's typed public-value row, in input order: the table values as
a vector, the claimed sum as a scalar and the round count as a count. -/
def publicRow (statement : PublicStatement F) : Row (Payload F G) :=
  [("table", .vector (statement.raw.map (.field "bls12-381.fr"))),
    ("claim", .scalar (.field "bls12-381.fr" statement.claim)),
    ("rounds", .count statement.count)]

/-- The host's initial transcript for a statement: one typed public-value binding
event of the application context and the statement's row. -/
def publicInitial (application : String) (statement : PublicStatement F) : History F G :=
  [.publicBinding ⟨application, publicRow statement⟩]

/-- The row determines the statement: it gives back the table values, the claim
and the round count, and the decoded table is a function of the values and the
count. -/
theorem publicRow_injective : Function.Injective (publicRow (F := F) (G := G)) := by
  rintro ⟨raw, claim, count, table, decoded⟩ ⟨raw', claim', count', table', decoded'⟩ same
  simp only [publicRow, List.cons.injEq, Prod.mk.injEq, PublicValue.vector.injEq,
    PublicValue.scalar.injEq, PublicValue.count.injEq, Payload.field.injEq, true_and,
    and_true] at same
  obtain ⟨rawEq, claimEq, countEq⟩ := same
  have values : raw = raw' :=
    List.map_injective_iff.mpr (fun _ _ same => by cases same; rfl) rawEq
  subst values claimEq countEq
  rw [decoded] at decoded'
  cases decoded'
  rfl

/-- The typed public-value binding determines the statement. -/
theorem publicInitial_determined (application : String) :
    Determined (publicInitial (F := F) (G := G) application) :=
  fun statement other rest otherRest same =>
    determined_single Event.publicBinding (fun _ _ same => by cases same; rfl) application
      publicRow publicRow_injective statement other rest otherRest same

end Binding

section Security
variable [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Fiat–Shamir soundness of the compiled Sumcheck proof Entry for a fixed
statement: against every prover with at most `queries` queries to one lazily
sampled random oracle on all typed histories (empty initial cache, shared with
the verifier's challenges), the compiled verifier accepts a false claim on the
raw table values with probability at most `(queries + count) / |F|`, for every
initial transcript. Acceptance here ignores unread proof messages, so the bound
also covers an acceptance of the same Domain execution that additionally
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

/-- The adaptive bound from the typed public-value binding of the statement: no
determination premise remains. -/
theorem adaptive_soundness_public {B : Type} [SampleableType B] (decode : B → F)
    (loss : ENNReal) (balanced : Balanced decode loss) (application : String)
    (prover : OracleComp (Oracle F G B) (PublicStatement F × Proof F G)) (queries : Nat)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (prover >>= fun claimed =>
        (fun result => (claimed.1, result)) <$>
          compiledVerifier (decodedQuery decode) claimed.1.raw claimed.1.claim claimed.1.count
            (publicInitial application claimed.1) claimed.2)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = some true) result.2.1] ≤
      (queries + 2) * (1 / (Fintype.card F : ENNReal) + loss) :=
  adaptive_soundness decode loss balanced (publicInitial application)
    (publicInitial_determined application) prover queries proverBound

end Security

end ZkcSecurity.Examples.CompiledSumcheckFiatShamir
