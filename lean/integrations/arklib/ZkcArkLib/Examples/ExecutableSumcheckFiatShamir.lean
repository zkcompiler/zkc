module

public import ZkcArkLib.Examples.CompiledSumcheckFiatShamir
public import ZkcSecurity.VCVio.Pruning
public import ZkcExamples.Executable.SumcheckProof

@[expose] public section

/-! Fiat–Shamir soundness of the executable Sumcheck verifier on proof bytes.

The subject is the validator participant of the `zkc.program/0` candidate that
the native deployment of the Sumcheck example's `example::Proof` carries and
the runtime admits (`ZkcExamples.Executable.SumcheckProof`). Its meaning is
`Zkc.Executable.validate`: the framing header must name the expected
invocation binding, length-framed messages are decoded at their receive types
by a decoder, every instruction is charged against a budget, loop iterations
and local calls enter and leave frames, helper calls run the program's local
functions, and the transcript is an affine unit of the ideal transcript model.
The lowering rule accepted it against the constructed validator of
`CompiledSumcheckFiatShamir`, and its helper functions implement the source's
checked helpers.

A prover here outputs proof bytes. `decoded` turns it into a prover of typed
proofs by decoding its bytes at the receive types of the statement's round
count. Host validation prunes the compiled verifier's acceptance of the decoded
proof by rejections, at every budget and with every framing header
(`verifyBytes_prunes`), so in the random-oracle experiment the executable
accepts at most as often as the compiled verifier accepts the decoded proofs
(`acceptance_le`), and the bounds of `CompiledSumcheckFiatShamir` transfer for
every decoder, budget and expected binding: for a fixed well-formed statement
(`soundness`) and for statements the prover chooses after its queries
(`adaptive_soundness`). No property of the decoder is needed.

The adaptive theorem uses the host's binding of the public inputs, the table
values, the claimed sum and the round count, as the initial transcript
(`initial`): one typed public-value binding event whose row holds the table as a
vector, the claim as a scalar and the round count as a count
(`CompiledSumcheckFiatShamir.publicInitial`). The row determines the statement
(`initial_determined`), which discharges the determining premise of
`CompiledSumcheckFiatShamir.adaptive_soundness`.

Named assumptions beyond those of `CompiledSumcheckFiatShamir`: the runtime
executes the admitted program as `validate` describes, its installed operations
implement the meanings of `Zkc.Executable.installed`, its codec is a function
of a message's bytes and type, and its managed transcript absorbs the public
inputs injectively, as the typed public-value binding event `initial` does.
-/

set_option autoImplicit false

namespace ZkcSecurity.Examples.ExecutableSumcheckFiatShamir
open OracleComp OracleSpec
open Zkc.Construction Zkc.Executable
open ZkcExamples.Construction
open ZkcSecurity.FiatShamir ZkcSecurity.Examples.SumcheckFiatShamir
open ZkcSecurity.Examples.CompiledSumcheckFiatShamir
open ZkcSecurity.VCVio.Pruning
open Zkc.Polynomial.Multilinear
open scoped ENNReal

abbrev executable : Validator := ZkcExamples.Executable.SumcheckProof.validator

variable {F G : Type}

section Bytes
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The typed proof the message bytes after the framing header decode to, at
the receive types of `count` rounds. -/
def decodedProof (decode : PhysicalType → List UInt8 → Option (Payload F G)) (count : Nat)
    (bytes : List UInt8) : Proof F G :=
  decodeProof decode (ZkcExamples.Executable.SumcheckProof.receives count) (bytes.drop 40)

/-- Host validation of proof bytes on the table values `raw`, the claimed sum
and the round count, from the initial transcript `initial`. -/
def verifyBytes {m : Type → Type} [Monad m] (challenge : History F G → m F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat) (binding : List UInt8)
    (raw : List F) (claim : F) (count : Nat) (initial : History F G) (bytes : List UInt8) : m Bool :=
  validate installed executable SumcheckProof.context challenge decode budget binding
    SumcheckProof.acceptancePosition (SumcheckProof.inputs raw claim count) initial bytes

/-- Host validation of proof bytes prunes, by rejections, the compiled
verifier's acceptance of the decoded proof. -/
theorem verifyBytes_prunes {m : Type → Type} [Monad m] [LawfulMonad m] (challenge : History F G → m F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat) (binding : List UInt8)
    (raw : List F) (claim : F) (count : Nat) (initial : History F G) (bytes : List UInt8) :
    Prunes (fun accepted => accepted = false)
      (verifyBytes challenge decode budget binding raw claim count initial bytes)
      (ZkcExamples.Executable.SumcheckProof.accepting <$>
        compiledVerifier challenge raw claim count initial (decodedProof decode count bytes)) := by
  simpa only [verifyBytes, compiledVerifier, SumcheckProof.compiledVerifier,
    decodedProof, ZkcExamples.Executable.SumcheckProof.plan_types] using
    ZkcExamples.Executable.SumcheckProof.domain_prunes challenge decode budget binding raw claim count initial bytes

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- An accepted result returned the decision true. -/
theorem accepted_true {result : PIR.Outcome (Option Bool) × Proof F G}
    (accepted : ZkcExamples.Executable.SumcheckProof.accepting result = true) :
    Accepted (· = some true) result.1 := by
  rcases result with ⟨outcome, unread⟩
  cases outcome with
  | stopped stop => simp [ZkcExamples.Executable.SumcheckProof.accepting] at accepted
  | returned value =>
      cases unread with
      | cons _ _ => simp [ZkcExamples.Executable.SumcheckProof.accepting] at accepted
      | nil =>
          cases value with
          | none => simp [ZkcExamples.Executable.SumcheckProof.accepting] at accepted
          | some decision =>
              simp only [ZkcExamples.Executable.SumcheckProof.accepting] at accepted
              subst accepted
              exact rfl

end Bytes

section Security
variable [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A byte prover's proofs, decoded at the receive types of `count` rounds. -/
def decoded {B : Type} (decode : PhysicalType → List UInt8 → Option (Payload F G)) (count : Nat)
    (prover : OracleComp (Oracle F G B) (List UInt8)) : OracleComp (Oracle F G B) (Proof F G) :=
  decodedProof decode count <$> prover

omit [Fintype F] in
/-- The executable accepts the prover's proof bytes at most as often as the
compiled verifier accepts the decoded proofs, in one lazily sampled random
oracle on all typed histories, for every decoder, budget and expected binding. -/
theorem acceptance_le (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (raw : List F) (claim : F) (count : Nat) (initial : History F G)
    (prover : OracleComp (FieldOracle F G) (List UInt8)) :
    Pr{let accepted ← (simulateQ randomOracle
        (prover >>= verifyBytes historyQuery decode budget binding raw claim count initial)).run' ∅}[
      accepted = true] ≤
      Pr{let result ← (simulateQ randomOracle
          (decoded decode count prover >>= compiledVerifier historyQuery raw claim count initial)).run' ∅}[
        Accepted (· = some true) result.1] := by
  have pruned : Prunes (fun accepted => accepted = false)
      (prover >>= verifyBytes historyQuery decode budget binding raw claim count initial)
      (prover >>= fun bytes => ZkcExamples.Executable.SumcheckProof.accepting <$>
        compiledVerifier historyQuery raw claim count initial (decodedProof decode count bytes)) :=
    .bind _ _ _ fun bytes =>
      verifyBytes_prunes historyQuery decode budget binding raw claim count initial bytes
  refine le_trans (Prunes.prEvent_le randomOracle (fun result rejected => by simp [rejected]) pruned ∅) ?_
  have reorganized : (prover >>= fun bytes => ZkcExamples.Executable.SumcheckProof.accepting <$>
        compiledVerifier historyQuery raw claim count initial (decodedProof decode count bytes)) =
      ZkcExamples.Executable.SumcheckProof.accepting <$>
        (decoded decode count prover >>= compiledVerifier historyQuery raw claim count initial) := by
    simp [decoded, map_bind]
  rw [reorganized, simulateQ_map, StateT.run'_map', prEvent_map]
  exact prEvent_mono _ _ _ fun result accepted => accepted_true accepted

/-- Fiat–Shamir soundness of the executable Sumcheck verifier on proof bytes
for a fixed well-formed statement: against every prover of proof bytes with at
most `queries` queries to one lazily sampled random oracle on all typed
histories, shared with the verifier's challenges, host validation accepts a
false claim on the table values with probability at most
`(queries + count) / |F|`, for every decoder, budget, expected binding and
initial transcript. -/
theorem soundness (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (count : Nat) (raw : List F) (table : Table F count)
    (decodedTable : ofList? count raw = some table) (claim : F) (falseClaim : claim ≠ raw.sum)
    (initial : History F G) (prover : OracleComp (FieldOracle F G) (List UInt8)) (queries : Nat)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let accepted ← (simulateQ randomOracle
        (prover >>= verifyBytes historyQuery decode budget binding raw claim count initial)).run' ∅}[
      accepted = true] ≤
      (queries + count) * (1 / (Fintype.card F : ENNReal)) :=
  le_trans (acceptance_le decode budget binding raw claim count initial prover)
    (CompiledSumcheckFiatShamir.soundness count raw table decodedTable claim falseClaim initial
      (decoded decode count prover) queries ((isQueryBound_map_iff prover _ queries _ _).mpr proverBound))

/-! ### Statements chosen by the prover -/

omit [Fintype F] [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The checked policy publishes the validator's three data inputs, in order:
the table values, the claimed sum and the round count. -/
theorem public_inputs : SumcheckProof.participant.policy.publicInputs = [0, 1, 2] := rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G]
  [DecidableEq G] in
/-- The host's initial transcript for a statement: one typed public-value binding
event of the application context and the statement's public inputs in policy
order, the table values as a vector, the claimed sum as a scalar and the round
count as a count (`CompiledSumcheckFiatShamir.publicInitial`). -/
def initial (application : String) (statement : PublicStatement F) : History F G :=
  CompiledSumcheckFiatShamir.publicInitial application statement

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G]
  [DecidableEq G] in
/-- The initial transcripts determine the statement, from the typed rows. -/
theorem initial_determined (application : String) :
    Determined (initial (F := F) (G := G) application) :=
  CompiledSumcheckFiatShamir.publicInitial_determined application

/-- A byte prover's statements with their proofs decoded at the receive types
of the statement's round count. -/
def decodedStatements {B : Type} (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (prover : OracleComp (Oracle F G B) (PublicStatement F × List UInt8)) :
    OracleComp (Oracle F G B) (PublicStatement F × Proof F G) :=
  (fun claimed => (claimed.1, decodedProof decode claimed.1.count claimed.2)) <$> prover

/-- Adaptive Fiat–Shamir soundness of the executable Sumcheck verifier on proof
bytes: the prover chooses a well-formed public statement and proof bytes after
its oracle queries, host validation starts from the statement's binding
(`initial`), and challenges are decoded oracle answers whose events exceed the
uniform field's by at most `loss`. A false claim is accepted with probability
at most `(queries + 2) * (1 / |F| + loss)`, for every decoder, budget, expected
binding and application context. -/
theorem adaptive_soundness {B : Type} [SampleableType B] (derive : B → F) (loss : ENNReal)
    (balanced : Balanced derive loss) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (budget : Nat) (binding : List UInt8) (application : String)
    (prover : OracleComp (Oracle F G B) (PublicStatement F × List UInt8)) (queries : Nat)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (prover >>= fun claimed =>
        (fun accepted => (claimed.1, accepted)) <$>
          verifyBytes (decodedQuery derive) decode budget binding claimed.1.raw claimed.1.claim
            claimed.1.count (initial application claimed.1) claimed.2)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ result.2 = true] ≤
      (queries + 2) * (1 / (Fintype.card F : ENNReal) + loss) := by
  have pruned : Prunes (fun result : PublicStatement F × Bool => result.2 = false)
      (prover >>= fun claimed => (fun accepted => (claimed.1, accepted)) <$>
        verifyBytes (decodedQuery derive) decode budget binding claimed.1.raw claimed.1.claim
          claimed.1.count (initial application claimed.1) claimed.2)
      (prover >>= fun claimed => (fun accepted => (claimed.1, accepted)) <$>
        (ZkcExamples.Executable.SumcheckProof.accepting <$>
          compiledVerifier (decodedQuery derive) claimed.1.raw claimed.1.claim claimed.1.count
            (initial application claimed.1) (decodedProof decode claimed.1.count claimed.2))) :=
    .bind _ _ _ fun claimed =>
      (verifyBytes_prunes (decodedQuery derive) decode budget binding claimed.1.raw claimed.1.claim
        claimed.1.count (initial application claimed.1) claimed.2).map (fun accepted => (claimed.1, accepted))
        fun _ rejected => rejected
  refine le_trans (Prunes.prEvent_le randomOracle (fun result rejected => by simp [rejected]) pruned ∅) ?_
  have reorganized : (prover >>= fun claimed => (fun accepted => (claimed.1, accepted)) <$>
        (ZkcExamples.Executable.SumcheckProof.accepting <$>
          compiledVerifier (decodedQuery derive) claimed.1.raw claimed.1.claim claimed.1.count
            (initial application claimed.1) (decodedProof decode claimed.1.count claimed.2))) =
      (fun result => (result.1, ZkcExamples.Executable.SumcheckProof.accepting result.2)) <$>
        (decodedStatements decode prover >>= fun claimed => (fun result => (claimed.1, result)) <$>
          compiledVerifier (decodedQuery derive) claimed.1.raw claimed.1.claim claimed.1.count
            (initial application claimed.1) claimed.2) := by
    simp [decodedStatements, map_bind, Functor.map_map]
  rw [reorganized, simulateQ_map, StateT.run'_map', prEvent_map]
  refine le_trans (prEvent_mono _ _
    (fun result => result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = some true) result.2.1)
    fun result holds => ⟨holds.1, accepted_true holds.2⟩) ?_
  exact CompiledSumcheckFiatShamir.adaptive_soundness derive loss balanced (initial application)
    (initial_determined application) (decodedStatements decode prover) queries
    ((isQueryBound_map_iff prover _ queries _ _).mpr proverBound)

/-- The adaptive bound with the suite's challenge derivation modelled as the
reduction modulo the field size of a uniform sample below `N`, read through a
numbering of the field: the decoding costs `|F| / N` per challenge. -/
theorem reduced_soundness (numbering : F ≃ Fin (Fintype.card F)) (N : Nat) [NeZero N]
    [SampleableType (Fin N)] (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (application : String)
    (prover : OracleComp (Oracle F G (Fin N)) (PublicStatement F × List UInt8)) (queries : Nat)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (prover >>= fun claimed =>
        (fun accepted => (claimed.1, accepted)) <$>
          verifyBytes (decodedQuery (reduce numbering N)) decode budget binding claimed.1.raw claimed.1.claim
            claimed.1.count (initial application claimed.1) claimed.2)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ result.2 = true] ≤
      (queries + 2) * (1 / (Fintype.card F : ENNReal) + (Fintype.card F : ENNReal) / N) :=
  adaptive_soundness (reduce numbering N) _ (balanced_reduce numbering N) decode budget binding application
    prover queries proverBound

end Security

end ZkcSecurity.Examples.ExecutableSumcheckFiatShamir
