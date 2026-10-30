module

public import ZkcSecurity.Bindings.Sigma.Schnorr
public import ZkcSecurity.Families.Sigma.SigmaAndSchnorr
public import Zkc.Protocols.Schnorr.Variants

@[expose] public section

/-! # The Schnorr variant families

The family packages of three Schnorr-style proofs of knowledge, generic over
the checked occurrence context and the verifier's wiring, for every compiled
Entry whose original validator is one of the common verifiers of
`Zkc.Protocols.Schnorr.Variants`:

- `equality` (Chaum–Pedersen): two commitment messages, one response. The Sigma
  protocol is VCVio's Schnorr protocol over the product module `G × G` at the
  base pair, with the verifier's two equations as its verification
  (`equalitySigma_eq`); special soundness is VCVio's.
- `conjunction` (two Schnorr proofs under one challenge): two commitment
  messages, two responses. The Sigma protocol is the shared-challenge
  composition of two VCVio Schnorr protocols (`SigmaAndSchnorr.sigma`), whose
  verification is the verifier's decision; special soundness is the
  composition's.
- `representation` (Okamoto): one commitment message, two responses. The Sigma
  protocol is Okamoto's over the two bases (`representationSigma`); special
  soundness divides each response difference by the challenge difference
  (`representationSigma_speciallySound`).

For each, the transform of the common verifier on the proof of commitments and
responses asks one challenge, at the initial transcript followed by the
commitments' messages and the challenge occurrence, and returns the protocol's
verification (`*_transform_shape`); every other typed proof is rejected on every
path (`*_transform_rejects`). The package imports no compiled Entry.
-/

set_option autoImplicit false

namespace ZkcSecurity.Families.SchnorrVariants
open OracleComp OracleSpec
open Zkc.Construction Zkc.Source.Structured
open Zkc.Protocols.Schnorr.Variants
open ZkcSecurity.Endpoint
open ZkcSecurity.Families.Schnorr (value_group value_field)

/-! ## Readers shared by the shapes -/

section Readers
variable {F G : Type}

/-- Two commitment messages at two occurrences, of one group domain. -/
def readPair (first second : Origin) (domain : String) : History F G → Option (G × G)
  | [.message origin₁ (.group domain₁ commitment₁), .message origin₂ (.group domain₂ commitment₂)] =>
      if origin₁ = first ∧ domain₁ = domain ∧ origin₂ = second ∧ domain₂ = domain then
        some (commitment₁, commitment₂)
      else none
  | _ => none

theorem readPair_events (first second : Origin) (domain : String) (events : History F G) (commitments : G × G)
    (found : readPair first second domain events = some commitments) :
    [.message first (.group domain commitments.1), .message second (.group domain commitments.2)] = events := by
  unfold readPair at found
  split at found
  · split_ifs at found with same
    obtain ⟨originEq₁, domainEq₁, originEq₂, domainEq₂⟩ := same
    cases found
    subst originEq₁ domainEq₁ originEq₂ domainEq₂
    rfl
  · cases found

/-- One commitment message at an occurrence, of a group domain. -/
def readOne (origin : Origin) (domain : String) : History F G → Option G
  | [.message found (.group foundDomain commitment)] =>
      if found = origin ∧ foundDomain = domain then some commitment else none
  | _ => none

theorem readOne_events (origin : Origin) (domain : String) (events : History F G) (commitment : G)
    (found : readOne origin domain events = some commitment) :
    [.message origin (.group domain commitment)] = events := by
  unfold readOne at found
  split at found
  · split_ifs at found with same
    obtain ⟨originEq, domainEq⟩ := same
    cases found
    subst originEq domainEq
    rfl
  · cases found

end Readers

/-- A statement/witness generator required by VCVio's transform. It carries no
hardness or efficiency claim and plays no role in extraction. -/
def generable {Stmt Wit : Type} [SampleableType Wit] (rel : Stmt → Wit → Bool) (statement : Wit → Stmt)
    (sound : ∀ witness, rel (statement witness) witness = true) : GenerableRelation Stmt Wit rel where
  gen := do
    let witness ← $ᵗ Wit
    pure (statement witness, witness)
  gen_sound := by
    intro key witness supported
    simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨sampled, -, same⟩ := supported
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact sound _

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-! ## Chaum–Pedersen -/

section Equality
variable (context : Context) (wiring : EqualityWiring)

def equalityFirst : Origin := context.message wiring.firstCommitmentSite wiring.prover context.validator
def equalitySecond : Origin := context.message wiring.secondCommitmentSite wiring.prover context.validator
def equalityChallenge : Origin := context.query wiring.challengeSite (.draw wiring.fieldDomain)

/-- The two commitments and the response a typed proof reads as; any other proof
reads as zero. -/
def readEqualityProof : Proof F G → (G × G) × F
  | [.group _ first, .group _ second, .field _ response] => ((first, second), response)
  | _ => ((0, 0), 0)

/-- The Chaum–Pedersen transcript shape. -/
def equalityShape : Sigma.Shape F G (G × G) F where
  commitments commitments :=
    [.message (equalityFirst context wiring) (.group wiring.groupDomain commitments.1),
      .message (equalitySecond context wiring) (.group wiring.groupDomain commitments.2)]
  width := 2
  width_eq _ := rfl
  readCommitment := readPair (equalityFirst context wiring) (equalitySecond context wiring) wiring.groupDomain
  read_commitments commitments := by simp [readPair]
  commitments_read := readPair_events _ _ _
  challenge := .challenge (equalityChallenge context wiring)
  proof commitments response :=
    [.group wiring.groupDomain commitments.1, .group wiring.groupDomain commitments.2,
      .field wiring.fieldDomain response]
  read := readEqualityProof
  read_proof _ _ := rfl
  fallback := (0, 0)

omit [DecidableEq F] in
theorem equality_transform_shape {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (firstBase firstKey secondBase secondKey : G) (handle : Nat)
    (initial : History F G) (commitments : G × G) (response : F) :
    transform context challenge (equality wiring firstBase firstKey secondBase secondKey handle) initial
        [.group wiring.groupDomain commitments.1, .group wiring.groupDomain commitments.2,
          .field wiring.fieldDomain response] =
      challenge (initial ++ [.message (equalityFirst context wiring) (.group wiring.groupDomain commitments.1),
          .message (equalitySecond context wiring) (.group wiring.groupDomain commitments.2)] ++
          [.challenge (equalityChallenge context wiring)]) >>= fun answer =>
        pure (.returned (some (decide (response • firstBase = commitments.1 + answer • firstKey) &&
          decide (response • secondBase = commitments.2 + answer • secondKey))), []) := by
  simp [equality, transform_eq_done, transform_eq_receive, transform_eq_query, transform_eq_send,
    Payload.value, Payload.ofValue, equalityFirst, equalitySecond, equalityChallenge]

omit [DecidableEq F] in
theorem equality_transform_rejects {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (firstBase firstKey secondBase secondKey : G) (handle : Nat)
    (initial : History F G) (proof : Proof F G)
    (bad : ∀ (first second : G) (response : F), proof ≠
      [.group wiring.groupDomain first, .group wiring.groupDomain second, .field wiring.fieldDomain response]) :
    verdict <$> transform context challenge (equality wiring firstBase firstKey secondBase secondKey handle)
        initial proof =
      (fun _ => false) <$> transform context challenge
        (equality wiring firstBase firstKey secondBase secondKey handle) initial proof := by
  unfold equality
  rcases proof with _ | ⟨first, rest⟩
  · simp [transform_eq_receive, verdict]
  cases decodedFirst : first.value (.group wiring.groupDomain) with
  | none => simp [transform_eq_receive, decodedFirst, verdict]
  | some firstCommitment =>
  have firstEq := value_group decodedFirst
  rcases rest with _ | ⟨second, rest⟩
  · simp [transform_eq_receive, decodedFirst, verdict]
  cases decodedSecond : second.value (.group wiring.groupDomain) with
  | none => simp [transform_eq_receive, decodedFirst, decodedSecond, verdict]
  | some secondCommitment =>
  have secondEq := value_group decodedSecond
  rcases rest with _ | ⟨third, rest⟩
  · simp [transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst, decodedSecond, verdict,
      Payload.ofValue]
  cases decodedThird : third.value (.field wiring.fieldDomain) with
  | none => simp [transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst, decodedSecond,
      decodedThird, verdict, Payload.ofValue]
  | some response =>
  have thirdEq := value_field decodedThird
  rcases rest with _ | ⟨fourth, rest⟩
  · exact absurd (by rw [firstEq, secondEq, thirdEq]) (bad firstCommitment secondCommitment response)
  · simp [transform_eq_done, transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst,
      decodedSecond, decodedThird, verdict, Payload.ofValue]

end Equality

/-- The verification of two equations at the base pair. -/
def equalityDecision (firstBase secondBase : G) (keys commitments : G × G) (challenge response : F) : Bool :=
  decide (response • firstBase = commitments.1 + challenge • keys.1) &&
    decide (response • secondBase = commitments.2 + challenge • keys.2)

omit [DecidableEq F] in
theorem equalityDecision_eq [SampleableType F] [SampleableType G] (firstBase secondBase : G) :
    equalityDecision (F := F) firstBase secondBase =
      (_root_.Schnorr.sigma F (G × G) (firstBase, secondBase)).verify := by
  funext keys commitments challenge response
  unfold equalityDecision
  rw [← Bool.decide_and]
  exact decide_eq_decide.mpr (by simp [Prod.ext_iff])

/-- VCVio's Schnorr protocol over `G × G` at the base pair, verified by the two
equations. -/
def equalitySigma [SampleableType F] [SampleableType G] (firstBase secondBase : G) :
    SigmaProtocol (G × G) F (G × G) F F F (fun keys witness => decide (witness • (firstBase, secondBase) = keys)) :=
  { _root_.Schnorr.sigma F (G × G) (firstBase, secondBase) with
    verify := equalityDecision firstBase secondBase }

omit [DecidableEq F] in
theorem equalitySigma_eq [SampleableType F] [SampleableType G] (firstBase secondBase : G) :
    equalitySigma (F := F) firstBase secondBase = _root_.Schnorr.sigma F (G × G) (firstBase, secondBase) := by
  unfold equalitySigma
  rw [equalityDecision_eq]

/-- The Chaum–Pedersen family over a checked context and wiring, for policy
statements with two bases and two keys (`parts`). -/
def equalityFamily [SampleableType F] [SampleableType G] (context : Context) (wiring : EqualityWiring)
    (handle : Nat) {Policy : Type} (parts : Policy → G × G × G × G) :
    SigmaFamily (F := F) (G := G) context Policy (G × G) F (G × G) F F where
  validator statement := equality wiring (parts statement).1 (parts statement).2.1 (parts statement).2.2.1
    (parts statement).2.2.2 handle
  shape := equalityShape context wiring
  key statement := ((parts statement).2.1, (parts statement).2.2.2)
  rel statement := fun keys witness => decide (witness • ((parts statement).1, (parts statement).2.2.1) = keys)
  sigma statement := equalitySigma (parts statement).1 (parts statement).2.2.1
  generable statement := generable _ (fun witness => witness • ((parts statement).1, (parts statement).2.2.1))
    fun _ => decide_eq_true rfl
  sound statement := by
    rw [equalitySigma_eq]
    exact _root_.Schnorr.sigma_speciallySound F (G × G) _
  transform_shape challenge statement initial commitments response :=
    equality_transform_shape context wiring challenge _ _ _ _ handle initial commitments response
  off_shape challenge statement initial proof := by
    by_cases good : ∃ (first second : G) (response : F),
        proof = [.group wiring.groupDomain first, .group wiring.groupDomain second, .field wiring.fieldDomain response]
    · obtain ⟨first, second, response, rfl⟩ := good
      exact .inl rfl
    · exact .inr (equality_transform_rejects context wiring challenge _ _ _ _ handle initial proof
        fun first second response same => good ⟨first, second, response, same⟩)

/-! ## Two Schnorr proofs under one challenge -/

section Conjunction
variable (context : Context) (wiring : ConjunctionWiring)

def conjunctionFirst : Origin := context.message wiring.firstCommitmentSite wiring.prover context.validator
def conjunctionSecond : Origin := context.message wiring.secondCommitmentSite wiring.prover context.validator
def conjunctionChallenge : Origin := context.query wiring.challengeSite (.draw wiring.fieldDomain)

/-- The two commitments and the two responses a typed proof reads as; any other
proof reads as zero. -/
def readConjunctionProof : Proof F G → (G × G) × (F × F)
  | [.group _ first, .group _ second, .field _ firstResponse, .field _ secondResponse] =>
      ((first, second), (firstResponse, secondResponse))
  | _ => ((0, 0), (0, 0))

/-- The transcript shape of two Schnorr proofs under one challenge. -/
def conjunctionShape : Sigma.Shape F G (G × G) (F × F) where
  commitments commitments :=
    [.message (conjunctionFirst context wiring) (.group wiring.groupDomain commitments.1),
      .message (conjunctionSecond context wiring) (.group wiring.groupDomain commitments.2)]
  width := 2
  width_eq _ := rfl
  readCommitment := readPair (conjunctionFirst context wiring) (conjunctionSecond context wiring)
    wiring.groupDomain
  read_commitments commitments := by simp [readPair]
  commitments_read := readPair_events _ _ _
  challenge := .challenge (conjunctionChallenge context wiring)
  proof commitments responses :=
    [.group wiring.groupDomain commitments.1, .group wiring.groupDomain commitments.2,
      .field wiring.fieldDomain responses.1, .field wiring.fieldDomain responses.2]
  read := readConjunctionProof
  read_proof _ _ := rfl
  fallback := (0, 0)

omit [DecidableEq F] in
theorem conjunction_transform_shape {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (firstBase firstKey secondBase secondKey : G) (handle : Nat)
    (initial : History F G) (commitments : G × G) (responses : F × F) :
    transform context challenge (conjunction wiring firstBase firstKey secondBase secondKey handle) initial
        [.group wiring.groupDomain commitments.1, .group wiring.groupDomain commitments.2,
          .field wiring.fieldDomain responses.1, .field wiring.fieldDomain responses.2] =
      challenge (initial ++ [.message (conjunctionFirst context wiring) (.group wiring.groupDomain commitments.1),
          .message (conjunctionSecond context wiring) (.group wiring.groupDomain commitments.2)] ++
          [.challenge (conjunctionChallenge context wiring)]) >>= fun answer =>
        pure (.returned (some (decide (responses.1 • firstBase = commitments.1 + answer • firstKey) &&
          decide (responses.2 • secondBase = commitments.2 + answer • secondKey))), []) := by
  simp [conjunction, transform_eq_done, transform_eq_receive, transform_eq_query, transform_eq_send,
    Payload.value, Payload.ofValue, conjunctionFirst, conjunctionSecond, conjunctionChallenge]

omit [DecidableEq F] in
theorem conjunction_transform_rejects {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (firstBase firstKey secondBase secondKey : G) (handle : Nat)
    (initial : History F G) (proof : Proof F G)
    (bad : ∀ (first second : G) (firstResponse secondResponse : F), proof ≠
      [.group wiring.groupDomain first, .group wiring.groupDomain second, .field wiring.fieldDomain firstResponse,
        .field wiring.fieldDomain secondResponse]) :
    verdict <$> transform context challenge (conjunction wiring firstBase firstKey secondBase secondKey handle)
        initial proof =
      (fun _ => false) <$> transform context challenge
        (conjunction wiring firstBase firstKey secondBase secondKey handle) initial proof := by
  unfold conjunction
  rcases proof with _ | ⟨first, rest⟩
  · simp [transform_eq_receive, verdict]
  cases decodedFirst : first.value (.group wiring.groupDomain) with
  | none => simp [transform_eq_receive, decodedFirst, verdict]
  | some firstCommitment =>
  have firstEq := value_group decodedFirst
  rcases rest with _ | ⟨second, rest⟩
  · simp [transform_eq_receive, decodedFirst, verdict]
  cases decodedSecond : second.value (.group wiring.groupDomain) with
  | none => simp [transform_eq_receive, decodedFirst, decodedSecond, verdict]
  | some secondCommitment =>
  have secondEq := value_group decodedSecond
  rcases rest with _ | ⟨third, rest⟩
  · simp [transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst, decodedSecond, verdict,
      Payload.ofValue]
  cases decodedThird : third.value (.field wiring.fieldDomain) with
  | none => simp [transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst, decodedSecond,
      decodedThird, verdict, Payload.ofValue]
  | some firstResponse =>
  have thirdEq := value_field decodedThird
  rcases rest with _ | ⟨fourth, rest⟩
  · simp [transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst, decodedSecond,
      decodedThird, verdict, Payload.ofValue]
  cases decodedFourth : fourth.value (.field wiring.fieldDomain) with
  | none => simp [transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst, decodedSecond,
      decodedThird, decodedFourth, verdict, Payload.ofValue]
  | some secondResponse =>
  have fourthEq := value_field decodedFourth
  rcases rest with _ | ⟨fifth, rest⟩
  · exact absurd (by rw [firstEq, secondEq, thirdEq, fourthEq])
      (bad firstCommitment secondCommitment firstResponse secondResponse)
  · simp [transform_eq_done, transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst,
      decodedSecond, decodedThird, decodedFourth, verdict, Payload.ofValue]

end Conjunction

/-- The conjunction family over a checked context and wiring, for policy
statements with two bases and two keys (`parts`). -/
def conjunctionFamily [SampleableType F] [SampleableType G] (context : Context) (wiring : ConjunctionWiring)
    (handle : Nat) {Policy : Type} (parts : Policy → G × G × G × G) :
    SigmaFamily (F := F) (G := G) context Policy (G × G) (F × F) (G × G) (F × F) (F × F) where
  validator statement := conjunction wiring (parts statement).1 (parts statement).2.1 (parts statement).2.2.1
    (parts statement).2.2.2 handle
  shape := conjunctionShape context wiring
  key statement := ((parts statement).2.1, (parts statement).2.2.2)
  rel statement := ZkcSecurity.VCVio.SigmaAnd.andRelation
    (fun key witness => decide (witness • (parts statement).1 = key))
    (fun key witness => decide (witness • (parts statement).2.2.1 = key))
  sigma statement := ZkcSecurity.VCVio.SigmaAndSchnorr.sigma F G (parts statement).1 (parts statement).2.2.1
  generable statement := generable _
    (fun witnesses => (witnesses.1 • (parts statement).1, witnesses.2 • (parts statement).2.2.1))
    fun _ => by simp [ZkcSecurity.VCVio.SigmaAnd.andRelation]
  sound statement := ZkcSecurity.VCVio.SigmaAndSchnorr.speciallySound F G _ _
  transform_shape challenge statement initial commitments responses :=
    conjunction_transform_shape context wiring challenge _ _ _ _ handle initial commitments responses
  off_shape challenge statement initial proof := by
    by_cases good : ∃ (first second : G) (firstResponse secondResponse : F),
        proof = [.group wiring.groupDomain first, .group wiring.groupDomain second,
          .field wiring.fieldDomain firstResponse, .field wiring.fieldDomain secondResponse]
    · obtain ⟨first, second, firstResponse, secondResponse, rfl⟩ := good
      exact .inl rfl
    · exact .inr (conjunction_transform_rejects context wiring challenge _ _ _ _ handle initial proof
        fun first second firstResponse secondResponse same =>
          good ⟨first, second, firstResponse, secondResponse, same⟩)

/-! ## Okamoto -/

section Representation
variable (context : Context) (wiring : RepresentationWiring)

def representationCommitment : Origin := context.message wiring.commitmentSite wiring.prover context.validator
def representationChallenge : Origin := context.query wiring.challengeSite (.draw wiring.fieldDomain)

/-- The commitment and the two responses a typed proof reads as; any other proof
reads as zero. -/
def readRepresentationProof : Proof F G → G × (F × F)
  | [.group _ commitment, .field _ firstResponse, .field _ secondResponse] =>
      (commitment, (firstResponse, secondResponse))
  | _ => (0, (0, 0))

/-- The Okamoto transcript shape. -/
def representationShape : Sigma.Shape F G G (F × F) where
  commitments commitment := [.message (representationCommitment context wiring) (.group wiring.groupDomain commitment)]
  width := 1
  width_eq _ := rfl
  readCommitment := readOne (representationCommitment context wiring) wiring.groupDomain
  read_commitments commitment := by simp [readOne]
  commitments_read := readOne_events _ _
  challenge := .challenge (representationChallenge context wiring)
  proof commitment responses :=
    [.group wiring.groupDomain commitment, .field wiring.fieldDomain responses.1,
      .field wiring.fieldDomain responses.2]
  read := readRepresentationProof
  read_proof _ _ := rfl
  fallback := 0

omit [DecidableEq F] in
theorem representation_transform_shape {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (firstBase secondBase point : G) (handle : Nat)
    (initial : History F G) (commitment : G) (responses : F × F) :
    transform context challenge (representation wiring firstBase secondBase point handle) initial
        [.group wiring.groupDomain commitment, .field wiring.fieldDomain responses.1,
          .field wiring.fieldDomain responses.2] =
      challenge (initial ++ [.message (representationCommitment context wiring) (.group wiring.groupDomain commitment)] ++
          [.challenge (representationChallenge context wiring)]) >>= fun answer =>
        pure (.returned (some (decide (responses.1 • firstBase + responses.2 • secondBase =
          commitment + answer • point))), []) := by
  simp [representation, transform_eq_done, transform_eq_receive, transform_eq_query, transform_eq_send,
    Payload.value, Payload.ofValue, representationCommitment, representationChallenge]

omit [DecidableEq F] in
theorem representation_transform_rejects {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (firstBase secondBase point : G) (handle : Nat)
    (initial : History F G) (proof : Proof F G)
    (bad : ∀ (commitment : G) (firstResponse secondResponse : F), proof ≠
      [.group wiring.groupDomain commitment, .field wiring.fieldDomain firstResponse,
        .field wiring.fieldDomain secondResponse]) :
    verdict <$> transform context challenge (representation wiring firstBase secondBase point handle)
        initial proof =
      (fun _ => false) <$> transform context challenge
        (representation wiring firstBase secondBase point handle) initial proof := by
  unfold representation
  rcases proof with _ | ⟨first, rest⟩
  · simp [transform_eq_receive, verdict]
  cases decodedFirst : first.value (.group wiring.groupDomain) with
  | none => simp [transform_eq_receive, decodedFirst, verdict]
  | some commitment =>
  have firstEq := value_group decodedFirst
  rcases rest with _ | ⟨second, rest⟩
  · simp [transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst, verdict, Payload.ofValue]
  cases decodedSecond : second.value (.field wiring.fieldDomain) with
  | none => simp [transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst, decodedSecond,
      verdict, Payload.ofValue]
  | some firstResponse =>
  have secondEq := value_field decodedSecond
  rcases rest with _ | ⟨third, rest⟩
  · simp [transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst, decodedSecond, verdict,
      Payload.ofValue]
  cases decodedThird : third.value (.field wiring.fieldDomain) with
  | none => simp [transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst, decodedSecond,
      decodedThird, verdict, Payload.ofValue]
  | some secondResponse =>
  have thirdEq := value_field decodedThird
  rcases rest with _ | ⟨fourth, rest⟩
  · exact absurd (by rw [firstEq, secondEq, thirdEq]) (bad commitment firstResponse secondResponse)
  · simp [transform_eq_done, transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst,
      decodedSecond, decodedThird, verdict, Payload.ofValue]

end Representation

section RepresentationSigma
variable [SampleableType F] [SampleableType G]

/-- Okamoto's Sigma protocol at two bases: knowledge of a representation of the
point. -/
def representationSigma (firstBase secondBase : G) :
    SigmaProtocol G (F × F) G (F × F) F (F × F)
      (fun point witnesses => decide (witnesses.1 • firstBase + witnesses.2 • secondBase = point)) where
  commit _ _ := do
    let firstNonce ← $ᵗ F
    let secondNonce ← $ᵗ F
    return (firstNonce • firstBase + secondNonce • secondBase, (firstNonce, secondNonce))
  respond _ witnesses nonces challenge :=
    pure (nonces.1 + challenge * witnesses.1, nonces.2 + challenge * witnesses.2)
  verify point commitment challenge responses :=
    decide (responses.1 • firstBase + responses.2 • secondBase = commitment + challenge • point)
  sim _ := $ᵗ G
  extract challenge₁ responses₁ challenge₂ responses₂ :=
    pure ((responses₁.1 - responses₂.1) * (challenge₁ - challenge₂)⁻¹,
      (responses₁.2 - responses₂.2) * (challenge₁ - challenge₂)⁻¹)

omit [DecidableEq F] in
/-- Two accepting transcripts with one commitment and distinct challenges give a
representation: each response difference divided by the challenge difference. -/
theorem representationSigma_speciallySound (firstBase secondBase : G) :
    (representationSigma (F := F) firstBase secondBase).SpeciallySound := by
  intro point commitment challenge₁ challenge₂ responses₁ responses₂ distinct accepted₁ accepted₂ witnesses
    extracted
  simp only [representationSigma, support_pure, Set.mem_singleton_iff] at extracted accepted₁ accepted₂
  subst extracted
  simp only [decide_eq_true_eq] at accepted₁ accepted₂ ⊢
  have difference : (responses₁.1 - responses₂.1) • firstBase + (responses₁.2 - responses₂.2) • secondBase =
      (challenge₁ - challenge₂) • point := by
    calc (responses₁.1 - responses₂.1) • firstBase + (responses₁.2 - responses₂.2) • secondBase
        = (responses₁.1 • firstBase + responses₁.2 • secondBase) -
            (responses₂.1 • firstBase + responses₂.2 • secondBase) := by
          rw [sub_smul, sub_smul]
          abel
      _ = (challenge₁ - challenge₂) • point := by
          rw [accepted₁, accepted₂, sub_smul]
          abel
  rw [mul_comm, ← smul_smul, mul_comm, ← smul_smul, ← smul_add, difference, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero.mpr distinct), one_smul]

/-- The Okamoto family over a checked context and wiring, for policy statements
with two bases and a point (`parts`). -/
def representationFamily (context : Context) (wiring : RepresentationWiring) (handle : Nat) {Policy : Type}
    (parts : Policy → G × G × G) :
    SigmaFamily (F := F) (G := G) context Policy G (F × F) G (F × F) (F × F) where
  validator statement := representation wiring (parts statement).1 (parts statement).2.1 (parts statement).2.2 handle
  shape := representationShape context wiring
  key statement := (parts statement).2.2
  rel statement := fun point witnesses =>
    decide (witnesses.1 • (parts statement).1 + witnesses.2 • (parts statement).2.1 = point)
  sigma statement := representationSigma (parts statement).1 (parts statement).2.1
  generable statement := generable _
    (fun witnesses => witnesses.1 • (parts statement).1 + witnesses.2 • (parts statement).2.1)
    fun _ => decide_eq_true rfl
  sound statement := representationSigma_speciallySound _ _
  transform_shape challenge statement initial commitment responses :=
    representation_transform_shape context wiring challenge _ _ _ handle initial commitment responses
  off_shape challenge statement initial proof := by
    by_cases good : ∃ (commitment : G) (firstResponse secondResponse : F),
        proof = [.group wiring.groupDomain commitment, .field wiring.fieldDomain firstResponse,
          .field wiring.fieldDomain secondResponse]
    · obtain ⟨commitment, firstResponse, secondResponse, rfl⟩ := good
      exact .inl rfl
    · exact .inr (representation_transform_rejects context wiring challenge _ _ _ handle initial proof
        fun commitment firstResponse secondResponse same => good ⟨commitment, firstResponse, secondResponse, same⟩)

end RepresentationSigma

end ZkcSecurity.Families.SchnorrVariants
