module

public import ZkcSecurity.Endpoint.Knowledge
public import Zkc.Protocols.Schnorr.Common
public import Examples.Schnorr.SigmaProtocol

@[expose] public section

/-! # The Schnorr family

The family package of Schnorr proofs of knowledge of a discrete logarithm,
generic over the checked occurrence context and the verifier's wiring: the
mathematics once for every compiled Entry whose original validator is the
common Schnorr verifier (`Zkc.Protocols.Schnorr.Common.experiment`).

- The one-challenge transcript shape (`shape`): one commitment message of the
  group domain, the challenge occurrence of the field draw, and proofs of a
  commitment followed by a response; any other typed proof reads as zero.
- The Sigma protocol is VCVio's Schnorr protocol at the statement's base, with
  the statement's key as its statement (`family`); special soundness is VCVio's.
- Verifier correspondence (`transform_shape`): on the proof of a commitment and
  a response, the transform of the common verifier asks one challenge, at the
  initial transcript followed by the commitment's message and the challenge
  occurrence, and checks the Schnorr equation.
- Shape (`off_shape`): every other typed proof is rejected on every path.

The package imports no compiled Entry; an Entry supplies its context, wiring and
the base and key of its published statement.
-/

set_option autoImplicit false

namespace ZkcSecurity.Families.Schnorr
open OracleComp OracleSpec
open Zkc.Construction Zkc.Source.Structured
open Zkc.Protocols.Schnorr.Common (Wiring experiment)
open ZkcSecurity.Endpoint

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The commitment's message occurrence. -/
def commitmentOrigin (context : Context) (wiring : Wiring) : Origin :=
  context.message wiring.commitmentSite wiring.prover context.validator

/-- The challenge occurrence. -/
def challengeOrigin (context : Context) (wiring : Wiring) : Origin :=
  context.query wiring.challengeSite (.draw wiring.fieldDomain)

/-- The commitment that events absorb: one commitment message of the group
domain. -/
def readCommitment (context : Context) (wiring : Wiring) : History F G → Option G
  | [.message origin (.group domain commitment)] =>
      if origin = commitmentOrigin context wiring ∧ domain = wiring.groupDomain then some commitment else none
  | _ => none

/-- The commitment and response a typed proof reads as; any other proof reads as
zero. -/
def readProof : Proof F G → G × F
  | [.group _ commitment, .field _ response] => (commitment, response)
  | _ => (0, 0)

/-- The Schnorr transcript shape. -/
def shape (context : Context) (wiring : Wiring) : Sigma.Shape F G G F where
  commitments commitment := [.message (commitmentOrigin context wiring) (.group wiring.groupDomain commitment)]
  width := 1
  width_eq _ := rfl
  readCommitment := readCommitment context wiring
  read_commitments commitment := by simp [readCommitment]
  commitments_read events commitment found := by
    unfold readCommitment at found
    split at found
    · split_ifs at found with same
      obtain ⟨originEq, domainEq⟩ := same
      cases found
      subst originEq domainEq
      rfl
    · cases found
  challenge := .challenge (challengeOrigin context wiring)
  proof commitment response := [.group wiring.groupDomain commitment, .field wiring.fieldDomain response]
  read := readProof
  read_proof _ _ := rfl
  fallback := 0

/-- A statement/witness generator required by VCVio's transform. It carries no
hardness or efficiency claim and plays no role in extraction. -/
def generable [SampleableType F] (base : G) :
    GenerableRelation G F (fun key witness => decide (witness • base = key)) where
  gen := do
    let witness ← $ᵗ F
    pure (witness • base, witness)
  gen_sound := by
    intro key witness supported
    simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨sampled, _, same⟩ := supported
    cases same
    simp

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem value_group {payload : Payload F G} {domain : String} {value : G}
    (decoded : payload.value (.group domain) = some value) : payload = .group domain value := by
  cases payload with
  | group other found =>
      simp only [Payload.value] at decoded
      split_ifs at decoded with same
      cases decoded
      rw [same]
  | boolean => simp [Payload.value] at decoded
  | field => simp [Payload.value] at decoded

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem value_field {payload : Payload F G} {domain : String} {value : F}
    (decoded : payload.value (.field domain) = some value) : payload = .field domain value := by
  cases payload with
  | field other found =>
      simp only [Payload.value] at decoded
      split_ifs at decoded with same
      cases decoded
      rw [same]
  | boolean => simp [Payload.value] at decoded
  | group => simp [Payload.value] at decoded

omit [DecidableEq F] in
/-- On the proof of a commitment and a response, the transform of the common
Schnorr verifier asks one challenge, at the initial transcript followed by the
commitment's message and the challenge occurrence, and checks the Schnorr
equation. -/
theorem transform_shape {m : Type → Type} [Monad m] [LawfulMonad m] (context : Context) (wiring : Wiring)
    (challenge : History F G → m F) (base key : G) (handle : Nat) (initial : History F G)
    (commitment : G) (response : F) :
    transform context challenge (experiment wiring base key handle) initial
        [.group wiring.groupDomain commitment, .field wiring.fieldDomain response] =
      challenge (initial ++ [.message (commitmentOrigin context wiring) (.group wiring.groupDomain commitment)] ++
          [.challenge (challengeOrigin context wiring)]) >>= fun answer =>
        pure (.returned (some (decide (response • base = commitment + answer • key))), []) := by
  simp [experiment, transform_eq_done, transform_eq_receive, transform_eq_query, transform_eq_send,
    Payload.value, Payload.ofValue, commitmentOrigin, challengeOrigin]

omit [DecidableEq F] in
/-- On a typed proof that is not a commitment of the group domain followed by a
response of the field domain, the transform of the common Schnorr verifier
rejects on every path. -/
theorem transform_rejects {m : Type → Type} [Monad m] [LawfulMonad m] (context : Context) (wiring : Wiring)
    (challenge : History F G → m F) (base key : G) (handle : Nat) (initial : History F G) (proof : Proof F G)
    (bad : ∀ (commitment : G) (response : F),
      proof ≠ [.group wiring.groupDomain commitment, .field wiring.fieldDomain response]) :
    verdict <$> transform context challenge (experiment wiring base key handle) initial proof =
      (fun _ => false) <$> transform context challenge (experiment wiring base key handle) initial proof := by
  unfold experiment
  rcases proof with _ | ⟨first, rest⟩
  · simp [transform_eq_receive, verdict]
  · cases decodedFirst : first.value (.group wiring.groupDomain) with
    | none => simp [transform_eq_receive, decodedFirst, verdict]
    | some commitment =>
        have firstEq : first = .group wiring.groupDomain commitment := value_group decodedFirst
        rcases rest with _ | ⟨second, rest₂⟩
        · simp [transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst, verdict,
            Payload.ofValue]
        · cases decodedSecond : second.value (.field wiring.fieldDomain) with
          | none => simp [transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst,
              decodedSecond, verdict, Payload.ofValue]
          | some response =>
              have secondEq : second = .field wiring.fieldDomain response := value_field decodedSecond
              rcases rest₂ with _ | ⟨third, rest₃⟩
              · exact absurd (by rw [firstEq, secondEq]) (bad commitment response)
              · simp [transform_eq_done, transform_eq_receive, transform_eq_query, transform_eq_send,
                  decodedFirst, decodedSecond, verdict, Payload.ofValue]

/-- The Schnorr family over a checked context and wiring, for policy statements
with a base and a key (`parts`): the common Schnorr verifier, VCVio's Schnorr
protocol at the base with the key as statement, the Schnorr shape. -/
def family [SampleableType F] [SampleableType G] (context : Context) (wiring : Wiring) (handle : Nat)
    {Policy : Type} (parts : Policy → G × G) : SigmaFamily (F := F) (G := G) context Policy G F G F F where
  validator statement := experiment wiring (parts statement).1 (parts statement).2 handle
  shape := shape context wiring
  key statement := (parts statement).2
  rel statement := fun key witness => decide (witness • (parts statement).1 = key)
  sigma statement := _root_.Schnorr.sigma F G (parts statement).1
  generable statement := generable (parts statement).1
  sound statement := _root_.Schnorr.sigma_speciallySound F G (parts statement).1
  transform_shape challenge statement initial commitment response :=
    transform_shape context wiring challenge _ _ handle initial commitment response
  off_shape challenge statement initial proof := by
    by_cases good : ∃ (commitment : G) (response : F),
        proof = [.group wiring.groupDomain commitment, .field wiring.fieldDomain response]
    · obtain ⟨commitment, response, rfl⟩ := good
      exact .inl rfl
    · exact .inr (transform_rejects context wiring challenge _ _ handle initial proof
        fun commitment response same => good ⟨commitment, response, same⟩)

end ZkcSecurity.Families.Schnorr
