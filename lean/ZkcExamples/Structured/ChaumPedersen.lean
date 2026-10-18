module

public import ZkcExamples.Structured.ChaumPedersenViews
public import Zkc.Source.Structured.OpenLaws
public import Zkc.Source.Structured.ReplyScript
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Defs

@[expose] public section

/-! The actual original-stage Chaum–Pedersen protocol of `sigma::ChaumPedersen`.

Both participant processes reduce definitionally from the admitted body. The
prover draws one nonce, commits to it at both bases and sends one response; the
verifier checks the Schnorr equation at both bases with that one response. A
reply script fixes one transcript to observe the verifier's returned decision
and the prover's actual sends. -/
namespace ZkcExamples.Structured.ChaumPedersen
open Zkc.Source Zkc.Source.Structured ChaumPedersenViews

set_option smartUnfolding false

/-! Retained action sites of the export. -/
def nonceSite : String := "s0"
def firstCommitmentSite : String := "label_66697273745f636f6d6d69746d656e74_0"
def secondCommitmentSite : String := "label_7365636f6e645f636f6d6d69746d656e74_0"
def challengeSite : String := "label_6368616c6c656e6765"
def deliverySite : String := "label_64656c6976657279_0"
def responseSite : String := "label_726573706f6e7365_0"

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The verifier's own inputs; the witness and nonce service are absent. -/
def verifierInputs (firstBase firstKey secondBase secondKey : G) (challengeService : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some firstBase) (.cons (some firstKey) (.cons (some secondBase) (.cons (some secondKey)
    (.cons none (.cons none (.cons (some challengeService) .nil))))))

def proverInputs (firstBase firstKey secondBase secondKey : G) (witness : F) (nonceService : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some firstBase) (.cons (some firstKey) (.cons (some secondBase) (.cons (some secondKey)
    (.cons (some witness) (.cons (some nonceService) (.cons none .nil))))))

/-- The actual checked verifier: one response checked at both bases. -/
theorem verifier_equation (firstBase firstKey secondBase secondKey : G) (challengeService : Nat) :
    program.participant F G 1 (verifierInputs firstBase firstKey secondBase secondKey challengeService) =
      .call (.receive (.group groupDomain) firstCommitmentSite 0) fun (firstCommitment : G) =>
      .call (.receive (.group groupDomain) secondCommitmentSite 0) fun (secondCommitment : G) =>
      .call (.query challengeSite scalarDomain (.cons challengeService .nil)) fun (challenge : F) =>
      .call (.send (ty := .field scalarDomain) deliverySite 0 challenge) fun _ =>
      .call (.receive (.field scalarDomain) responseSite 0) fun (response : F) =>
      .done (.cons (some (decide (response • firstBase = firstCommitment + challenge • firstKey) &&
        decide (response • secondBase = secondCommitment + challenge • secondKey))) .nil) := by
  rfl

/-- The actual checked prover: one nonce at both bases and one response. -/
theorem prover_equation (firstBase firstKey secondBase secondKey : G) (witness : F) (nonceService : Nat) :
    program.participant F G 0 (proverInputs firstBase firstKey secondBase secondKey witness nonceService) =
      .call (.query nonceSite scalarDomain (.cons nonceService .nil)) fun (nonce : F) =>
      .call (.send (ty := .group groupDomain) firstCommitmentSite 1 (nonce • firstBase)) fun _ =>
      .call (.send (ty := .group groupDomain) secondCommitmentSite 1 (nonce • secondBase)) fun _ =>
      .call (.receive (.field scalarDomain) deliverySite 1) fun (challenge : F) =>
      .call (.send (ty := .field scalarDomain) responseSite 1 (nonce + challenge * witness)) fun _ =>
      .done (.cons none .nil) := by
  rfl

/-- One public transcript as verifier replies. -/
def transcript (commitments : G × G) (challenge response : F) : ReplyScript F G where
  receive
    | .group _, site => if site = firstCommitmentSite then some commitments.1
        else if site = secondCommitmentSite then some commitments.2 else none
    | .field _, site => if site = responseSite then some response else none
    | _, _ => none
  draw site := if site = challengeSite then some challenge else none

/-- The verifier's actual run on one transcript, with its full returned tuple. -/
def execute (firstBase firstKey secondBase secondKey : G) (challengeService : Nat)
    (commitments : G × G) (challenge response : F) :=
  (transcript commitments challenge response).run
    (program.participant F G 1 (verifierInputs firstBase firstKey secondBase secondKey challengeService))

theorem execute_eq (firstBase firstKey secondBase secondKey : G) (challengeService : Nat)
    (commitments : G × G) (challenge response : F) :
    execute firstBase firstKey secondBase secondKey challengeService commitments challenge response =
      ⟨.returned (.cons (some (decide (response • firstBase = commitments.1 + challenge • firstKey) &&
          decide (response • secondBase = commitments.2 + challenge • secondKey))) .nil), (),
        [.receive (.group groupDomain) firstCommitmentSite 0,
         .receive (.group groupDomain) secondCommitmentSite 0,
         .query challengeSite scalarDomain (.cons challengeService .nil),
         .send (ty := .field scalarDomain) deliverySite 0 challenge,
         .receive (.field scalarDomain) responseSite 0]⟩ := by
  rw [execute, verifier_equation]
  rfl

/-- The prover's replies: its nonce and the delivered challenge. -/
def nonces (nonce challenge : F) : ReplyScript F G where
  receive
    | .field _, site => if site = deliverySite then some challenge else none
    | _, _ => none
  draw site := if site = nonceSite then some nonce else none

/-- The prover's actual sends for a given nonce and challenge, in order. -/
theorem prover_run (firstBase firstKey secondBase secondKey : G) (witness : F) (nonceService : Nat)
    (nonce challenge : F) :
    (nonces nonce challenge).run (program.participant F G 0
        (proverInputs firstBase firstKey secondBase secondKey witness nonceService)) =
      ⟨.returned (.cons none .nil), (),
        [.query nonceSite scalarDomain (.cons nonceService .nil),
         .send (ty := .group groupDomain) firstCommitmentSite 1 (nonce • firstBase),
         .send (ty := .group groupDomain) secondCommitmentSite 1 (nonce • secondBase),
         .receive (.field scalarDomain) deliverySite 1,
         .send (ty := .field scalarDomain) responseSite 1 (nonce + challenge * witness)]⟩ := by
  rw [prover_equation]
  rfl

end ZkcExamples.Structured.ChaumPedersen
