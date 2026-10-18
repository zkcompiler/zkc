module

public import ZkcExamples.Structured.SchnorrAndViews
public import Zkc.Source.Structured.OpenLaws
public import Zkc.Source.Structured.ReplyScript
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Defs

@[expose] public section

/-! The actual original-stage Schnorr AND protocol of `sigma::SchnorrAnd`.

Both participant processes reduce definitionally from the admitted body, for
arbitrary scalar fields and modules and independent typed replies. The prover
draws one nonce per statement and answers the single delivered challenge in both
components; the verifier receives two commitments, draws one challenge and
accepts when both Schnorr equations hold. A reply script fixes one transcript to
observe the verifier's actual returned decision and the prover's actual sends. -/
namespace ZkcExamples.Structured.SchnorrAnd
open Zkc.Source Zkc.Source.Structured SchnorrAndViews

set_option smartUnfolding false

/-! Retained action sites of the export. -/
def firstNonceSite : String := "s0"
def secondNonceSite : String := "s2"
def firstCommitmentSite : String := "label_66697273745f636f6d6d69746d656e74_0"
def secondCommitmentSite : String := "label_7365636f6e645f636f6d6d69746d656e74_0"
def challengeSite : String := "label_6368616c6c656e6765"
def deliverySite : String := "label_64656c6976657279_0"
def firstResponseSite : String := "label_66697273745f726573706f6e7365_0"
def secondResponseSite : String := "label_7365636f6e645f726573706f6e7365_0"

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The verifier's own inputs: both bases and keys and its challenge service.
The prover's witnesses and nonce service are absent, never fabricated. -/
def verifierInputs (firstBase firstKey secondBase secondKey : G) (challengeService : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some firstBase) (.cons (some firstKey) (.cons (some secondBase) (.cons (some secondKey)
    (.cons none (.cons none (.cons none (.cons (some challengeService) .nil)))))))

def proverInputs (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F)
    (nonceService : Nat) : Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some firstBase) (.cons (some firstKey) (.cons (some secondBase) (.cons (some secondKey)
    (.cons (some firstWitness) (.cons (some secondWitness) (.cons (some nonceService) (.cons none .nil)))))))

/-- The actual checked verifier: every continuation consumes the real reply. -/
theorem verifier_equation (firstBase firstKey secondBase secondKey : G) (challengeService : Nat) :
    program.participant F G 1 (verifierInputs firstBase firstKey secondBase secondKey challengeService) =
      .call (.receive (.group groupDomain) firstCommitmentSite 0) fun (firstCommitment : G) =>
      .call (.receive (.group groupDomain) secondCommitmentSite 0) fun (secondCommitment : G) =>
      .call (.query challengeSite scalarDomain (.cons challengeService .nil)) fun (challenge : F) =>
      .call (.send (ty := .field scalarDomain) deliverySite 0 challenge) fun _ =>
      .call (.receive (.field scalarDomain) firstResponseSite 0) fun (firstResponse : F) =>
      .call (.receive (.field scalarDomain) secondResponseSite 0) fun (secondResponse : F) =>
      .done (.cons (some (decide (firstResponse • firstBase = firstCommitment + challenge • firstKey) &&
        decide (secondResponse • secondBase = secondCommitment + challenge • secondKey))) .nil) := by
  rfl

/-- The actual checked prover: two nonce draws, then the commitments, one
received challenge and both responses. Its key copies are never inspected. -/
theorem prover_equation (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F)
    (nonceService : Nat) :
    program.participant F G 0
        (proverInputs firstBase firstKey secondBase secondKey firstWitness secondWitness nonceService) =
      .call (.query firstNonceSite scalarDomain (.cons nonceService .nil)) fun (firstNonce : F) =>
      .call (.query secondNonceSite scalarDomain (.cons nonceService .nil)) fun (secondNonce : F) =>
      .call (.send (ty := .group groupDomain) firstCommitmentSite 1 (firstNonce • firstBase)) fun _ =>
      .call (.send (ty := .group groupDomain) secondCommitmentSite 1 (secondNonce • secondBase)) fun _ =>
      .call (.receive (.field scalarDomain) deliverySite 1) fun (challenge : F) =>
      .call (.send (ty := .field scalarDomain) firstResponseSite 1 (firstNonce + challenge * firstWitness))
        fun _ =>
      .call (.send (ty := .field scalarDomain) secondResponseSite 1
        (secondNonce + challenge * secondWitness)) fun _ =>
      .done (.cons none .nil) := by
  rfl

/-- One public transcript as verifier replies: both commitments, the challenge
and both responses, each at its own site. -/
def transcript (commitments : G × G) (challenge : F) (responses : F × F) : ReplyScript F G where
  receive
    | .group _, site => if site = firstCommitmentSite then some commitments.1
        else if site = secondCommitmentSite then some commitments.2 else none
    | .field _, site => if site = firstResponseSite then some responses.1
        else if site = secondResponseSite then some responses.2 else none
    | _, _ => none
  draw site := if site = challengeSite then some challenge else none

/-- The verifier's actual run on one transcript, with its full returned tuple. -/
def execute (firstBase firstKey secondBase secondKey : G) (challengeService : Nat)
    (commitments : G × G) (challenge : F) (responses : F × F) :=
  (transcript commitments challenge responses).run
    (program.participant F G 1 (verifierInputs firstBase firstKey secondBase secondKey challengeService))

theorem execute_eq (firstBase firstKey secondBase secondKey : G) (challengeService : Nat)
    (commitments : G × G) (challenge : F) (responses : F × F) :
    execute firstBase firstKey secondBase secondKey challengeService commitments challenge responses =
      ⟨.returned (.cons (some (decide (responses.1 • firstBase = commitments.1 + challenge • firstKey) &&
          decide (responses.2 • secondBase = commitments.2 + challenge • secondKey))) .nil), (),
        [.receive (.group groupDomain) firstCommitmentSite 0,
         .receive (.group groupDomain) secondCommitmentSite 0,
         .query challengeSite scalarDomain (.cons challengeService .nil),
         .send (ty := .field scalarDomain) deliverySite 0 challenge,
         .receive (.field scalarDomain) firstResponseSite 0,
         .receive (.field scalarDomain) secondResponseSite 0]⟩ := by
  rw [execute, verifier_equation]
  rfl

/-- The prover's replies: one nonce per draw site and the delivered challenge. -/
def nonces (firstNonce secondNonce challenge : F) : ReplyScript F G where
  receive
    | .field _, site => if site = deliverySite then some challenge else none
    | _, _ => none
  draw site := if site = firstNonceSite then some firstNonce
    else if site = secondNonceSite then some secondNonce else none

/-- The prover's actual sends for given nonces and challenge, in order. -/
theorem prover_run (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F)
    (nonceService : Nat) (firstNonce secondNonce challenge : F) :
    (nonces firstNonce secondNonce challenge).run (program.participant F G 0
        (proverInputs firstBase firstKey secondBase secondKey firstWitness secondWitness nonceService)) =
      ⟨.returned (.cons none .nil), (),
        [.query firstNonceSite scalarDomain (.cons nonceService .nil),
         .query secondNonceSite scalarDomain (.cons nonceService .nil),
         .send (ty := .group groupDomain) firstCommitmentSite 1 (firstNonce • firstBase),
         .send (ty := .group groupDomain) secondCommitmentSite 1 (secondNonce • secondBase),
         .receive (.field scalarDomain) deliverySite 1,
         .send (ty := .field scalarDomain) firstResponseSite 1 (firstNonce + challenge * firstWitness),
         .send (ty := .field scalarDomain) secondResponseSite 1
           (secondNonce + challenge * secondWitness)]⟩ := by
  rw [prover_equation]
  rfl

end ZkcExamples.Structured.SchnorrAnd
