module

public import ZkcExamples.Structured.ChaumPedersenViews
public import ZkcExamples.Structured.ChaumPedersenNormalForms
public import Zkc.Source.Structured.OpenLaws
public import Zkc.Source.Structured.ReplyScript
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Defs

@[expose] public section

/-! The actual original-stage Chaum–Pedersen protocol of `sigma::ChaumPedersen`.

Both participant processes are the generated normal forms of the admitted body
(`ChaumPedersenNormalForms`). The prover draws one nonce, commits to it at both
bases and sends one response; the verifier checks the Schnorr equation at both
bases with that one response. A reply script fixes one transcript to observe
the verifier's returned decision and the prover's actual sends. -/
namespace ZkcExamples.Structured.ChaumPedersen
open Zkc.Source Zkc.Source.Structured ChaumPedersenViews

set_option smartUnfolding false

/-! Retained action sites of the export. -/
abbrev nonceSite : String := ChaumPedersenNormalForms.nonceSite
abbrev firstCommitmentSite : String := ChaumPedersenNormalForms.firstCommitmentSite
abbrev secondCommitmentSite : String := ChaumPedersenNormalForms.secondCommitmentSite
abbrev challengeSite : String := ChaumPedersenNormalForms.challengeSite
abbrev deliverySite : String := ChaumPedersenNormalForms.deliverySite
abbrev responseSite : String := ChaumPedersenNormalForms.responseSite

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The verifier's own inputs; the witness and nonce service are absent. -/
abbrev verifierInputs (firstBase firstKey secondBase secondKey : G) (challengeService : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  ChaumPedersenNormalForms.verifierInputs firstBase firstKey secondBase secondKey challengeService

abbrev proverInputs (firstBase firstKey secondBase secondKey : G) (witness : F) (nonceService : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  ChaumPedersenNormalForms.proverInputs firstBase firstKey secondBase secondKey witness nonceService

/-- The actual checked verifier: one response checked at both bases. -/
theorem verifier_equation (firstBase firstKey secondBase secondKey : G) (challengeService : Nat) :
    program.participant F G 1 (verifierInputs firstBase firstKey secondBase secondKey challengeService) =
      .call (.receive (.group groupDomain) firstCommitmentSite 0) fun (firstCommitment : G) =>
      .call (.receive (.group groupDomain) secondCommitmentSite 0) fun (secondCommitment : G) =>
      .call (.query challengeSite scalarDomain (.cons challengeService .nil)) fun (challenge : F) =>
      .call (.send (ty := .field scalarDomain) deliverySite 0 challenge) fun _ =>
      .call (.receive (.field scalarDomain) responseSite 0) fun (response : F) =>
      .done (.cons (some (decide (response • firstBase = firstCommitment + challenge • firstKey) &&
        decide (response • secondBase = secondCommitment + challenge • secondKey))) .nil) :=
  ChaumPedersenNormalForms.verifier_process firstBase firstKey secondBase secondKey challengeService

/-- The actual checked prover: one nonce at both bases and one response. -/
theorem prover_equation (firstBase firstKey secondBase secondKey : G) (witness : F) (nonceService : Nat) :
    program.participant F G 0 (proverInputs firstBase firstKey secondBase secondKey witness nonceService) =
      .call (.query nonceSite scalarDomain (.cons nonceService .nil)) fun (nonce : F) =>
      .call (.send (ty := .group groupDomain) firstCommitmentSite 1 (nonce • firstBase)) fun _ =>
      .call (.send (ty := .group groupDomain) secondCommitmentSite 1 (nonce • secondBase)) fun _ =>
      .call (.receive (.field scalarDomain) deliverySite 1) fun (challenge : F) =>
      .call (.send (ty := .field scalarDomain) responseSite 1 (nonce + challenge * witness)) fun _ =>
      .done (.cons none .nil) :=
  ChaumPedersenNormalForms.prover_process firstBase firstKey secondBase secondKey witness nonceService

/-- One public transcript as verifier replies. -/
abbrev transcript (commitments : G × G) (challenge response : F) : ReplyScript F G :=
  ChaumPedersenNormalForms.verifierReplies commitments.1 commitments.2 challenge response

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
         .receive (.field scalarDomain) responseSite 0]⟩ :=
  ChaumPedersenNormalForms.verifier_run firstBase firstKey secondBase secondKey challengeService
    commitments.1 commitments.2 challenge response

/-- The prover's replies: its nonce and the delivered challenge. -/
abbrev nonces (nonce challenge : F) : ReplyScript F G :=
  ChaumPedersenNormalForms.proverReplies nonce challenge

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
         .send (ty := .field scalarDomain) responseSite 1 (nonce + challenge * witness)]⟩ :=
  ChaumPedersenNormalForms.prover_run firstBase firstKey secondBase secondKey witness nonceService
    nonce challenge

end ZkcExamples.Structured.ChaumPedersen
