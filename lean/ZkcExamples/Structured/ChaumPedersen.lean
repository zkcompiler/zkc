module

public import ZkcExamples.Structured.ChaumPedersenNormalForms

@[expose] public section

/-! The actual original-stage Chaum–Pedersen protocol of `sigma::ChaumPedersen`.

Both participant processes, their runs on reply scripts and the knowledge
clause's binding are the generated ones of `ChaumPedersenNormalForms`. The
prover draws one nonce, commits to it at both bases and sends one response; the
verifier checks the Schnorr equation at both bases with that one response. This
module keeps the prover-side names that the Σ-protocol instantiation states its
theorems with. -/
namespace ZkcExamples.Structured.ChaumPedersen
open Zkc.Source Zkc.Source.Structured ChaumPedersenViews

/-! Retained action sites of the export. -/
abbrev nonceSite : String := ChaumPedersenNormalForms.nonceSite
abbrev firstCommitmentSite : String := ChaumPedersenNormalForms.firstCommitmentSite
abbrev secondCommitmentSite : String := ChaumPedersenNormalForms.secondCommitmentSite
abbrev deliverySite : String := ChaumPedersenNormalForms.deliverySite
abbrev responseSite : String := ChaumPedersenNormalForms.responseSite

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev proverInputs (firstBase firstKey secondBase secondKey : G) (witness : F) (nonceService : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  ChaumPedersenNormalForms.proverInputs firstBase firstKey secondBase secondKey witness nonceService

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
