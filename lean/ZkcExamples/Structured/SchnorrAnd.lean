module

public import ZkcExamples.Structured.SchnorrAndNormalForms

@[expose] public section

/-! The actual original-stage Schnorr AND protocol of `sigma::SchnorrAnd`.

Both participant processes, their runs on reply scripts and the knowledge
clause's binding are the generated ones of `SchnorrAndNormalForms`. The prover
draws one nonce per statement and answers the single delivered challenge in both
components; the verifier receives two commitments, draws one challenge and
accepts when both Schnorr equations hold. This module keeps the prover-side
names that the Σ-protocol instantiation states its theorems with. -/
namespace ZkcExamples.Structured.SchnorrAnd
open Zkc.Source Zkc.Source.Structured SchnorrAndViews

/-! Retained action sites of the export. -/
abbrev firstNonceSite : String := SchnorrAndNormalForms.firstNonceSite
abbrev secondNonceSite : String := SchnorrAndNormalForms.secondNonceSite
abbrev firstCommitmentSite : String := SchnorrAndNormalForms.firstCommitmentSite
abbrev secondCommitmentSite : String := SchnorrAndNormalForms.secondCommitmentSite
abbrev challengeSite : String := SchnorrAndNormalForms.challengeSite
abbrev deliverySite : String := SchnorrAndNormalForms.deliverySite
abbrev firstResponseSite : String := SchnorrAndNormalForms.firstResponseSite
abbrev secondResponseSite : String := SchnorrAndNormalForms.secondResponseSite

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The prover's own inputs; the verifier's challenge service is absent. -/
abbrev proverInputs (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F)
    (nonceService : Nat) : Values (Component (assignment F G)) program.payload.entry.inputs :=
  SchnorrAndNormalForms.proverInputs firstBase firstKey secondBase secondKey firstWitness secondWitness
    nonceService

/-- The prover's replies: one nonce per draw site and the delivered challenge. -/
abbrev nonces (firstNonce secondNonce challenge : F) : ReplyScript F G :=
  SchnorrAndNormalForms.proverReplies firstNonce secondNonce challenge

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
           (secondNonce + challenge * secondWitness)]⟩ :=
  SchnorrAndNormalForms.prover_run firstBase firstKey secondBase secondKey firstWitness secondWitness
    nonceService firstNonce secondNonce challenge

end ZkcExamples.Structured.SchnorrAnd
