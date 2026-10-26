module

public import ZkcExamples.Construction.SumcheckArtifact
public import ZkcExamples.Construction.SumcheckSourceConnection
public import ZkcExamples.Construction.SumcheckLegacyRoot

@[expose] public section
/-! Maintained Sumcheck source correspondence at the authoritative Domain
instruction Process. The legacy comparison preserves the previous typed
proposition. The previous raw-environment `spec_transform` is retired; its
model-transition disposition and checked counterexample are recorded in
`docs/semantic-model-transition.md`. -/
set_option autoImplicit false
namespace ZkcExamples.Construction.SumcheckProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- For arbitrary typed public values, every proof and every challenge in a
lawful monad, the Domain participant preserves the original transform's
acceptance, stops and exact unread suffix. -/
theorem compiled_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (valuesValue : List F) (claim : F) (rounds : Nat) (handle : Nat)
    (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        SumcheckDomainConnection.retained challenge valuesValue claim rounds initial proof =
      transform context challenge (verifier valuesValue claim rounds handle) initial proof :=
  SumcheckDomainConnection.retained_transform challenge valuesValue claim rounds handle initial proof

/-- Exact previous typed proposition, now a historical comparison through the
checked artifact bridge. This does not identify the two raw models. -/
theorem legacy_compiled_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (valuesValue : List F) (claim : F) (rounds : Nat) (handle : Nat)
    (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge table participant.returned participant.instructions
          (inputs valuesValue claim rounds ++ [.transcript initial]) proof =
      transform context challenge (verifier valuesValue claim rounds handle) initial proof := by
  rw [SumcheckDomainConnection.retained_legacy]
  exact compiled_transform challenge valuesValue claim rounds handle initial proof

end ZkcExamples.Construction.SumcheckProof
