module

public import ZkcExamples.Construction.SumcheckScalarRound

@[expose] public section
/-! The authoritative retained Sumcheck validator and its checked root projection. -/
set_option autoImplicit false
namespace ZkcExamples.Construction.SumcheckDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def nominalFinish (initial : History F G) (values : Domain.Environment (uniformCarriers F G))
    (unread : Proof F G) : m (PIR.Outcome (List (Value F G)) × Proof F G) :=
  pure (readbackOutcome SumcheckProof.context.suite legacyOrigin initial (.returned values), unread)

def retained (challenge : History F G → m F) (values : List F) (claim : F) (rounds : Nat)
    (initial : History F G) (proof : Proof F G) : m (PIR.Outcome (List (Value F G)) × Proof F G) :=
  validate SumcheckProof.program SumcheckProof.context SumcheckProof.participant legacyOrigin challenge
    (inputs values claim rounds) initial proof

omit [LawfulMonad m] in
theorem retained_root (challenge : History F G → m F) (values : List F) (claim : F) (rounds : Nat)
    (initial : History F G) (proof : Proof F G) :
    retained challenge values claim rounds initial proof =
      runK legacyOrigin initial challenge (rootProcess values claim rounds []) proof (nominalFinish initial) := by
  have projection := congrArg
    (fun process => runK legacyOrigin initial challenge process proof (nominalFinish initial))
    (root_projection values claim rounds ([] : Domain.History (uniformCarriers F G)))
  simpa only [retained, validate, rootProjection, runK_forgetCheckpoints, runK_bind,
    inputs, frame, runK, nominalFinish] using projection

end ZkcExamples.Construction.SumcheckDomainConnection
