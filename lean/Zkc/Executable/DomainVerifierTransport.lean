module

public import Zkc.Executable.DomainParticipant
public import Zkc.Construction.ScalarVerifier

@[expose] public section

/-! The selected scalar verifier and its canonical returned-value observation
share one participant execution. This transport is independent of a property,
proof method, message decoder, source relation or native resource budget. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Source.Structured
open Zkc.Construction.Uniform.DomainAdapter
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Select the actual participant's returned values after forgetting only its
administrative checkpoints, with every stop and unread message unchanged. -/
theorem verifier_observation {m : Type → Type} [Monad m] [LawfulMonad m]
    (program : Structured.Program) (context : Context) (artifact : Participant) (position : Nat)
    (challenge : History F G → m F) (published : List (Value F G))
    (env : Environment F G) (encoded : ScalarVerifier.inputs context published = some env)
    (schema : env.map Domain.Value.sort = artifact.inputs) (returned : ReturnSchema artifact)
    (initial : History F G) (messages : Proof F G) :
    ScalarVerifier.verify program context artifact position challenge published initial messages =
      (fun result => (mapOutcome (fun values => ScalarVerifier.acceptance position ⟨values, []⟩) result.1,
        result.2)) <$>
        run (ScalarVerifier.origin artifact) initial challenge
          (observation program context artifact.instructions artifact.returned env) messages := by
  rw [ScalarVerifier.verify_eq_runK program context artifact position challenge published env encoded,
    run_map]
  exact runK_participant program context artifact env schema returned _ initial challenge messages
    (fun values unread => pure (.returned (ScalarVerifier.acceptance position ⟨values, []⟩), unread))

end Zkc.Executable.DomainVM
