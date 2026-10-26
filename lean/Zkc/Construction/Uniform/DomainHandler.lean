module

public import Zkc.Construction.Uniform.DomainExecution

@[expose] public section
/-! The scalar proof property is a projection of the installed Domain handler.
The adapter maps a query before invoking the existing challenge function. -/
set_option autoImplicit false
namespace Zkc.Construction.Uniform.DomainAdapter
open Zkc.Source
variable {F G : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

def embedProof (proof : Proof F G) : Domain.Proof (Structured.uniformCarriers F G) :=
  proof.map embedPayload

theorem payload_decode (ty : Structured.Ty) (payload : Payload F G) :
    (embedPayload payload).value ty = Value.decode ty (.data payload) := by
  exact decode_embed ty (value := .data payload) (encoded := .data (embedPayload payload))
    (by cases payload <;> rfl)

theorem run_actual {A : Type} (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (frame : Domain.Environment (Structured.uniformCarriers F G)) (proof : Proof F G) :
    (fun result => (result.outcome, result.state.proof)) <$>
        Domain.run .validator (oracle key initial challenge) process ⟨frame, embedProof proof, ()⟩ =
      (fun result => (result.1, embedProof result.2)) <$> run key initial challenge process proof := by
  rw [Domain.validator_eq_direct]
  simp only [run]
  induction process generalizing frame proof with
  | done => simp [Domain.validateDirect, runK]
  | halt => simp [Domain.validateDirect, runK]
  | call operation next ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => simp [Domain.validateDirect, runK, embedProof]
          | cons payload unread =>
              simp only [embedProof, List.map_cons, Domain.validateDirect, runK, payload_decode]
              cases Value.decode ty (.data payload)
              · simp
              · exact ih _ frame unread
      | send => simp only [Domain.validateDirect, runK]; exact ih () frame proof
      | checkpoint env => simp only [Domain.validateDirect, runK]; exact ih () env proof
      | observe event =>
          simp only [Domain.validateDirect, runK]
          simp [← ih () frame proof, Functor.map_map]
      | localService => simp [Domain.validateDirect, runK]
      | query history origin =>
          simp only [Domain.validateDirect, runK]
          split
          · simp [oracle, PIR.Execution.followM]
            congr 1
            funext answer
            cases answer <;> simp [Functor.map_map, ih]
          · simp

end Zkc.Construction.Uniform.DomainAdapter
