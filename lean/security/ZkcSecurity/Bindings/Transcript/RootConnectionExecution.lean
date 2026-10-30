module

public import Zkc.Construction.ConnectionRootCertificate
public import ZkcSecurity.Bindings.Transcript.OriginalReadback

@[expose] public section

/-! Property-specific root consumers beyond public endpoint reading. The
existing Simulation handler projection retains all runtime state, private
service replies and observations. Successful deterministic honest-pair readback
is transported separately; it remains a mathematical property of the source
pair, not a consequence of having a source/artifact connection.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.RootConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot

attribute [local implicit_reducible] CheckedProtocol.signature

variable {program : Program} {routing : Original.Routing} {role : Nat} {artifact : Participant}

/-- The existing certificate-instrumented source retains both entire returns
and each certified physical checkpoint, for any profile or local routing. -/
noncomputable def instrumented (root : RootCertificate program routing role artifact)
    (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  (root.simulation model physical).paired

theorem instrumented_returns (root : RootCertificate program routing role artifact)
    (model : DomainModel) (physical : Domain.Environment model.toCarriers) :
    PIR.Yields (fun pair => Original.CompleteReturns program.payload.entry.signature
      routing.context role artifact pair.1 pair.2) (instrumented root model physical) :=
  (root.simulation model physical).paired_yields

/-- Any lawful installed handler retains its entire state and event list.
Unlike public reading, this projection supports plain delivery, both runtime
roles, local services and their failed/stopped replies. It does not assert an
honest input law, successful execution or a sampling distribution. -/
theorem runtime (root : RootCertificate program routing role artifact)
    (model : DomainModel) (physical : Domain.Environment model.toCarriers)
    {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (mode : Domain.Mode) (oracle : Domain.Oracle m model.toCarriers S)
    (services : Domain.LocalServices m model.toCarriers S)
    (state : Domain.RuntimeState model.toCarriers S) :
    Domain.run mode oracle (Domain.participant model program routing.context artifact physical) state services =
      (do let execution ← Domain.run mode oracle (instrumented root model physical) state services
          pure (Original.mapExecution Prod.snd execution)) :=
  (root.simulation model physical).runM (Domain.handler mode oracle services) state

/-- Deterministic honest-pair readback reuses its own existing interpretation.
Each actual artifact return remains related to the complete source return.
No public-profile or no-local-route restriction is imposed by this assembler;
Readback itself determines which successful pairs it can describe. -/
theorem honestReadback {routingP routingV : Original.Routing} {roleP roleV : Nat}
    {artifactP artifactV : Participant}
    (producer : RootCertificate program routingP roleP artifactP)
    (validator : RootCertificate program routingV roleV artifactV)
    (model : DomainModel) (inputsP inputsV : Domain.Environment model.toCarriers)
    (Post : (Values (Component model.Value) program.payload.entry.outputs × Original.State model.toCarriers) →
      (Values (Component model.Value) program.payload.entry.outputs × Original.State model.toCarriers) → Prop)
    (sourceReadback : Readback Post (producer.source model inputsP) (validator.source model inputsV)) :
    Readback (fun actualP actualV => ∃ sourceP sourceV, Post sourceP sourceV ∧
      Original.CompleteReturns program.payload.entry.signature routingP.context roleP artifactP sourceP actualP ∧
      Original.CompleteReturns program.payload.entry.signature routingV.context roleV artifactV sourceV actualV)
      (Domain.participant model program routingP.context artifactP inputsP)
      (Domain.participant model program routingV.context artifactV inputsV) :=
  Readback.original (producer.simulation model inputsP) (validator.simulation model inputsV) sourceReadback

end ZkcSecurity.FiatShamir.RootConnection
