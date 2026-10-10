import Examples.TableProtocol.Endpoint
import Tools.DeclarationAudit

set_option autoImplicit false
namespace Tests.EndpointAdmission
open Zkc.Source Zkc.Compiler PhaseAdmission TableProtocol TableProtocol.Admission

/-- A different source is admitted from a retained sent endpoint, rather than
replaying a round's ready-state evidence. -/
def draw : Region Protocol.language [] (.scalar .seven) := .letOp .draw .nil (.ret .here)
def certificate : Certificate Phase := .next .terminal
def request : RegionArtifact.Request Ty Protocol.Operation :=
  ⟨⟨Endpoint.role, [], .scalar .seven, dependencies⟩, [], draw.erase⟩
def candidate : RegionArtifact.Candidate Ty Protocol.Operation :=
  ⟨⟨formatVersion, RegionArtifact.semanticsVersion, [], "direct-logical-plan", "direct-lowering",
    completeExecution, request.context, []⟩, draw.erase⟩
def checked : RegionArtifact.Checked (language := Protocol.language) request candidate :=
  (RegionArtifact.check (language := Protocol.language) request candidate).toOption.get (by decide)

/-- Successful checking of the actual entry supplies the phase premise needed
by the existing theorem for the decoded candidate. -/
theorem artifact_calls (state : Endpoint.State)
    (entry : Endpoint.validateEntry ⟨Endpoint.role, .sent⟩ state = .ok ())
    (env : Environment Value []) :
    ∀ before op, Sum.inl (before, op) ∈
      ((checked.region.denote Protocol.meaning env).run
        (PIR.ExecutionPath.handler interaction Protocol.handler) (state.entry.phase, state.data)).events →
      interaction.enabled before op :=
  checked.calls_permitted policy certificate [.sent] [.ready]
    (by decide) Protocol.meaning interaction summaryLaws env state.entry.phase
    (Endpoint.entry_coverage _ state (Endpoint.validated_entry _ state entry).2)
    Protocol.handler state.data checked.region checked.candidateDecoded

/-- A normally returning endpoint reaches ready. A stopped call has no such
postcondition; its actual state is retained by the endpoint interpreter. -/
theorem artifact_return (state : Endpoint.State)
    (entry : Endpoint.validateEntry ⟨Endpoint.role, .sent⟩ state = .ok ())
    (env : Environment Value []) (value : Field .seven)
    (returned : (Endpoint.run (checked.region.denote Protocol.meaning env) state).outcome = .returned value) :
    Covered summaryLaws [.ready]
      (Endpoint.run (checked.region.denote Protocol.meaning env) state).state.entry.phase :=
  checked.return_permitted policy certificate [.sent] [.ready] [.ready]
    (by decide) (fun _ h => h) Protocol.meaning interaction summaryLaws env state.entry.phase
    (Endpoint.entry_coverage _ state (Endpoint.validated_entry _ state entry).2)
    Protocol.handler state.data checked.region checked.candidateDecoded value returned

example : checkRegion policy draw certificate [.ready] = none := by decide
example : checkRegion policy draw certificate [.sent] = some [.ready] := by decide
example (state : Endpoint.State) :
    (Endpoint.run (.call .draw .done) {state with data.tape := []}).outcome = .stopped .exhausted := rfl

end Tests.EndpointAdmission
-- A module is not in its own environment while it elaborates, so it cannot
-- audit itself; Tests/Audit.lean covers the Tests family from a module that
-- imports them all.
run_cmd Tools.DeclarationAudit.check [`Examples.TableProtocol.Endpoint] "ENDPOINT-ADMISSION-AUDIT-PASS"
