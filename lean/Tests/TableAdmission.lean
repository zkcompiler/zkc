import Examples.TableProtocol.Admission
import Tools.DeclarationAudit

set_option autoImplicit false

namespace Tests.TableAdmission
open Zkc.Source Zkc.Compiler PhaseAdmission TableProtocol TableProtocol.Admission

abbrev context : List Ty := [.scalar .seven, .scalar .seven]

def round : Region Protocol.language context (.scalar .seven) :=
  .bind (.letOp .send (.cons .here (.cons (.there .here) .nil)) (.ret .here))
    (.letOp .draw .nil (.ret .here))

def certificate : Certificate Phase := .bind (.next .terminal) (.next .terminal)

def request : RegionArtifact.Request Ty Protocol.Operation :=
  ⟨⟨"trace", [⟨"a", .scalar .seven, .shared, .argument⟩,
    ⟨"b", .scalar .seven, .shared, .capture⟩], .scalar .seven, dependencies⟩, [], round.erase⟩

def candidate : RegionArtifact.Candidate Ty Protocol.Operation :=
  ⟨⟨formatVersion, RegionArtifact.semanticsVersion, [], "direct-logical-plan", "direct-lowering",
    completeExecution, request.context, []⟩, round.erase⟩

def checked : RegionArtifact.Checked (language := Protocol.language) request candidate :=
  (RegionArtifact.check (language := Protocol.language) request candidate).toOption.get (by decide)

theorem artifact_calls {S E : Type} (provider : PIR.Handler Protocol.protocolInterface S E)
    (env : Environment Value context) (state : S) :
    ∀ before op, Sum.inl (before, op) ∈
      ((checked.region.denote Protocol.meaning env).run
        (PIR.ExecutionPath.handler interaction provider) (.ready, state)).events →
      interaction.enabled before op :=
  checked.calls_permitted policy certificate [.ready] [.ready]
    (by decide) Protocol.meaning interaction summaryLaws env .ready ⟨.ready, by simp, rfl⟩
    provider state checked.region checked.candidateDecoded

theorem artifact_return {S E : Type} (provider : PIR.Handler Protocol.protocolInterface S E)
    (env : Environment Value context) (state : S) (value : Field .seven)
    (returned : ((checked.region.denote Protocol.meaning env).run
      (PIR.ExecutionPath.handler interaction provider) (.ready, state)).outcome = .returned value) :
    Covered summaryLaws [.ready]
      ((checked.region.denote Protocol.meaning env).run
        (PIR.ExecutionPath.handler interaction provider) (.ready, state)).state.1 :=
  checked.return_permitted policy certificate [.ready] [.ready] [.ready]
    (by decide) (fun _ h => h) Protocol.meaning interaction summaryLaws env .ready
    ⟨.ready, by simp, rfl⟩ provider state checked.region checked.candidateDecoded value returned

example : checkRegion policy round certificate [.ready] = some [.ready] := by decide

example : checkRegion policy
    (Region.letOp (language := Protocol.language) (Γ := context) .draw .nil (.ret .here))
    (.next .terminal) [.ready] = none := by decide

example : checkRegion policy round (.bind .terminal (.next .terminal)) [.ready] = none := by decide

example (a b : Field .seven) : interaction.advance .ready (.send a b) false = .sent := rfl

example : (certificateCodec.decode (certificateCodec.encode certificate)) = .ok certificate := rfl

end Tests.TableAdmission

-- A module is not in its own environment while it elaborates, so it cannot
-- audit itself; Tests/Audit.lean covers the Tests family from a module that
-- imports them all.
run_cmd Tools.DeclarationAudit.check [`Examples.TableProtocol.Admission] "TABLE-ADMISSION-AUDIT-PASS"
