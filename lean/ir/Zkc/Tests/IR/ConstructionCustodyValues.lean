module

public import Zkc.IR.Construction.DomainExecutionLaws
public import Zkc.IR.Construction.DomainView

@[expose] public section

/-! Custody has nominal local frame transport, never a wire payload. These
kernel checks do not assert operational ledger soundness or source connection. -/
namespace Tests.ConstructionCustodyValues
open Zkc.Source Zkc.Source.Structured Zkc.Construction
variable {carriers : Carriers}

theorem local_only (slot : String) :
    Domain.localType (.resourceUnit slot) = true ∧
      Domain.dataType (.resourceUnit slot) = false := by constructor <;> rfl

theorem local_roundtrip (slot : String) (token : CustodyToken) :
    (Domain.Value.encode (.resourceUnit slot) token : Option (Domain.Value carriers)) =
      some (.custody slot token) ∧
    Domain.Value.decode (.resourceUnit slot) (.custody slot token : Domain.Value carriers) =
      some token := by
  exact ⟨rfl, by simp [Domain.Value.decode]⟩

theorem wrong_slot (expected actual : String) (different : expected ≠ actual)
    (token : CustodyToken) :
    Domain.Value.decode (.resourceUnit expected) (.custody actual token : Domain.Value carriers) =
      none := by simp [Domain.Value.decode, different]

theorem exact_sort (slot : String) (token : CustodyToken) :
    (Domain.Value.custody (carriers := carriers) slot token).sort = .data (.resourceUnit slot) := rfl

theorem no_payload (slot : String) (token : CustodyToken) :
    Domain.Payload.ofValue (carriers := carriers) (.resourceUnit slot) token = none := rfl

theorem no_custody_sequence (slot : String) :
    Domain.localType (.sequence (.resourceUnit slot)) = false := rfl

theorem no_service (contract : String) : Domain.localType (.service contract) = false := rfl

theorem no_wire_receive (slot site peer : String) (environment : Domain.Environment carriers) :
    Domain.View.receive site site peer (.resourceUnit slot) [.data (.resourceUnit slot)] environment =
      .halt .refused := by simp [Domain.View.receive, Domain.dataType, Ty.isHandle]

theorem no_wire_send (slot site peer : String) (token : CustodyToken) :
    Domain.View.send (carriers := carriers) site site peer 0 [] [.custody slot token] =
      .halt .refused := rfl

theorem no_transcript_observation (context : Context) (template : Template)
    (slot : String) (token : CustodyToken) (history : Domain.History carriers) :
    Domain.View.observe context context.suite template 0 1 2 [.transcript context.suite]
      [.transcript context.suite history, .custody slot token, .indices []] =
      .halt .refused := rfl

#print axioms local_roundtrip
#print axioms wrong_slot
#print axioms no_wire_receive
#print axioms no_transcript_observation
end Tests.ConstructionCustodyValues
