module

public import Zkc.Construction.DomainTranscript

@[expose] public section

/-! Nominal table-round histories, independent of source views and compiler plans. -/
set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.TableComponent.Execution
open Zkc.Source Zkc.Source.Structured Zkc.Construction

variable {F G : Type}

def receivedHistory (field : String) (lowOrigin highOrigin : Origin)
    (history : Domain.History (uniformCarriers F G)) (low high : F) :=
  (history ++ [.message lowOrigin (.field field low)]) ++ [.message highOrigin (.field field high)]

def finalHistory (field : String) (lowOrigin highOrigin queryOrigin deliveryOrigin : Origin)
    (history : Domain.History (uniformCarriers F G)) (low high challenge : F) :=
  (receivedHistory field lowOrigin highOrigin history low high ++ [.challenge queryOrigin]) ++
    [.message deliveryOrigin (.field field challenge)]

end ZkcSecurity.Families.Sumcheck.TableComponent.Execution
