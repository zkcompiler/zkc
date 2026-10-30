module

public import ZkcSecurity.Bindings.Participants.Evidence

@[expose] public section

/-! The claims adapters accept only proved Evidence hypotheses. The legacy
Evidence field is retained for the strict manifest endpoint ledger; its notes
are not assumptions of a request-fixed receipt. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open ZkcSecurity.Endpoint

/-- Every hypothesis is carried by `.proved`, including its proof of the actual
proposition. `.assumed` is a note and cannot satisfy this admission boundary. -/
def HypothesesProved : List Hypothesis → Prop
  | [] => True
  | hypothesis :: rest => hypothesis.status.Discharged ∧ HypothesesProved rest

end ZkcSecurity.Claims
