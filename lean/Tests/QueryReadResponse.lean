module

public import Zkc.Realization.QueryReadResponse

@[expose] public section
set_option autoImplicit false
namespace Tests.QueryReadResponse
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization

def readPlacement : TableRead.Placement := ⟨17, 15, 16, 2, "read"⟩
def responsePlacement : QueryResumption.Placement :=
  ⟨19, 6, 5, ⟨0, 1, 2, 3, 4⟩, ⟨0, 1, 2, 3, 4⟩, 8, 18,
    "phase", "kind", !["constructor", "instance", "position", "continuation", "frame"]⟩
def body := QueryReadResponse.instructions "F" 0 readPlacement responsePlacement

theorem checked_compound : (QueryReadResponse.recognize body).isSome = true := by decide +kernel

/-- A successful read of a different position cannot supply the pending query,
even when the result and both position references have exactly the right types. -/
theorem unrelated_position_refused :
    (QueryReadResponse.recognize (QueryReadResponse.instructions "F" 0
      { readPlacement with position := 7 } responsePlacement)).isNone = true := by decide +kernel

theorem stale_answer_refused :
    (QueryReadResponse.recognize (QueryReadResponse.instructions "F" 0 readPlacement
      { responsePlacement with answer := 14 })).isNone = true := by decide +kernel

/-- Failed table access wins over later arena exhaustion. The closed-computation
composition rule keeps the first actual stop without asking for a continuation. -/
theorem read_refusal_first (model : DomainModel) (rows position : Nat)
    (outside : ¬ (position < indexLimit ∧ rows < indexLimit ∧ position < rows))
    (cells : List (model.Field "F"))
    (next : model.Field "F" → PIR.Process (Domain.effects model.toCarriers) Nat) :
    ((TableRead.read model "F" cells rows position).interpret
      (closedLift (I := Domain.effects model.toCarriers))).bind next = .halt .refused := by
  rw [TableRead.read_eq]
  simp only [outside, ↓reduceIte, PIR.Process.interpret, PIR.Process.bind]

#print axioms checked_compound
#print axioms read_refusal_first
end Tests.QueryReadResponse
