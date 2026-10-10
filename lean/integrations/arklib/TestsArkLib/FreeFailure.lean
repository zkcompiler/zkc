import ZkcArkLib.PolyFun.Failure

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace TestsArkLib.FreeFailure
def loseFailure (x : Except Zkc.Realization.InstructionSequence.Exit Unit × Nat) : Except Zkc.Realization.InstructionSequence.Exit (Unit × Nat) :=
  x.1.map (fun v => (v,x.2))

theorem lost_state_not_recoverable :
    ¬ ∃ recover : Except Zkc.Realization.InstructionSequence.Exit (Unit × Nat) → Nat,
      ∀ s, recover (loseFailure (.error (.reject "bad"),s)) = s := by
  rintro ⟨recover,h⟩
  have a := h 0
  have b := h 1
  simp only [loseFailure,Except.map] at a b
  omega

end TestsArkLib.FreeFailure
