import Zkc.Protocols.Sumcheck.LocalProver.Code
import Zkc.Semantics.MonadExecution
import Zkc.Semantics.Boundary

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Protocols.Sumcheck.LocalProver.Source
open PIR

def sig : Signature := ⟨Nat, fun n => Fin (n+1)⟩

/-- Local state lives in the source continuation and complete returned Cut.
    These local histories are not automatically public network emissions. -/
def source {F : Type} [Ring F] [DecidableEq F] : Code → State F → Proc sig (Cut F)
  | .abort, st => .done (.stopped st)
  | .assign i e p, st => source p (write st i (eval st e))
  | .random n i p, st => .call n (fun x => source p (coin st n i x))
  | .ifz e p q, st => if eval st e = 0 then source p (branch st true)
      else source q (branch st false)
  | .commit s a b c, st => .done (.committed (boundary st s a b c))

/-- A public syntactic upper bound, independent of input values, register
    contents and every local coin reply. Local assignments are not calls. -/
def calls : Code → Nat
  | .abort | .commit _ _ _ _ => 0
  | .assign _ _ p => calls p
  | .random _ _ p => calls p + 1
  | .ifz _ p q => max (calls p) (calls q)

/-- This fragment's effects are role-local coins. Network interaction is a
    separate wrapper after the committed cut, not permission to read ahead. -/
def localInteraction : Interaction sig where
  Role := Unit
  Phase := Unit
  owner := fun _ => ()
  enabled := fun _ _ => True
  advance := fun _ _ _ => ()

variable {F : Type} [Ring F] [DecidableEq F]

theorem source_conforms (p : Code) (st : State F) :
    Conforms localInteraction (source p st) () := by
  induction p generalizing st with
  | abort | commit => trivial
  | assign i e p ih => exact ih _
  | random n i p ih => exact ⟨trivial, fun _ => ih _⟩
  | ifz e p q ihp ihq =>
    by_cases h : eval st e = 0 <;> simp only [source, h, reduceIte]
    · exact ihp _
    · exact ihq _

theorem source_bound (p : Code) (st : State F) :
    Within (calls p) (source p st) := by
  induction p generalizing st with
  | abort | commit => trivial
  | assign i e p ih => exact ih _
  | random n i p ih => exact fun _ => ih _
  | ifz e p q ihp ihq =>
    by_cases h : eval st e = 0 <;> simp only [source, h, reduceIte, calls]
    · exact Boundary.within_mono _ _ _ (Nat.le_max_left _ _) (ihp _)
    · exact Boundary.within_mono _ _ _ (Nat.le_max_right _ _) (ihq _)

/-- Both local abort and commit retain the captured input vector. This says
    nothing about the public visibility of the returned local history. -/
theorem source_returns_inputs (p : Code) (st : State F) :
    Boundary.Returns localInteraction (fun out phase =>
      Cut.inputs out = st.inputs ∧ phase = ()) (source p st) () := by
  induction p generalizing st with
  | abort | commit => exact ⟨rfl, rfl⟩
  | assign i e p ih => simpa only [source, write] using ih (write st i (eval st e))
  | random n i p ih =>
    intro x
    simpa only [coin, write, localInteraction] using ih (coin st n i x)
  | ifz e p q ihp ihq =>
    by_cases h : eval st e = 0 <;> simp only [source, h, reduceIte]
    · simpa only [branch] using ihp (branch st true)
    · simpa only [branch] using ihq (branch st false)


end Zkc.Protocols.Sumcheck.LocalProver.Source
