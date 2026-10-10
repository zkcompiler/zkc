import Zkc.Realization.InstructionSequence
import PolyFun.PFunctor.Free.Basic

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.PolyFun.Failure
open PFunctor

-- A genuinely dependent operation signature can make abort have no resumption.
-- State placement remains an interpreter decision; the signature alone cannot
-- recover state that an implementation discards.
def stopSignature : PFunctor where
  A := Zkc.Realization.InstructionSequence.Exit
  B := fun _ => PEmpty

def abort (why : Zkc.Realization.InstructionSequence.Exit) : FreeM stopSignature Unit := .liftBind why PEmpty.elim
def keepFailure (why : Zkc.Realization.InstructionSequence.Exit) : StateM Nat (Except Zkc.Realization.InstructionSequence.Exit PEmpty) :=
  fun s => (.error why,s)

theorem abort_retains (why : Zkc.Realization.InstructionSequence.Exit) (s : Nat) :
    ((abort why).liftM (m := ExceptT Zkc.Realization.InstructionSequence.Exit (StateM Nat)) keepFailure).run s =
      (.error why,s) := rfl

end ZkcArkLib.PolyFun.Failure
