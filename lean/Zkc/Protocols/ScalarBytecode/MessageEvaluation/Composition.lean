import Zkc.Protocols.ScalarBytecode.MessageEvaluation.Receiving
import Zkc.Realization.InstructionComposition

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.MessageEvaluation
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality

def afterPure (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (t : Zkc.Protocols.ScalarBytecode.Execution.Tail) : Terminal Zkc.Protocols.ScalarBytecode.Execution.Tail Zkc.Protocols.ScalarBytecode.Execution.Event :=
 match Zkc.Protocols.ScalarBytecode.Execution.tailStep hash checkInstr (evaluated hash t).state with
 | .next u es => ⟨.incomplete,u,es⟩
 | .halt why u es => ⟨why,u,es⟩

theorem actual_pure_check (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (t : Zkc.Protocols.ScalarBytecode.Execution.Tail) :
 run (Zkc.Protocols.ScalarBytecode.Execution.tailStep hash) ((Zkc.Protocols.ScalarBytecode.Schedules.sumcheck.drop 19).take 9) t = afterPure hash t := by
 have hs : (Zkc.Protocols.ScalarBytecode.Schedules.sumcheck.drop 19).take 9 = pureSlice ++ [checkInstr] := by rfl
 rw [hs,run_append _ (Zkc.Protocols.ScalarBytecode.Execution.no_incomplete_halt hash)]
 change resume (run (Zkc.Protocols.ScalarBytecode.Execution.tailStep hash) [checkInstr]) (evaluated hash t) = _
 have ho := (actual_operands hash t).1
 have he := (actual_operands hash t).2.1
 simp only [resume,ho,↓reduceIte,he,List.nil_append]
 simp only [run,afterPure]
 cases Zkc.Protocols.ScalarBytecode.Execution.tailStep hash checkInstr (evaluated hash t).state <;> simp

theorem continuation_is_actual (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (out : Terminal Zkc.Protocols.ScalarBytecode.Execution.Tail Zkc.Protocols.ScalarBytecode.Execution.Event) :
 continueOriginal hash out = resume
 (run (Zkc.Protocols.ScalarBytecode.Execution.tailStep hash) ((Zkc.Protocols.ScalarBytecode.Schedules.sumcheck.drop 19).take 9)) out := by
 simp only [continueOriginal,resume,actual_pure_check,afterPure]
 split
 · cases Zkc.Protocols.ScalarBytecode.Execution.tailStep hash checkInstr (evaluated hash out.state).state <;> rfl
 · rfl

-- Whole actual rows13..27, all raw bytes and all Core states. Exact terminal equality.
theorem actual_schedule_join (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (t : Zkc.Protocols.ScalarBytecode.Execution.Tail) :
 continueJoin hash (receive hash t) =
 run (Zkc.Protocols.ScalarBytecode.Execution.tailStep hash) ((Zkc.Protocols.ScalarBytecode.Schedules.sumcheck.drop 13).take 15) t := by
 rw [stream_checked_composition,continuation_is_actual]
 change resume (run (Zkc.Protocols.ScalarBytecode.Execution.tailStep hash) ((Zkc.Protocols.ScalarBytecode.Schedules.sumcheck.drop 19).take 9))
   (run (Zkc.Protocols.ScalarBytecode.Execution.tailStep hash) ((Zkc.Protocols.ScalarBytecode.Schedules.sumcheck.drop 13).take 6) t) = _
 rw [← run_append _ (Zkc.Protocols.ScalarBytecode.Execution.no_incomplete_halt hash)]
 rfl

-- The same theorem specifically consumes bytes of the Zkc.Protocols.ScalarBytecode.Messages fixed scalar carrier block.
theorem fixed_family_actual_join (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (core : Zkc.Protocols.ScalarBytecode.Execution.Core) (offset : Nat)
 (b : Block) (tail : Bytes) :
 continueJoin hash (receive hash ⟨Zkc.Protocols.ScalarBytecode.Codec.wire (values b) ++ tail,offset,core⟩) =
 run (Zkc.Protocols.ScalarBytecode.Execution.tailStep hash) ((Zkc.Protocols.ScalarBytecode.Schedules.sumcheck.drop 13).take 15)
   ⟨Zkc.Protocols.ScalarBytecode.Codec.wire (values b) ++ tail,offset,core⟩ := actual_schedule_join hash _

-- The adapter preserves the original pure arithmetic, so this is a full-run
-- replacement law in the selected interpreter, not an optimization theorem.
def execute (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (t : Zkc.Protocols.ScalarBytecode.Execution.Tail) : Terminal Zkc.Protocols.ScalarBytecode.Execution.Tail Zkc.Protocols.ScalarBytecode.Execution.Event :=
  Zkc.Realization.InstructionSequence.resume (run (Zkc.Protocols.ScalarBytecode.Execution.tailStep hash) (Zkc.Protocols.ScalarBytecode.Schedules.sumcheck.drop 28))
    (Zkc.Realization.InstructionSequence.resume (fun s => Zkc.Protocols.ScalarBytecode.MessageEvaluation.continueJoin hash (Zkc.Protocols.ScalarBytecode.MessageEvaluation.receive hash s))
      (run (Zkc.Protocols.ScalarBytecode.Execution.tailStep hash) (Zkc.Protocols.ScalarBytecode.Schedules.sumcheck.take 13) t))

theorem execution_exact (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (t : Zkc.Protocols.ScalarBytecode.Execution.Tail) :
    execute hash t = run (Zkc.Protocols.ScalarBytecode.Execution.tailStep hash) Zkc.Protocols.ScalarBytecode.Schedules.sumcheck t := by
  unfold execute
  simp only [Zkc.Protocols.ScalarBytecode.MessageEvaluation.actual_schedule_join]
  rw [← Zkc.Realization.InstructionSequence.run_append _ (Zkc.Protocols.ScalarBytecode.Execution.no_incomplete_halt hash),
      ← Zkc.Realization.InstructionSequence.run_append _ (Zkc.Protocols.ScalarBytecode.Execution.no_incomplete_halt hash)]
  rfl

end Zkc.Protocols.ScalarBytecode.MessageEvaluation
