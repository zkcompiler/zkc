import Zkc.Protocols.ScalarBytecode.Frames
import Zkc.Protocols.ScalarBytecode.MessageEvaluation.Composition
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Horner
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Schedules Zkc.Protocols.ScalarBytecode.Frames

-- Minimal hidden set for this chosen scratch allocation, retaining all other registers.
def Live (n : Nat) : Prop := n ≠ 44 ∧ n ≠ 46 ∧ n ≠ 48
instance (n : Nat) : Decidable (Live n) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def oldPure : List Instr := (sumcheck.drop 22).take 5
def newPure : List Instr := [
 ⟨22,.mul,.reg 13,.reg 25,0,[],"",44⟩,
 ⟨24,.add,.reg 9,.reg 44,0,[],"",48⟩,
 ⟨25,.mul,.reg 48,.reg 25,0,[],"",50⟩,
 ⟨26,.add,.reg 5,.reg 50,0,[],"",52⟩]
def suffix := sumcheck.drop 27

theorem suffix_safe : ∀ i ∈ suffix, Safe Live i := by
 simp [suffix,sumcheck,Safe,Reads,Live]

theorem horner (a b c x q : Nat) :
 (a + ((b*x)%q + (c*((x*x)%q))%q)%q)%q =
 (a + (((b+(c*x)%q)%q)*x)%q)%q := by
 simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.mod_mul_mod,
   Nat.mul_mod_mod]
 congr 1
 ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem pure_replacement (hash : Hash) (t : Tail) :
 TerminalRel (Rel Live) (run (tailStep hash) oldPure t) (run (tailStep hash) newPure t) := by
 simp [TerminalRel,Rel,CoreRel,oldPure,newPure,sumcheck,run,tailStep,tailHandler,
 effect,request,Zkc.Protocols.ScalarBytecode.Execution.get,put]

 intro n hn
 rcases hn with ⟨h44,h46,h48⟩
 simp only [h44,h46,h48,↓reduceIte]
 by_cases h52 : n = 52
 · subst n
   simp only [↓reduceIte]
   congr 1
   ring
 · by_cases h50 : n = 50
   · subst n
     simp only [h52,↓reduceIte]
     congr 1
     ring
   · simp [h52,h50]
def optimized := sumcheck.take 22 ++ (newPure ++ suffix)

theorem full_qualified (hash : Hash) (t : Tail) :
 TerminalRel (Rel Live) (run (tailStep hash) sumcheck t)
   (run (tailStep hash) optimized t) := by
 have h := block_context Live hash oldPure newPure (sumcheck.take 22) suffix
   (pure_replacement hash) suffix_safe t
 exact h

theorem message_evaluation_refinement (hash : Hash) (t : Tail) :
 TerminalRel (Rel Live) (Zkc.Protocols.ScalarBytecode.MessageEvaluation.execute hash t)
   (run (tailStep hash) optimized t) := by
 rw [Zkc.Protocols.ScalarBytecode.MessageEvaluation.execution_exact]
 exact full_qualified hash t

-- Immutable original bytes are part of the observer, in addition to exact suffix.
def observe (full : Bytes) (out : Terminal Tail Event) :=
 (full,out.outcome,out.state.rest,out.state.offset,out.state.core.provider,
  out.state.core.binding,(fun n => if Live n then out.state.core.regs n else 0),out.events)

theorem observe_eq (full : Bytes) (a b : Terminal Tail Event)
 (h : TerminalRel (Rel Live) a b) : observe full a = observe full b := by
 have hm : (fun n => if Live n then a.state.core.regs n else 0) =
    (fun n => if Live n then b.state.core.regs n else 0) := by
   funext n
   split
   · exact h.2.1.2.2.2.2 n ‹Live n›
   · rfl
 simp only [observe,h.1,h.2.1.1,h.2.1.2.1,h.2.1.2.2.1,h.2.1.2.2.2.1,hm,h.2.2]

theorem full_observation (hash : Hash) (t : Tail) (full : Bytes) :
 observe full (Zkc.Protocols.ScalarBytecode.MessageEvaluation.execute hash t) =
 observe full (run (tailStep hash) optimized t) :=
 observe_eq full _ _ (message_evaluation_refinement hash t)

-- Same qualified boundary remains usable by further safe effectful continuations.
theorem future_safe (hash : Hash) (t : Tail) (ops : List Instr)
 (safe : ∀ i ∈ ops, Safe Live i) :
 TerminalRel (Rel Live)
   (Zkc.Realization.InstructionSequence.resume (run (tailStep hash) ops) (run (tailStep hash) oldPure t))
   (Zkc.Realization.InstructionSequence.resume (run (tailStep hash) ops) (run (tailStep hash) newPure t)) :=
 resume_frame Live hash ops safe _ _ (pure_replacement hash t)

end Zkc.Protocols.ScalarBytecode.Horner
