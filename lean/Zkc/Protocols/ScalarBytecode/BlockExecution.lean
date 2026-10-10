import Zkc.Protocols.ScalarBytecode.Suppliers.Representations
import Zkc.Compiler.Blocks.StateRefinement
import Zkc.Protocols.ScalarBytecode.Residue

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Zkc.Protocols.ScalarBytecode.BlockExecution
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers Zkc.Compiler.Blocks


-- A terminal packet, with state outside failure. No caller can silently restart
-- a halted packet by invoking the adapter again.
structure Packet (S : Type) where
  world : World S
  stopped : Option Exit

def Related {S T : Type} (R : S → T → Prop) (s : Packet S) (t : Packet T) : Prop :=
  WorldRel R s.world t.world ∧ s.stopped = t.stopped

inductive Action where
  | steps : List Instr → Action
  | publish : Nat → Zkc.Protocols.ScalarBytecode.Residue → Action

-- A steps action runs the *existing* failure-aware Zkc.Protocols.ScalarBytecode.Suppliers interpreter. A successful
-- finite list falls off with incomplete; protocol halts retain their outcome.
def finish {S : Type} (x : Terminal (World S) Event) : Zkc.Protocols.ScalarBytecode.Residue × Packet S × List Event :=
  (if x.outcome = .incomplete then 1 else 0,
   ⟨x.state, if x.outcome = .incomplete then none else some x.outcome⟩, x.events)

def handler {S : Type} (hash : Hash) (supplier : Supplier S) :
    Action → Packet S → Zkc.Protocols.ScalarBytecode.Residue × Packet S × List Event := fun a s =>
  match s.stopped with
  | some _ => (0,s,[])
  | none => match a with
    | .steps ops => finish (run (openStep hash supplier) ops s.world)
    | .publish dst v =>
      (v,⟨⟨{s.world.verifier with core := put s.world.verifier.core dst v.val},
           s.world.external⟩,none⟩,[])

theorem finish_related {S T : Type} (R : S → T → Prop)
    (s : Terminal (World S) Event) (t : Terminal (World T) Event)
    (h : TerminalRel (WorldRel R) s t) :
    (finish s).1 = (finish t).1 ∧ (finish s).2.2 = (finish t).2.2 ∧
    Related R (finish s).2.1 (finish t).2.1 := by
  rcases h with ⟨out, states, events⟩
  exact ⟨by simp [finish,out], events, states, by simp [finish,out]⟩

theorem handlers_related {S T : Type} (hash : Hash)
    (left : Supplier S) (right : Supplier T) (R : S → T → Prop)
    (suppliers : SupplierRel left right R) :
    Zkc.Compiler.Blocks.StateRefinement.HandlerRel (Related R) (handler hash left) (handler hash right) := by
  intro a s t h
  rcases h with ⟨worlds, stops⟩
  cases hs : s.stopped with
  | some why => simp only [handler,hs,← stops]; exact ⟨trivial,trivial,worlds,stops⟩
  | none =>
    cases a with
    | steps ops =>
      simp only [handler,hs,← stops]
      exact finish_related R _ _ (supplier_run suppliers hash ops s.world t.world worlds)
    | publish dst v =>
      simp only [handler,hs,← stops]
      exact ⟨trivial,trivial,⟨by simp only [WorldRel] at worlds; simp [worlds.1],worlds.2⟩,rfl⟩

theorem stopped_inert {S : Type} (hash : Hash) (supplier : Supplier S)
    (a : Action) (s : Packet S) (why : Exit) (h : s.stopped = some why) :
    handler hash supplier a s = (0,s,[]) := by simp [handler,h]

-- The branch prevents invocation of the supplied continuation on failure.
def guarded (ops : List Instr) (next : Program Zkc.Protocols.ScalarBytecode.Residue Action Unit) : Program Zkc.Protocols.ScalarBytecode.Residue Action Unit :=
  .action (.steps ops) (fun ok => if ok = 1 then next else .done ())

theorem failed_guard {S : Type} (hash : Hash) (supplier : Supplier S)
    (ops : List Instr) (next : Program Zkc.Protocols.ScalarBytecode.Residue Action Unit) (s : Packet S)
    (h : (handler hash supplier (.steps ops) s).1 = 0) :
    runProgram Zkc.Compiler.Blocks.arithmetic (handler hash supplier) (guarded ops next) s =
      ((handler hash supplier (.steps ops) s).2.2,
       (), (handler hash supplier (.steps ops) s).2.1) := by
  have h01 : (0 : Zkc.Protocols.ScalarBytecode.Residue) ≠ 1 := by decide
  simp [guarded,runProgram,h,h01]

abbrev Result (S : Type) := List Event × Unit × Packet S

def asTerminal {S : Type} (r : Result S) : Terminal (World S) Event :=
  ⟨r.2.2.stopped.getD .incomplete,r.2.2.world,r.1⟩

theorem guarded_done {S : Type} (hash : Hash) (supplier : Supplier S)
    (post : List Instr) (g : World S) :
    runProgram arithmetic (handler hash supplier) (guarded post (.done ())) ⟨g,none⟩ =
    let t := run (openStep hash supplier) post g
    (t.events,(),⟨t.state,if t.outcome = .incomplete then none else some t.outcome⟩) := by
  simp only [guarded,runProgram,Zkc.Protocols.ScalarBytecode.BlockExecution.handler,finish]
  split <;> simp [runProgram]

theorem related_eq_world {S : Type} (a b : World S) (h : WorldRel Eq a b) : a = b := by
  rcases a with ⟨v,s⟩; rcases b with ⟨w,t⟩
  rcases h with ⟨hv,hs⟩
  cases hv; cases hs; rfl

theorem related_eq_result {S : Type} (a b : Result S)
    (h : Zkc.Compiler.Blocks.StateRefinement.RunRel (Related Eq) a b) : a = b := by
  rcases a with ⟨es,o,s⟩; rcases b with ⟨fs,p,t⟩
  rcases h with ⟨he,ho,hw,hstop⟩
  have heq := related_eq_world s.world t.world hw
  cases s; cases t
  cases he; cases ho; cases heq; cases hstop; rfl

end Zkc.Protocols.ScalarBytecode.BlockExecution
