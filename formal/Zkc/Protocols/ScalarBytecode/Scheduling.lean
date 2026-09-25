import Zkc.Protocols.ScalarBytecode.Endpoint.Frames

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Zkc.Protocols.ScalarBytecode.Scheduling
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers

def allRegs : Nat → Prop := fun _ => True
def mulI (site x y dest : Nat) : Instr :=
  ⟨site,.mul,.reg x,.reg y,0,[],"",dest⟩
def addI (site x y dest : Nat) : Instr :=
  ⟨site,.add,.reg x,.reg y,0,[],"",dest⟩
def drawI (site dest : Nat) (domain : Bytes) : Instr :=
  ⟨site,.draw,.binding,.binding,0,domain,"",dest⟩

def canCrossDraw (x y dest challenge : Nat) : Bool :=
  decide (x ≠ challenge ∧ y ≠ challenge ∧ dest ≠ challenge)

/- Operand stability and disjoint writes suffice for this total scalar opcode.
    They do not characterize arbitrary operations called pure by a frontend. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem mul_draw {S : Type} (supplier : Supplier S) (hash : Hash)
    (m k x y d c : Nat) (domain : Bytes)
    (hx : x ≠ c) (hy : y ≠ c) (hd : d ≠ c) (s : World S) :
    TerminalRel (OpenRel allRegs Eq)
      (run (openStep hash supplier) [drawI k c domain, mulI m x y d] s)
      (run (openStep hash supplier) [mulI m x y d, drawI k c domain] s) := by
  simp [TerminalRel,OpenRel,LocalRel,Zkc.Protocols.ScalarBytecode.Frames.CoreRel,allRegs,drawI,mulI,run,
    openStep,serve,notify,update,mapStep,eventsOf,effect,request,Zkc.Protocols.ScalarBytecode.Execution.get,put,hx,hy]
  intro n
  by_cases hnc : n = c
  · subst n; simp [Ne.symm hd]
  · simp [hnc]

theorem checked_mul_draw {S : Type} (supplier : Supplier S) (hash : Hash)
    (m k x y d c : Nat) (domain : Bytes)
    (checked : canCrossDraw x y d c = true) (s : World S) :
    TerminalRel (OpenRel allRegs Eq)
      (run (openStep hash supplier) [drawI k c domain, mulI m x y d] s)
      (run (openStep hash supplier) [mulI m x y d, drawI k c domain] s) := by
  have h : x ≠ c ∧ y ≠ c ∧ d ≠ c := by simpa [canCrossDraw] using checked
  exact mul_draw supplier hash m k x y d c domain h.1 h.2.1 h.2.2 s

/-- Selective intrinsic packaging of the SAME certificate, not a new logic. -/
structure DrawStableMul (challenge : Nat) where
  site : Nat
  x : Nat
  y : Nat
  dest : Nat
  checked : canCrossDraw x y dest challenge = true

theorem indexed_mul_draw {S : Type} (supplier : Supplier S) (hash : Hash)
    (k c : Nat) (domain : Bytes) (m : DrawStableMul c) (s : World S) :
    TerminalRel (OpenRel allRegs Eq)
      (run (openStep hash supplier) [drawI k c domain, mulI m.site m.x m.y m.dest] s)
      (run (openStep hash supplier) [mulI m.site m.x m.y m.dest, drawI k c domain] s) :=
  checked_mul_draw supplier hash _ _ _ _ _ _ _ m.checked s

theorem all_safe (i : Instr) : Zkc.Protocols.ScalarBytecode.Frames.Safe allRegs i := by
  constructor
  · cases i.x <;> trivial
  · cases i.y <;> trivial

def arithI (isAdd : Bool) (site x y dest : Nat) : Instr :=
  if isAdd then addI site x y dest else mulI site x y dest

def canCrossArith (x y d a b e : Nat) : Bool :=
  decide (x ≠ e ∧ y ≠ e ∧ a ≠ d ∧ b ≠ d ∧ d ≠ e)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem checked_mul_arith {S : Type} (supplier : Supplier S) (hash : Hash)
    (isAdd : Bool) (m k x y d a b e : Nat)
    (checked : canCrossArith x y d a b e = true) (s : World S) :
    TerminalRel (OpenRel allRegs Eq)
      (run (openStep hash supplier) [arithI isAdd k a b e,mulI m x y d] s)
      (run (openStep hash supplier) [mulI m x y d,arithI isAdd k a b e] s) := by
  have h : x ≠ e ∧ y ≠ e ∧ a ≠ d ∧ b ≠ d ∧ d ≠ e := by
    simpa [canCrossArith] using checked
  rcases h with ⟨hx,hy,ha,hb,hd⟩
  cases isAdd <;>
    simp [TerminalRel,OpenRel,LocalRel,Zkc.Protocols.ScalarBytecode.Frames.CoreRel,allRegs,arithI,mulI,addI,run,
      openStep,serve,notify,update,mapStep,eventsOf,effect,request,Zkc.Protocols.ScalarBytecode.Execution.get,put,hx,hy,ha,hb]
  all_goals
    intro n
    by_cases hne : n = e
    · subst n; simp [Ne.symm hd]
    · simp [hne]

theorem rel_trans {S : Type} {a b c : Terminal (World S) Event}
    (hab : TerminalRel (OpenRel allRegs Eq) a b)
    (hbc : TerminalRel (OpenRel allRegs Eq) b c) :
    TerminalRel (OpenRel allRegs Eq) a c :=
  terminal_trans allRegs hab hbc

theorem exchange_context {S : Type} (supplier : Supplier S) (hash : Hash)
    (a b : Instr) (pre post : List Instr)
    (exchange : ∀ s, TerminalRel (OpenRel allRegs Eq)
      (run (openStep hash supplier) [a,b] s)
      (run (openStep hash supplier) [b,a] s)) (s : World S) :
    TerminalRel (OpenRel allRegs Eq)
      (run (openStep hash supplier) (pre ++ ([a,b] ++ post)) s)
      (run (openStep hash supplier) (pre ++ ([b,a] ++ post)) s) :=
  open_block_context supplier allRegs hash [a,b] [b,a] pre post exchange
    (fun i _ => all_safe i) s

end Zkc.Protocols.ScalarBytecode.Scheduling
